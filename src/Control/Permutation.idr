module Control.Permutation

import Data.List
import Data.Vect

%default total

%access public export

||| This is something like `Vector k a`, except we restrict ourselves to only 1,...,n for `Permutation n`.
data Permutation : Nat -> Type where
  Nil : Permutation Z
  (::) : Fin (S n) -> Permutation n -> Permutation (S n)

implementation Eq (Permutation n) where
  (==) Nil Nil = True
  (==) (x :: xs) (y :: ys) = x == y && xs == ys

||| This extends 'Monoid' by defining an inverse for every element.
interface (Monoid t) => Group (t : Type) where
  inverse : t -> t

||| This is essentially a group action. Given a permutation, we apply it to the vector.
||| We do not require that the vector's elements come from a set of size n.
sigma : Permutation n -> Vect n a -> Vect n a
sigma [] [] = []
sigma (p::ps) (x::xs) = insert (sigma ps xs) p
  where
    -- insert 'x' at the index specified.
    insert : Vect n a -> Fin (S n) -> Vect (S n) a
    insert l FZ = x::l
    insert [] (FS i) = [x]
    insert (e::es) (FS k) = e :: insert es k

toVector : Permutation n -> Vect n (Fin n)
toVector {n} p = sigma p (sequential n)
  where
    sequential : (n : Nat) -> Vect n (Fin n)
    sequential Z = []
    sequential (S k) = FZ :: map FS (sequential k)

factorial : Nat -> Nat
factorial Z = 1
factorial (S n) = (S n) * factorial n

private
natToFin : (n : Nat) -> Fin (S n)
natToFin Z = FZ
natToFin (S k) = FS k' where k' = natToFin k

private
finiteL : (n : Nat) -> Vect n (Fin (S n))
finiteL Z = Nil
finiteL n@(S m) = natToFin n :: (map weaken $ finiteL m)

||| Returns all permutations of a certain order.
export
getAll : (n : Nat) -> List (Permutation (S n)) -- Vect (factorial (S n)) (Permutation (S n))
getAll Z = ((FZ :: Nil) :: Nil)
getAll n@(S m) = (::) <$> (toList $ finiteL n) <*> (getAll m)

getElem : Permutation n -> Fin n -> Fin n
getElem p n = index n $ toVector p

||| Orbit generated by a given element.
orbit : Permutation (S n) -> Fin (S n) -> Stream (Fin (S n))
orbit p {n} i = i :: go i where
  go : Fin (S n) -> Stream (Fin (S n))
  go j = next :: go next where
    next : Fin (S n)
    next = getElem p j

||| Return the orbit of some permutation.
finOrbit : Permutation (S n) -> Fin (S n) -> List (Fin (S n))
finOrbit p {n} i = nub $ take n (orbit p i)

||| Return a list of disjoint cycles given a permutation
export
cycles : Permutation (S n) -> List (List (Fin (S n)))
cycles p {n} = nub . map sort . map (finOrbit p) . enumFromTo 0 $ (natToFin n)

private
getSwapsHelp : (List (Fin (S n)) -> List (Fin (S n), Fin (S n))) -> Permutation (S n) -> List (Fin (S n), Fin (S n))
getSwapsHelp f p = (>>= f) $ cycles p

||| Decompose a permutation into a product of swaps.
export
decompose : Permutation (S n) -> List (Fin (S n), Fin (S n))
decompose = getSwapsHelp overlappingPairs
  where
    overlappingPairs [] = []
    overlappingPairs [x] = []
    overlappingPairs (x::xs@(y::_))= (x, y) :: overlappingPairs xs

even : Nat -> Bool
even Z = True
even (S k) = odd k
  where
    odd : Nat -> Bool
    odd Z = False
    odd (S k) = even k

export
isEven : Permutation (S n) -> Bool
isEven = even . length . decompose

implementation Show (Fin n) where
  show FZ = "0"
  show (FS k) = show $ (finToNat k) + 1

implementation Show (Permutation n) where
  show p = show (toVector p)

-- Also nice: take a string, return a permutation! Or also "fromVector" would be v useful.

id : Permutation n
id {n=Z} = []
id {n=S _} = FZ :: id

reverse : Permutation n
reverse {n=Z} = []
reverse {n=S _} = last :: reverse

||| E.g. (1234) for S_4
cycle : Permutation n
cycle {n=Z} = []
cycle {n=S _} = FZ :: cycle

private
fill : Fin n -> Permutation n
fill FZ = id
fill (FS k) = FS (zeros k) :: fill k
  where zeros : Fin m -> Fin m
        zeros FZ = FZ
        zeros (FS _) = FZ

private
injects : Permutation m -> Permutation n -> Bool
injects {m} {n} _ _ = m < n

||| The permutation π_ij
export
pi : Fin n -> Fin n -> Permutation n
pi (FS j) (FS k) = FZ :: pi j k
pi (FS j) FZ = FS j :: fill j
pi FZ (FS k) = FS k :: fill k
pi FZ FZ = id

||| FIXME this is dumb.
compose : Permutation n -> Permutation n -> Permutation n
compose x Nil = x
compose Nil y = y
compose (FZ :: xs) (y :: ys) = y :: (compose xs ys)
compose (x :: xs) (FZ :: ys) = x :: (compose xs ys)
compose x y = ?f x y

-- TODO: apply a permutation to a vector, then use that to find an inverse?
invert : Permutation n -> Permutation n
invert Nil = Nil
invert x = ?f x

implementation Semigroup (Permutation n) where
  (<+>) = compose

implementation Monoid (Permutation n) where
  neutral = id

implementation Group (Permutation n) where
  inverse = invert

-- TODO Permutations are a type of lens!! And should be viewed as such.
