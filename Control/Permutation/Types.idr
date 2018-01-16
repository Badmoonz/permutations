module Control.Permutation.Types

import Data.List
import Data.Vect
import Data.Group
import Data.Vect.Lazy

import Data.Rel
import Decidable.Order
import Decidable.Decidable

import Control.Algebra

%default total

%access public export

||| This is something like `Vector k a`, except we restrict ourselves to only 1,...,n for `Permutation n`.
data Permutation : Nat -> Type where
  Nil : Permutation Z
  (::) : Fin (S n) -> Permutation n -> Permutation (S n)

implementation Eq (Permutation n) where
  (==) Nil Nil = True
  (==) (x :: xs) (y :: ys) = x == y && xs == ys

private
id : Permutation n
id {n=Z} = []
id {n=S _} = FZ :: id

||| This is essentially a group action. Given a permutation, we apply it to a vector.
sigma : Permutation n -> Vect n a -> Vect n a
sigma [] [] = []
sigma (p::ps) (x::xs) = insert (sigma ps xs) p
  where
    insert : Vect n a -> Fin (S n) -> Vect (S n) a
    insert l FZ = x::l
    insert (e::es) (FS k) = e :: insert es k

decideFinLTE : (m,n : Fin k) -> Dec(FinLTE m n)
decideFinLTE m n  with (decideLTE (finToNat m) (finToNat n))
  | Yes prf    = Yes (FromNatPrf prf)
  | No  disprf = No (\ (FromNatPrf prf) => disprf prf)


shiftFlip :  Fin n -> (m : Nat) -> Fin (n + m)
shiftFlip {n} f m = rewrite (plusCommutative n m) in Data.Fin.shift m f


shiftZ : Fin n -> Permutation n -> Permutation n
shiftZ {n = (S k)} FZ y = y
shiftZ {n = (S k)} (FS x) (a :: b) with (decideFinLTE (FS x) a) 
  shiftZ {n = (S k)} (FS x) (a :: b) | Yes FinLTE  = (pred a) :: shiftZ x b
  shiftZ {n = (S (S Z))} (FS FZ) (a :: b) | No _ = a :: b
  shiftZ {n = (S (S k))} (FS x) (a :: b) | No _ = a :: shiftZ (succ x) b

shift : (k : Nat) -> Fin n -> Permutation (n + k) -> Permutation (n + k)
shift {n} Z x p = let p' = replace (plusZeroRightNeutral n) p in
                  rewrite (plusZeroRightNeutral n) in (shiftZ x p')
shift (S k) FZ p = p
shift {n = S m} (S k) (FS x) (a :: b) with (decideFinLTE (FS (shiftFlip x (S k))) a)
  shift {n = S m} (S k) (FS x) (a :: b) | Yes _ = 
      let b' = replace (sym $ plusSuccRightSucc m k) b in
      let tail =  replace (plusSuccRightSucc m k) (shift k (weaken x) b') in (pred a) :: tail
  shift {n = S (S Z)}(S k) (FS FZ) (a :: b) | No _ = a :: b  
  shift {n = S (S m)} (S k) (FS x) (a :: b) | No _ = 
    let b' = replace (sym $ plusSuccRightSucc (S m) k) b in
    let tail =  replace (plusSuccRightSucc (S m) k) (shift k (weaken (succ x)) b') in a :: tail


thin : Fin (S n) -> Fin n -> Fin (S n)
thin  FZ i          = FS i
thin (FS j) FZ       = FZ
thin (FS j) (FS i)  = FS (thin j i)

indices : Permutation n -> Vect n (Fin n)
indices  []    = []
indices (p :: ps ) = p :: map (thin p) (indices ps)


toVector : Permutation n -> Vect n (Fin n)
toVector {n} p = sigma p (sequential n)
  where
    sequential : (n : Nat) -> Vect n (Fin n)
    sequential Z = []
    sequential (S k) = FZ :: map FS (sequential k)

-- fromVect : Vect n (Fin n) -> Permutation n
-- fromVect [] = []
-- fromVect (FZ::xs) = FZ::fromVect xs
-- fromVect ((FS FZ)::xs) = (FS FZ)::fromVect xs
-- fromVect ((FS k)::xs) = FZ::fromVect xs



delete : Fin (S n) -> Permutation (S n) -> Permutation n
delete FZ (j :: p) = p
delete {n=Z} (FS _)  _ = Nil
delete {n=S _} (FS i) (FZ :: p) = FZ :: delete i p
delete {n=S _} (FS i) (j :: p) = (either lifter id $ strengthen j) :: delete i p
  where
    lifter (FS k) = k
    lifter FZ = FZ

compose : Permutation n -> Permutation n -> Permutation n
compose Nil Nil = Nil
-- compose {n= S Z} [FZ] [FZ] = [FZ]
-- compose {n= S (S Z)} (FZ :: FZ :: []) (FZ :: FZ :: []) = (FZ :: FZ :: [])
-- compose {n= S (S Z)} (FZ :: FZ :: []) (FS FZ :: FZ :: []) = (FS FZ :: FZ :: [])
-- compose {n= S (S Z)} (FS FZ :: FZ :: [])  (FZ :: FZ :: [])  = (FS FZ :: FZ :: [])
-- compose {n= S (S Z)} (FS FZ :: FZ :: [])  (FS FZ :: FZ :: [])  = (FZ :: FZ :: [])
compose (i :: p) p' = (index i (toVector p')) :: (compose p (delete i p'))

export
invert : Permutation n -> Permutation n
invert Nil = Nil
invert p@(i :: is) = (index (i' p) (toVector p)) :: (delete (i' p) p)
  where
    i' p = Data.Vect.index i (toVector p)

implementation Show a => Show (Lazy a) where
  show (Delay x) = show x

implementation Eq a => Eq (Lazy a) where
  (==) (Delay x) (Delay y) = x == y

implementation Show (Fin n) where
  show FZ = "0"
  show (FS k) = show $ (finToNat k) + 1

implementation Semigroup (Permutation n) where
  (<+>) = compose

implementation Monoid (Permutation n) where
  neutral = id

implementation Group (Permutation n) where
  inverse = invert
