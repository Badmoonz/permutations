module Control.Permutation.Arity

import Data.Vect
import Control.Permutation

%default total

%access public export

||| Represent a function as a vector of types.
arityVect : (Vect n Type) -> (b : Type) -> Type
arityVect Nil b = b
arityVect (t::ts) b = t -> (arityVect ts b)

private
f : arityVect [Int, Int, Int] Bool 
f m n p = m + n == p

||| Use this to rewrite the result of 'permuteInputs'.
prf : (p : Permutation 3) -> (Int -> Int -> Int -> Bool) = arityVect (sigma p [Int, Int, Int]) Bool
prf (FZ::FZ::FZ::Nil) = Refl
prf ((FS (FS FZ))::(FS FZ)::FZ::Nil) = Refl
prf ((FS FZ)::(FS FZ)::FZ::Nil) = Refl
prf ((FS FZ)::FZ::FZ::Nil) = Refl
prf (FZ::(FS FZ)::FZ::Nil) = Refl
prf ((FS (FS FZ))::FZ::FZ::Nil) = Refl

||| Permutes inputs to a 3-ary function.
permuteInputs : (p : Permutation 3) -> arityVect [a, b, c] d -> arityVect (sigma p [a, b, c]) d
permuteInputs (FZ::FZ::FZ::Nil) f x y z = f x y z
permuteInputs ((FS (FS FZ))::(FS FZ)::FZ::Nil) f x y z = f z y x
permuteInputs ((FS FZ)::(FS FZ)::FZ::Nil) f x y z = f y z x
permuteInputs ((FS FZ)::FZ::FZ::Nil) f x y z = f y x z
permuteInputs (FZ::(FS FZ)::FZ::Nil) f x y z = f x z y
permuteInputs ((FS (FS FZ))::FZ::FZ::Nil) f x y z = f z x y

export
g : Int -> Int -> Int -> Bool
g = rewrite prf (pi 1 2) in permuteInputs (pi 1 2) f
