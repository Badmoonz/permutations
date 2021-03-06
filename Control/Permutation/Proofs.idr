module Control.Permutation.Proofs

import Control.Permutation.Types
import Control.Permutation.Mod
import Data.Fin
import Data.Vect
import Control.Algebra
import Interfaces.Verified
import Data.Vect.Lazy


%access export
%default total

||| Proof that (n + 1)! >= n!
private
factorialIncr : (n : Nat) -> LTE (factorial n) (factorial (S n))
factorialIncr Z = lteRefl
factorialIncr n = lteAddRight (factorial n)

||| Proof that n! >= 1
export
factorialLTE : (n : Nat) -> LTE 1 (factorial n)
factorialLTE Z = lteRefl
factorialLTE (S k) = lteTransitive (factorialLTE k) (factorialIncr k)

add0Permutation : (a : Permutation 0) -> (b : Permutation 0) -> a <+> b =  Nil
add0Permutation [] [] = Refl

add1Permutation : (a : Permutation 1) -> (b : Permutation 1) -> a <+> b =  [FZ]
add1Permutation [FZ] [FZ] = Refl

assocZ : (l : Permutation 0) -> (c : Permutation 0) -> (r : Permutation 0) -> compose l (compose c r) = compose (compose l c) r
assocZ = proof
  intros
  rewrite (sym $ add0Permutation c r)
  rewrite (sym $ add0Permutation l c)
  rewrite (sym $ add0Permutation l [])
  rewrite (sym $ add0Permutation [] r)
  trivial

assocSZ : (l : Permutation 1) -> (c : Permutation 1) -> (r : Permutation 1) -> compose l (compose c r) = compose (compose l c) r
assocSZ = proof
  intros
  rewrite (sym $ add1Permutation c r)
  rewrite (sym $ add1Permutation l c)
  rewrite (sym $ add1Permutation l [FZ])
  rewrite (sym $ add1Permutation  [FZ] r)
  trivial

VerifiedSemigroup (Permutation n) where
  semigroupOpIsAssociative {n = Z} l c r =
    rewrite (add0Permutation c r) in
    rewrite (add0Permutation l c) in 
    rewrite (add0Permutation l []) in
    rewrite (add0Permutation [] r) in Refl
  -- semigroupOpIsAssociative {n = (S Z)} l c r = assocSZ l c r
  semigroupOpIsAssociative {n = S k} l c r = ?wtf
      
  

---------- Proofs ----------
  

-- Control.Permutation.Proofs.assocZ = 

-- Control.Permutation.Proofs.assocSZ = proof
--   intros
--   rewrite (sym $ add1Permutation c r)
--   rewrite (sym $ add1Permutation l c)
--   rewrite (sym $ add1Permutation l [FZ])
--   rewrite (sym $ add1Permutation  [FZ] r)
--   trivial


