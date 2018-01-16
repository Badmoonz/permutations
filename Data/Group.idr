module Data.Group

import Control.Algebra
%default total

%access public export

||| Stream of elements starting at some given element.
generate : (Group g) => g -> Stream g
generate g1 = h where
  h = assert_total $ neutral :: map (<+> g1) h

||| (Positive) integer exponentiation.
exp : (Group g) => (n : Nat) -> g -> g
exp n g = (head . drop n) (generate g)

||| Whether a group element is idempotent
idempotent : (Eq g, Semigroup g) => g -> Bool
idempotent x = x == (x <+> x)

||| Commutator of two elements.
commutator : (Group g) => g -> g -> g
commutator a b = inverse a <+> inverse b <+> a <+> b
