module Test.Spec

import Specdris.Spec
import Control.Permutation
import Control.Permutation.Arity
import Data.Vect

import Control.Algebra

export
specSuite : IO ()
specSuite =
  spec $ do

    describe "Monad Laws" $ do 
        it "should Neutral (1/2)" $ do  
          trivial <+> neutral `shouldBe` neutral <+> trivial
        it "should Neutral (2/2)" $ do  
          circ <+> neutral `shouldBe` neutral <+> circ
    describe "circulate" $ do
      it "should work (1/2)" $ do
        show circ `shouldBe` "(01234)"
      it "should work (2/2)" $ do
        sigma circulate [0, 1, 2, 3, 4] `shouldBe` [1, 2, 3, 4, 0]
    describe "isEven" $ do
      it "should work" $ do
        map isEven ps `shouldBe` [False, True]
      it "should work with exp" $ do
        map (isEven . exp 2) ps `shouldBe` [True, True]
    describe "trivial" $ do
      it "should permute a vector" $
        toVector trivial `shouldBe` [0, 3, 2, 1]
      it "work on reversed" $
        toVector reverse `shouldBe` [3, 2, 1, 0]
    describe "cycle precursor" $ do
      it "should give a fixNat function" $
        fixNat trivial 1 `shouldBe` 3
      it "should give a orbit function" $
        finOrbit trivial 1 `shouldBe` [1, 3]
    describe "show" $ do
      it "should pretty-print for n < 10" $ do
        show trivial `shouldBe` "(13)"
    describe "compose" $ do
      it "should compose nicely (1/2)" $ do
        toVector (trivial <+> disjoint) `shouldBe` [2, 3, 0, 1]
      it "should compose nicely (2/2)" $ do
        show (trivial <+> swap) `shouldBe` "(02)(13)"
    describe "invert" $ do
      it "should invert a permutation" $
        inverse trivial `shouldBe` trivial
      it "should satisfy x⁻¹x=e" $
        inverse trivial <+> trivial `shouldBe` neutral
        
        -- TODO property test: composing disjoint swaps should commute!
        -- Also associativity.
  where trivial : Permutation 4
        trivial = pi (FS 0) (FS 2)
        disjoint : Permutation 4
        disjoint = pi (FZ) (FS 1)
        big : Permutation 11
        big = pi (FS 0) (FS 9)
        swap : Permutation 4
        swap = pi FZ (FS 1)
        ps : Vect 2 (Permutation 2)
        ps = enumerateStrict
        circ : Permutation 5
        circ = circulate
