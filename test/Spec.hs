{-# OPTIONS_GHC -fno-warn-orphans #-}

import Data.Foldable
import qualified Data.Map as M
import GHC.Word
import Test.Hspec
import Test.QuickCheck

import PopKey


main :: IO ()
main = hspec $ do
  describe "PopKey" $ do
    it "sanity checks for fixed-size data" $ property \(xs :: [ Int ]) ->
      toList (makePopKey' xs) == xs

    it "sanity checks for fixed-size data" $ property \(xs :: [ (Int , Word8) ]) ->
      toList (makePopKey' xs) == xs

    it "sanity checks for var-size data" $ property \(xs :: [ [ Int ] ]) ->
      toList (makePopKey' xs) == xs

    it "sanity checks for var-size data" $ property \(xs :: [ String ]) ->
      toList (makePopKey' xs) == xs

    it "sanity checks for key data" $ property \(xs :: [ (Int , Word8) ]) -> do
      let m = M.fromList xs
          pk = makePopKey xs
          ks = fst <$> xs
      all (\k -> m M.! k == pk ! k) ks

