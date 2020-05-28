{-# OPTIONS_GHC -fno-warn-orphans #-}

import Data.Foldable
import qualified Data.Map as M
import qualified Data.Store as S
import GHC.Word
import Test.Hspec
import Test.QuickCheck

import PopKey


scode :: S.Store a => a -> a
scode = S.decodeEx . S.encode

main :: IO ()
main = hspec $ do
  describe "PopKey" $ do
    it "sanity checks for fixed-size data" $ property \(xs :: [ Int ]) ->
      toList (scode $ fmap (+1) $ makePopKey' xs) == fmap (+1) xs

    it "sanity checks for fixed-size data" $ property \(xs :: [ (Int , Word8) ]) ->
      toList (scode $ makePopKey' xs) == xs

    it "sanity checks for var-size data" $ property \(xs :: [ [ Int ] ]) ->
      toList (scode $ makePopKey' xs) == xs

    it "sanity checks for var-size data" $ property \(xs :: [ String ]) ->
      toList (scode $ makePopKey' xs) == xs

    it "sanity checks for key data" $ property \(xs :: [ (String , Int) ]) -> do
      let m = M.fromList xs
          pk = makePopKey xs
          ks = fst <$> xs
      all (\k -> m M.! k == pk ! k) ks

