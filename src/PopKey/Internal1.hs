{-# OPTIONS_HADDOCK hide #-}

module PopKey.Internal1 where

import Control.Monad.ST
import Data.Bit as B
import qualified Data.ByteString as BS
import Data.Foldable
import Data.STRef
import qualified Data.Vector.Storable as SV
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector.Unboxed.Mutable as MUV
import GHC.Generics (Generic)
import GHC.Word
import HaskellWorks.Data.Bits.PopCount.PopCount1
import qualified HaskellWorks.Data.RankSelect.Base.Select1
import HaskellWorks.Data.RankSelect.CsPoppy
import Unsafe.Coerce


data PKPrim =
    ConstSize !BS.ByteString {-# UNPACK #-} !Word32 {-# UNPACK #-} !Word32 -- raw / item size / item count
  | Var !CsPoppy !BS.ByteString {-# UNPACK #-} !Word32 {-# UNPACK #-} !Word32 -- poppy / raw / min size / step size
  deriving (Generic,Eq)


-- 0-based indexing, for my sanity
{-# INLINE select1' #-}
select1' :: CsPoppy -> Int -> Int
select1' p i =
  fromIntegral (HaskellWorks.Data.RankSelect.Base.Select1.select1 p (fromIntegral i + 1)) - 1

{-# INLINABLE pkLength #-}
pkLength :: PKPrim -> Int
pkLength (ConstSize _ _ l) = fromIntegral l
pkLength (Var p _ _ _) = (fromIntegral . (\x -> x - 1) . popCount1) p

{-# INLINABLE pkIndex #-}
pkIndex :: PKPrim -> Int -> BS.ByteString
pkIndex (ConstSize r (fromIntegral -> s) _) i = if s == 0 then mempty else BS.take s (BS.drop (i * s) r)
pkIndex (Var p r (fromIntegral -> minSize) (fromIntegral -> step)) i = do
  let o :: Int = select1' p i
      d :: Int = select1' p (i + 1) - o

  BS.take (minSize + step * (d - 1)) (BS.drop (step * (o - i) + i * minSize) r)

makePK :: [ BS.ByteString ] -> PKPrim
makePK [] = ConstSize mempty 0 0
makePK bs = runST do
  let minSize = minimum (BS.length <$> bs)
      step = foldl' (\a x -> gcd (BS.length x - minSize) a) (BS.length (head bs) - minSize) bs

  if all ((minSize==) . BS.length) bs
     then pure do ConstSize (BS.concat bs) (fromIntegral minSize) (fromIntegral do length bs)
     else do
       -- raw indexing vector
       bv :: UV.Vector Bit <- do
         v <- MUV.new do 1 + foldl' (\a x -> a + 1 + (BS.length x - minSize) `div` step) 0 bs
         MUV.unsafeWrite v 0 1

         base_ref <- newSTRef 0

         for_ bs \x -> do
           let d = ((BS.length x - minSize) `div` step) + 1
           b <- readSTRef base_ref
           MUV.unsafeWrite v (b + d) 1
           writeSTRef base_ref (b + d)

         UV.unsafeFreeze v

       let uv64 :: UV.Vector Word64 = unsafeCoerce do cloneToWords bv
           sv64 :: SV.Vector Word64 = SV.convert uv64

           ppy :: CsPoppy = makeCsPoppy sv64

       pure $ Var ppy (BS.concat bs) (fromIntegral minSize) (fromIntegral step)

-- returns @-1@ if not found
{-# INLINABLE bin_search #-}
bin_search :: PKPrim -> BS.ByteString -> Int -> Int -> Int
bin_search vs q = go
  where
    go :: Int -> Int -> Int
    go l r
      | r >= l = do
          let m = l + (r - l) `div` 2
              p = pkIndex vs m
          if p > q
             then go l (m - 1)
             else if p == q
                     then m
                     else go (m + 1) r
      | otherwise = -1

