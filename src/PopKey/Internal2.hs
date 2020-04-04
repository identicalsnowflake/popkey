module PopKey.Internal2 where

import Control.Monad.ST
import Data.Bit as B
import qualified Data.ByteString as BS
import Data.Either
import Data.Foldable
import HaskellWorks.Data.RankSelect.CsPoppy
import qualified Data.Vector.Storable as SV
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector.Unboxed.Mutable as MUV
import GHC.Word
import HaskellWorks.Data.Bits.BitWise ((.?.))
import HaskellWorks.Data.RankSelect.Base.Rank0
import HaskellWorks.Data.RankSelect.Base.Rank1
import Unsafe.Coerce

import PopKey.Internal1


data F s a where
  Single :: !a -> F () a
  Prod :: !(F s1 a) -> !(F s2 a) -> F (s1 , s2) a
  Sum :: {-# UNPACK #-} !Word32 -> CsPoppy -> !(F s1 a) -> !(F s2 a) -> F (Either s1 s2) a
  -- cardinality / poppy ; poppy undefined if cardinality = 0
  -- 0 indicates storage in the left / 1 indicates storage in the right

data F' s a where
  Single' :: a -> F' () a
  Prod' :: (F' s1 a) -> (F' s2 a) -> F' (s1 , s2) a
  Sum' :: (Either (F' s1 a) (F' s2 a)) -> F' (Either s1 s2) a

instance Eq a => Eq (F' s a) where
  {-# INLINEABLE (==) #-}
  (==) (Single' x) (Single' y) = x == y
  (==) (Prod' x1 y1) (Prod' x2 y2) = (x1 == x2) && (y1 == y2)
  (==) (Sum' s1) (Sum' s2) = s1 == s2

instance Ord a => Ord (F' s a) where
  {-# INLINABLE (<=) #-}
  (<=) (Single' x) (Single' y) = x <= y
  (<=) (Prod' x1 y1) (Prod' x2 y2) = (x1 , y1) <= (x2 , y2)
  (<=) (Sum' s1) (Sum' s2) = s1 <= s2

flength :: F s PKPrim -> Int
flength (Single a) = pkLength a
flength (Prod x _) = flength x
flength (Sum l _ _ _) = fromIntegral l

data I s where
  ISingle :: I ()
  IProd :: I s1 -> I s2 -> I (s1 , s2)
  ISum :: I s1 -> I s2 -> I (Either s1 s2)

-- index must be valid
rawq :: Int -> F s PKPrim -> F' s BS.ByteString
rawq i = go
  where
    go :: F s PKPrim -> F' s BS.ByteString
    go (Single pk) = Single' (pkIndex pk i)
    go (Prod x y) = Prod' (go x) (go y)
    go (Sum _ pk l r) = do
      let b1pos = fromIntegral i + 1
      if pk .?. b1pos
         then Sum' (Right (rawq (fromIntegral (rank1 pk (fromIntegral b1pos) - 1)) r))
         else Sum' (Left (rawq (fromIntegral (rank0 pk (fromIntegral b1pos) - 1)) l))

-- returns @-1@ if not found
{-# INLINABLE bin_search2 #-}
bin_search2 :: F s PKPrim -> F' s BS.ByteString -> Int -> Int -> Int
bin_search2 vs q = go
  where
    go :: Int -> Int -> Int
    go l r
      | r >= l = do
          let m = l + (r - l) `div` 2
              p = rawq m vs
          if p > q
             then go l (m - 1)
             else if p == q
                     then m
                     else go (m + 1) r
      | otherwise = -1

{-# INLINE query #-}
query :: forall a s . (F' s BS.ByteString -> a) -> F s PKPrim -> Int -> a
query d pk i = d (rawq i pk)

{-# INLINABLE construct #-}
construct :: forall a s f . Foldable f
          => I s
          -> (a -> F' s BS.ByteString) 
          -> f a
          -> F s PKPrim
construct = \s e f -> if length f == 0
  then fancyZero s
  else go s (foldr ((:) . e) mempty f)
  where
    fancyZero :: forall t . I t -> F t PKPrim
    fancyZero ISingle = Single (ConstSize mempty 0 0)
    fancyZero (IProd x y) = Prod (fancyZero x) (fancyZero y)
    fancyZero (ISum x y) = Sum 0 undefined (fancyZero x) (fancyZero y)

    go :: forall t . I t -> [ F' t BS.ByteString ] -> F t PKPrim
    go ISingle = \ys -> Single (makePK (fromSingle <$> ys))
      where
        fromSingle :: F' () BS.ByteString -> BS.ByteString
        fromSingle (Single' x) = x
    go (IProd s1 s2) = \ys -> do
      let (as , bs) = unzip (fromProd <$> ys)
      Prod (go s1 as) (go s2 bs)
      where
        fromProd :: forall s1 s2 . F' (s1 , s2) BS.ByteString
                 -> (F' s1 BS.ByteString , F' s2 BS.ByteString)
        fromProd (Prod' x y) = (x , y)
    go (ISum s1 s2) = \ys -> do
      let zs = fromSum <$> ys
          l = length ys

          bv :: UV.Vector Bit = runST do
            v <- MUV.new l

            for_ (zip [ 0 .. ] zs) \(i,x) -> case x of
              Left _ -> pure ()
              Right _ -> MUV.unsafeWrite v i 1

            UV.unsafeFreeze v

          uv64 :: UV.Vector Word64 = unsafeCoerce do cloneToWords bv
          sv64 :: SV.Vector Word64 = SV.convert uv64

          !(ppy :: CsPoppy) = makeCsPoppy sv64

          (as , bs) = partitionEithers zs
      
      Sum (fromIntegral l) ppy (f s1 as) (f s2 bs)
      where
        f s [] = fancyZero s
        f s xs = go s xs
        
        fromSum :: forall s1 s2 . F' (Either s1 s2) BS.ByteString
                -> Either (F' s1 BS.ByteString) (F' s2 BS.ByteString)
        fromSum (Sum' x) = x

