-- | PopKey gives you a static key-value storage structure backed by poppy indices. Construction is slow (multiple passes are made over the data to choose a good indexing structure), but querying should be fast, and space overhead should be much lower than Data.Map—on the data set I'm working with, Data.Map has 8.3x more overhead than PopKey—and the raw data transparently lives in an mmap'd region if you use @storage@, meaning the actual memory needed for usage is very low.
--
-- To construct, you will need @PopKeyEncoding@ instances. You may choose the granularity by which you encode your data types by choosing one of two auto-deriving patterns. The first, implicitly derived via GHC Generics, will use a granular encoding, indexing fields separately internally, while the second, derived via the @StoreBlob@ newtype, will encode the data as a single unit. Which is better depends on the situation, but as a general rule you should pack your constant-size structures into a single blob while letting your variable-sized fields use the granular encoding.
--
-- @
-- -- Encode @MyType@ with separate indices for the @[ String ]@ and @String@ fields.
-- data MyType = MyType [ String ] String
--   deriving (Generic,PopKeyEncoding)
-- @
-- 
-- @
-- -- Encode @Point@ as a blob, with all 3 @Int@ fields stored contiguously.
-- data Point = Point Int Int Int
--   deriving (Generic,Store) -- @Store@ here is from Data.Store
--   deriving PopKeyEncoding via StoreBlob Point
-- @
--
-- Reading from and storing to disk come pre-packaged, in such a way that loading your structure from the disk will strictly load the small index metadata while leaving the large raw data to be backed by mmap. You may use this functionality as follows:
--
-- @
-- myData :: PopKeyStore Point MyType
-- myData = storage "myindex.poppy"
-- 
-- main :: IO ()
-- main = do
--   -- your data
--   let dat :: [ (Point , MyType) ] = ...
-- 
--   -- store the indexed data to disk
--   storePopKey myData dat
-- 
--   -- load the indexed data from disk
--   pk :: PopKey Point MyType <- loadPopKey myData
-- 
--   ...
-- @
--
-- Poppy natively supports array-style indexing, so if your "key" set is simply the dense set of integers  @[ 0 .. n - 1 ]@ where @n@ is the number of items in your data set, key storage may be left implicit and elided entirely. In this API, when the distinction is necessary, working with such an implicit index is signified by a trailing ', e.g., @storage@ vs @storage'@.
--
-- Note that constant-factor space & time overhead is fairly high, so unless you have at least a couple thousand items, it is recommended to avoid PopKey. Once you have 10k+ items, the asymptotics should win out, and PopKey should perform well.

module PopKey
       ( type PopKey
       , (!)
       , PopKey.lookup
       , makePopKey
       , makePopKey'
       , foldrWithKey
       , foldlWithKey'
       , storage
       , storage'
       , StoreBlob(..)
       , PopKeyEncoding
       , PopKeyStore
       , PopKeyStore'
       , StorePopKey(..)
       ) where

import qualified Data.ByteString as BS
import Data.Store (encode , decodeEx)
import GHC.Word
import HaskellWorks.Data.FromForeignRegion
import System.IO

import PopKey.Internal2
import PopKey.Internal3
import PopKey.Encoding


{-# INLINE (!) #-}
-- | Lookup by a key known to be in the structure.
(!) :: PopKeyEncoding k => PopKey k v -> k -> v
(!) (PopKeyInt _ p vd) k = vd do rawq k p
(!) (PopKeyAny _ pv vd pk) k =
  vd do rawq (bin_search2 pk (pkEncode k) 0 (flength pk - 1)) pv

{-# INLINE lookup #-}
-- | Lookup by a key which may or may not be in the structure.
lookup :: PopKeyEncoding k => PopKey k v -> k -> Maybe v
lookup s@(PopKeyInt _ p vd) i = if i >= 0 && i < length s
  then Just (vd do rawq i p)
  else Nothing
lookup (PopKeyAny _ pv vd pk) k = do
  let i = bin_search2 pk (pkEncode k) 0 (flength pk - 1)
  if i == -1
     then Nothing
     else Just (vd do rawq i pv)


-- | You may use @storage@ to gain a pair of operations to serialize and read your structure from disk. This will be more efficient than if you naively serialize and store the data, as it strictly reads index metadata into memory while leaving the larger raw chunks to be backed by mmap.
storage :: (PopKeyEncoding k , PopKeyEncoding v)
        => FilePath -> PopKeyStore k v
storage p =
  PopKeyStore
    do \d -> do
         let (b1,b2) = bencode (toSPopKey (makePopKey d))
         withBinaryFile p WriteMode \fh -> do
           BS.hPut fh (encode (fromIntegral (BS.length b1) :: Word64))
           BS.hPut fh b1
           BS.hPut fh b2
    do fh <- openBinaryFile p ReadMode
       w64 :: Word64 <- decodeEx <$> BS.hGet fh 8
       let s = fromIntegral w64
       b1 <- BS.hGet fh s
       hClose fh
       b2 <- BS.drop (8 + s) <$> mmapFromForeignRegion p
       pure (fromSPopKey (bdecode (b1,b2)))

-- | Like @storage@, but for canonical integer keys.
storage' :: PopKeyEncoding v
         => FilePath -> PopKeyStore' v
storage' p = PopKeyStore'
  do \d -> do
       let (b1,b2) = bencode (toSPopKey (makePopKey' d))
       withBinaryFile p WriteMode \fh -> do
         BS.hPut fh (encode (fromIntegral (BS.length b1) :: Word64))
         BS.hPut fh b1
         BS.hPut fh b2
  do fh <- openBinaryFile p ReadMode
     w64 :: Word64 <- decodeEx <$> BS.hGet fh 8
     let s = fromIntegral w64
     b1 <- BS.hGet fh s
     hClose fh
     b2 <- BS.drop (8 + s) <$> mmapFromForeignRegion p
     pure (fromSPopKey' (bdecode (b1,b2)))

