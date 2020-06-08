{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_HADDOCK hide #-}

module PopKey.Encoding where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Store as S
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Encoding as LT

import PopKey.Internal2

-- for instance decls only
import Data.Functor.Const
import Data.Functor.Identity
import Data.Graph (Graph)
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import Data.Map (Map)
import Data.Proxy
import Data.Ratio
import Data.Semigroup
import Data.Sequence (Seq)
import Data.Set (Set)
-- import Data.Tree (Tree) - no store instance available
import GHC.Generics
import GHC.Natural
import GHC.Int
import GHC.Word


-- | A simple wrapper to declare you do not want this data to be granularly partitioned by poppy.
newtype StoreBlob a = StoreBlob { unStoreBlob :: a }
  deriving (Generic,Eq,Ord,Show,Bounded)
  deriving newtype Enum


-- | Inverse law: @pkDecode . pkEncode = id@. Note that this encoding is explicitly for use with poppy - use your discretion (or better, test!) to decide the granularity with which you wish to use this encoding as opposed to the standard store encoding. Relying more on PopKeyEncoding will probably use less space, but at the cost of storing items in less contiguous memory.
class PopKeyEncoding a where
  type Shape a
  type Shape a = GShape (Rep a)
  shape :: I (Shape a)
  default shape :: (GPopKeyEncoding a (Rep a) , GShape (Rep a) ~ Shape a) => I (Shape a)
  shape = gshape @a @(Rep a)
  
  pkEncode :: a -> F' (Shape a) BS.ByteString
  default pkEncode :: (Generic a , GPopKeyEncoding a (Rep a) , GShape (Rep a) ~ Shape a) => a -> F' (Shape a) BS.ByteString
  pkEncode = gpkEncode @a @(Rep a) . from
  
  pkDecode :: F' (Shape a) BS.ByteString -> a
  default pkDecode :: (Generic a , GPopKeyEncoding a (Rep a) , GShape (Rep a) ~ Shape a) => F' (Shape a) BS.ByteString -> a
  pkDecode = to . gpkDecode @a @(Rep a)

class GPopKeyEncoding s f where
  type GShape f
  gshape :: I (GShape f)

  gpkEncode :: f a -> F' (GShape f) BS.ByteString
  gpkDecode :: F' (GShape f) BS.ByteString -> f a

instance GPopKeyEncoding s U1 where
  type GShape U1 = ()
  {-# INLINE gshape #-}
  gshape = ISingle
  {-# INLINE gpkEncode #-}
  gpkEncode = const (Single' mempty)
  {-# INLINE gpkDecode #-}
  gpkDecode = const U1


instance PopKeyEncoding a => GPopKeyEncoding s (K1 i a) where
  type GShape (K1 i a) = Shape a
  {-# INLINE gshape #-}
  gshape = shape @a
  {-# INLINE gpkEncode #-}
  gpkEncode (K1 x) = pkEncode x
  {-# INLINE gpkDecode #-}
  gpkDecode = K1 . pkDecode

instance (GPopKeyEncoding s a , GPopKeyEncoding s b) => GPopKeyEncoding s (a :*: b) where
  type GShape (a :*: b) = (GShape a , GShape b)
  {-# INLINE gshape #-}
  gshape = IProd (gshape @s @a) (gshape @s @b)
  {-# INLINE gpkEncode #-}
  gpkEncode (a :*: b) = Prod' (gpkEncode @s a) (gpkEncode @s b)
  {-# INLINE gpkDecode #-}
  gpkDecode (Prod' a b) = gpkDecode @s a :*: gpkDecode @s b

instance (GPopKeyEncoding s a , GPopKeyEncoding s b) => GPopKeyEncoding s (a :+: b) where
  type GShape (a :+: b) = Either (GShape a) (GShape b)
  {-# INLINE gshape #-}
  gshape = ISum (gshape @s @a) (gshape @s @b)
  {-# INLINE gpkEncode #-}
  gpkEncode (L1 x) = Sum' (Left (gpkEncode @s x))
  gpkEncode (R1 x) = Sum' (Right (gpkEncode @s x))
  {-# INLINE gpkDecode #-}
  gpkDecode (Sum' x) = case x of
    Left l -> L1 (gpkDecode @s l)
    Right r -> R1 (gpkDecode @s r)

instance GPopKeyEncoding s f => GPopKeyEncoding s (M1 i t f) where
  type GShape (M1 i t f) = GShape f
  {-# INLINE gshape #-}
  gshape = gshape @s @f
  {-# INLINE gpkEncode #-}
  gpkEncode (M1 x) = gpkEncode @s x
  {-# INLINE gpkDecode #-}
  gpkDecode = M1 . gpkDecode @s

---------------
-- INSTANCES --
---------------

instance S.Store a => PopKeyEncoding (StoreBlob a) where
  type Shape (StoreBlob a) = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode . unStoreBlob
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = StoreBlob do S.decodeEx x

instance PopKeyEncoding BS.ByteString where
  type Shape BS.ByteString = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single'
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = x

instance PopKeyEncoding LBS.ByteString where
  type Shape LBS.ByteString = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . LBS.toStrict
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = LBS.fromStrict x

instance S.Store a => PopKeyEncoding [ a ] where
  type Shape [ a ] = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = case S.size @a of
    S.ConstSize _ -> Single' . BS.concat . fmap S.encode
    _ -> Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode = \(Single' r) -> case S.size @a of
    S.ConstSize k -> S.decodeEx <$> chunks k r
    _ -> S.decodeEx r
    where
      chunks :: Int -> BS.ByteString -> [ BS.ByteString ]
      chunks i b
        | BS.length b == 0 = []
        | otherwise = let (x , xs) = BS.splitAt i b in x : chunks i xs

-- override text store instance since it uses Haskell's bloaded UTF16 encoding, which in this
-- context would be a terrible choice.
instance PopKeyEncoding T.Text where
  type Shape T.Text = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . T.encodeUtf8
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = T.decodeUtf8 x

instance PopKeyEncoding LT.Text where
  type Shape LT.Text = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . LBS.toStrict . LT.encodeUtf8
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = LT.decodeUtf8 (LBS.fromStrict x)

instance PopKeyEncoding Char where
  type Shape Char = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Double where
  type Shape Double = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Float where
  type Shape Float = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Int8 where
  type Shape Int8 = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Int16 where
  type Shape Int16 = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Int32 where
  type Shape Int32 = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Int64 where
  type Shape Int64 = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Int where
  type Shape Int = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Word8 where
  type Shape Word8 = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Word16 where
  type Shape Word16 = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Word32 where
  type Shape Word32 = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Word64 where
  type Shape Word64 = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Word where
  type Shape Word = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Integer where
  type Shape Integer = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Natural where
  type Shape Natural = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode . toInteger
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = fromInteger do S.decodeEx x

instance PopKeyEncoding Rational where
  type Shape Rational = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance S.Store a => PopKeyEncoding (Ratio a) where
  type Shape (Ratio a) = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding Graph where
  type Shape Graph = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance S.Store a => PopKeyEncoding (IntMap a) where
  type Shape (IntMap a) = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance PopKeyEncoding IntSet where
  type Shape IntSet = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x

instance (Ord a , S.Store a , S.Store b) => PopKeyEncoding (Map a b) where
  type Shape (Map a b) = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x  

instance S.Store a => PopKeyEncoding (Seq a) where
  type Shape (Seq a) = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x  

instance (Ord a , S.Store a) => PopKeyEncoding (Set a) where
  type Shape (Set a) = ()
  {-# INLINE shape #-}
  shape = ISingle
  {-# INLINE pkEncode #-}
  pkEncode = Single' . S.encode
  {-# INLINE pkDecode #-}
  pkDecode (Single' x) = S.decodeEx x  

instance PopKeyEncoding ()
instance PopKeyEncoding (Proxy a)
instance PopKeyEncoding Bool
instance PopKeyEncoding a => PopKeyEncoding (Maybe a)
instance PopKeyEncoding a => PopKeyEncoding (Min a)
instance PopKeyEncoding a => PopKeyEncoding (Max a)
instance PopKeyEncoding a => PopKeyEncoding (First a)
instance PopKeyEncoding a => PopKeyEncoding (Last a)
instance PopKeyEncoding a => PopKeyEncoding (Option a)
instance PopKeyEncoding a => PopKeyEncoding (Identity a)
instance PopKeyEncoding a => PopKeyEncoding (Sum a)
instance PopKeyEncoding a => PopKeyEncoding (Product a)
instance PopKeyEncoding a => PopKeyEncoding (Const a b)

instance (PopKeyEncoding a , PopKeyEncoding b) => PopKeyEncoding (Arg a b)
instance (PopKeyEncoding a , PopKeyEncoding b) => PopKeyEncoding (Either a b)

instance (PopKeyEncoding a , PopKeyEncoding b) => PopKeyEncoding (a , b)
instance (PopKeyEncoding a , PopKeyEncoding b , PopKeyEncoding c) => PopKeyEncoding (a , b , c)
instance (PopKeyEncoding a , PopKeyEncoding b , PopKeyEncoding c , PopKeyEncoding d) => PopKeyEncoding (a , b , c , d)
instance (PopKeyEncoding a , PopKeyEncoding b , PopKeyEncoding c , PopKeyEncoding d , PopKeyEncoding e) => PopKeyEncoding (a , b , c , d , e)


