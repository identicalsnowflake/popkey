{-# LANGUAGE AllowAmbiguousTypes #-}

module PopKey.Internal3 where

import qualified Data.ByteString as BS
import HaskellWorks.Data.RankSelect.CsPoppy
import qualified HaskellWorks.Data.RankSelect.CsPoppy.Internal.Alpha0 as A0
import qualified HaskellWorks.Data.RankSelect.CsPoppy.Internal.Alpha1 as A1
import Data.Profunctor
import Data.Store (encode , decodeEx)
import GHC.Generics hiding (R)
import GHC.Word
import Unsafe.Coerce

import PopKey.Internal1
import PopKey.Internal2
import PopKey.Encoding


data PopKey k v =
    forall s . PopKeyInt !(F s PKPrim) (F' s BS.ByteString -> v) (k -> Int)
  | forall s1 s2 . PopKeyAny !(F s1 PKPrim) (F' s1 BS.ByteString -> v) (k -> F' s2 BS.ByteString) !(F s2 PKPrim)

instance Functor (PopKey k) where
  {-# INLINE fmap #-}
  fmap f (PopKeyInt p d e) = PopKeyInt p (f . d) e
  fmap f (PopKeyAny pv d e pk) = PopKeyAny pv (f . d) e pk

instance Profunctor PopKey where
  {-# INLINE dimap #-}
  dimap f g (PopKeyInt p d e) = PopKeyInt p (g . d) (e . f)
  dimap f g (PopKeyAny pv d e pk) = PopKeyAny pv (g . d) (e . f) pk

instance Foldable (PopKey k) where
  {-# INLINE foldr #-}
  foldr f z p@(PopKeyInt pr vd _) = foldr (\i -> f (vd do rawq i pr)) z [ 0 .. (length p - 1) ]
  foldr f z p@(PopKeyAny pr vd _ _) = foldr (\i -> f (vd do rawq i pr)) z [ 0 .. (length p - 1) ]

  {-# INLINE length #-}
  length (PopKeyInt p _ _) = flength p
  length (PopKeyAny _ _ _ p) = flength p

-------------------------------------------
-- PopKey serialization for mmap loading --
-------------------------------------------

class BiSerialize a where
  bencode :: a -> (BS.ByteString , BS.ByteString)
  default bencode :: (Generic a , GBiSerialize a (Rep a)) => a -> (BS.ByteString , BS.ByteString)
  bencode = gbencode @a @(Rep a) . from
  
  bdecode :: (BS.ByteString , BS.ByteString) -> a
  default bdecode :: (Generic a , GBiSerialize a (Rep a)) => (BS.ByteString , BS.ByteString) -> a
  bdecode = to . gbdecode @a @(Rep a)

class GBiSerialize s f where
  gbencode :: f a -> (BS.ByteString , BS.ByteString)
  gbdecode :: (BS.ByteString , BS.ByteString) -> f a

instance GBiSerialize s U1 where
  {-# INLINE gbencode #-}
  gbencode = const mempty
  {-# INLINE gbdecode #-}
  gbdecode = const mempty

instance BiSerialize a => GBiSerialize s (K1 i a) where
  {-# INLINE gbencode #-}
  gbencode (K1 x) = bencode x
  {-# INLINE gbdecode #-}
  gbdecode = K1 . bdecode

instance (GBiSerialize s a , GBiSerialize s b) => GBiSerialize s (a :*: b) where
  {-# INLINE gbencode #-}
  gbencode (a :*: b) = do
    let (a1 , a2) = gbencode @s a
        (b1 , b2) = gbencode @s b
    (encode (a1 , b1) , encode (a2 , b2))
  {-# INLINE gbdecode #-}
  gbdecode (r1 , r2) = do
    let (a1 , b1) = decodeEx r1
        (a2 , b2) = decodeEx r2
    gbdecode @s (a1 , a2) :*: gbdecode @s (b1 , b2)

instance (GBiSerialize s a , GBiSerialize s b) => GBiSerialize s (a :+: b) where
  gbencode (L1 x) = do
    let (b1 , b2) = gbencode @s x
    (encode False <> b1 , b2)
  gbencode (R1 x) = do
    let (b1 , b2) = gbencode @s x
    (encode True <> b1 , b2)
  gbdecode ((BS.splitAt 1 -> (b , b1)) , b2) =
    if decodeEx b
       then R1 (gbdecode @s (b1 , b2))
       else L1 (gbdecode @s (b1 , b2))

instance GBiSerialize s f => GBiSerialize s (M1 i t f) where
  {-# INLINE gbencode #-}
  gbencode (M1 x) = gbencode @s x
  {-# INLINE gbdecode #-}
  gbdecode = M1 . gbdecode @s

instance BiSerialize CsPoppy where
  bencode (CsPoppy bv (A0.CsPoppyIndex a01 a02) (A1.CsPoppyIndex a11 a12)) =
    (,) do encode (a01 , a02 , a11 , a12)
        do encode bv
  bdecode (bs , bv) = do
    let (a01 , a02 , a11 , a12) = decodeEx bs
    CsPoppy (decodeEx bv) (A0.CsPoppyIndex a01 a02) (A1.CsPoppyIndex a11 a12)

-- newtype L a = L a deriving (Generic)
-- newtype R a = R a deriving (Generic)

-- instance Store a => BiSerialize (L a) where
--   {-# INLINE bencode #-}
--   bencode (L x) = (encode x , mempty)
--   {-# INLINE bdecode #-}
--   bdecode (b , _) = L do decodeEx b

-- instance Store a => BiSerialize (R a) where
--   {-# INLINE bencode #-}
--   bencode (R x) = (mempty , encode x)
--   {-# INLINE bdecode #-}
--   bdecode (_ , b) = R do decodeEx b

instance BiSerialize BS.ByteString where
  {-# INLINE bencode #-}
  bencode x = (mempty , x)
  {-# INLINE bdecode #-}
  bdecode (_ , x) = x

instance BiSerialize Word32 where
  {-# INLINE bencode #-}
  bencode x = (encode x , mempty)
  {-# INLINE bdecode #-}
  bdecode (x , _) = decodeEx x

instance BiSerialize PKPrim
instance BiSerialize a => BiSerialize (Maybe a)
instance (BiSerialize a , BiSerialize b) => BiSerialize (a , b)

-- poppy is undefined here if the first value is 0
data Custom = Custom {-# UNPACK #-} !Word32 CsPoppy

instance BiSerialize Custom where
  bencode (Custom l ppy) = do
    let x :: Maybe (Word32 , CsPoppy) =
          if l == 0
             then Nothing
             else Just (l , ppy)
    bencode x
  bdecode r = case bdecode r of
    Nothing -> Custom 0 undefined
    Just (l , ppy) -> Custom l ppy

-- serializable format for F
data SF a =
    SSingle a
  | SProd !(SF a) !(SF a)
  | SSum !Custom !(SF a) !(SF a)
  deriving (Generic,BiSerialize)

fromF :: F s a -> SF a
fromF (Single x) = SSingle x
fromF (Prod x y) = SProd (fromF x) (fromF y)
fromF (Sum l ppy x y) = SSum (Custom l ppy) (fromF x) (fromF y)

-- there's a reason this module is internal
toF :: SF a -> F s a
toF (SSingle x) = unsafeCoerce do Single x
toF (SProd x y) = unsafeCoerce do Prod (toF x) (toF y)
toF (SSum (Custom l ppy) x y) = unsafeCoerce do Sum l ppy (toF x) (toF y)

data SPopKey k v =
    SPopKeyInt !(SF PKPrim)
  | SPopKeyAny !(SF PKPrim) !(SF PKPrim)
  deriving (Generic,BiSerialize)

toSPopKey :: PopKey k v -> SPopKey k v
toSPopKey (PopKeyInt p _ _) = SPopKeyInt (fromF p)
toSPopKey (PopKeyAny p1 _ _ p2) = SPopKeyAny (fromF p1) (fromF p2)

fromSPopKey :: forall k v . (PopKeyEncoding k , PopKeyEncoding v) => SPopKey k v -> PopKey k v
fromSPopKey (SPopKeyInt p) = PopKeyInt (toF p) (pkDecode @v) (unsafeCoerce id)
fromSPopKey (SPopKeyAny pv pk) = PopKeyAny (toF pv) (pkDecode @v) (pkEncode @k) (toF pk)

fromSPopKey' :: PopKeyEncoding v => SPopKey Int v -> PopKey Int v
fromSPopKey' (SPopKeyInt p) = PopKeyInt (toF p) pkDecode (unsafeCoerce id)
fromSPopKey' _ = error "Incorrect PopKey type: expected Int."

data PopKeyStore k v =
  PopKeyStore (forall f . Foldable f => f (k , v) -> IO ())
              (IO (PopKey k v))

data PopKeyStore' v =
  PopKeyStore' (forall f . Foldable f => f v -> IO ())
                 (IO (PopKey Int v))

class StorePopKey k v f | f -> k , f -> v where
  type Input f
  storePopKey :: Foldable t => f -> t (Input f) -> IO ()
  loadPopKey :: f -> IO (PopKey k v)

instance StorePopKey k v (PopKeyStore k v) where
  type Input (PopKeyStore k v) = (k , v)
  storePopKey (PopKeyStore a _) = a
  loadPopKey (PopKeyStore _ b) = b

instance StorePopKey Int v (PopKeyStore' v) where
  type Input (PopKeyStore' v) = v
  storePopKey (PopKeyStore' a _) = a
  loadPopKey (PopKeyStore' _ b) = b

