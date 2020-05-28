{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_HADDOCK hide #-}

module PopKey.Internal3 where

import Data.Bifunctor
import qualified Data.ByteString as BS
import Data.Functor.Contravariant
import HaskellWorks.Data.RankSelect.CsPoppy
import qualified HaskellWorks.Data.RankSelect.CsPoppy.Internal.Alpha0 as A0
import qualified HaskellWorks.Data.RankSelect.CsPoppy.Internal.Alpha1 as A1
import Data.Foldable
import Data.List (sortOn)
import Data.Store
import GHC.Generics hiding (R)
import GHC.Word
import Unsafe.Coerce

import PopKey.Internal1
import PopKey.Internal2
import PopKey.Encoding


-- Bool here is whether the decoding function is the canonical decoding function from when
-- the index was first built. it allows the Store instance to skip re-building the structure
-- before serialization. the Functor instance should still be observably-valid from the safe public API,
-- at least modulo bottoms and the fact that mapping the identity will cause performance artefacts.
data PopKey k v where
  PopKeyInt :: forall s v . Bool -> F s PKPrim -> (F' s BS.ByteString -> v) -> PopKey Int v
  PopKeyAny :: forall s k v . Bool -> F s PKPrim -> (F' s BS.ByteString -> v) -> F (Shape k) PKPrim -> PopKey k v

instance Functor (PopKey k) where
  {-# INLINE fmap #-}
  fmap f (PopKeyInt _ p d) = PopKeyInt False p (f . d)
  fmap f (PopKeyAny _ pv d pk) = PopKeyAny False pv (f . d) pk

instance Foldable (PopKey k) where
  {-# INLINE foldr #-}
  foldr f z p@(PopKeyInt _ pr vd) = foldr (\i -> f (vd do rawq i pr)) z [ 0 .. (length p - 1) ]
  foldr f z p@(PopKeyAny _ pr vd _) = foldr (\i -> f (vd do rawq i pr)) z [ 0 .. (length p - 1) ]

  {-# INLINE length #-}
  length (PopKeyInt _ p _) = flength p
  length (PopKeyAny _ _ _ p) = flength p

{-# INLINABLE foldrWithKey #-}
foldrWithKey :: PopKeyEncoding k => (k -> v -> b -> b) -> b -> PopKey k v -> b
foldrWithKey f z p@(PopKeyInt _ pr vd) =
  foldr do \i -> f i (vd do rawq i pr)
        do z
        do [ 0 .. (length p - 1) ]
foldrWithKey f z p@(PopKeyAny _ pr vd pk) =
  foldr do \i -> f (pkDecode $ rawq i pk) (vd do rawq i pr)
        do z
        do [ 0 .. (length p - 1) ]

{-# INLINABLE foldlWithKey' #-}
foldlWithKey' :: PopKeyEncoding k => (a -> k -> v -> a) -> a -> PopKey k v -> a
foldlWithKey' f z p@(PopKeyInt _ pr vd) =
  foldl' do \a i -> f a i (vd do rawq i pr)
         do z
         do [ 0 .. (length p - 1) ]
foldlWithKey' f z p@(PopKeyAny _ pr vd pk) =
  foldl' do \a i -> f a (pkDecode $ rawq i pk) (vd do rawq i pr)
         do z
         do [ 0 .. (length p - 1) ]  

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
toSPopKey (PopKeyInt _ p _) = SPopKeyInt (fromF p)
toSPopKey (PopKeyAny _ p1 _ p2) = SPopKeyAny (fromF p1) (fromF p2)

fromSPopKey :: forall k v . (PopKeyEncoding k , PopKeyEncoding v) => SPopKey k v -> PopKey k v
fromSPopKey (SPopKeyInt p) = unsafeCoerce (PopKeyInt True (toF p) (pkDecode @v))
fromSPopKey (SPopKeyAny pv pk) = PopKeyAny True (toF pv) (pkDecode @v) (toF pk)

fromSPopKey' :: PopKeyEncoding v => SPopKey Int v -> PopKey Int v
fromSPopKey' (SPopKeyInt p) = PopKeyInt True (toF p) pkDecode
fromSPopKey' _ = error "Incorrect PopKey type: expected Int."

-- re-encode using whatever the current value encoding is
{-# INLINABLE normalise #-}
normalise :: (PopKeyEncoding k , PopKeyEncoding v) => PopKey k v -> PopKey k v
normalise p@(PopKeyInt True _ _) = p
normalise p@(PopKeyInt _ _ _) =
  makePopKey' (toList p)
normalise p@(PopKeyAny True _ _ _) = p
normalise p@(PopKeyAny _ _ _ _) =
  makePopKey (foldrWithKey (\k v -> (:) (k,v)) [] p)

toStoreEnc :: (PopKeyEncoding k , PopKeyEncoding v) => PopKey k v -> (Bool , BS.ByteString , BS.ByteString)
toStoreEnc (normalise -> p) = do
  let (b1 , b2) = bencode (toSPopKey p)
  case p of
    PopKeyInt _ _ _ -> (True , b1 , b2)
    PopKeyAny _ _ _ _ -> (False , b1 , b2)

fromStoreEnc :: forall k v . (PopKeyEncoding k , PopKeyEncoding v) => (Bool , BS.ByteString , BS.ByteString) -> PopKey k v
fromStoreEnc (True , b1 , b2) = unsafeCoerce (fromSPopKey' (bdecode (b1 , b2) :: SPopKey Int v))
fromStoreEnc (False , b1 , b2) = fromSPopKey (bdecode (b1 , b2))

instance (PopKeyEncoding k , PopKeyEncoding v) => Store (PopKey k v) where
  size = contramap toStoreEnc size
  peek = fmap fromStoreEnc peek
  poke = poke . toStoreEnc

{-# INLINE makePopKey #-}
-- | Create a poppy-backed key-value storage structure.
makePopKey :: forall f k v . (Foldable f , PopKeyEncoding k , PopKeyEncoding v) => f (k , v) -> PopKey k v
makePopKey =
  makePopKeyWithEncoding (shape @k) (shape @v) (pkEncode @v) (pkDecode @v)
  where
    makePopKeyWithEncoding :: Foldable f
                           => I (Shape k)
                           -> I s -> (v -> F' s BS.ByteString) -> (F' s BS.ByteString -> v)
                           -> f (k , v)
                           -> PopKey k v
    makePopKeyWithEncoding ik iv ev dv xs = do
      let (ks , vs) = unzip (lastv $ sortOn fst (foldr ((:) . first pkEncode) [] xs))
      PopKeyAny do True
                do construct iv ev vs
                do dv
                do construct ik id ks
      where
        -- for duplicate keys, use the last value
        lastv :: forall a b . Ord a => [(a,b)] -> [(a,b)]
        lastv [] = []
        lastv [ x ] = [ x ]
        lastv (x : ys@(y : _)) =
          if fst x == fst y
             then lastv ys
             else x : lastv ys

-- | Create a poppy-backed structure with elements implicitly indexed by their position.
{-# INLINE makePopKey' #-}
makePopKey' :: forall f v . (Foldable f , PopKeyEncoding v) => f v -> PopKey Int v
makePopKey' = go (shape @v) (pkEncode @v) (pkDecode @v) . foldr (:) []
  where
    go :: I s -> (a -> F' s BS.ByteString) -> (F' s BS.ByteString -> a) -> [ a ] -> PopKey Int a
    go i e d xs =
      PopKeyInt do True
                do construct i e xs
                do d

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

