# PopKey

PopKey gives you a static key-value storage structure backed by poppy indices. Construction is slow (multiple passes are made over the data to choose a good indexing structure), but querying should be fast, and space overhead should be much lower than Data.Map—on the data set I'm working with, Data.Map has 8.3x more overhead than PopKey—and the raw data transparently lives in an mmap'd region if you use `storage`, meaning the actual memory needed for usage is very low.

To construct, you will need `PopKeyEncoding` instances. You may choose the granularity by which you encode your data types by choosing one of two auto-deriving patterns. The first, implicitly derived via GHC Generics, will use a granular encoding, indexing fields separately internally, while the second, derived via the `StoreBlob` newtype, will encode the data as a single unit. Which is better depends on the situation, but as a general rule you should pack your constant-size structures into a single blob while letting your variable-sized fields use the granular encoding.

```haskell
-- Encode @MyType@ with separate indices for the @[ String ]@ and @String@ fields.
data MyType = MyType [ String ] String
  deriving (Generic,PopKeyEncoding)
```

```haskell
-- Encode @Point@ as a blob, with all 3 @Int@ fields stored contiguously.
data Point = Point Int Int Int
  deriving (Generic,Store) -- @Store@ here is from Data.Store
  deriving PopKeyEncoding via StoreBlob Point
```

Reading from and storing to disk come pre-packaged, in such a way that loading your structure from the disk will strictly load the small index metadata while leaving the large raw data to be backed by mmap. You may use this functionality as follows:

```haskell
myData :: PopKeyStore Point MyType
myData = storage "myindex.poppy"

main :: IO ()
main = do
  -- your data
  let dat :: [ (Point , MyType) ] = ...

  -- store the indexed data to disk
  storePopKey myData dat

  -- load the indexed data from disk
  pk :: PopKey Point MyType <- loadPopKey myData

  ...
```

Poppy natively supports array-style indexing, so if your "key" set is simply the dense set of integers  `[ 0 .. n - 1 ]` where `n` is the number of items in your data set, key storage may be left implicit and elided entirely. In this API, when the distinction is necessary, working with such an implicit index is signified by a trailing ', e.g., `storage` vs `storage'`.

