{-# LANGUAGE DeriveFoldable  #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

-- | Merkle tree implementation.
--
-- See <https://tools.ietf.org/html/rfc6962>.
module Pos.Merkle
       ( MerkleRoot(..)
       , MerkleTree (..)
       , mtRoot
       , mkMerkleTree

       , MerkleNode (..)
       , mkBranch
       , mkLeaf
       ) where

import qualified Data.ByteString.Lazy as BL (toStrict)
import           Data.Coerce          (coerce)
import qualified Data.Foldable        as Foldable
import           Data.SafeCopy        (base, deriveSafeCopySimple)
import           Prelude              (Show (..))
import           Universum            hiding (show)

import           Data.ByteArray       (ByteArrayAccess, convert)
import           Pos.Binary.Class     (Bi, encode)
import           Pos.Binary.Crypto    ()
import           Pos.Crypto           (Hash, hashRaw)
import           Pos.Util.Binary      (Raw)

-- | Data type for root of merkle tree.
newtype MerkleRoot a = MerkleRoot
    { getMerkleRoot :: Hash Raw  -- ^ returns root 'Hash' of Merkle Tree
    } deriving (Show, Eq, Ord, Generic, ByteArrayAccess, Typeable)

-- This gives a “redundant constraint” warning due to
-- https://github.com/acid-state/safecopy/issues/46.
deriveSafeCopySimple 0 'base ''MerkleRoot

-- | Straightforward merkle tree representation in Haskell.
data MerkleTree a = MerkleEmpty | MerkleTree Word32 (MerkleNode a)
    deriving (Eq, Generic)

instance Foldable MerkleTree where
    foldMap _ MerkleEmpty      = mempty
    foldMap f (MerkleTree _ n) = foldMap f n

    null MerkleEmpty = True
    null _           = False

    length MerkleEmpty      = 0
    length (MerkleTree s _) = fromIntegral s

instance Show a => Show (MerkleTree a) where
  show tree = "Merkle tree: " <> show (toList tree)

data MerkleNode a
    = MerkleBranch { mRoot  :: MerkleRoot a
                   , mLeft  :: MerkleNode a
                   , mRight :: MerkleNode a}
    | MerkleLeaf { mRoot :: MerkleRoot a
                 , mVal  :: a}
    deriving (Eq, Show, Generic)

instance Foldable MerkleNode where
    foldMap f x = case x of
        MerkleLeaf{mVal}            -> f mVal
        MerkleBranch{mLeft, mRight} ->
            foldMap f mLeft `mappend` foldMap f mRight

deriveSafeCopySimple 0 'base ''MerkleNode
deriveSafeCopySimple 0 'base ''MerkleTree

mkLeaf :: Bi a => a -> MerkleNode a
mkLeaf a =
    MerkleLeaf
    { mVal  = a
    , mRoot = MerkleRoot $ coerce $
              hashRaw (one 0 <> BL.toStrict (encode a))
    }

mkBranch :: MerkleNode a -> MerkleNode a -> MerkleNode a
mkBranch a b =
    MerkleBranch
    { mLeft  = a
    , mRight = b
    , mRoot  = MerkleRoot $ coerce $
               hashRaw $ mconcat [ one 1
                                 , convert (mRoot a)
                                 , convert (mRoot b) ]
    }

-- | Smart constructor for 'MerkleTree'.
mkMerkleTree :: Bi a => [a] -> MerkleTree a
mkMerkleTree [] = MerkleEmpty
mkMerkleTree ls = MerkleTree (fromIntegral lsLen) (go lsLen ls)
  where
    lsLen = length ls
    go _  [x] = mkLeaf x
    go len xs = mkBranch (go i l) (go (len - i) r)
      where
        i = powerOfTwo len
        (l, r) = splitAt i xs

-- | Returns root of merkle tree.
mtRoot :: MerkleTree a -> MerkleRoot a
mtRoot MerkleEmpty      = emptyHash
mtRoot (MerkleTree _ x) = mRoot x

emptyHash :: MerkleRoot a
emptyHash = MerkleRoot (hashRaw mempty)

-- | Return the largest power of two such that it's smaller than X.
--
-- >>> powerOfTwo 64
-- 32
-- >>> powerOfTwo 65
-- 64
powerOfTwo :: (Bits a, Num a) => a -> a
powerOfTwo n
    | n .&. (n - 1) == 0 = n `shiftR` 1
    | otherwise = go n
 where
    {- “x .&. (x - 1)” clears the least significant bit:

           ↓
       01101000     x
       01100111     x - 1
       --------
       01100000     x .&. (x - 1)

       I could've used something like “until (\x -> x*2 > w) (*2) 1”,
       but bit tricks are fun. -}
    go w = if w .&. (w - 1) == 0 then w else go (w .&. (w - 1))
