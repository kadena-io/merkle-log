{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- |
-- Module: Data.MerkleLog
-- Copyright: Copyright © 2019 Kadena LLC.
-- License: MIT
-- Maintainer: Lars Kuhtz <lars@kadena.io>
-- Stability: experimental
--
-- Merkle Logs are a append-only data structure. This implementation is based on
-- the description in RFC 6962. Extending a Merkle tree requires chaining a
-- logarithmic number of nodes at the end of the tree.
--
-- TODO:
--
-- * implement extension of trees (possibly by linking memory chunks of maximal full trees)
--   (how important is this?)
-- * implement consistency proofs
-- * more tests
-- * Exceptions + MonadThrow (or at least as SomeException?)
-- * document encodings and hash format
-- * describe tree layout
-- * more code cleanup
-- * Resolve all TODOs and FIXMEs
-- * reduce dependency on memory package by storing everything in
--   (pinned) 'B.ByteString's or unpinned 'BA.ByteArray's
-- * put on Hackage?
--
module Data.MerkleLog
(
-- * Merkle Tree
  MerkleTree
, merkleTree
, encodeMerkleTree
, decodeMerkleTree

-- * Merkle Root
, MerkleRoot
, merkleRoot
, encodeMerkleRoot
, decodeMerkleRoot

-- * Merkle Proofs
, MerkleProof(..)
, MerkleProofSubject(..)
, MerkleProofObject
, encodeMerkleProofObject
, decodeMerkleProofObject
, merkleProof
, runMerkleProof

-- * Internal

, isEmpty
, emptyMerkleTree
, size
, leafCount
, MerkleHash
, getHash

) where

import Control.DeepSeq
import Control.Monad

import Crypto.Hash (hash)
import Crypto.Hash.Algorithms (HashAlgorithm)
import Crypto.Hash.IO

import qualified Data.ByteArray as BA
import Data.ByteArray.Encoding
import qualified Data.ByteString as B
import Data.Word

import Foreign.Ptr
import Foreign.Storable

import GHC.Generics

-- -------------------------------------------------------------------------- --
-- Hashes

newtype MerkleHash a = MerkleHash BA.Bytes
    deriving (Eq, Generic)
    deriving newtype (NFData, BA.ByteArrayAccess)

instance Show (MerkleHash a) where
    show = fmap (toEnum . fromEnum)
        . BA.unpack @BA.Bytes
        . convertToBase Base64URLUnpadded
    {-# INLINEABLE show #-}

hashSize :: forall a c . HashAlgorithm a => Num c => c
hashSize = fromIntegral $ hashDigestSize @a undefined
    -- the 'undefined' argument is a type proxy that isn't evaluated
{-# INLINE hashSize #-}

decodeMerkleHash
    :: forall a b
    . HashAlgorithm a
    => BA.ByteArrayAccess b
    => b
    -> Either String (MerkleHash a)
decodeMerkleHash b
    | BA.length b /= hashSize @a = Left m
    | otherwise = Right $ MerkleHash $ BA.convert b
  where
    m = "failed to decode Merkle hash. Expected size: "
        <> show (hashSize @a @Int) <> ". Actual size: " <> show (BA.length b)
{-# INLINE decodeMerkleHash #-}

-- -------------------------------------------------------------------------- --
-- Merkle Tree Nodes

leafTag :: BA.ByteArray a => a
leafTag = BA.singleton 0
{-# INLINE leafTag #-}

nodeTag :: BA.ByteArray a => a
nodeTag = BA.singleton 1
{-# INLINE nodeTag #-}

merkleLeaf
    :: forall a b
    . HashAlgorithm a
    => BA.ByteArrayAccess b
    => b
    -> MerkleHash a
merkleLeaf !bytes = MerkleHash $ BA.allocAndFreeze (hashSize @a) $ \ptr -> do
    !ctx <- hashMutableInit @a
    merkleLeafPtr ctx bytes ptr

merkleNodePtr
    :: forall a
    . HashAlgorithm a
    => MutableContext a
    -> Ptr (MerkleHash a)
    -> Ptr (MerkleHash a)
    -> Ptr (MerkleHash a)
    -> IO ()
merkleNodePtr !ctx !a !b !r = do
    hashMutableReset ctx
    hashMutableUpdate ctx (nodeTag @BA.Bytes)
    BA.withByteArray ctx $ \ctxPtr -> do
        hashInternalUpdate @a ctxPtr (castPtr a) (hashSize @a)
        hashInternalUpdate ctxPtr (castPtr b) (hashSize @a)
        hashInternalFinalize ctxPtr (castPtr r)

merkleLeafPtr
    :: forall a b
    . HashAlgorithm a
    => BA.ByteArrayAccess b
    => MutableContext a
    -> b
    -> Ptr (MerkleHash a)
    -> IO ()
merkleLeafPtr !ctx !b !r = do
    hashMutableReset ctx
    hashMutableUpdate ctx (leafTag @BA.Bytes)
    hashMutableUpdate ctx b
    BA.withByteArray ctx $ \ctxPtr ->
        hashInternalFinalize @a ctxPtr (castPtr r)

-- -------------------------------------------------------------------------- --
-- Merkle Tree
--
-- Using unsafe operations in the implementation is fine, since proof testing
-- of Merkle proof validation provides robust assurance that the data in the
-- underlying memory is correct to the bit level.
--

-- | Binary Merkle Tree.
--
-- A Merkle Tree is only an index. It doesn't store any data but only hashes of
-- the data that is referenced in the tree.
--
newtype MerkleTree a = MerkleTree BA.Bytes
    deriving (Eq, Generic)
    deriving newtype (NFData, BA.ByteArrayAccess)

instance Show (MerkleTree a) where
    show = fmap (toEnum . fromEnum)
        . BA.unpack @BA.Bytes
        . convertToBase Base64URLUnpadded
    {-# INLINEABLE show #-}

-- | Merkle Tree as described in RFC 6962, but with configurable hash function.
--
-- For full RFC 6962 compliance 'Crypto.Hash.SHA256' should be used as hash algorithm.
--
-- The Merkle tree for the empty input log is the hash of the empty string.
--
-- TODO: The length of the list is forced before the algorithm starts processing
-- the items. Either demand a strict structure (e.g. vector or array) or
-- allocate tree memory dynamically while traversing the log structure.
--
merkleTree
    :: forall a b
    . HashAlgorithm a
    => BA.ByteArrayAccess b
    => [b]
    -> MerkleTree a
merkleTree [] = MerkleTree $ BA.convert $ hash @_ @a (mempty @B.ByteString)
merkleTree !items = MerkleTree $ BA.allocAndFreeze (tsize * hashSize @a) $ \ptr -> do

    !ctx <- hashMutableInit @a

    -- TODO compare performance with explicit construction
    let
        -- | This uses logarithmic stack space
        --
        go
            :: Ptr (MerkleHash a)
                -- ^ ptr into output tree
            -> [b]
                -- ^ input log
            -> [(Int, Ptr (MerkleHash a))]
                -- stack of tree hight and ptr into tree
            -> IO ()

        -- Create new inner node from stack tree positions on stack
        --
        go !i t ((!a, !ia) : (!b, !ib) : s) | a == b = do
            merkleNodePtr ctx ib ia i
            go (i `plusPtr` hs) t ((succ a, i) : s)

        -- Create new leaf node on the stack
        --
        go !i (h : t) !s = do
            merkleLeafPtr ctx h i
            go (i `plusPtr` hs) t ((0, i) : s)

        -- When all inputs are consumed, include remaining nodes on the
        -- stack as unbalanced subtree
        --
        go !i [] ((!a, !ia) : (!_, !ib) : s) = do
            merkleNodePtr ctx ib ia i
            go (i `plusPtr` hs) [] ((succ a, i) : s)

        go _ [] [_] = return ()

        go _ [] [] = error "TODO: empty hash"

    go ptr items []

  where
    !isize = length items
    !tsize = isize + (isize - 1)
    !hs = hashSize @a

-- | Test a Merkle tree is the tree of the empty log.
--
isEmpty :: forall a . HashAlgorithm a => MerkleTree a -> Bool
isEmpty = BA.constEq (emptyMerkleTree @a)
{-# INLINE isEmpty #-}

-- | The Merkle tree of the empty log. RFC 6962 specifies that this is the hash
-- of the empty string.
--
emptyMerkleTree :: forall a . HashAlgorithm a => MerkleTree a
emptyMerkleTree = merkleTree @a ([] @B.ByteString)
{-# INLINEABLE emptyMerkleTree #-}

-- | Binary encoding of a Merkle tree.
--
encodeMerkleTree :: BA.ByteArray b => MerkleTree a -> b
encodeMerkleTree = BA.convert
{-# INLINE encodeMerkleTree #-}

-- | The number of nodes (including leafs) in a Merkle tree.
--
size :: forall a . HashAlgorithm a => MerkleTree a -> Int
size t = BA.length t `div` hashSize @a
{-# INLINE size #-}

-- | Decode are Merkle tree from a binary representation.
--
decodeMerkleTree
    :: forall a b
    . HashAlgorithm a
    => BA.ByteArrayAccess b
    => b
    -> Either String (MerkleTree a)
decodeMerkleTree b
    | BA.length b `mod` hashSize @a == 0 = Right $ MerkleTree $ BA.convert b
    | otherwise = Left
        $ "failed to decode Merkle tree. The size must be a multiple of "
        <> show (hashSize @a @Int)
        <> ". But the input has size " <> show (BA.length b)
{-# INLINE decodeMerkleTree #-}

-- -------------------------------------------------------------------------- --
-- Merkle Root

-- | The root of a Merkle tree.
--
newtype MerkleRoot a = MerkleRoot (MerkleHash a)
    deriving (Eq, Generic)
    deriving newtype (Show, NFData, BA.ByteArrayAccess)

-- | Get the root of Merkle tree.
--
merkleRoot :: forall a . HashAlgorithm a => MerkleTree a -> MerkleRoot a
merkleRoot t = MerkleRoot $ getHash t (size t - 1)
{-# INLINE merkleRoot #-}

-- | Encode a Merkle tree root into binary format.
--
encodeMerkleRoot :: BA.ByteArray b => MerkleRoot a -> b
encodeMerkleRoot = BA.convert
{-# INLINE encodeMerkleRoot #-}

-- | Decode a Merkle tree root from a binary representation.
--
decodeMerkleRoot
    :: HashAlgorithm a
    => BA.ByteArrayAccess b
    => b
    -> Either String (MerkleRoot a)
decodeMerkleRoot = fmap MerkleRoot . decodeMerkleHash
{-# INLINE decodeMerkleRoot #-}

-- -------------------------------------------------------------------------- --
-- Proof Object

-- | Opaque proof object.
--
newtype MerkleProofObject a = MerkleProofObject BA.Bytes
    deriving (Eq, Generic)
    deriving anyclass (NFData)
    deriving newtype (BA.ByteArrayAccess)

instance Show (MerkleProofObject a) where
    show = fmap (toEnum . fromEnum)
        . BA.unpack @BA.Bytes
        . convertToBase @_ @BA.Bytes Base64URLUnpadded
    {-# INLINEABLE show #-}

-- | Encode a Merkle proof object into binary format.
--
encodeMerkleProofObject :: BA.ByteArray b => MerkleProofObject a -> b
encodeMerkleProofObject = BA.convert
{-# INLINE encodeMerkleProofObject #-}

-- | Encode a Merkle proof object from a binary representation.
--
decodeMerkleProofObject
    :: forall a b
    . HashAlgorithm a
    => BA.ByteArrayAccess b
    => b
    -> Either String (MerkleProofObject a)
decodeMerkleProofObject bytes
    | BA.length bytes `mod` stepSize @a /= 0 =
        Left "invalid merkle proof object, wrong size"
    | otherwise = Right $ MerkleProofObject $ BA.convert bytes

stepSize :: forall a . HashAlgorithm a => Int
stepSize = hashSize @a + 1
{-# INLINE stepSize #-}

-- -------------------------------------------------------------------------- --
-- Proof Subject

-- | The subject for which inclusion is proven.
--
newtype MerkleProofSubject = MerkleProofSubject B.ByteString
    deriving (Show, Eq, Ord, Generic)
    deriving newtype (BA.ByteArrayAccess)
    deriving anyclass (NFData)

-- -------------------------------------------------------------------------- --
-- Merkle Proof

-- | Merkle Inclusion Proof. In RFC 6962 this is called an audit proof.
--
-- The proof is self-contained. It is independent of the concrete implementation
-- of the Merkle tree. This type works with any binary Merkle tree type and
-- doesn't make any assumptions about the balancing of the tree.
--
-- The proof includes the subject of the proof (for which inclusion is proven)
-- as a plaintext bytestring. The proof does not include the root hash of the
-- Merkle tree, because the proof is only meaningful if the root is available
-- from a trusted source. Including it into the proof would thus be redundant or
-- even misleading.
--
-- A more compact encoding would use the first bit of each hash to encode the
-- side, but that would require to alter the hash computation. We also could
-- pack the sides into a bit array. However, the total number of bytes for the
-- sides will be most likely less than two hashes, so the overhead is small and
-- doesn't justify more clever encodings.
--
data MerkleProof a = MerkleProof
    { _merkleProofSubject :: !MerkleProofSubject
    , _merkleProofObject :: !(MerkleProofObject a)
    }
    deriving (Show, Eq, Generic)
    deriving anyclass (NFData)

-- | Construct a self-contained Merkle inclusion proof.
--
merkleProof
    :: forall a
    . HashAlgorithm a
    => Int
    -> B.ByteString
    -> MerkleTree a
    -> Either String (MerkleProof a)
merkleProof pos a t
    | pos < 0 = Left "index too small"
    | pos >= leafCount t = Left "index too large"
    | not (BA.constEq (view t tpos) (merkleLeaf @a a)) = Left "item not in the tree at the given index"
    | otherwise = Right $ MerkleProof
        { _merkleProofSubject = MerkleProofSubject a
        , _merkleProofObject = MerkleProofObject go
        }
  where
    (tpos, path) = proofPath pos (leafCount t)
    go = BA.allocAndFreeze (length path * stepSize @a) $ \ptr ->
        forM_ (path `zip` [0, fromIntegral (stepSize @a) ..]) $ \((s, i), x) -> do
            poke (ptr `plusPtr` x) (sideWord8 s)
            BA.copyByteArrayToPtr (view t i) (ptr `plusPtr` succ x)

proofPath
    :: Int
        -- ^ Position in log
    -> Int
        -- ^ Size of log
    -> (Int, [(Side, Int)])
        -- ^ The tree position of the target node and tree
        -- positions and directions of the audit proof.
proofPath b c = go 0 0 b c []
  where
    go _ !treeOff _ 1 !acc = (treeOff, acc)
    go !logOff !treeOff !m !n !acc
        | m < k = go logOff treeOff m k $ (R, treeOff + 2 * n - 3) : acc
        | otherwise = go (logOff + k) (treeOff + 2 * k - 1) (m - k) (n - k)
            $ (L, treeOff + 2 * k - 2) : acc
      where
        k = k2 n

-- | Execute an inclusion proof. The result of the execution is a Merkle root
-- that must be compared to the trusted root of the Merkle tree.
--
runMerkleProof :: forall a . HashAlgorithm a => MerkleProof a -> MerkleRoot a
runMerkleProof p = MerkleRoot
    $ MerkleHash
    $ BA.allocAndFreeze hs $ \ptr -> do
        ctx <- hashMutableInit @a
        merkleLeafPtr ctx subj ptr
        BA.withByteArray obj $ \objPtr ->
            forM_ [0, stepSize @a .. BA.length obj - 1] $ \i ->
                peekByteOff @Word8 objPtr i >>= \case
                    0x00 -> merkleNodePtr ctx (objPtr `plusPtr` succ i) ptr ptr
                    0x01 -> merkleNodePtr ctx ptr (objPtr `plusPtr` succ i) ptr
                    _ -> error "invalid proof object"
                        -- FIXME: check this when decoding ?
  where
    MerkleProofSubject subj = _merkleProofSubject p
    MerkleProofObject obj = _merkleProofObject p
    hs = hashSize @a

-- -------------------------------------------------------------------------- --
-- Utils

k2 :: Int -> Int
k2 i = 2 ^ floor @Double @Int (logBase 2 $ fromIntegral i - 1)
{-# INLINE k2 #-}

data Side = L | R
    deriving (Show, Eq)

sideWord8 :: Side -> Word8
sideWord8 L = 0x00
sideWord8 R = 0x01
{-# INLINE sideWord8 #-}

view :: forall a . HashAlgorithm a => MerkleTree a -> Int -> BA.View BA.Bytes
view (MerkleTree v) i = BA.view v (i * hashSize @a) (hashSize @a)
{-# INLINE view #-}

-- | Get the hash of a node in the Merkle tree.
--
getHash :: HashAlgorithm a => MerkleTree a -> Int -> MerkleHash a
getHash t = MerkleHash . BA.convert . view t
{-# INLINE getHash #-}

-- | Get the number of leafs in a Merkle tree.
--
leafCount :: HashAlgorithm a => MerkleTree a -> Int
leafCount t
    | isEmpty t = 0
    | otherwise = 1 + size t `div` 2
{-# INLINE leafCount #-}

{- Useful for debugging

hex :: BA.ByteArrayAccess a => a -> String
hex = fmap (toEnum . fromEnum)
    . BA.unpack @BA.Bytes
    . convertToBase Base16

b64 :: BA.ByteArrayAccess a => a -> String
b64 = fmap (toEnum . fromEnum)
    . BA.unpack @BA.Bytes
    . convertToBase Base64URLUnpadded
-}

