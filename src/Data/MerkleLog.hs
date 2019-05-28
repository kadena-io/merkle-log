{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- |
-- Module: Data.MerkleLog
-- Copyright: Copyright © 2019 Kadena LLC.
-- License: MIT
-- Maintainer: Lars Kuhtz <lars@kadena.io>
-- Stability: experimental
--
-- Merkle Logs are a append-only data structure. The tree layout in this
-- implementation of Merkle trees is based on the description of Merkle trees in
-- RFC 6962. With this tree layout extending a Merkle tree requires chaining a
-- logarithmic number of nodes at the end of the tree. Unlike RFC 6962 the
-- Merkle trees in this module support the creation unbalanced MerkleTrees by
-- nesting sub-trees as leafs of Merkle trees. Also, unlike RFC 6962 this module
-- generates fully self-contained inclusion proofs that don't rely on the client
-- being aware of the balancing of the Merkle Tree that was used to generate the
-- proof.
--
-- The API requires the usage of type applications which can be enabled with the
-- following pragma.
--
-- @
-- {-\# LANGUAGE TypeApplications #-}
-- @
--
-- = Example
--
-- @
-- {-\# LANGUAGE TypeApplications #-}
-- {-\# LANGUAGE OverloadedStrings #-}
--
-- import qualified Data.ByteString as B
-- import Crypto.Hash.Algorithms (SHA512t_256)
--
-- inputs = ["a", "b", "c"] :: [B.ByteString]
--
-- -- create tree
-- t = merkleTree @SHA512t_256 inputs
--
-- -- create inclusion proof
-- p = either (error . show) id $ merkleProof 1 (inputs !! 1) t
--
-- -- verify proof
-- runMerkleProof p == merkleRoot t
-- @
--
-- = TODO
--
-- * implement extension of trees (possibly by linking memory chunks of maximal full trees)
--   (how important is this?)
-- * implement consistency proofs
-- * document encodings and hash format
-- * describe tree layout
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
, MerkleNodeType(..)
, MerkleProof(..)
, MerkleProofSubject(..)
, MerkleProofObject
, encodeMerkleProofObject
, decodeMerkleProofObject
, merkleProof
, merkleProof_
, runMerkleProof

-- * Exceptions
, Expected(..)
, Actual(..)
, MerkleTreeException(..)
, textMessage

-- * Internal

, isEmpty
, emptyMerkleTree
, size
, leafCount
, MerkleHash
, getHash
, merkleLeaf
, merkleNode

) where

import Control.DeepSeq
import Control.Monad
import Control.Monad.Catch

import Crypto.Hash (hash)
import Crypto.Hash.Algorithms (HashAlgorithm)
import Crypto.Hash.IO

import qualified Data.ByteArray as BA
import Data.ByteArray.Encoding
import qualified Data.ByteString as B
import qualified Data.List.NonEmpty as NE
import qualified Data.Memory.Endian as BA
import Data.String
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Word

import Foreign.Ptr
import Foreign.Storable

import GHC.Generics
import GHC.Stack

import System.IO.Unsafe

-- -------------------------------------------------------------------------- --
-- Exceptions

-- | An expected value.
--
newtype Expected a = Expected a
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | An actual value.
--
newtype Actual a = Actual a
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | Format a text messages that compares an 'Expected' with an 'Actual' value.
--
expectedMessage :: Show a => Expected a -> Actual a -> T.Text
expectedMessage (Expected e) (Actual a)
    = "Expected: " <> sshow e <> ", Actual: " <> sshow a

-- | Exceptions that are thrown by functions in "Data.MerkleLog". All functions
-- that throw exceptions can be called as pure functions in `Either
-- SomeException`.
--
data MerkleTreeException
    = EncodingSizeException T.Text (Expected Int) (Actual Int)
    | EncodingSizeConstraintException T.Text (Expected T.Text) (Actual Int)
    | IndexOutOfBoundsException T.Text (Expected (Int, Int)) (Actual Int)
    | InputNotInTreeException T.Text Int B.ByteString
    | MerkleRootNotInTreeException T.Text Int B.ByteString
    | InvalidProofObjectException T.Text
    deriving (Eq, Generic)
    deriving anyclass (NFData)

instance Exception MerkleTreeException where
    displayException = T.unpack . textMessage

instance Show MerkleTreeException where
    show = T.unpack . textMessage

-- | Display 'MerkleTreeException' values as text messages.
--
textMessage :: MerkleTreeException -> T.Text
textMessage (EncodingSizeException ty e a)
    = "Failed to decode " <> ty <> " because the input is of wrong size"
    <> ". " <> expectedMessage e a
textMessage (EncodingSizeConstraintException ty (Expected e) (Actual a))
    = "Failed to decode " <> ty <> " because the input is of wrong size"
    <> ". " <> "Expected: " <> e
    <> ", " <> "Actual: " <> sshow a
textMessage (IndexOutOfBoundsException ty (Expected e) (Actual a))
    = "Index out of bounds"
    <> ". " <> ty
    <> ". " <> "Expected: " <> sshow e
    <> ", " <> "Actual: " <> sshow a
textMessage (InputNotInTreeException t i b)
    = "Item not in tree"
    <> ". " <> t
    <> ". Position: " <> sshow i
    <> ". Input (b64): " <> T.take 1024 (b64 b)
textMessage (MerkleRootNotInTreeException t i b)
    = "Item not in tree"
    <> ". " <> t
    <> ". Position: " <> sshow i
    <> ". Input (b64): " <> b64 b
textMessage (InvalidProofObjectException t)
    = "Invalid ProofObject: " <> t

inputNotInTreeException
    :: T.Text
    -> Int
    -> MerkleNodeType a B.ByteString
    -> MerkleTreeException
inputNotInTreeException t pos (TreeNode r)
    = MerkleRootNotInTreeException t pos $ encodeMerkleRoot r
inputNotInTreeException t pos (InputNode b)
    = InputNotInTreeException t pos b

-- -------------------------------------------------------------------------- --
-- Hashes

-- | Internal type to represent hash values.
--
newtype MerkleHash a = MerkleHash BA.Bytes
    deriving (Eq, Ord, Generic)
    deriving newtype (NFData, BA.ByteArrayAccess)

instance Show (MerkleHash a) where
    show = fmap (toEnum . fromEnum)
        . BA.unpack @BA.Bytes
        . convertToBase Base64URLUnpadded
    {-# INLINEABLE show #-}

-- | The size of 'MerkleHash' values in bytes.
--
hashSize :: forall a c . HashAlgorithm a => Num c => c
hashSize = fromIntegral $ hashDigestSize @a undefined
    -- the 'undefined' argument is a type proxy that isn't evaluated
{-# INLINE hashSize #-}

-- | Decode a 'MerkleHash' from bytes.
--
decodeMerkleHash
    :: forall a b m
    . MonadThrow m
    => HashAlgorithm a
    => BA.ByteArrayAccess b
    => b
    -> m (MerkleHash a)
decodeMerkleHash b
    | BA.length b /= hashSize @a = throwM e
    | otherwise = return $ MerkleHash $ BA.convert b
  where
    e = EncodingSizeException "MerkleHash"
        (Expected (hashSize @a @Int))
        (Actual (BA.length b))
{-# INLINE decodeMerkleHash #-}

-- -------------------------------------------------------------------------- --
-- Merkle Tree Nodes

leafTag :: BA.ByteArray a => a
leafTag = BA.singleton 0
{-# INLINE leafTag #-}

nodeTag :: BA.ByteArray a => a
nodeTag = BA.singleton 1
{-# INLINE nodeTag #-}

-- | Compute hash for a leaf node in a Merkle tree.
--
merkleLeaf
    :: forall a b
    . HashAlgorithm a
    => BA.ByteArrayAccess b
    => b
    -> MerkleHash a
merkleLeaf !bytes = MerkleHash $ BA.allocAndFreeze (hashSize @a) $ \ptr -> do
    !ctx <- hashMutableInit @a
    merkleLeafPtr ctx bytes ptr

-- | Compute hash for an inner node of a Merkle tree.
--
merkleNode
    :: forall a
    . HashAlgorithm a
    => MerkleHash a
    -> MerkleHash a
    -> MerkleRoot a
merkleNode !a !b = MerkleRoot $ MerkleHash $ BA.allocAndFreeze (hashSize @a) $ \ptr -> do
    !ctx <- hashMutableInit @a
    BA.withByteArray a $ \aptr ->
        BA.withByteArray b $ \bptr ->
            merkleNodePtr ctx aptr bptr ptr

-- | Compute hash for inner node of a Merkle tree.
--
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

-- | Compute hash for a leaf node in a Merkle tree.
--
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
-- Using unsafe operations in the implementation is fine, since proof testing of
-- Merkle proof validation provides robust assurance that the data in the
-- underlying memory is correct to the bit level, i.e. it's very unlikely that a
-- bug would slip through the unit tests.
--

-- | The Type of leafs nodes in a Merkle tree. A node is either an input value
-- or a root of another nested Merkle tree.
--
data MerkleNodeType a b
    = TreeNode (MerkleRoot a)
    | InputNode b
    deriving (Show, Eq, Ord, Generic, Functor)
    deriving anyclass (NFData)

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

-- | Merkle Tree as described in RFC 6962, but with a configurable hash function
-- and support for nested Merkle trees.
--
-- The Merkle tree for the empty input log is the hash of the empty string.
--
-- TODO: The length of the list is forced before the algorithm starts processing
-- the items. Either demand a strict structure (e.g. vector or array) or
-- allocate tree memory dynamically while traversing the log structure.
--
merkleTree
    :: forall a b
    . HasCallStack
    => HashAlgorithm a
    => BA.ByteArrayAccess b
    => [MerkleNodeType a b]
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
            -> [MerkleNodeType a b]
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
        go !i (InputNode h : t) !s = do
            merkleLeafPtr ctx h i
            go (i `plusPtr` hs) t ((0, i) : s)

        go !i (TreeNode h : t) !s = do
            BA.copyByteArrayToPtr h i
            go (i `plusPtr` hs) t ((0, i) : s)

        -- When all inputs are consumed, include remaining nodes on the
        -- stack as unbalanced subtree
        --
        go !i [] ((!a, !ia) : (!_, !ib) : s) = do
            merkleNodePtr ctx ib ia i
            go (i `plusPtr` hs) [] ((succ a, i) : s)

        go _ [] [_] = return ()

        go _ [] [] = error "code invariant violation"

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
emptyMerkleTree = merkleTree @a ([] @(MerkleNodeType a B.ByteString))
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
    :: forall a b m
    . MonadThrow m
    => HashAlgorithm a
    => BA.ByteArrayAccess b
    => b
    -> m (MerkleTree a)
decodeMerkleTree b
    | BA.length b `mod` hashSize @a == 0 = return $ MerkleTree $ BA.convert b
    | otherwise = throwM $ EncodingSizeConstraintException
        "MerkleTree"
        (Expected $ "multiple of " <> sshow (hashSize @a @Int))
        (Actual $ BA.length b)
{-# INLINE decodeMerkleTree #-}

-- -------------------------------------------------------------------------- --
-- Merkle Root

-- | The root of a Merkle tree.
--
newtype MerkleRoot a = MerkleRoot (MerkleHash a)
    deriving (Eq, Ord, Generic)
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
    :: MonadThrow m
    => HashAlgorithm a
    => BA.ByteArrayAccess b
    => b
    -> m (MerkleRoot a)
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
-- This copies the bytes of the underlying byte array. The encoded object
-- doesn't reference the 'MerkleProofObject'
--
encodeMerkleProofObject :: BA.ByteArray b => MerkleProofObject a -> b
encodeMerkleProofObject = BA.convert
{-# INLINE encodeMerkleProofObject #-}

-- | Encode a Merkle proof object from a binary representation.
--
-- This copies the original bytes and doesn't keep a reference to the input
-- bytes.
--
decodeMerkleProofObject
    :: forall a b m
    . MonadThrow m
    => HashAlgorithm a
    => BA.ByteArrayAccess b
    => b
    -> m (MerkleProofObject a)
decodeMerkleProofObject bytes
    | BA.length bytes < 12 = throwM
        $ EncodingSizeConstraintException
            "MerkleProofObject"
            (Expected "larger than 12")
            (Actual $ BA.length bytes)
    | BA.length bytes /= proofObjectSizeInBytes @a stepCount = throwM
        $ EncodingSizeException
            "MerkleProofObject"
            (Expected $ proofObjectSizeInBytes @a stepCount)
            (Actual $ BA.length bytes)
    | otherwise = return $ MerkleProofObject $ BA.convert bytes
  where
    stepCount = fromIntegral $ BA.fromBE $ peekBA @(BA.BE Word32) bytes

stepSize :: forall a . HashAlgorithm a => Int
stepSize = hashSize @a + 1
{-# INLINE stepSize #-}

proofObjectSizeInBytes :: forall a . HashAlgorithm a => Int -> Int
proofObjectSizeInBytes stepCount = stepSize @a * stepCount + 12
{-# INLINE proofObjectSizeInBytes #-}

-- -------------------------------------------------------------------------- --
-- Proof Subject

-- | The subject for which inclusion is proven.
--
newtype MerkleProofSubject a = MerkleProofSubject
    { _getMerkleProofSubject :: (MerkleNodeType a B.ByteString) }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- -------------------------------------------------------------------------- --
-- Merkle Proof

-- | Merkle Inclusion Proof. In RFC 6962 this is called an audit proof. The
-- proof in this module are not compatible with RFC 6962. They support proving
-- inclusion of subtrees and proof for unbalanced trees of unknown size.
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
    { _merkleProofSubject :: !(MerkleProofSubject a)
    , _merkleProofObject :: !(MerkleProofObject a)
    }
    deriving (Show, Eq, Generic)
    deriving anyclass (NFData)

-- | Construct a self-contained Merkle inclusion proof.
--
merkleProof
    :: forall a m
    . MonadThrow m
    => HashAlgorithm a
    => MerkleNodeType a B.ByteString
    -> Int
    -> MerkleTree a
    -> m (MerkleProof a)
merkleProof a pos t
    | pos < 0 || pos >= leafCount t = throwM $ IndexOutOfBoundsException
        "merkleProof"
        (Expected (0,leafCount t - 1))
        (Actual pos)
    | not (BA.constEq (view t tpos) (inputHash a)) = throwM
        $ inputNotInTreeException "merkleProof" pos a
    | otherwise = return $ MerkleProof
        { _merkleProofSubject = MerkleProofSubject a
        , _merkleProofObject = MerkleProofObject go
        }
  where
    inputHash (InputNode bytes) = merkleLeaf @a bytes
    inputHash (TreeNode (MerkleRoot bytes)) = bytes

    (tpos, path) = proofPath pos (leafCount t)
    go = BA.allocAndFreeze (proofObjectSizeInBytes @a (length path)) $ \ptr -> do
        -- encode number of proof stepts in 4 bytes
        pokeBE @Word32 ptr $ fromIntegral $ length path

        -- encode index of subject in input order in 8 bytes
        pokeBE @Word64 (ptr `plusPtr` 4) (fromIntegral pos)

        -- encode path
        let pathPtr = ptr `plusPtr` 12
        forM_ (path `zip` [0, fromIntegral (stepSize @a) ..]) $ \((s, i), x) -> do
            poke (pathPtr `plusPtr` x) (sideWord8 s)
            BA.copyByteArrayToPtr (view t i) (pathPtr `plusPtr` succ x)

-- | Construct a Merkle proof for a proof subject in a nested sub-tree.
--
-- FIXME: make this function more efficient by implementing it more directly.
--
merkleProof_
    :: forall a m
    . MonadThrow m
    => HashAlgorithm a
    => MerkleNodeType a B.ByteString
        -- ^ The proof subject
    -> NE.NonEmpty (Int, MerkleTree a)
        -- ^ The proof components
    -> m (MerkleProof a)
merkleProof_ a l
    = MerkleProof (MerkleProofSubject a) . MerkleProofObject . assemble <$> go a (NE.toList l)
  where
    go _ [] = return []
    go sub ((pos, tree) : t) = do
        -- create sub-proof
        MerkleProof (MerkleProofSubject _) (MerkleProofObject o) <- merkleProof sub pos tree
        -- collect step counts and stripped proof objects
        (:) (strip o) <$> go (TreeNode $ merkleRoot tree) t

    -- strip path length and subject position from proof object
    strip o = (peekBeBA o :: Word32, BA.drop 12 o)
    assemble ps =
        let (s, os) = unzip ps
        in BA.concat
            -- inject length of overall path
            $ BA.allocAndFreeze 4 (flip pokeBE $ sum s)
            -- inject position of proof subject
            : BA.allocAndFreeze 8 (flip (pokeBE @Word64) $ fromIntegral $ fst $ NE.head l)
            : os

proofPath
    :: Int
        -- ^ Position in log
    -> Int
        -- ^ Size of log
    -> (Int, [(Side, Int)])
        -- ^ The tree position of the target node and tree positions and
        -- directions of the audit proof.
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
runMerkleProof p = MerkleRoot $ MerkleHash $ runMerkleProofInternal @a subj obj
  where
    MerkleProofSubject subj = _merkleProofSubject p
    MerkleProofObject obj = _merkleProofObject p

runMerkleProofInternal
    :: forall a b c d
    . HashAlgorithm a
    => BA.ByteArrayAccess b
    => BA.ByteArrayAccess c
    => BA.ByteArray d
    => MerkleNodeType a b
        -- ^ proof subject
    -> c
        -- ^ proof object
    -> d
runMerkleProofInternal subj obj = BA.allocAndFreeze (hashSize @a) $ \ptr -> do
    ctx <- hashMutableInit @a
    case subj of
        InputNode x -> merkleLeafPtr ctx x ptr
        TreeNode x -> BA.copyByteArrayToPtr x ptr
    BA.withByteArray obj $ \objPtr -> do
        stepCount <- fromIntegral <$> peekBE @Word32 objPtr
        forM_ [0 .. stepCount - 1] $ \(i :: Int) -> do
            let off = 12 + i * stepSize @a
            peekByteOff @Word8 objPtr off >>= \case
                0x00 -> merkleNodePtr ctx (objPtr `plusPtr` succ off) ptr ptr
                0x01 -> merkleNodePtr ctx ptr (objPtr `plusPtr` succ off) ptr
                _ -> throwM $ InvalidProofObjectException "runMerkleProofInternal"

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

peekBE :: forall a . BA.ByteSwap a => Storable a => Ptr (BA.BE a) -> IO a
peekBE ptr = BA.fromBE <$> peek @(BA.BE a) ptr
{-# INLINE peekBE #-}

pokeBE :: forall a . BA.ByteSwap a => Storable a => Ptr (BA.BE a) -> a -> IO ()
pokeBE ptr = poke ptr . BA.toBE @a
{-# INLINE pokeBE #-}

peekBA :: forall a b . Storable a => BA.ByteArrayAccess b => b -> a
peekBA bytes = unsafePerformIO $ BA.withByteArray bytes (peek @a)
{-# INLINE peekBA #-}

peekBeBA :: forall a b . BA.ByteSwap a => Storable a => BA.ByteArrayAccess b => b -> a
peekBeBA = BA.fromBE . peekBA @(BA.BE a)
{-# INLINE peekBeBA #-}

{- Useful for debugging
hex :: BA.ByteArrayAccess a => a -> String
hex = fmap (toEnum . fromEnum)
    . BA.unpack @BA.Bytes
    . convertToBase Base16
-}

b64 :: BA.ByteArrayAccess a => a -> T.Text
b64 = T.decodeUtf8 . convertToBase Base64URLUnpadded
{-# INLINE b64 #-}

sshow :: Show a => IsString b => a -> b
sshow = fromString . show
{-# INLINE sshow #-}
