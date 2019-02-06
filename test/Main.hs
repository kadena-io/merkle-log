{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
-- Module: Main
-- Copyright: Copyright © 2019 Kadena LLC.
-- License: MIT
-- Maintainer: Lars Kuhtz <lars@kadena.io>
-- Stability: experimental
--
-- TODO
--
module Main
( main

-- * Properties
, properties
, prop_proof
, prop_proofExhaustive
, prop_proofSize
, prop_encodeProofObject
, prop_encodeMerkleRoot
, prop_encodeMerkleTree
) where

import Control.DeepSeq
import Control.Monad.Catch

import Crypto.Hash.Algorithms (SHA512t_256, HashAlgorithm)

import Data.Bitraversable
import qualified Data.ByteArray as BA
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as B8
import qualified Data.List.NonEmpty as NE

import System.Exit

import Test.QuickCheck

-- internal modules

import Data.MerkleLog

-- -------------------------------------------------------------------------- --
-- Support for QuickCheck < 2.12

#if ! MIN_VERSION_QuickCheck(2,12,0)
infix 4 =/=
(=/=) :: (Eq a, Show a) => a -> a -> Property
x =/= y = counterexample (show x ++ interpret res ++ show y) res
  where
    res = x /= y
    interpret True  = " /= "
    interpret False = " == "

isSuccess :: Result -> Bool
isSuccess Success{} = True
isSuccess _ = False
#endif

-- -------------------------------------------------------------------------- --
-- Main

main :: IO ()
main = do
    results <- traverse (bitraverse print quickCheckResult) properties
    if and $ isSuccess . snd <$> results
        then exitSuccess
        else exitFailure

-- | Properties
--
properties :: [(String, Property)]
properties =
    [ ("create merkle tree and confirm the size", property prop_tree)
    , ("create and verify merkle proof", property prop_proof)
    , ("create and verify merkle proof for all tree items for tree of size 30", prop_proofExhaustive 30)
    , ("create and verify merkle proof for tree of size 1000 with items of sizes up to 1000 bytes", prop_proofSize 1000 1000)
    , ("creating proof for invalid input fails", property prop_proofInvalidInput)
    , ("running proof with invalid subject fails", property prop_proofInvalidSubject)
    , ("running proof with invalid object path fails", property prop_proofInvalidObjectPath)
    , ("running proof with invalid object hash fails", property prop_proofInvalidObjectHash)
    , ("running proof with invalid object step count fails", property prop_proofInvalidStepCount)
    , ("create and verify merkle proof for nested trees", property prop_chainProof)
    , ("encoding roundtrip for merkle proof object", property prop_encodeProofObject)
    , ("encoding roundtrip for merkle proof chain object", property prop_encodeProofChainObject)
    , ("encoding roundtrip for merkle root", property prop_encodeMerkleRoot)
    , ("encoding roundtrip for merkle tree", property prop_encodeMerkleTree)
    ]

-- -------------------------------------------------------------------------- --
-- Utils

nodeCount :: Int -> Int
nodeCount i = max 1 (2 * i - 1)
{-# INLINE nodeCount #-}

-- | Change diretion of first proof step. Throws error is the proof
-- is empty (singleton tree).
--
changeProofPath :: HashAlgorithm a => MerkleProof a -> MerkleProof a
changeProofPath p = p { _merkleProofObject = o }
  where
    Right o = decodeMerkleProofObject . BA.pack @BA.Bytes
        $ case splitAt 12 (BA.unpack (_merkleProofObject p)) of
            (h, 0x00 : t) -> h <> (0x01 : t)
            (h, 0x01 : t) -> h <> (0x00 : t)
            (_, _ : _) -> error "invalid proof object"
            (_, []) -> error "unexpected empty proof object"


-- | Change hash of first proof step. Throws error is the proof
-- is empty (singleton tree).
--
changeProofHash :: HashAlgorithm a => MerkleProof a -> MerkleProof a
changeProofHash p = p { _merkleProofObject = o }
  where
    Right o = decodeMerkleProofObject . BA.pack @BA.Bytes
        $ case splitAt 12 (BA.unpack (_merkleProofObject p)) of
            (h, h1 : h2 : t) -> h <> (h1 : 1 + h2 : t)
            (_, []) -> error "unexpected empty proof object"
            _ -> error "invalid proof object"

-- | Changes the proof step count and verifies that decoding of the modified proof object fails.
-- Throws error is the proof is empty (singleton tree).
--
changeProofStepCount :: forall a . HashAlgorithm a => MerkleProof a -> Bool
changeProofStepCount p = case r of
    Left _ -> True
    Right _ -> False
  where
    r = decodeMerkleProofObject @a . BA.pack @BA.Bytes
        $ case splitAt 3 (BA.unpack (_merkleProofObject p)) of
            (h, c : t) -> h <> (c + 1 : t)
            (_, []) -> error "unexpected empty proof object"

-- -------------------------------------------------------------------------- --
-- Generators

newtype UniqueInputs a = UniqueInputs [MerkleNodeType a B.ByteString]
    deriving Show

instance HashAlgorithm a => Arbitrary (UniqueInputs a) where
    arbitrary = UniqueInputs
        . zipWith (\a () -> InputNode $ B8.pack (show a)) [0 :: Int .. ]
        <$> arbitrary

instance HashAlgorithm a => Arbitrary (MerkleNodeType a B.ByteString) where
    arbitrary = oneof
        [ InputNode . B.pack <$> arbitrary
        , TreeNode <$> arbitrary
        ]

instance HashAlgorithm a => Arbitrary (MerkleRoot a) where
    arbitrary = merkleNode <$> arbitrary <*> arbitrary

instance HashAlgorithm a => Arbitrary (MerkleHash a) where
    arbitrary = merkleLeaf @a . B.pack <$> arbitrary

instance HashAlgorithm a => Arbitrary (MerkleTree a) where
    arbitrary = merkleTree <$> arbitrary @[MerkleNodeType a B.ByteString]

instance HashAlgorithm a => Arbitrary (MerkleProof a) where
    arbitrary = go `suchThatMap` either (const Nothing) Just
      where
        go = do
            NonEmpty l <- arbitrary @(NonEmptyList (MerkleNodeType a B.ByteString))
            i <- choose (0, length l - 1)
            return (merkleProof (l !! i) i (merkleTree l))

-- | A chain of nested Merkle trees.
--
newtype MerkleTreeChain a = MerkleTreeChain
    { _getMerkleTreeChain :: NE.NonEmpty (Int, MerkleTree a)
        -- ^ a list of of merkle trees along with the position of the previous
        -- tree in the chain
    }
    deriving Show

genTrees
    :: forall a
    . HashAlgorithm a
    => Gen (MerkleTreeChain a)
genTrees = do
    a <- genTree (InputNode "a")
    i <- choose @Int (0, 10)
    MerkleTreeChain . (NE.:|) a <$> go i (merkleRoot $ snd a)
  where
    genTree x = do
        il <- arbitrary @[MerkleNodeType a B.ByteString]
        ir <- arbitrary
        return (length il , merkleTree (concat [il, pure x, ir]))

    go 0 _ = return []
    go i r = do
        a <- genTree (TreeNode r)
        (:) a <$> go (pred i) (merkleRoot $ snd a)

instance HashAlgorithm a => Arbitrary (MerkleTreeChain a) where
    arbitrary = genTrees

-- -------------------------------------------------------------------------- --
-- Properties

prop_tree :: [MerkleNodeType SHA512t_256 B.ByteString] -> Property
prop_tree l = size t === nodeCount (length l) .&. leafCount t === length l
  where
    t = force $ merkleTree @SHA512t_256 l

prop_proof :: [MerkleNodeType SHA512t_256 B.ByteString] -> NonNegative Int -> Property
prop_proof l (NonNegative i) = i < length l ==> runMerkleProof p === merkleRoot t
  where
    t = merkleTree @SHA512t_256 l
    p = case merkleProof (l !! i) i t of
        Left e -> error (displayException e)
        Right x -> x

-- | Runtime is quadradic in the input parameter. 50 ~ 1sec, 100 ~ 5sec.
--
prop_proofExhaustive :: Int -> Property
prop_proofExhaustive n = once $ conjoin
    [ prop_proof ((InputNode . B.singleton . fromIntegral) <$> [0 .. i]) (NonNegative j)
    | i <- [0..n]
    , j <- [0..i]
    ]

-- | Runtime of @testSize n m@ can be expected to be bounded by @Ω(n * m)@.
-- @testSize 1000 1000@ ~ 1sec.
--
prop_proofSize :: Int -> Int -> Property
prop_proofSize n m = once $ do
    l <- vectorOf n (resize m arbitrary)
    i <- choose (0, n - 1)
    return $ prop_proof l (NonNegative i)

prop_proofInvalidInput
    :: [MerkleNodeType SHA512t_256 B.ByteString]
    -> NonNegative Int
    -> Property
prop_proofInvalidInput a (NonNegative i) = i < length a
    ==> case merkleProof (InputNode "a") i (merkleTree @SHA512t_256 a) of
        Left _ -> True
        Right _ -> False

prop_proofInvalidSubject
    :: [MerkleNodeType SHA512t_256 B.ByteString]
    -> NonNegative Int
    -> Property
prop_proofInvalidSubject l (NonNegative i) = i < length l
    ==> runMerkleProof p' =/= merkleRoot t
  where
    t = merkleTree @SHA512t_256 l
    p = case merkleProof (l !! i) i t of
        Left e -> error (displayException e)
        Right x -> x
    p' = p { _merkleProofSubject = MerkleProofSubject (InputNode "a") }

prop_proofInvalidObjectPath
    :: UniqueInputs SHA512t_256
    -> NonNegative Int
    -> Property
prop_proofInvalidObjectPath (UniqueInputs l) (NonNegative i)
    = length l > 1 && i < length l
    ==> runMerkleProof (changeProofPath p) =/= merkleRoot t
  where
    t = merkleTree @SHA512t_256 l
    p = case merkleProof (l !! i) i t of
        Left e -> error (displayException e)
        Right x -> x

prop_proofInvalidStepCount
    :: NonEmptyList (MerkleNodeType SHA512t_256 B.ByteString)
    -> NonNegative Int
    -> Property
prop_proofInvalidStepCount (NonEmpty l) (NonNegative i)
    = i < length l ==> changeProofStepCount p
  where
    t = merkleTree @SHA512t_256 l
    p = case merkleProof (l !! i) i t of
        Left e -> error (displayException e)
        Right x -> x

prop_proofInvalidObjectHash
    :: NonEmptyList (MerkleNodeType SHA512t_256 B.ByteString)
    -> NonNegative Int
    -> Property
prop_proofInvalidObjectHash (NonEmpty l) (NonNegative i)
    = 1 < length l && i < length l
    ==> runMerkleProof (changeProofHash p) =/= merkleRoot t
  where
    t = merkleTree @SHA512t_256 l
    p = case merkleProof (l !! i) i t of
        Left e -> error (displayException e)
        Right x -> x

prop_chainProof :: MerkleTreeChain SHA512t_256 -> Property
prop_chainProof (MerkleTreeChain l)
    = runMerkleProof @SHA512t_256 p === merkleRoot (snd $ NE.last l)
  where
    Right p = merkleProof_ (InputNode "a") l

prop_encodeProofObject :: MerkleProof SHA512t_256 -> Property
prop_encodeProofObject p
    = case decodeMerkleProofObject (encodeMerkleProofObject @BA.Bytes po) of
        Left e -> error (displayException e)
        Right x -> po === x
  where
    po = _merkleProofObject p

prop_encodeProofChainObject :: MerkleTreeChain SHA512t_256 -> Property
prop_encodeProofChainObject (MerkleTreeChain l)
    = case decodeMerkleProofObject (encodeMerkleProofObject @BA.Bytes po) of
        Left e -> error (displayException e)
        Right x -> po === x
  where
    p = case merkleProof_ (InputNode "a") l of
        Left e -> error (displayException e)
        Right x -> x
    po = _merkleProofObject p

prop_encodeMerkleRoot :: MerkleTree SHA512t_256 -> Property
prop_encodeMerkleRoot t
    = case decodeMerkleRoot (encodeMerkleRoot @BA.Bytes r) of
        Left e -> error (displayException e)
        Right x -> r === x
  where
    r = merkleRoot t

prop_encodeMerkleTree :: MerkleTree SHA512t_256 -> Property
prop_encodeMerkleTree t
    = case decodeMerkleTree (encodeMerkleTree @BA.Bytes t) of
        Left e -> error (displayException e)
        Right x -> t === x

