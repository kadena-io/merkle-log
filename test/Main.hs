{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

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

import Crypto.Hash.Algorithms (SHA512t_256, HashAlgorithm)

import Data.Bitraversable
import qualified Data.ByteArray as BA
import qualified Data.ByteString as B
import Data.Word

import System.Exit

import Test.QuickCheck

-- internal modules

import Data.MerkleLog

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
    , ("runnig proof with invalid object hash fails", property prop_proofInvalidObjectHash)
    , ("encoding roundtrip for merkle proof object", property prop_encodeProofObject)
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
        $ case BA.unpack (_merkleProofObject p) of
            (0x00 : t) -> 0x01 : t
            (0x01 : t) -> 0x00 : t
            (_ : _) -> error "invalid proof object"
            [] -> error "unexpected empty proof object"


-- | Change hash of first proof step. Throws error is the proof
-- is empty (singleton tree).
--
changeProofHash :: HashAlgorithm a => MerkleProof a -> MerkleProof a
changeProofHash p = p { _merkleProofObject = o }
  where
    Right o = decodeMerkleProofObject . BA.pack @BA.Bytes
        $ case BA.unpack (_merkleProofObject p) of
            (h1 : h2 : t) -> h1 : 1 + h2 : t
            [] -> error "unexpected empty proof object"
            _ -> error "invalid proof object"

-- -------------------------------------------------------------------------- --
-- Properties

prop_tree :: [[Word8]] -> Property
prop_tree a = size t === nodeCount (length a) .&. leafCount t === length a
  where
    l = B.pack <$> a
    t = force $ merkleTree @SHA512t_256 l

prop_proof :: [[Word8]] -> NonNegative Int -> Property
prop_proof a (NonNegative i) = i < length a ==> runMerkleProof p === merkleRoot t
  where
    l = B.pack <$> a
    t = merkleTree @SHA512t_256 l
    p = case merkleProof i (l !! i) t of
            Left e -> error e
            Right x -> x

-- | Runtime is quadradic in the input parameter. 50 ~ 1sec, 100 ~ 5sec.
--
prop_proofExhaustive :: Int -> Property
prop_proofExhaustive n = once $ conjoin
    [ prop_proof (pure <$> [0 .. fromIntegral i]) (NonNegative j)
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

prop_proofInvalidInput :: [[Word8]] -> NonNegative Int -> Property
prop_proofInvalidInput a (NonNegative i) = i < length a
    ==> case merkleProof i "a" (merkleTree @SHA512t_256 (B.pack <$> a)) of
        Left _ -> True
        Right _ -> False

prop_proofInvalidSubject :: [[Word8]] -> NonNegative Int -> Property
prop_proofInvalidSubject a (NonNegative i) = i < length a
    ==> runMerkleProof p' =/= merkleRoot t
  where
    l = B.pack <$> a
    t = merkleTree @SHA512t_256 l
    p = case merkleProof i (l !! i) t of
        Left e -> error e
        Right x -> x
    p' = p { _merkleProofSubject = MerkleProofSubject "a" }

prop_proofInvalidObjectPath :: [[Word8]] -> NonNegative Int -> Property
prop_proofInvalidObjectPath a (NonNegative i) = length a > 1 && i < length a
    ==> runMerkleProof (changeProofPath p) =/= merkleRoot t
  where
    l = B.pack <$> a
    t = merkleTree @SHA512t_256 l
    p = case merkleProof i (l !! i) t of
        Left e -> error e
        Right x -> x

prop_proofInvalidObjectHash :: [[Word8]] -> NonNegative Int -> Property
prop_proofInvalidObjectHash a (NonNegative i) = length a > 1 && i < length a
    ==> runMerkleProof (changeProofHash p) =/= merkleRoot t
  where
    l = B.pack <$> a
    t = merkleTree @SHA512t_256 l
    p = case merkleProof i (l !! i) t of
        Left e -> error e
        Right x -> x

prop_encodeProofObject :: NonEmptyList [Word8] -> NonNegative Int -> Property
prop_encodeProofObject a (NonNegative i) = i < length l
    ==> Right po === decodeMerkleProofObject (encodeMerkleProofObject @BA.Bytes po)
  where
    l = B.pack <$> getNonEmpty a
    t = merkleTree @SHA512t_256 l
    p = case merkleProof i (l !! i) t of
        Left e -> error e
        Right x -> x
    po = _merkleProofObject p

prop_encodeMerkleRoot :: NonEmptyList [Word8] -> Property
prop_encodeMerkleRoot a
    = Right r === decodeMerkleRoot (encodeMerkleRoot @BA.Bytes r)
  where
    l = B.pack <$> getNonEmpty a
    t = merkleTree @SHA512t_256 l
    r = merkleRoot t

prop_encodeMerkleTree :: NonEmptyList [Word8] -> Property
prop_encodeMerkleTree a
    = Right t === decodeMerkleTree (encodeMerkleTree @BA.Bytes t)
  where
    l = B.pack <$> getNonEmpty a
    t = merkleTree @SHA512t_256 l
