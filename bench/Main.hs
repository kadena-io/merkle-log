{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

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
) where

import Control.DeepSeq

import Criterion
import Criterion.Main

import Crypto.Hash
import qualified Crypto.Hash.MerkleTree as MT

import qualified Data.ByteArray as BA
import qualified Data.ByteString as B
import Data.ByteString.Random.MWC
import qualified Data.HashTree as HT
import Data.Maybe
import Data.Serialize (encode)

import GHC.Generics

import Numeric.Natural

import System.Random
import qualified System.Random.MWC as MWC

-- internal modules

import qualified Data.MerkleLog as ML

-- -------------------------------------------------------------------------- --
-- Main

main :: IO ()
main = defaultMain
    [ env globalEnv $ \ ~e -> bgroup "main"
        [ bgroup "create tree"
            [ bgroup "SHA512t_256"
                [ createBench @(ML SHA512t_256) e
                , createBench @(HT SHA512t_256) e
                ]
            , bgroup "SHA256"
                [ createBench @(ML SHA256) e
                , createBench @(HT SHA256) e
                ]
            , bgroup "SHA3_256"
                [ createBench @(ML SHA3_256) e
                , createBench @(HT SHA3_256) e
                , createBench @MT e
                ]
            , bgroup "BLAKE2b_256"
                [ createBench @(ML Blake2b_256) e
                ]
            ]
        , bgroup "create inclusion proof"
            [ bgroup "SHA512t_256"
                [ proofBench @(ML SHA512t_256) e
                , proofBench @(HT SHA512t_256) e
                ]
            , bgroup "SHA256"
                [ proofBench @(ML SHA256) e
                , proofBench @(HT SHA256) e
                ]
            , bgroup "SHA3_256"
                [ proofBench @(ML SHA3_256) e
                , proofBench @(HT SHA3_256) e
                , proofBench @MT e
                ]
            , bgroup "BLAKE2b_256"
                [ proofBench @(ML Blake2b_256) e
                ]
            ]
        , bgroup "verify inclusion proof"
            [ bgroup "SHA512t_256"
                [ verifyBench @(ML SHA512t_256) e
                , verifyBench @(HT SHA512t_256) e
                ]
            , bgroup "SHA256"
                [ verifyBench @(ML SHA256) e
                , verifyBench @(HT SHA256) e
                ]
            , bgroup "SHA3_256"
                [ verifyBench @(ML SHA3_256) e
                , verifyBench @(HT SHA3_256) e
                , verifyBench @MT e
                ]
            , bgroup "BLAKE2b_256"
                [ verifyBench @(ML Blake2b_256) e
                ]
            ]
        ]
    ]

-- -------------------------------------------------------------------------- --
-- Merkle Tree Implementations
-- -------------------------------------------------------------------------- --

-- -------------------------------------------------------------------------- --
-- Global Environment

leafCount :: Int
leafCount = 10000

leafMaxSize :: Int
leafMaxSize = 1000

type GlobalEnv = [B.ByteString]

globalEnv :: IO GlobalEnv
globalEnv = do
    gen <- MWC.create
    traverse (randomGen gen) (randomNats leafCount)
  where

randomNats :: Int -> [Natural]
randomNats i = fmap fromIntegral $ take i $ randomRs @Int (0,leafMaxSize) $ mkStdGen 1

-- -------------------------------------------------------------------------- --
-- Create Benchmark

createBench :: forall a . Impl a => GlobalEnv -> Benchmark
createBench = bench (label @a) . nf (tree @a)

-- -------------------------------------------------------------------------- --
-- Proof Benchmark

type ProofEnv a = (Tree a, B.ByteString, Int)

proofEnv :: forall a . Impl a => GlobalEnv -> IO (ProofEnv a)
proofEnv e = return (tree @a e, e !! 277, 277)

-- | Note that this also includes verification of the proof, because that's the
-- only way we can ensure that the resulting proofs are in normal form.
--
proofBench
    :: forall a
    . Impl a
    => GlobalEnv
    -> Benchmark
proofBench e = env (proofEnv @a e)
    $ bench (label @a) . nf (\(t, ix, i) -> proof @a t ix i)

-- -------------------------------------------------------------------------- --
-- Verify Benchmark

type VerifyEnv a = Proof a

verifyEnv :: forall a . Impl a => GlobalEnv -> IO (VerifyEnv a)
verifyEnv e = return $ proof @a (tree @a e) (e !! 277) 277

verifyBench
    :: forall a
    . Impl a
    => GlobalEnv
    -> Benchmark
verifyBench e = env (verifyEnv @a e) $ bench (label @a) . nf verifyThrow
  where
    verifyThrow p
        | verify @a p = ()
        | otherwise = error "benchmark failure"

-- -------------------------------------------------------------------------- --
-- Merkle Tree Implementations
-- -------------------------------------------------------------------------- --

-- -------------------------------------------------------------------------- --
-- Merkle Tree Implementation Class

class (NFData (Tree a), NFData (Root a), NFData (Proof a)) => Impl a where
    type Tree a
    type Proof a
    type Root a

    label :: String
    tree :: [B.ByteString] -> Tree a
    root :: Tree a -> Root a
    proof :: Tree a -> B.ByteString -> Int -> Proof a
    verify :: Proof a -> Bool

-- -------------------------------------------------------------------------- --
-- merkle-log

data MLProof a = MLProof
    {-# UNPACK #-} !(ML.MerkleProof a)
    {-# UNPACK #-} !(ML.MerkleRoot a)
        -- ^ Root of the Tree
    deriving (Generic)

instance NFData (MLProof a)

data ML a

instance HashAlgorithm a => Impl (ML a) where
    type Tree (ML a) = ML.MerkleTree a
    type Proof (ML a) = MLProof a
    type Root (ML a) = ML.MerkleRoot a

    label = "merkle-log"
    tree = ML.merkleTree @a . fmap ML.InputNode
    root = ML.merkleRoot
    proof t ix i =
        let Right p = ML.merkleProof (ML.InputNode ix) i t
        in MLProof p (ML.merkleRoot t)
    verify (MLProof p r) = ML.runMerkleProof p == r

    {-# INLINE label #-}
    {-# INLINE tree #-}
    {-# INLINE root #-}
    {-# INLINE proof #-}
    {-# INLINE verify #-}

-- -------------------------------------------------------------------------- --
-- merkle-tree package

data MTProof = MTProof
    !(MT.MerkleProof B.ByteString)
    {-# UNPACK #-} !B.ByteString
        -- ^ Proof subject (leaf)
    {-# UNPACK #-} !(MT.MerkleRoot B.ByteString)
        -- ^ Root of the Tree

-- | The merkle-tree package doesn't export the 'ProofElem'. Without that the
-- 'Generic' instance for 'MT.MerkleProof' become almost useless. In particular
-- we can't define an 'NFData' instance.
--
-- This instance is a workaround that probably leads to worse benchmark results.
--
instance NFData MTProof where
    -- rnf (MTProof p subj r) = rnf
    --     $ MT.validateMerkleProof p r $ MT.mkLeafRootHash subj
    rnf (MTProof p _ _) = rnf $ encode p
    {-# INLINE rnf #-}

instance NFData (MT.MerkleRoot B.ByteString) where
    rnf r = rnf (MT.getMerkleRoot r)
    {-# INLINE rnf #-}

instance NFData (MT.MerkleTree B.ByteString) where
    rnf t = rnf $ MT.mtRoot t
    {-# INLINE rnf #-}

data MT

instance Impl MT where
    type Tree MT = MT.MerkleTree B.ByteString
    type Proof MT = MTProof
    type Root MT = MT.MerkleRoot B.ByteString

    label = "merkle-tree"
    tree = MT.mkMerkleTree
    root = MT.mtRoot
    proof t subj _ = MTProof
        (MT.merkleProof t (MT.mkLeafRootHash subj))
        subj
        (MT.mtRoot t)
    verify (MTProof p subj r)
        = MT.validateMerkleProof p r (MT.mkLeafRootHash subj)

    {-# INLINE label #-}
    {-# INLINE tree #-}
    {-# INLINE root #-}
    {-# INLINE proof #-}
    {-# INLINE verify #-}

-- -------------------------------------------------------------------------- --
-- hash-tree package

data HTProof a = HTProof
    {-# UNPACK #-} !(HT.InclusionProof a)
    {-# UNPACK #-} !B.ByteString
        -- ^ Proof subject (leaf)
    {-# UNPACK #-} !(Digest a)
        -- ^ Root of the Tree
    deriving (Generic)

instance NFData (HTProof a)

instance NFData (HT.MerkleHashTrees B.ByteString a) where
    rnf t = rnf $ HT.digest (HT.size t) t
    {-# INLINE rnf #-}

instance NFData (HT.InclusionProof a) where
    rnf p = rnf (HT.leafIndex p)
        `seq` rnf (HT.treeSize p)
        `seq` rnf (HT.inclusion p)
    {-# INLINE rnf #-}

data HT a

htSettings :: forall a . HashAlgorithm a => HT.Settings B.ByteString a
htSettings = HT.defaultSettings
    { HT.hash0 = hash @B.ByteString @a mempty
    , HT.hash1 = \x -> hash @_ @a (B.singleton 0x00 `B.append` x)
    , HT.hash2 = \x y -> hash @_ @a $ B.concat [B.singleton 0x01, BA.convert x, BA.convert y]
    }

instance HashAlgorithm a => Impl (HT a) where
    type Tree (HT a) = HT.MerkleHashTrees B.ByteString a
    type Proof (HT a) = HTProof a
    type Root (HT a) = Digest a

    label = "hash-tree"
    tree = HT.fromList htSettings
    root t = fromJust $ HT.digest (HT.size t) t
    proof t ix _ = HTProof
        (fromJust $ HT.generateInclusionProof (HT.hash1 (htSettings @a) ix) (HT.size t) t)
        ix
        (root @(HT a) t)
    verify (HTProof p subj r) = HT.verifyInclusionProof
        (htSettings @a) (HT.hash1 (htSettings @a) subj) r p

    {-# INLINE label #-}
    {-# INLINE tree #-}
    {-# INLINE root #-}
    {-# INLINE proof #-}
    {-# INLINE verify #-}

