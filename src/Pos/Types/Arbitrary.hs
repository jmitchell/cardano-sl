{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}

-- | `Arbitrary` instances for core types for using in tests and benchmarks

module Pos.Types.Arbitrary
       ( BadSigsTx (..)
       , GoodTx (..)
       , SmallBadSigsTx (..)
       , SmallHashMap (..)
       , SmallGoodTx (..)
       ) where

import qualified Data.ByteString            as BS (pack)
import           Data.Char                  (chr)
import           Data.DeriveTH              (derive, makeArbitrary)
import           Data.Time.Units            (Microsecond, Millisecond, fromMicroseconds)
import           System.Random              (Random)
import           Test.QuickCheck            (Arbitrary (..), Gen, NonEmptyList (..),
                                             choose, choose, elements, oneof, scale)
import           Test.QuickCheck.Instances  ()
import           Universum

import           Pos.Binary.Class           (FixedSizeInt (..), SignedVarInt (..),
                                             UnsignedVarInt (..))
import           Pos.Binary.Types           ()
import           Pos.Constants              (epochSlots, sharedSeedLength)
import           Pos.Crypto                 (PublicKey, SecretKey, Share, hash, sign,
                                             toPublic)
import           Pos.Data.Attributes        (mkAttributes)
import           Pos.Script                 (Script)
import           Pos.Script.Examples        (badIntRedeemer, goodIntRedeemer,
                                             intValidator)
import           Pos.Types.Address          (makePubKeyAddress, makeScriptAddress)
import           Pos.Types.Arbitrary.Unsafe ()
import           Pos.Types.Core             (Address (..), ChainDifficulty (..), Coin,
                                             CoinPortion, EpochIndex (..),
                                             EpochOrSlot (..), LocalSlotIndex (..),
                                             SlotId (..), Timestamp (..), mkCoin,
                                             unsafeCoinPortionFromDouble, unsafeGetCoin)
import           Pos.Types.Types            (SharedSeed (..), Tx (..),
                                             TxDistribution (..), TxIn (..),
                                             TxInWitness (..), TxOut (..), TxOutAux)
import           Pos.Types.Version          (ApplicationName (..), BlockVersion (..),
                                             SoftwareVersion (..),
                                             applicationNameMaxLength)
import           Pos.Util                   (AsBinary, makeSmall)

----------------------------------------------------------------------------
-- Arbitrary core types
----------------------------------------------------------------------------

instance Arbitrary Script where
    arbitrary = elements
        [intValidator, goodIntRedeemer, badIntRedeemer]

instance Arbitrary Address where
    arbitrary = oneof [
        makePubKeyAddress <$> arbitrary,
        makeScriptAddress <$> arbitrary,
        UnknownAddressType <$> choose (2, 255) <*> scale (min 150) arbitrary
        ]

deriving instance Arbitrary ChainDifficulty

derive makeArbitrary ''TxOut

instance Arbitrary Coin where
    arbitrary = mkCoin <$> choose (1, unsafeGetCoin maxBound)

instance Arbitrary CoinPortion where
    arbitrary = unsafeCoinPortionFromDouble . (1/) <$> choose (1, 20)

maxReasonableEpoch :: Integral a => a
maxReasonableEpoch = 5 * 1000 * 1000 * 1000 * 1000  -- 5 * 10^12, because why not

deriving instance Random EpochIndex

instance Arbitrary EpochIndex where
    arbitrary = choose (0, maxReasonableEpoch)

deriving instance Random LocalSlotIndex

instance Arbitrary LocalSlotIndex where
    arbitrary = choose (0, epochSlots - 1)

instance Arbitrary SlotId where
    arbitrary = SlotId
        <$> arbitrary
        <*> arbitrary

instance Arbitrary EpochOrSlot where
    arbitrary = oneof [
          EpochOrSlot . Left <$> arbitrary
        , EpochOrSlot . Right <$> arbitrary
        ]

instance Arbitrary TxInWitness where
    arbitrary = oneof [
        PkWitness <$> arbitrary <*> arbitrary,
        -- this can generate a redeemer script where a validator script is
        -- needed and vice-versa, but it doesn't matter
        ScriptWitness <$> arbitrary <*> arbitrary,
        UnknownWitnessType <$> choose (2, 255) <*> scale (min 150) arbitrary ]

derive makeArbitrary ''TxDistribution
derive makeArbitrary ''TxIn

-- | Arbitrary transactions generated from this instance will only be valid
-- with regards to 'verifyTxAlone'

instance Arbitrary Tx where
    arbitrary = do
        txIns <- getNonEmpty <$> arbitrary
        txOuts <- getNonEmpty <$> arbitrary
        return $ Tx txIns txOuts (mkAttributes ())

-- | Type used to generate valid (w.r.t 'verifyTxAlone' and 'verifyTx')
-- transactions and accompanying input information.
-- It's not entirely general because it only generates transactions whose
-- outputs are in the same number as its inputs in a one-to-one correspondence.
--
-- The GoodTx type is a list of triples where the third elements are the
-- transaction's outputs, the second elements are its inputs, and the first are
-- the transactions from where the tuple's TxIn came from.
--
-- The OverflowTx type is the same as GoodTx, except its values, both for
-- inputs as well as outputs, are very close to maxBound :: Coin so as to cause
-- overflow in the Coin type if they are summed.
--
-- The BadSigTx type is also the same as GoodTx, with the difference that all
-- signatures in the transaction's inputs have been replaced with a bogus one.

buildProperTx
    :: [(Tx, SecretKey, SecretKey, Coin)]
    -> (Coin -> Coin, Coin -> Coin)
    -> Gen [((Tx, TxDistribution), TxIn, TxOutAux, TxInWitness)]
buildProperTx triplesList (inCoin, outCoin) = do
        let fun (Tx txIn txOut _, fromSk, toSk, c) =
                let inC = inCoin c
                    outC = outCoin c
                    txToBeSpent = Tx txIn ((makeTxOutput fromSk inC) : txOut) (mkAttributes ())
                in (txToBeSpent, fromSk, makeTxOutput toSk outC)
            -- why is it called txList? I've no idea what's going on here
            txList = fmap fun triplesList
            txOutsHash = hash $ fmap (view _3) txList
            distrHash = hash (TxDistribution (replicate (length txList) []))
            makeNullDistribution tx =
                TxDistribution (replicate (length (txOutputs tx)) [])
            newTx (tx, fromSk, txOutput) =
                let txHash = hash tx
                    txIn = TxIn txHash 0
                    witness = PkWitness {
                        twKey = toPublic fromSk,
                        twSig = sign fromSk (txHash, 0, txOutsHash, distrHash) }
                in ((tx, makeNullDistribution tx),
                    txIn, (txOutput, []), witness)
            makeTxOutput s c = TxOut (makePubKeyAddress $ toPublic s) c
            goodTx = fmap newTx txList
        return goodTx

-- | Well-formed transaction 'Tx'.
newtype GoodTx = GoodTx
    { getGoodTx :: [((Tx, TxDistribution), TxIn, TxOutAux, TxInWitness)]
    } deriving (Show)

newtype SmallGoodTx =
    SmallGoodTx GoodTx
    deriving Show

instance Arbitrary GoodTx where
    arbitrary = GoodTx <$> do
        txsList <- getNonEmpty <$>
            (arbitrary :: Gen (NonEmptyList (Tx, SecretKey, SecretKey, Coin)))
        buildProperTx txsList (identity, identity)

instance Arbitrary SmallGoodTx where
    arbitrary = SmallGoodTx <$> makeSmall arbitrary


-- | Ill-formed 'Tx' with bad signatures.
newtype BadSigsTx = BadSigsTx
    { getBadSigsTx :: [((Tx, TxDistribution), TxIn, TxOutAux, TxInWitness)]
    } deriving (Show)

newtype SmallBadSigsTx =
    SmallBadSigsTx BadSigsTx
    deriving Show

instance Arbitrary BadSigsTx where
    arbitrary = BadSigsTx <$> do
        goodTxList <- getGoodTx <$> arbitrary
        badSig <- arbitrary
        return $ map (set _4 badSig) goodTxList

instance Arbitrary SmallBadSigsTx where
    arbitrary = SmallBadSigsTx <$> makeSmall arbitrary

instance Arbitrary SharedSeed where
    arbitrary = do
        bs <- replicateM sharedSeedLength (choose (0, 255))
        return $ SharedSeed $ BS.pack bs

----------------------------------------------------------------------------
-- Arbitrary types from MainExtra[header/body]data
----------------------------------------------------------------------------

instance Arbitrary ApplicationName where
    arbitrary = ApplicationName  .
        toText                   .
        map (chr . flip mod 128) .
        take applicationNameMaxLength <$> arbitrary

derive makeArbitrary ''BlockVersion
derive makeArbitrary ''SoftwareVersion

----------------------------------------------------------------------------
-- Arbitrary miscellaneous types
----------------------------------------------------------------------------

instance Arbitrary Millisecond where
    arbitrary = fromMicroseconds <$> choose (0, 600 * 1000 * 1000)

instance Arbitrary Microsecond where
    arbitrary = fromMicroseconds <$> choose (0, 600 * 1000 * 1000)

deriving instance Arbitrary Timestamp

newtype SmallHashMap =
    SmallHashMap (HashMap PublicKey (HashMap PublicKey (AsBinary Share)))
    deriving Show

instance Arbitrary SmallHashMap where
    arbitrary = SmallHashMap <$> makeSmall arbitrary

derive makeArbitrary ''UnsignedVarInt
derive makeArbitrary ''SignedVarInt
derive makeArbitrary ''FixedSizeInt
