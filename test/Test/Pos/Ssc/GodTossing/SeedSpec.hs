-- | Specification of Pos.calculateSeed

module Test.Pos.Ssc.GodTossing.SeedSpec
       ( spec
       ) where

import           Crypto.Random            (MonadRandom)
import qualified Data.HashMap.Strict      as HM
import           Data.List                (unzip, (\\))
import qualified Data.List.NonEmpty       as NE
import           Formatting               (build, int, sformat, (%))
import           Serokell.Util            (listJson)
import           Test.Hspec               (Spec, describe, pending)
import           Test.Hspec.QuickCheck    (modifyMaxSize, modifyMaxSuccess, prop)
import           Test.QuickCheck          (Property, choose, counterexample, generate,
                                           ioProperty, property, sized, (===))
import           Test.QuickCheck.Property (failed, succeeded)
import           Universum
import           Unsafe                   ()

import           Pos.Crypto               (KeyPair (..), PublicKey, Share, Threshold,
                                           VssKeyPair, decryptShare, sign, toVssPublicKey)
import           Pos.Ssc.GodTossing       (Commitment (..), CommitmentsMap, Opening (..),
                                           SeedError (..), calculateSeed,
                                           genCommitmentAndOpening, mkCommitmentsMap,
                                           secretToSharedSeed)
import           Pos.Types                (SharedSeed (..))
import           Pos.Types.Address        (AddressHash, addressHash)
import           Pos.Util                 (AsBinaryClass (..), nonrepeating, sublistN)

getPubAddr :: KeyPair -> AddressHash PublicKey
getPubAddr = addressHash . getPub

spec :: Spec
spec = do
    -- note that we can't make max size larger than 50 without changing it in
    -- Test.Pos.Util as well
    describe "SharedSeed" $ do
        prop description_xorFormsAbelianGroup xorFormsAbelianGroup
    let smaller = modifyMaxSize (const 40) . modifyMaxSuccess (const 30)
    describe "calculateSeed" $ smaller $ do
        prop
            "finds the seed when all openings are present" $
            do n <- sized $ \size -> choose (1, max size 1)
               return $ recoverSecretsProp n n 0 0
        prop
            "finds the seed when all shares are present" $
            do n <- sized $ \size -> choose (1, max size 1)
               return $ recoverSecretsProp n 0 n 0
        prop
            "finds the seed when all secrets can be recovered" $
            do n <- sized $ \size -> choose (1, max size 1)
               n_overlap <- choose (0, n)
               n_openings <- choose (n_overlap, n)
               let n_shares = n - n_openings + n_overlap
               return $ recoverSecretsProp n n_openings n_shares n_overlap
        -- [CSL-50]: we are in process of thinking about this property
        -- prop
        --     "fails to find the seed when some secrets can't be recovered" $
        --     do n <- sized $ \size -> choose (1, max size 1)
        --        n_overlap <- choose (0, n-1)
        --        n_openings <- choose (n_overlap, n-1)
        --        n_shares <- choose (n_overlap, n - n_openings + n_overlap - 1)
        --        -- to succeed, it must be that
        --        -- n_openings + n_shares - n_overlap >= n
        --        return $ recoverSecretsProp n n_openings n_shares n_overlap
        prop "secret recovering works" pending
  where
      description_xorFormsAbelianGroup =
          "under the xor operation, the set of ftsSeedLength-byte SharedSeeds is an\
          \ abelian group"

----------------------------------------------------------------------------
-- Properties
----------------------------------------------------------------------------

xorFormsAbelianGroup :: SharedSeed -> SharedSeed -> SharedSeed -> Bool
xorFormsAbelianGroup fts1 fts2 fts3 =
    let isAssociative =
            let assoc1 = (fts1 <> fts2) <> fts3
                assoc2 = fts1 <> (fts2 <> fts3)
            in assoc1 == assoc2
        hasIdentity =
            let id1 = mempty <> fts1
                id2 = fts1 <> mempty
            in (fts1 == id1) && (fts1 == id2)
        hasInverses =
            let inv1 = fts1 <> fts2
                inv2 = inv1 <> fts2
                inv3 = fts1 <> inv1
            in inv2 == fts1 && inv3 == fts2
        isCommutative =
            let comm1 = fts1 <> fts2
                comm2 = fts2 <> fts1
            in comm1 == comm2
    in isAssociative && hasIdentity && hasInverses && isCommutative

-- | When each party has provided either an opening or shares (or both), we
-- should be able to recover the secret. When at least somebody hasn't
-- provided an opening or a secret, we should fail.
--
-- Specifically, we simulate the following scenario:
--
-- * Everybody has sent a commitment and generated a seed.
-- * 'n_openings' nodes have sent openings to the blockchain.
-- * 'n_shares' nodes have sent their shares to other nodes.
-- * /Among those,/ 'n_overlap' nodes have sent both.
-- * All nodes have sent -shares they have received- to the blockchain.
--   'n' shares are required to recover a secret.
recoverSecretsProp
    :: Int         -- ^ Number of parties
    -> Int         -- ^ How many have sent an opening
    -> Int         -- ^ How many have sent shares
    -> Int         -- ^ How many have sent both (the “overlap” parameter)
    -> Property
recoverSecretsProp n n_openings n_shares n_overlap
    | any (< 0) [n, n_openings, n_shares, n_overlap] = panic "negative"
    | n == 0                 = panic "n == 0"
    | n_overlap > n_openings = panic "n_overlap > n_openings"
    | n_overlap > n_shares   = panic "n_overlap > n_shares"
    | n_openings > n         = panic "n_openings > n"
    | n_shares > n           = panic "n_shares > n"
    -- there's a lower bound for the overlap, too (e.g. n=3,
    -- openings=2, shares=2, then overlap must be at least 1)
    | n - n_openings - n_shares + n_overlap < 0 = panic "overlap condition"

recoverSecretsProp n n_openings n_shares n_overlap = ioProperty $ do
    let threshold = pickThreshold n
    (keys, vssKeys, comms, opens) <- generateKeysAndMpc threshold n
    let des = fromBinary
        seeds :: [SharedSeed]
        seeds = rights $ map (fmap secretToSharedSeed . des . getOpening) opens
    let expectedSharedSeed :: SharedSeed
        expectedSharedSeed = mconcat seeds
    haveSentBoth <- generate $
        sublistN n_overlap keys
    haveSentOpening <- generate $
        (haveSentBoth ++) <$>
        sublistN (n_openings - n_overlap) (keys \\ haveSentBoth)
    haveSentShares <- generate $
        (haveSentBoth ++) <$>
        sublistN (n_shares - n_overlap) (keys \\ haveSentOpening)
    let commitmentsMap = mkCommitmentsMap' keys comms
    let openingsMap = HM.fromList
            [(getPubAddr k, o)
              | (k, o) <- zip keys opens
              , k `elem` haveSentOpening]
    -- @generatedShares ! X@ = shares that X generated and sent to others
    -- generatedShares :: HashMap PublicKey (HashMap PublicKey Share)
    generatedShares <- do
        let sentShares (kp, _) = kp `elem` haveSentShares
        fmap HM.fromList $ forM (filter sentShares (zip keys comms)) $
            \(kp, comm) -> do
                let addr = getPubAddr kp
                decShares <- concat <$> getDecryptedShares vssKeys comm
                return (addr, HM.fromList (zip (map getPubAddr keys) decShares))
    -- @sharesMap ! X@ = shares that X received from others
    let sharesMap = HM.fromList $ do
             addr <- getPubAddr <$> keys
             let ser = asBinary @Share
                 receivedShares = HM.fromList $ do
                     (sender, senderShares) <- HM.toList generatedShares
                     case HM.lookup addr senderShares of
                         Nothing -> []
                         Just s  -> return (sender, one $ ser s)
             return (addr, receivedShares)

    let shouldSucceed = n_openings + n_shares - n_overlap >= n
    let result = calculateSeed commitmentsMap openingsMap sharesMap
    let debugInfo = sformat ("n = "%int%", n_openings = "%int%", "%
                             "n_shares = "%int%", n_overlap = "%int%
                             "\n"%
                             "these keys have sent openings:\n"%
                             "  "%listJson%"\n"%
                             "these keys have sent shares they got:\n"%
                             "  "%listJson)
                        n n_openings n_shares n_overlap
                        (map getPub haveSentOpening)
                        (map getPub haveSentShares)
    return $ counterexample (toString debugInfo) $ case (shouldSucceed, result) of
        -- we were supposed to find the seed
        (True, Right sharedSeed) ->
            sharedSeed === expectedSharedSeed
        (True, Left ftsErr) ->
            let err = sformat ("calculateSeed didn't find the seed (but "%
                               "should've) and failed with error:\n"%
                               "  "%build)
                              ftsErr
            in counterexample (toString err) failed
        -- we weren't supposed to find the seed
        (False, Left (NoSecretFound _)) ->
            property succeeded
        (False, Left ftsErr) ->
            let err = sformat ("calculateSeed failed with error "%build%" "%
                               "instead of NoSecretFound")
                              ftsErr
            in counterexample (toString err) failed
        (False, Right sharedSeed) ->
            let err = sformat ("calculateSeed succeeded, "%
                               "even though it couldn't\n"%
                               "  found seed: "%build%"\n"%
                               "  right seed: "%build)
                              sharedSeed expectedSharedSeed
            in counterexample (toString err <> "\n\n" <> show (n, threshold) <> "\n\n" <> show commitmentsMap <> "\n\n" <> show openingsMap <> "\n\n" <> show sharesMap) failed

----------------------------------------------------------------------------
-- Helper functions
----------------------------------------------------------------------------

generateKeysAndMpc
    :: Threshold
    -> Int
    -> IO ([KeyPair], NonEmpty VssKeyPair, [Commitment], [Opening])
-- genCommitmentAndOpening fails on 0
generateKeysAndMpc _         0 = panic "generateKeysAndMpc: 0 is passed"
generateKeysAndMpc threshold n = do
    keys           <- generate $ nonrepeating n
    vssKeys        <- generate $ nonrepeating n
    let lvssPubKeys = NE.fromList $ map (asBinary . toVssPublicKey) vssKeys
    (comms, opens) <-
        unzip <$>
            replicateM n (genCommitmentAndOpening threshold lvssPubKeys)
    return (keys, NE.fromList vssKeys, comms, opens)

mkCommitmentsMap' :: [KeyPair] -> [Commitment] -> CommitmentsMap
mkCommitmentsMap' keys comms =
    mkCommitmentsMap $ do
        (KeyPair pk sk, comm) <- zip keys comms
        let epochIdx = 0  -- we don't care here
        let sig = sign sk (epochIdx, comm)
        return (pk, comm, sig)

getDecryptedShares
    :: MonadRandom m
    => NonEmpty VssKeyPair -> Commitment -> m [[Share]]
getDecryptedShares vssKeys comm =
    forM (fmap (second $ traverse fromBinary) $ HM.toList (commShares comm)) $
        \(pubKey, encShare) -> do
            let secKey = case find ((== pubKey) . asBinary . toVssPublicKey) vssKeys of
                    Just k  -> k
                    Nothing -> panic $
                        sformat ("getDecryptedShares: counldn't \
                                 \find key "%build) pubKey
                encShare' = case encShare of
                    Right encS -> encS
                    _          -> panic $
                        "@getDecryptedShares: could not deserialize LEncShare"
            toList <$> mapM (decryptShare secKey) encShare'

pickThreshold :: Int -> Threshold
pickThreshold n = fromIntegral (n `div` 2 + n `mod` 2)
