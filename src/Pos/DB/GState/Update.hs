{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

-- | Part of GState DB which stores data necessary for update system.

module Pos.DB.GState.Update
       (
         -- * Getters
         getAdoptedBV
       , getAdoptedBVData
       , getAdoptedBVFull
       , getBVState
       , getProposalState
       , getAppProposal
       , getProposalStateByApp
       , getConfirmedSV
       , getSlotDuration
       , getMaxBlockSize

         -- * Operations
       , UpdateOp (..)

         -- * Initialization
       , prepareGStateUS

        -- * Iteration
       , PropIter
       , runProposalMapIterator
       , runProposalIterator
       , getOldProposals
       , getDeepProposals

       , ConfPropIter
       , getConfirmedProposals

       , BVIter
       , getProposedBVs
       , getConfirmedBVStates
       , getProposedBVStates
       ) where

import           Control.Monad.Trans.Maybe  (MaybeT (..), runMaybeT)
import           Data.Time.Units            (Millisecond)
import qualified Database.RocksDB           as Rocks
import           Serokell.Data.Memory.Units (Byte)
import           Universum

import           Pos.Binary.Class           (encodeStrict)
import           Pos.Binary.DB              ()
import           Pos.Constants              (ourAppName)
import           Pos.Crypto                 (hash)
import           Pos.DB.Class               (MonadDB, getUtxoDB)
import           Pos.DB.Error               (DBError (DBMalformed))
import           Pos.DB.Functions           (RocksBatchOp (..), encodeWithKeyPrefix,
                                             rocksWriteBatch)
import           Pos.DB.GState.Common       (getBi)
import           Pos.DB.Iterator            (DBIteratorClass (..), DBnIterator,
                                             DBnMapIterator, IterType, runDBnIterator,
                                             runDBnMapIterator)
import           Pos.DB.Types               (NodeDBs (..))
import           Pos.Genesis                (genesisBlockVersion, genesisBlockVersionData,
                                             genesisSlotDuration, genesisSoftwareVersions)
import           Pos.Types                  (ApplicationName, BlockVersion,
                                             ChainDifficulty, NumSoftwareVersion, SlotId,
                                             SoftwareVersion (..))
import           Pos.Update.Core            (BlockVersionData (..), UpId,
                                             UpdateProposal (..))
import           Pos.Update.Poll.Types      (BlockVersionState (..),
                                             ConfirmedProposalState,
                                             DecidedProposalState (dpsDifficulty),
                                             ProposalState (..),
                                             UndecidedProposalState (upsSlot),
                                             cpsSoftwareVersion, psProposal)
import           Pos.Util                   (maybeThrow)
import           Pos.Util.Iterator          (MonadIterator (..))

----------------------------------------------------------------------------
-- Getters
----------------------------------------------------------------------------

-- | Get last adopted block version.
getAdoptedBV :: MonadDB ssc m => m BlockVersion
getAdoptedBV = fst <$> getAdoptedBVFull

-- | Get state of last adopted BlockVersion.
getAdoptedBVData :: MonadDB ssc m => m BlockVersionData
getAdoptedBVData = snd <$> getAdoptedBVFull

-- | Get last adopted BlockVersion and data associated with it.
getAdoptedBVFull :: MonadDB ssc m => m (BlockVersion, BlockVersionData)
getAdoptedBVFull = maybeThrow (DBMalformed msg) =<< getAdoptedBVFullMaybe
  where
    msg =
        "Update System part of GState DB is not initialized (last adopted BV is missing)"

-- | Get actual slot duration.
getSlotDuration :: MonadDB ssc m => m Millisecond
getSlotDuration = pure genesisSlotDuration
-- getSlotDuration = bvdSlotDuration <$> getAdoptedBVData

-- | Get maximum block size (in bytes).
getMaxBlockSize :: MonadDB ssc m => m Byte
getMaxBlockSize = bvdMaxBlockSize <$> getAdoptedBVData

-- | Get 'BlockVersionState' associated with given BlockVersion.
getBVState :: MonadDB ssc m => BlockVersion -> m (Maybe BlockVersionState)
getBVState = getBi . bvStateKey

-- | Get state of UpdateProposal for given UpId
getProposalState :: MonadDB ssc m => UpId -> m (Maybe ProposalState)
getProposalState = getBi . proposalKey

-- | Get UpId of current proposal for given appName
getAppProposal :: MonadDB ssc m => ApplicationName -> m (Maybe UpId)
getAppProposal = getBi . proposalAppKey

-- | Get state of Update Proposal for given AppName
getProposalStateByApp :: MonadDB ssc m => ApplicationName -> m (Maybe ProposalState)
getProposalStateByApp appName =
    runMaybeT $ MaybeT (getAppProposal appName) >>= MaybeT . getProposalState

-- | Get last confirmed SoftwareVersion of given application.
getConfirmedSV
    :: MonadDB ssc m
    => ApplicationName -> m (Maybe NumSoftwareVersion)
getConfirmedSV = getBi . confirmedVersionKey

----------------------------------------------------------------------------
-- Operations
----------------------------------------------------------------------------

data UpdateOp
    = PutProposal !ProposalState
    | DeleteProposal !UpId !ApplicationName
    | ConfirmVersion !SoftwareVersion
    | DelConfirmedVersion !ApplicationName
    | AddConfirmedProposal !ConfirmedProposalState
    | DelConfirmedProposal !SoftwareVersion
    | SetAdopted !BlockVersion BlockVersionData
    | SetBVState !BlockVersion !BlockVersionState
    | DelBV !BlockVersion

instance RocksBatchOp UpdateOp where
    toBatchOp (PutProposal ps) =
        [ Rocks.Put (proposalKey upId) (encodeStrict ps)
        , Rocks.Put (proposalAppKey appName) (encodeStrict upId)
        ]
      where
        up = psProposal ps
        upId = hash up
        appName = svAppName $ upSoftwareVersion up
    toBatchOp (DeleteProposal upId appName) =
        [Rocks.Del (proposalAppKey appName), Rocks.Del (proposalKey upId)]
    toBatchOp (ConfirmVersion sv) =
        [Rocks.Put (confirmedVersionKey $ svAppName sv) (encodeStrict $ svNumber sv)]
    toBatchOp (DelConfirmedVersion app) =
        [Rocks.Del (confirmedVersionKey app)]
    toBatchOp (AddConfirmedProposal cps) =
        [Rocks.Put (confirmedProposalKey cps) (encodeStrict cps)]
    toBatchOp (DelConfirmedProposal sv) =
        [Rocks.Del (confirmedProposalKeySV sv)]
    toBatchOp (SetAdopted bv bvd) =
        [Rocks.Put adoptedBVKey (encodeStrict (bv, bvd))]
    toBatchOp (SetBVState bv st) =
        [Rocks.Put (bvStateKey bv) (encodeStrict st)]
    toBatchOp (DelBV bv) =
        [Rocks.Del (bvStateKey bv)]

----------------------------------------------------------------------------
-- Initialization
----------------------------------------------------------------------------

prepareGStateUS
    :: forall ssc m.
       MonadDB ssc m
    => m ()
prepareGStateUS =
    unlessM isInitialized $ do
        db <- getUtxoDB
        flip rocksWriteBatch db $
            SetAdopted genesisBlockVersion genesisBlockVersionData :
            map ConfirmVersion genesisSoftwareVersions

isInitialized :: MonadDB ssc m => m Bool
isInitialized = isJust <$> getAdoptedBVFullMaybe

----------------------------------------------------------------------------
-- Iteration
----------------------------------------------------------------------------

data PropIter

instance DBIteratorClass PropIter where
    type IterKey PropIter = UpId
    type IterValue PropIter = ProposalState
    iterKeyPrefix _ = iterationPrefix

runProposalIterator
    :: forall m ssc a . MonadDB ssc m
    => DBnIterator ssc PropIter a -> m a
runProposalIterator = runDBnIterator @PropIter _gStateDB

runProposalMapIterator
    :: forall v m ssc a . MonadDB ssc m
    => DBnMapIterator ssc PropIter v a -> (IterType PropIter -> v) -> m a
runProposalMapIterator = runDBnMapIterator @PropIter _gStateDB


-- TODO: it can be optimized by storing some index sorted by
-- 'SlotId's, but I don't think it may be crucial.
-- | Get all proposals which were issued no later than given slot.
getOldProposals
    :: forall ssc m. MonadDB ssc m
    => SlotId -> m [UndecidedProposalState]
getOldProposals slotId = runProposalMapIterator (step []) snd
  where
    step res = nextItem >>= maybe (pure res) (onItem res)
    onItem res e
        | PSUndecided u <- e
        , upsSlot u <= slotId = step (u:res)
        | otherwise = step res

-- TODO: eliminate copy-paste here!

-- | Get all decided proposals which were accepted deeper than given
-- difficulty.
getDeepProposals
    :: forall ssc m. MonadDB ssc m
    => ChainDifficulty -> m [DecidedProposalState]
getDeepProposals cd = runProposalMapIterator (step []) snd
  where
    step res = nextItem >>= maybe (pure res) (onItem res)
    onItem res e
        | PSDecided u <- e
        , Just proposalDifficulty <- dpsDifficulty u
        , proposalDifficulty <= cd = step (u : res)
        | otherwise = step res

-- Iterator by confirmed proposals
data ConfPropIter

instance DBIteratorClass ConfPropIter where
    type IterKey ConfPropIter = SoftwareVersion
    type IterValue ConfPropIter = ConfirmedProposalState
    iterKeyPrefix _ = confirmedIterationPrefix

-- | Get confirmed proposals which update our application and have
-- version bigger than argument (or all proposals if 'Nothing' is
-- passed). For instance, current software version can be passed to
-- this function to get all proposals with bigger version.
getConfirmedProposals
    :: MonadDB ssc m
    => Maybe NumSoftwareVersion -> m [ConfirmedProposalState]
getConfirmedProposals reqNsv = runDBnIterator @ConfPropIter _gStateDB (step [])
  where
    step res = nextItem >>= maybe (pure res) (onItem res)
    onItem res (SoftwareVersion {..}, cps) =
        step $
        case reqNsv of
            Nothing -> cps : res
            Just v
                | svAppName == ourAppName && svNumber > v -> cps : res
                | otherwise -> res

-- Iterator by block versions
data BVIter

instance DBIteratorClass BVIter where
    type IterKey BVIter = BlockVersion
    type IterValue BVIter = BlockVersionState
    iterKeyPrefix _ = bvStateIterationPrefix

-- | Get all proposed 'BlockVersion's.
getProposedBVs :: MonadDB ssc m => m [BlockVersion]
getProposedBVs = runDBnMapIterator @BVIter _gStateDB (step []) fst
  where
    step res = nextItem >>= maybe (pure res) (onItem res)
    onItem res = step . (: res)

getProposedBVStates :: MonadDB ssc m => m [BlockVersionState]
getProposedBVStates = runDBnMapIterator @BVIter _gStateDB (step []) snd
  where
    step res = nextItem >>= maybe (pure res) (onItem res)
    onItem res = step . (: res)

-- | Get all confirmed 'BlockVersion's and their states.
getConfirmedBVStates :: MonadDB ssc m => m [(BlockVersion, BlockVersionState)]
getConfirmedBVStates = runDBnIterator @BVIter _gStateDB (step [])
  where
    step res = nextItem >>= maybe (pure res) (onItem res)
    onItem res (bv, bvs@BlockVersionState {..})
        | bvsIsConfirmed = step ((bv, bvs) : res)
        | otherwise = step res

----------------------------------------------------------------------------
-- Keys ('us' prefix stands for Update System)
----------------------------------------------------------------------------

adoptedBVKey :: ByteString
adoptedBVKey = "us/adopted-block-version/"

bvStateKey :: BlockVersion -> ByteString
bvStateKey = encodeWithKeyPrefix @BVIter

bvStateIterationPrefix :: ByteString
bvStateIterationPrefix = "us/bvs/"

proposalKey :: UpId -> ByteString
proposalKey = encodeWithKeyPrefix @PropIter

proposalAppKey :: ApplicationName -> ByteString
proposalAppKey = mappend "us/an/" . encodeStrict

confirmedVersionKey :: ApplicationName -> ByteString
confirmedVersionKey = mappend "us/cv/" . encodeStrict

iterationPrefix :: ByteString
iterationPrefix = "us/p/"

confirmedProposalKey :: ConfirmedProposalState -> ByteString
confirmedProposalKey = encodeWithKeyPrefix @ConfPropIter . cpsSoftwareVersion

confirmedProposalKeySV :: SoftwareVersion -> ByteString
confirmedProposalKeySV = encodeWithKeyPrefix @ConfPropIter

confirmedIterationPrefix :: ByteString
confirmedIterationPrefix = "us/cp/"

----------------------------------------------------------------------------
-- Details
----------------------------------------------------------------------------

getAdoptedBVFullMaybe :: MonadDB ssc m => m (Maybe (BlockVersion, BlockVersionData))
getAdoptedBVFullMaybe = getBi adoptedBVKey
