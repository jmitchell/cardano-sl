{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}

-- | Instance of SscWorkersClass.

module Pos.Ssc.GodTossing.Worker.Workers
       ( -- * Instances
         -- ** instance SscWorkersClass SscGodTossing
       ) where

import           Control.Lens                            (view, _2, _3)
import           Control.TimeWarp.Timed                  (Microsecond, Millisecond,
                                                          currentTime, for, wait)
import           Data.Tagged                             (Tagged (..))
import           Data.Time.Units                         (convertUnit)
import           Formatting                              (build, ords, sformat, shown,
                                                          (%))
import           Serokell.Util.Exceptions                ()
import           System.FilePath                         ((</>))
import           System.Wlog                             (logDebug, logWarning)
import           Universum

import           Pos.Communication.Methods               (sendToNeighborsSafe)
import           Pos.Constants                           (k, mpcSendInterval)
import           Pos.Crypto                              (PublicKey, SecretKey,
                                                          randomNumber, runSecureRandom,
                                                          toPublic)
import           Pos.Slotting                            (getSlotStart, onNewSlot)
import           Pos.Ssc.Class.Workers                   (SscWorkersClass (..))
import           Pos.Ssc.GodTossing.Functions            (genCommitmentAndOpening,
                                                          genCommitmentAndOpening,
                                                          hasCommitment, hasOpening,
                                                          hasShares, isCommitmentIdx,
                                                          isOpeningIdx, isSharesIdx,
                                                          mkSignedCommitment)
import           Pos.Ssc.GodTossing.LocalData.LocalData  (localOnNewSlot,
                                                          sscProcessMessage)
import           Pos.Ssc.GodTossing.Types.Base           (Opening, SignedCommitment)
import           Pos.Ssc.GodTossing.Types.Instance       ()
import           Pos.Ssc.GodTossing.Types.Message        (InvMsg (..), MsgTag (..))
import           Pos.Ssc.GodTossing.Types.Message        (DataMsg (..))
import           Pos.Ssc.GodTossing.Types.Type           (SscGodTossing)
import           Pos.Ssc.GodTossing.Worker.SecretStorage (SecretStorage, bracket',
                                                          checkpointSecret, getSecret,
                                                          prepareSecretToNewSlot,
                                                          setSecret)
import           Pos.Ssc.GodTossing.Worker.Types         ()
import           Pos.State                               (getGlobalMpcData, getOurShares,
                                                          getParticipants, getThreshold)
import           Pos.Types                               (EpochIndex, LocalSlotIndex,
                                                          SlotId (..), Timestamp (..))
import           Pos.WorkMode                            (WorkMode, getNodeContext,
                                                          ncDbPath, ncPublicKey,
                                                          ncSecretKey, ncVssKeyPair)
instance SscWorkersClass SscGodTossing where
    sscWorkers = Tagged [onNewSlotSsc]

onNewSlotSsc :: WorkMode SscGodTossing m => m ()
onNewSlotSsc = do
    path <- pathToSecret
    bracket' path $ onNewSlot True . onNewSlotImpl

onNewSlotImpl :: WorkMode SscGodTossing m => SecretStorage -> SlotId -> m ()
onNewSlotImpl storage slotId = do
    localOnNewSlot slotId
    prepareSecretToNewSlot storage slotId
    onNewSlotCommitment storage slotId
    onNewSlotOpening storage slotId
    onNewSlotShares slotId
    checkpointSecret storage


-- Commitments-related part of new slot processing
onNewSlotCommitment :: WorkMode SscGodTossing m => SecretStorage -> SlotId -> m ()
onNewSlotCommitment storage SlotId {..} = do
    ourPk <- ncPublicKey <$> getNodeContext
    ourSk <- ncSecretKey <$> getNodeContext
    shouldCreateCommitment <- do
        secret <- getSecret storage
        return $ isCommitmentIdx siSlot && isNothing secret
    when shouldCreateCommitment $ do
        logDebug $ sformat ("Generating secret for "%ords%" epoch") siEpoch
        generated <- generateAndSetNewSecret storage ourSk siEpoch
        case generated of
            Nothing -> logWarning "I failed to generate secret for Mpc"
            Just _ -> logDebug $
                sformat ("Generated secret for "%ords%" epoch") siEpoch
    shouldSendCommitment <- do
        commitmentInBlockchain <- hasCommitment ourPk <$> getGlobalMpcData
        return $ isCommitmentIdx siSlot && not commitmentInBlockchain
    when shouldSendCommitment $ do
        mbComm <- fmap (view _2) <$> (getSecret storage)
        whenJust mbComm $ \comm -> do
            _ <- sscProcessMessage $ DMCommitment ourPk comm
            sendOurData CommitmentMsg siEpoch 0 ourPk

-- Openings-related part of new slot processing
onNewSlotOpening :: WorkMode SscGodTossing m => SecretStorage -> SlotId -> m ()
onNewSlotOpening storage SlotId {..} = do
    ourPk <- ncPublicKey <$> getNodeContext
    shouldSendOpening <- do
        globalData <- getGlobalMpcData
        let openingInBlockchain = hasOpening ourPk globalData
        let commitmentInBlockchain = hasCommitment ourPk globalData
        return $ and [ isOpeningIdx siSlot
                     , not openingInBlockchain
                     , commitmentInBlockchain]
    when shouldSendOpening $ do
        mbOpen <- fmap (view _3) <$> (getSecret storage)
        whenJust mbOpen $ \open -> do
            _ <- sscProcessMessage $ DMOpening ourPk open
            sendOurData OpeningMsg siEpoch 2 ourPk

-- Shares-related part of new slot processing
onNewSlotShares :: WorkMode SscGodTossing m => SlotId -> m ()
onNewSlotShares SlotId {..} = do
    ourPk <- ncPublicKey <$> getNodeContext
    -- Send decrypted shares that others have sent us
    shouldSendShares <- do
        -- TODO: here we assume that all shares are always sent as a whole
        -- package.
        sharesInBlockchain <- hasShares ourPk <$> getGlobalMpcData
        return $ isSharesIdx siSlot && not sharesInBlockchain
    when shouldSendShares $ do
        ourVss <- ncVssKeyPair <$> getNodeContext
        shares <- getOurShares ourVss
        unless (null shares) $ do
            _ <- sscProcessMessage $ DMShares ourPk shares
            sendOurData SharesMsg siEpoch 4 ourPk

sendOurData
    :: WorkMode SscGodTossing m
    => MsgTag -> EpochIndex -> LocalSlotIndex -> PublicKey -> m ()
sendOurData msgTag epoch kMultiplier ourPk = do
    -- Note: it's not necessary to create a new thread here, because
    -- in one invocation of onNewSlot we can't process more than one
    -- type of message.
    waitUntilSend msgTag epoch kMultiplier
    logDebug $ sformat ("Announcing our "%build) msgTag
    let msg = InvMsg {imType = msgTag, imKeys = pure ourPk}
    sendToNeighborsSafe msg
    logDebug $ sformat ("Sent our " %build%" to neighbors") msgTag

-- | Generate new commitment and opening and use them for the current
-- epoch. Assumes that the genesis block has already been generated and
-- processed by MPC (when the genesis block is processed, the secret is
-- cleared) (otherwise 'generateNewSecret' will fail because 'A.SetSecret'
-- won't set the secret if there's one already).
-- Nothing is returned if node is not ready.
generateAndSetNewSecret
    :: WorkMode SscGodTossing m
    => SecretStorage
    -> SecretKey
    -> EpochIndex                         -- ^ Current epoch
    -> m (Maybe (SignedCommitment, Opening))
generateAndSetNewSecret storage sk epoch = do
    -- TODO: I think it's safe here to perform 3 operations which aren't
    -- grouped into a single transaction here, but I'm still a bit nervous.
    threshold <- getThreshold epoch
    participants <- getParticipants epoch
    case (,) <$> threshold <*> participants of
        Nothing -> return Nothing
        Just (th, ps) -> do
            (comm, op) <-
                first (mkSignedCommitment sk epoch) <$>
                genCommitmentAndOpening th ps
            Just (comm, op) <$ setSecret storage (toPublic sk, comm, op)

pathToSecret :: WorkMode SscGodTossing m => m (Maybe FilePath)
pathToSecret = fmap (</> "secret") <$> (ncDbPath <$> getNodeContext)

randomTimeInInterval
    :: WorkMode SscGodTossing m
    => Microsecond -> m Microsecond
randomTimeInInterval interval =
    -- Type applications here ensure that the same time units are used.
    (fromInteger @Microsecond) <$>
    liftIO (runSecureRandom (randomNumber n))
  where
    n = toInteger @Microsecond interval

waitUntilSend
    :: WorkMode SscGodTossing m
    => MsgTag -> EpochIndex -> LocalSlotIndex -> m ()
waitUntilSend msgTag epoch kMultiplier = do
    Timestamp beginning <-
        getSlotStart $ SlotId {siEpoch = epoch, siSlot = kMultiplier * k}
    curTime <- currentTime
    let minToSend = curTime
    let maxToSend = beginning + mpcSendInterval
    when (minToSend < maxToSend) $ do
        let delta = maxToSend - minToSend
        timeToWait <- randomTimeInInterval delta
        let ttwMillisecond :: Millisecond
            ttwMillisecond = convertUnit timeToWait
        logDebug $
            sformat ("Waiting for "%shown%" before sending "%build)
                ttwMillisecond msgTag
        wait $ for timeToWait