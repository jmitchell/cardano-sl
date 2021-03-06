{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

-- | Types used for communication about Blocks.

module Pos.Txp.Types.Communication
       ( TxMsgTag (..)
       , TxMsgContents (..)
       ) where

import qualified Data.Text.Buildable as Buildable
import           Formatting          (bprint, build, (%))
import           Universum

import           Pos.Types           (Tx, TxDistribution, TxWitness)

data TxMsgTag = TxMsgTag deriving (Eq, Show)

instance Buildable TxMsgTag where
    build _ = "TxMsgTag"

-- | Data message. Can be used to send one transaction per message.
data TxMsgContents = TxMsgContents
    { dmTx           :: !Tx
    , dmWitness      :: !TxWitness
    , dmDistribution :: !TxDistribution
    } deriving (Generic, Show, Eq)

instance Buildable TxMsgContents where
    build TxMsgContents {..} = bprint ("TxMsgContents { tx="%build%", .. }") dmTx
