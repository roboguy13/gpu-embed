{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}

module Rewrite.Rewrite
  where

import           GHC.Generics

import           Data.STRef

import           Control.Monad.ST
import           Control.Monad.State
import           Control.Monad.Writer


-- data ADTTree a
--   = UnitADT
--   | NodeADT a (ADTTree a) -- Internal node
--   | PairADT (ADTTree a) (ADTTree a)
--   | InLADT (ADTTree a)
--   | InRADT (ADTTree a)

-- TODO: How do we know and keep track of whether a cursor is clobbered?
data Cursor a where
  -- = ClobberedCursor
  TopCursor :: a -> Cursor a
  CursorFst :: Cursor a -> Cursor (a, b)
  CursorSnd :: Cursor b -> Cursor (a, b)
  CursorInL :: Cursor a -> Cursor (Either a b)
  CursorInR :: Cursor b -> Cursor (Either a b)

type Clobbered = Bool

-- For keeping track of cursors, reflecting the data structure being
-- "indexed"
-- newtype CursorTree a = CursorTree (ADTTree (STRef s (Cursor a)))
data CursorTree s a
  = UnitCT
  | NodeCT Clobbered 

-- isClobbered :: CursorTree a -> Cursor a -> Bool
-- isClobbered = undefined

-- newtype Rewrite a = Rewrite { runRewrite :: a -> Maybe (a, Maybe (Cursor a)) }

-- data RewriteM a b
--   = forall s. RewriteM { runRewriteM :: State (CursorTree s a) b }

data Rewrite a b
  = forall s. Rewrite { runRewrite :: a -> StateT (CursorTree s a) (Writer (Maybe (Cursor a))) b }

