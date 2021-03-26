-- State machine examples (in the form of recursive NFAs)

{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Machines where

import           Control.Monad

class Machine s where
  initial :: s
  isFinal :: s -> Bool

-- | For "wiring" the final state from a recursive "call" to a state machine
-- to a different state
finishIn :: Machine s => s -> s -> s
finishIn inS newFinal
  | isFinal inS = newFinal
  | otherwise   = inS

data AB = A | B deriving (Show)

data Paired = Paired_Q0 | Paired_Q1 | Paired_Q2 | Paired_Q3 deriving (Show)

pattern Paired_Initial = Paired_Q0
pattern Paired_Final0 = Paired_Q3

instance Machine Paired where
  initial = Paired_Initial

  isFinal Paired_Final0 = True
  isFinal _ = False

data RecMachine s
  = Rec s
  | Step s
  | NoTransition


-- This accepts the language {A^nB^n | n : Nat}
--
--   paired
--    ,------------------------------------,
--    |       _________epsilon________     |
--    |      /                        `v   |
--  --+--> Q0                         (Q3) |
--    |      `---> Q1 ---------> Q2 ---^   |
--    |        A        paired       B     |
--    '------------------------------------'

paired :: Paired -> Maybe AB -> RecMachine Paired
paired Paired_Q0 Nothing  = Step Paired_Q3
paired Paired_Q0 (Just A) = Step Paired_Q1
paired Paired_Q1 x        = Rec Paired_Q2
-- paired Paired_Q1 x        = paired Paired_Initial x `finishIn` Paired_Q2
paired Paired_Q2 (Just B) = Step Paired_Q3
paired Paired_Q3 _        = Step Paired_Q3
paired _         _        = NoTransition

data MachineCont s a
  = MachineDone (Maybe s)
  | MachineStep ([a] -> Maybe s)

runMachine :: forall s a. Machine s => (s -> Maybe a -> RecMachine s) -> [a] -> Maybe s
runMachine t = go finishUp initial
  where
    finishUp s [] = Just s
    finishUp s _ = Nothing

    -- goCompose f g s = f s . g s
    goCompose :: (s -> [a] -> Maybe s) -> (s -> [a] -> Maybe s) -> s -> [a] -> Maybe s
    goCompose f g s xs = g s xs >>= (\s' -> f s' xs)

    go :: (s -> [a] -> Maybe s) -> s -> [a] -> Maybe s
    go k s xs | isFinal s = k s xs --Just (k s)

    go k s [] =
      case t s Nothing of
        Rec s' -> -- go initial [] `finishIn` s'
          go (const (go k s')) initial []
        Step s'
          | isFinal s' -> k s' []
          | otherwise  -> go k s' []
        NoTransition -> Nothing

    go k s (x:xs) =
      case t s Nothing of
        Rec s' -> -- go k initial xs `finishIn` s'
          go (const (go k s')) initial xs
        Step s'
          | isFinal s' -> k s' xs
          | otherwise  -> go k s' xs
        NoTransition ->
          case t s (Just x) of
            Rec s' -> -- go k initial xs `finishIn` s'
              go (const (go k s')) initial xs
            Step s'
              | isFinal s' -> k s' xs
              | otherwise  -> go k s' xs
            NoTransition -> Nothing

