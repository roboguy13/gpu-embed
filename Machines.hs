-- State machine examples (in the form of recursive "restricted" NFAs)

{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DerivingVia #-}

module Machines where

import           Control.Monad
import           Control.Applicative
import           Control.Category
import           Control.Arrow

import           Control.Monad.State

class Machine s where
  initial :: s
  isFinal :: s -> Bool

-- | For "wiring" the final state from a recursive "call" to a state machine
-- to a different state
finishIn :: Machine s => s -> s -> s
finishIn inS newFinal
  | isFinal inS = newFinal
  | otherwise   = inS

finishIn_maybe :: Machine s => Maybe s -> s -> Maybe s
finishIn_maybe inS_maybe newFinal = finishIn <$> inS_maybe <*> pure newFinal

data AB = A | B deriving (Show)

data Paired = Paired_Q0 | Paired_Q1 Paired | Paired_Q2 | Paired_Q3 deriving (Show)

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

paired :: Paired -> Maybe AB -> Maybe Paired
paired Paired_Q0 Nothing  = Just Paired_Q3
paired Paired_Q0 (Just A) = Just (Paired_Q1 Paired_Q2)
-- paired (Paired_Q1 p) x    = paired initial x `finishIn_maybe` p
paired (Paired_Q1 p) x    = Paired_Q1 <$> paired initial x

-- paired Paired_Q1 x        = Rec Paired_Q2
-- paired Paired_Q1 x        = paired Paired_Initial x `finishIn` Paired_Q2
paired Paired_Q2 (Just B) = Just Paired_Q3
paired Paired_Q3 _        = Just Paired_Q3
paired _         _        = Nothing

runMachine :: forall a s. Machine s => (s -> Maybe a -> Maybe s) -> [a] -> Maybe s
runMachine t = evalState (go initial)
  where
    pop :: State [a] (Maybe a)
    pop = do
      xs <- get
      case xs of
        [] -> return Nothing
        (x:xs') -> do
          put xs'
          return (Just x)

    ensureNull :: [a] -> (Maybe ())
    ensureNull xs =
      case xs of
        [] -> Just ()
        _ -> Nothing

    go :: s -> State [a] (Maybe s)
    go s = liftA2 (<|>) (get >>= \xs -> return (ensureNull xs *> t s Nothing)) $ do
      x_maybe <- pop
      case x_maybe of
        Nothing -> return Nothing
        Just x ->
          case t s (Just x) of
            Nothing -> return Nothing
            Just s'
              | isFinal s' -> return $ Just s'
              | otherwise  -> go s'

-- paired :: Paired -> Maybe AB -> RecMachine Paired
-- paired Paired_Q0 Nothing  = Step Paired_Q3
-- paired Paired_Q0 (Just A) = Step Paired_Q1
-- paired Paired_Q1 x        = Rec Paired_Q2
-- -- paired Paired_Q1 x        = paired Paired_Initial x `finishIn` Paired_Q2
-- paired Paired_Q2 (Just B) = Step Paired_Q3
-- paired Paired_Q3 _        = Step Paired_Q3
-- paired _         _        = NoTransition


-- runMachine :: forall a s. Machine s => (s -> Maybe a -> RecMachine s) -> [a] -> Maybe s
-- runMachine t = evalState (go initial)
--   where
--     pop :: State [a] (Maybe a)
--     pop = do
--       xs <- get
--       case xs of
--         [] -> return Nothing
--         (x:xs') -> do
--           put xs'
--           return (Just x)

--     go :: s -> State [a] (Maybe s)
--     go s
--       | isFinal s = return $ Just s
--       | otherwise =
--           case t s Nothing of
--             Step s'      -> liftA2 (<|>) (go s') (goPop s)
--             Rec s'       -> liftA2 (<|>) (goRec s') (goPop s)
--             NoTransition -> goPop s


--     goRec :: s -> State [a] (Maybe s)
--     goRec newS = do
--       s_maybe <- go initial
--       case s_maybe of
--         Nothing -> undefined

--     goPop :: s -> State [a] (Maybe s)
--     goPop s = do
--       x_maybe <- pop
--       case x_maybe of
--         Nothing -> undefined




-- data MachineCont a s
--   = MachineDone (Maybe s)
--   | MachineWait
--   | MachineStep ([a] -> (MachineCont a s, [a]))

-- (<.>) :: MachineCont a s -> MachineCont a s -> MachineCont a s
-- x@(MachineDone _) <.> _ = MachineDone
-- -- MachineStep _ <.> MachineDone = MachineDone
-- x <.> MachineWait = x
-- MachineWait <.> y = y
-- MachineStep f <.> MachineStep g = MachineStep go
--   where
--     go xs =
--       case f xs of
--         (Nothing, xs') -> g xs'
--         (Just s, xs') -> g xs'

-- runMachineCont :: Machine s => MachineCont a s -> s -> [a] -> Maybe s
-- runMachineCont MachineDone     _ []    = Nothing
-- runMachineCont MachineDone     s (_:_) = Just s
-- runMachineCont MachineWait     s _ = Just s
-- runMachineCont (MachineStep f) _ xs    = fst $ f xs

-- -- mkMachineCont :: ([a] -> Maybe s) -> MachineCont a s
-- -- mkMachineCont f = MachineStep 

-- runMachine :: forall s a. Machine s => (s -> Maybe a -> RecMachine s) -> [a] -> Maybe s
-- runMachine t = undefined --go MachineDone initial
--   where
--     -- finishUp s [] = Just s
--     -- finishUp s _ = Nothing

--     go :: MachineCont a s -> s -> MachineCont a s
--     go k s | isFinal s = k

    -- go k s =
    --   MachineStep (\list ->
    --     case list of
    --       [] ->
    --         case t s Nothing of
    --           Rec s' -> go (k <.> go MachineWait s') undefined
    --           Step s' -> undefined
    --           NoTransition -> undefined)

    -- go :: MachineCont a s -> s -> [a] -> Maybe s
    -- go k s xs | isFinal s = runMachineCont k s xs --Just (k s)

    -- go k s [] =
    --   case t s Nothing of
    --     Rec s' -> -- go initial [] `finishIn` s'
    --       go (const (go k s')) initial []
    --     Step s'
    --       | isFinal s' -> runMachineCont k s' []
    --       | otherwise  -> go k s' []
    --     NoTransition -> Nothing

    -- go k s (x:xs) =
    --   case t s Nothing of
    --     Rec s' -> -- go k initial xs `finishIn` s'
    --       go (const (go k s')) initial xs
    --     Step s'
    --       | isFinal s' -> runMachineCont k s' xs
    --       | otherwise  -> go k s' xs
    --     NoTransition ->
    --       case t s (Just x) of
    --         Rec s' -> -- go k initial xs `finishIn` s'
    --           go (const (go k s')) initial xs
    --         Step s'
    --           | isFinal s' -> runMachineCont k s' xs
    --           | otherwise  -> go k s' xs
    --         NoTransition -> Nothing

