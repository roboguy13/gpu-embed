{-# LANGUAGE DeriveGeneric #-}

{-# OPTIONS_GHC -ddump-simpl -O0 -dcore-lint -fplugin=Plugin.MatchPlugin #-}

module Test.PluginExample where

import           Data.List

import           Deep.Expr
import           Deep.Delineate

import           Data.Char (ord)

import           GHC.Generics
import           Data.Void

import           Data.Bifunctor

import           Data.Complex

import           Data.Ratio

import           GHC.Real

import           Data.Proxy

-- import           Debug.Trace

-- deriving instance Generic (Ratio a) -- XXX: This instance should probably be in 'base'

data Nat = Z | S Nat deriving (Generic, Show)

data Example = N Nat | B Bool deriving (Generic, Show)

eitherExample :: Int -> Either Int Bool
eitherExample x = Right False

-- example1 :: Int
-- example1 =
--   internalize (externalize
--     (case eitherExample 1 of
--       Left x -> x * 2
--       Right y -> fromEnum y))
-- {-# NOINLINE example1 #-}

data Example' = N' Int | B' Bool deriving (Show, Generic)

instance GPURep Example'

-- example2_ :: Int -> Example'
-- example2_ x = B' False
-- {-# NOINLINE example2_ #-}

-- example2 :: Example'
-- example2 =
--   internalize (externalize
--     (case example2_ 0 of
--       N' n -> N' (n+2)
--       B' b -> B' (not b)))
-- {-# NOINLINE example2 #-}

-- example3 :: (Bool, Int) -> Int
-- example3 p =
--   internalize (externalize
--     (case p of
--       (x, y) -> fromEnum x + y))

data Example4 = E1 Int | E2 Float | E3 Bool deriving (Show, Generic)

instance GPURep Example4

-- example4_ :: Int -> Example4
-- example4_ x = E2 23.0

-- example4 :: Int
-- example4 =
--   internalize (externalize
--     (case example4_ 0 of
--       E1 x -> 2
--       E2 y -> 4
--       E3 z -> 6))

data Example5 = A1 Float Float | A2 Int deriving (Show, Generic)

instance GPURep Example5

-- example5_ :: Int -> Example5
-- example5_ x = A1 2.3 7.5

-- example5 :: Float
-- example5 =
--   internalize (externalize
--     (case example5_ 0 of
--       A2 x -> fromIntegral x
--       A1 x y -> x + y))

-- example6 :: Int -> Bool
-- example6 x =
--   (internalize (externalize
--     (case x == 0 of
--       True -> True
--       False ->
--         case x == 1 of
--           True -> False
--           False -> example6 (x - 2))))


data IntPair = IntPair Int Int deriving (Show, Generic)

instance GPURep IntPair where

example7_ :: Int -> IntPair
example7_ x = IntPair 1 2

example7 :: Int
example7 =
  internalize (externalize
    (case example7_ 0 of
      IntPair x y ->
        if x == 0
          then y
          else x))

example8 :: IntPair -> Int
example8 p =
  internalize (externalize
    (case p of
      IntPair x y -> y))



-- main :: IO ()
-- main = print example1

-- thExample2 :: Q Exp
-- thExample2 = do
--   exp <-
--     [| case (True, the @Int 7) of
--          (x, y) -> fromEnum x + y
--     |]
--   transformExpr exp

-- data Example' = N' Int | B' Bool deriving (Show, Generic)

-- thExample3 :: Q Exp
-- thExample3 = do
--   exp <-
--     [|
--       case B' False of
--         N' n -> N' (n+2)
--         B' b -> B' (not b)
--     |]
--   transformExpr exp
