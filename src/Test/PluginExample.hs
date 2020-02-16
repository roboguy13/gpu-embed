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

thExample1 :: Int
thExample1 = do
  internalize (externalize
    (case eitherExample 1 of
      Left x -> x * 2
      Right y -> fromEnum y))
{-# NOINLINE thExample1 #-}

main :: IO ()
main = print thExample1

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
