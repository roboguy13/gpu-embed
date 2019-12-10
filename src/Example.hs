{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}

module Example where

import           Data.List
import           Case

import           Language.Haskell.TH

import           Data.Char (ord)

import           GHC.Generics
import           Data.Void

import           Data.Bifunctor

data Nat = Z | S Nat deriving (Generic, Show)

data Example = N Nat | B Bool deriving (Generic, Show)

thExample1 :: Q Exp
thExample1 = do
  exp <-
    [|
      case Left 4 of
        Left x -> x * 2
        Right y -> fromEnum (y :: Bool)
    |]
  transformCase exp

thExample2 :: Q Exp
thExample2 = do
  exp <-
    [| case (True, 7 :: Int) of
         (x, y) -> fromEnum (x :: Bool) + y
    |]
  transformCase exp

data Example' = N' Int | B' Bool deriving (Show, Generic)

thExample3 :: Q Exp
thExample3 = do
  exp <-
    [|
      case B' False of
        N' n -> N' (n+2)
        B' b -> B' (not b)
    |]
  transformCase exp

instance GPURep Example'



data Example3 = X Int Float deriving (Show, Generic)

instance GPURep Example3 where

data Example4 = E1 Int | E2 Float | E3 Bool deriving (Show, Generic)

instance GPURep Example4

thExample4 :: Q Exp
thExample4 = do
  exp <-
    [| case E2 23.0 of
        E1 x -> 2
        E2 y -> 4
        E3 z -> 6 :: Int
    |]
  transformCase exp

data Example5 = A1 Float Float | A2 Int deriving (Show, Generic)

instance GPURep Example5

thExample5 :: Q Exp
thExample5 = do
  exp <-
    [| case A1 2.3 7.5 of
        A2 x -> fromIntegral x
        A1 x y -> x + y
    |]

  transformCase exp

transformDecTailRec
  [d|
  thExample6 :: Int -> Bool
  thExample6 x =
    if x == 0
      then True
      else if x == 1
            then False
            else thExample6 (x - 2)
  |]

