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

thExample :: IO Int
thExample =
  runQ $ countCases
     [|
        case 'a' of
          'b' -> case True of
                    _ -> 27
          'c' -> 42
          'd' -> 500
          _ -> case [] of [] -> 100
     |]

thExample2 :: IO [(Name, Exp)]
thExample2 = do
  matches <- runQ $ getCaseMatchesFirst
    [|
      case B False of
        N n -> N (S (S n))
        B b -> B (not b)
    |]
  runQ $ gatherCaseAlts matches

thExample3 :: Q Exp
thExample3 = do
  exp <-
    [|
      case Left 4 of
        Left x -> x * 2
        Right y -> fromEnum (y :: Bool)
    |]
  transformCase exp

thExample4 :: Q Exp
thExample4 = do
  exp <-
    [| case (True, 7 :: Int) of
         (x, y) -> fromEnum (x :: Bool) + y
    |]
  transformCase exp

data Example' = N' Int | B' Bool deriving (Show, Generic)

thExample5 :: Q Exp
thExample5 = do
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

thExample6 :: Q Exp
thExample6 = do
  exp <-
    [| case E2 23.0 of
        E1 x -> 2
        E2 y -> 4
        E3 z -> 6 :: Int
    |]
  transformCase exp

-- main :: IO ()
-- main = do
  -- print $(thExample5)

  -- $(thExample6)

  -- transformed <- runQ thExample6
  -- putStrLn (pprint transformed)

  -- print $transformed
  -- x <- thExample2
  -- print x


-- $(iHateDelete
--     [d|
--         mapDelete x = map (delete x)
--         myElem x xs = length (delete x (delete x xs)) /= length xs
--     |])
