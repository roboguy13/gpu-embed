{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}

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

thExample3 :: IO Exp
thExample3 = do
  exp <- runQ
    [|
      case Left 4 of
        Left x -> x * 2
        Right y -> fromEnum (y :: Bool)
    |]
  -- runQ $ transformEitherMatch exp
  runQ $ transformSumMatch exp

thExample4 :: IO Exp
thExample4 = do
  exp <- runQ
    [| case (True, 7 :: Int) of
         (x, y) -> fromEnum (x :: Bool) + y
    |]
  runQ $ transformPairMatch exp

data Example' = N' Int | B' Bool deriving (Show, Generic)

thExample5 :: IO Exp
thExample5 = do
  exp <- runQ
    [|
      case B' False of
        N' n -> N' (n+2)
        B' b -> B' (not b)
    |]
  runQ $ transformSumMatch exp

instance GPURep Example' where
  type GPURepTy Example' = Either (GPURepTy (K1 R Int Void)) (GPURepTy (K1 R Bool Void))

  rep = Repped . rep'

  rep' = bimap rep' rep' . toEither . unM1 . (from @Example' @Void)
  unrep' = to . M1 . fromEither . bimap (M1 . M1 . K1) (M1 . M1 . K1)

main :: IO ()
main = do
  transformed <- thExample5
  putStrLn (pprint transformed)

  -- print $transformed
  -- x <- thExample2
  -- print x


-- $(iHateDelete
--     [d|
--         mapDelete x = map (delete x)
--         myElem x xs = length (delete x (delete x xs)) /= length xs
--     |])
