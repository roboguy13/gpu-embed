{-# LANGUAGE TemplateHaskell #-}

import           Data.List
import           Case

import           Language.Haskell.TH

import           Data.Char (ord)

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

data Example' = N' Int | B' Bool deriving (Show)

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
  type GPURepTy Example' = Either Bool Int
  rep = Repped . rep'

  rep' (N' n) = Right n
  rep' (B' b) = Left b

  unrep' (Right n) = N' n
  unrep' (Left b) = B' b

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
