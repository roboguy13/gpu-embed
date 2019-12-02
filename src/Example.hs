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
  runQ $ transformEitherMatch exp

thExample4 :: IO Exp
thExample4 = do
  exp <- runQ
    [| case (True, 7 :: Int) of
         (x, y) -> fromEnum (x :: Bool) + y
    |]
  runQ $ transformPairMatch exp

main :: IO ()
main = do
  transformed <- thExample4
  putStrLn (pprint transformed)

  -- print $transformed
  -- x <- thExample2
  -- print x


-- $(iHateDelete
--     [d|
--         mapDelete x = map (delete x)
--         myElem x xs = length (delete x (delete x xs)) /= length xs
--     |])
