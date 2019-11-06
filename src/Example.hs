{-# LANGUAGE TemplateHaskell #-}

import           Data.List
import           Case

import           Language.Haskell.TH

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

main :: IO ()
main = do
  x <- thExample2
  print x


-- $(iHateDelete
--     [d|
--         mapDelete x = map (delete x)
--         myElem x xs = length (delete x (delete x xs)) /= length xs
--     |])
