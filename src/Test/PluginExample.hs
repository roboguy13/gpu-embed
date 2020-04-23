{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}

-- {-# LANGUAGE TypeOperators #-}
-- {-# LANGUAGE DataKinds #-}
-- {-# LANGUAGE KindSignatures #-}
-- {-# LANGUAGE StandaloneDeriving #-}
-- {-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -O0 -Wtype-defaults -fexpose-all-unfoldings -dcore-lint -dsuppress-all -dno-suppress-coercions -fplugin=Plugin.MatchPlugin #-}

module Test.PluginExample where


import           GHC.Float
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

import           CodeGen.C

-- import           Debug.Trace

-- deriving instance Generic (Ratio a) -- XXX: This instance should probably be in 'base'

default (Int, Double)

data Nat = Z | S Nat deriving (Generic, Show)

data Example = N Nat | B Bool deriving (Generic, Show)

eitherExample :: Int -> Either Int Bool
eitherExample x = Right False

example1 :: Int
example1 =
  internalize (externalize
    (case eitherExample 1 of
      Left x -> x * 2
      Right y -> fromEnum y))
{-# NOINLINE example1 #-}

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

example4_ :: Int -> Example4
example4_ x = E2 23.0

-- example4 :: Int
-- example4 =
--   internalize (externalize
--     (case example4_ 0 of
--       E1 x -> 2
--       E2 y -> 4
--       E3 z -> 6))

data Example5 = A1 Float Float | A2 Int deriving (Show, Generic)

instance GPURep Example5

example5_ :: Int -> Example5
example5_ x = A1 2.3 7.5

-- example5 :: Float
-- example5 =
--   internalize (externalize
--     (case example5_ 0 of
--       A2 x -> fromIntegral x
--       A1 x y -> x + y))

-- | isEven

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

-- example7 :: Int
-- example7 =
--   internalize (externalize
--     (case example7_ 0 of
--       IntPair x y ->
--         if x == 0
--           then y
--           else x))

example8 :: IntPair -> Int
example8 p =
  internalize (externalize
    (case p of
      IntPair x y -> y))

example9 :: IntPair -> Int
example9 p =
  internalize (externalize
    (case p of
      IntPair x y ->
        if x == 0
          then example8 p
          else example9 (IntPair (x-1) (x*y))))

-- floatTest :: Float
-- floatTest =
--   internalize (externalize
--     (case True of
--       False -> 3 * 2
--       True -> 3 * 3))

data ComplexPair where
  ComplexPair :: Complex Double
                 -> Complex Double
                 -> ComplexPair
  deriving (Generic, Show)

instance GPURep ComplexPair

sumComplexPair :: ComplexPair -> Complex Double
sumComplexPair t =
  internalize (externalize
    (case t of
      ComplexPair a b -> a + b))

realSum :: ComplexPair -> Double
realSum p =
  internalize (externalize
    (case p of
      ComplexPair (a :+ _) (b :+ _) ->
        a + b))

mandelbrot_nextZ :: (Complex Double, Complex Double) -> Complex Double
mandelbrot_nextZ t =
  internalize (externalize
    (case t of
      (c, z) -> (z*z) + c))
{-# NOINLINE mandelbrot_nextZ #-}

mandelbrot_helper :: (Int, Complex Double, Complex Double) -> Maybe Int
mandelbrot_helper t =
  internalize (externalize
    (case t of
      (iters, c, z) ->
        if iters == 50
          then Nothing
          else
            case z of
              real :+ imag ->
                if (real*real) + (imag*imag) > 4
                  then Just iters
                  else mandelbrot_helper (iters+1, c, mandelbrot_nextZ (c, z))))
{-# NOINLINE mandelbrot_helper #-}

mandelbrot_point :: Complex Double -> Maybe Int
mandelbrot_point c =
  internalize (externalize
    (mandelbrot_helper (0, c, 0)))

mandelbrot_pointE :: Complex Double -> GPUExp (Maybe Int)
mandelbrot_pointE c =
  externalize
    (mandelbrot_helper (0, c, 0))

data IntList = Nil | Cons Int IntList
  deriving (Generic, Show)

instance GPURep IntList

isEmpty :: IntList -> Bool
isEmpty t =
  internalize (externalize
    (case t of
      Nil -> True
      Cons x xs -> False))

intListLength_helper :: (Int, IntList) -> Int
intListLength_helper p =
  internalize (externalize
    (case p of
      (acc, t) ->
        case t of
          Nil -> acc
          Cons _ xs -> intListLength_helper (acc+1, xs)))
{-# NOINLINE intListLength_helper #-}

intListLength :: IntList -> Int
intListLength t = internalize (externalize (intListLength_helper (0, t)))

intListSum_helper :: (Int, IntList) -> Int
intListSum_helper p =
  internalize (externalize
    (case p of
       (acc, t) ->
         case t of
           Nil -> acc
           Cons x xs -> intListSum_helper (x+acc, xs)))
{-# NOINLINE intListSum_helper #-}

intListSum :: IntList -> Int
intListSum t =
  internalize (externalize (intListSum_helper (0, t)))

intListSumE :: IntList -> GPUExp Int
intListSumE t = externalize (intListSum_helper (0, t))

example_x :: Either Char Int
example_x = Left 'a'
{-# INLINE example_x #-}

example :: Int
example =
  internalize (externalize
    (case example_x of
      Left  c -> ord c
      Right i -> i))
{-# NOINLINE example #-}

data DoubleList = DNil | DCons Double DoubleList deriving (Generic)

instance GPURep DoubleList

doubleListSum_helper :: (Double, DoubleList) -> Double
doubleListSum_helper p =
  internalize (externalize
    (case p of
      (acc, t) ->
        case t of
          DNil -> acc
          DCons x xs -> doubleListSum_helper (x+acc, xs)))

doubleListSumE :: DoubleList -> GPUExp Double
doubleListSumE t = externalize (doubleListSum_helper (0, t))

-- data FinBitTree (n :: TL.Nat) where
--   FBTLeafZero :: FinBitTree n
--   FBTLeafOne  :: FinBitTree n
--   FBTNode     :: FinBitTree n -> FinBitTree m -> FinBitTree (n+m)

-- deriving instance Generic1 FinBitTree

-- nonterm_test0 :: Int -> Int
-- nonterm_test0 0 = 0
-- nonterm_test0 n = nonterm_test1 (n-1)

-- nonterm_test1 :: Int -> Int
-- nonterm_test1 0 = 1
-- nonterm_test1 n = nonterm_test0 (n-1)

-- nonterm_test :: Int -> Int
-- nonterm_test x =
--   internalize (externalize
--     (nonterm_test0 4))


main :: IO ()
main = do
  let intList = Cons 10 (Cons 100 (Cons 1000 (Cons 10000 Nil)))
      doubleList = DCons 3.2 (DCons 1 (DCons 2.5 DNil))
  -- print $ mandelbrot_point (1 :+ 0)
  putStrLn $ genProgram (mandelbrot_pointE (1 :+ 0))
  -- putStrLn (genProgram (doubleListSumE doubleList)) --putStrLn (genProgram cTest6)
  -- print (isEmpty Nil, isEmpty (Cons 1 Nil)
  --       ,intListLength intList
  --       ,intListSum intList
  --       ,example
  --       )
  -- print $ realSum (ComplexPair (2 :+ 100) (3 :+ 10000))
  -- putStrLn mandelbrotTestAscii



-- main :: IO ()
-- main =
--   -- print (example6 3, example6 4, example9 (IntPair 5 1))
--   print example1




mandelbrotTestAscii :: String
mandelbrotTestAscii =
  unlines
    (map go [0..mandelbrot_height-1])
  where
    go y = map (go2 y) [0..mandelbrot_width-1]

    go2 y x =
      case mandelbrot_point (mandelbrot_toCoord x y) of
        Just _ -> ' '
        Nothing -> '*'


mandelbrot_toCoord :: Int -> Int -> Complex Double
mandelbrot_toCoord x0 y0 =
    (mandelbrot_xMin + x * mandelbrot_xIncr) :+ (mandelbrot_yMin + y * mandelbrot_yIncr)
  where
    x, y :: Double
    x = fromIntegral x0
    y = fromIntegral y0

mandelbrot_xIncr :: Double
mandelbrot_xIncr = (mandelbrot_xMax - mandelbrot_xMin) / (fromIntegral mandelbrot_width - 1)

mandelbrot_yIncr :: Double
mandelbrot_yIncr = (mandelbrot_yMax - mandelbrot_yMin) / (fromIntegral mandelbrot_height - 1)

mandelbrot_xMin :: Double
mandelbrot_xMin = -2.5

mandelbrot_xMax :: Double
mandelbrot_xMax = 1

mandelbrot_yMin :: Double
mandelbrot_yMin = -1.5

mandelbrot_yMax :: Double
mandelbrot_yMax = 1

mandelbrot_width :: Int
mandelbrot_width = 200

mandelbrot_height :: Int
mandelbrot_height = 40


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

