{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
-- {-# LANGUAGE PolyKinds #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -ddump-splices #-}
{-# OPTIONS_GHC -fprint-explicit-kinds #-}

module Deep.Example where

import           Data.List

import           Deep.Expr

import           Language.Haskell.TH

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

thExample1 :: Q Exp
thExample1 = do
  exp <-
    [|
      case the @(Either Int Bool) (Right False) of
        Left x -> x * 2
        Right y -> fromEnum y
    |]
  transformExpr exp

thExample2 :: Q Exp
thExample2 = do
  exp <-
    [| case (True, the @Int 7) of
         (x, y) -> fromEnum x + y
    |]
  transformExpr exp

data Example' = N' Int | B' Bool deriving (Show, Generic)

thExample3 :: Q Exp
thExample3 = do
  exp <-
    [|
      case B' False of
        N' n -> N' (n+2)
        B' b -> B' (not b)
    |]
  transformExpr exp

instance GPURep Example' where
  type TypeHead Example' = Example'



data Example3 = X Int Float deriving (Show, Generic)

instance GPURep Example3 where
  type TypeHead Example3 = Example3

data Example4 = E1 Int | E2 Float | E3 Bool deriving (Show, Generic)

instance GPURep Example4 where
  type TypeHead Example4 = Example4

thExample4 :: Q Exp
thExample4 = do
  exp <-
    [| case E2 23.0 of
        E1 x -> 2
        E2 y -> 4
        E3 z -> 6
    |]
  transformExpr exp

data Example5 = A1 Float Float | A2 Int deriving (Show, Generic)

instance GPURep Example5 where
  type TypeHead Example5 = Example5

thExample5 :: Q Exp
thExample5 = do
  exp <-
    [| case A1 2.3 7.5 of
        A2 x -> fromIntegral x
        A1 x y -> x + y
    |]

  transformExpr exp

-- instance GPURep a => GPURep (Ratio a)

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

data IntPair = IntPair Int Int deriving (Show, Generic)

instance GPURep IntPair where
  type TypeHead IntPair = IntPair

thExample7 :: Q Exp
thExample7 = do
  exp <-
    [| case IntPair 1 2 of
        IntPair x y ->
          if x == 0
            then y
            else y
    |]
  r <- transformExpr exp
  return r


-- transformDecTailRec
--   [d|
thExample8 :: IntPair -> Int
thExample8 p =
  case p of
    IntPair x y -> y

-- -- thExample9_aj5t :: IntPair -> Int
-- -- thExample9_aj5t p_aj5x
-- --   = (gpuAbs
-- --        (TailRec
-- --           ((\ thExample9_aj5t
-- --               -> \ p_aj5x
-- --                    -> (CaseExp p_aj5x)
-- --                         ((SafeSumMatch (Data.Proxy.Proxy :: Proxy (TypeHead (Tagged2 (TypeHead IntPair :: *) IntPair (Int, Int)) :: *)))
-- --                            (OneSumMatch
-- --                               (ProdMatch
-- --                                  (\ x_aj5y
-- --                                     -> OneProdMatch
-- --                                          (\ y_aj5z
-- --                                             -> ((IfThenElse ((Equal x_aj5y) (Lit 0)))
-- --                                                   (DoneExp
-- --                                                      ((construct thExample8) p_aj5x)))
-- --                                                  (thExample9_aj5t
-- --                                                     (((construct IntPair)
-- --                                                         ((Sub x_aj5y) (Lit 1)))
-- --                                                        ((Mul x_aj5y) y_aj5z)))))))))
-- --              StepExp)))
-- --       p_aj5x

--   thExample9 :: IntPair -> Int
--   thExample9 p =
--     case p of
--       IntPair x y ->
--         if x == 0
--           then thExample8 p
--           else thExample9 (IntPair (x-1) (x*y))

--   |]

thExample9_aijJ :: IntPair -> Int
thExample9_aijJ p_aijN
  = (gpuAbs
       (TailRec
          ((\ thExample9_aijJ
              -> \ p_aijN
                   -> (CaseExp p_aijN)
                        ((SafeSumMatch (Proxy @(KindOf IntPair)) (Proxy @IntPair))
                           (OneSumMatch
                              (ProdMatch
                                 (\ x_aijO
                                    -> OneProdMatch
                                         (\ y_aijP -> undefined))))))
                                            -- -> ((IfThenElse ((Equal x_aijO) (Lit 0)))
                                            --       (DoneExp
                                            --          ((construct thExample8) p_aijN)))
                                            --      (thExample9_aijJ
                                            --         (((construct IntPair)
                                            --             ((Sub x_aijO) (Lit 1)))
                                            --            ((Mul x_aijO) y_aijP)))))))))
             StepExp)))
      p_aijN



-- transformDecTailRec
--   [d|
--   mandelbrot_nextZ :: (Complex (Ratio Integer), Complex (Ratio Integer)) -> Complex (Ratio Integer)
--   mandelbrot_nextZ t =
--     case t of
--       (c, z) -> (z*z) + c

--   -- shouldFail :: Complex (Ratio Integer) -> (Ratio Integer)
--   -- shouldFail t =
--   --   case t of
--   --     (x, y) -> x + y

--   mandelbrot_helper :: (Int, Complex (Ratio Integer), Complex (Ratio Integer)) -> Maybe Int
--   mandelbrot_helper t =
--     case t of
--       (iters, c, z) ->
--         if iters == 50
--           then Nothing
--           else
--             case z of
--               (:+) real imag ->
--                 if ((real*real) + (imag*imag)) > 4
--                   then Just iters
--                   else mandelbrot_helper (iters+1, c, mandelbrot_nextZ (c, z))

--   mandelbrot_point :: Complex (Ratio Integer) -> Maybe Int
--   mandelbrot_point c = mandelbrot_helper (0, c, 0)

--   |]

