-- Based on "Monad Transformers and Modular Algebraic Effects" [2019]

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}

module Effect where

import           Control.Monad

data Free sig x = Var x | Op (sig (Free sig x))

instance Functor sig => Functor (Free sig) where
  fmap f (Var x) = Var (f x)
  fmap f (Op s)  = Op (fmap (fmap f) s)

instance Functor sig => Applicative (Free sig) where
  pure = return
  (<*>) = ap

instance Functor sig => Monad (Free sig) where
  return = Var
  Var x >>= f = f x
  Op k >>= f = Op (fmap (>>= f) k)

data State s k
  = Get (s -> k)
  | Put s (() -> k)
  deriving (Functor)

get' :: Free (State s) s
get' = Op (Get return)

put' :: s -> Free (State s) ()
put' s = Op (Put s return)

incr' :: Free (State Int) ()
incr' = get' >>= put' . succ


fold :: Functor sig => (a -> b) -> (sig b -> b) -> (Free sig a -> b)
fold gen alg (Var x) = gen x
fold gen alg (Op op) = alg (fmap (fold gen alg) op)

data (sig1 + sig2) a = Inl (sig1 a) | Inr (sig2 a)

data Void1 k deriving (Functor)

runVoid :: Free Void1 a -> a
runVoid = fold id undefined


(<+>) :: (sig1 b -> b) -> (sig2 b -> b) -> ((sig1 + sig2) b -> b)
(alg1 <+> alg2) (Inl op) = alg1 op
(alg1 <+> alg2) (Inr op) = alg2 op




