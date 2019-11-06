{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Scott where

import           GHC.Generics
import           Data.Void
import           Data.Proxy

type family ScottRep rec rep r where
  ScottRep rec (M1 i c f p) r  = ScottRep rec (f p) r
  ScottRep rec (Rec0 rec p) r  = rec
  ScottRep rec (Rec0 t p) r    = ScottRep'' t
  ScottRep rec ((f :+: g) x) r = (ScottRep rec (f x) r -> r) -> (ScottRep rec (g x) r -> r) -> r
  ScottRep rec ((f :*: g) x) r = (ScottRep rec (f x) r -> ScottRep rec (g x) r -> r) -> r
  ScottRep rec (U1 p) r        = U1 p

type ScottRep' t r =
  (Proxy r, (ScottRep (ScottRep'' t) (Rep t Void) r))

data ScottRep'' t = ScottRep'' (forall r. ScottRep' t r)

data Nat = Z | S Nat deriving (Generic, Show)

data Example = N Nat | B Bool deriving (Generic, Show)

scott_False :: ScottRep'' Bool
scott_False = ScottRep'' (Proxy, \f _g -> f U1)

scott_True :: ScottRep'' Bool
scott_True = ScottRep'' (Proxy, \_f g -> g U1)

scott_Z :: ScottRep'' Nat
scott_Z = ScottRep'' (Proxy, \f _g -> f U1)

scott_S :: ScottRep'' Nat -> ScottRep'' Nat
scott_S nat = ScottRep'' (Proxy, \_f g -> g nat)

scott_ExampleN :: ScottRep'' Nat -> ScottRep'' Example
scott_ExampleN nat = ScottRep'' (Proxy, \f _g -> f nat)

scott_ExampleB :: ScottRep'' Bool -> ScottRep'' Example
scott_ExampleB bool = ScottRep'' (Proxy, \_f g -> g bool)

scottBoolToBool :: ScottRep'' Bool -> Bool
scottBoolToBool (ScottRep'' (Proxy, bool)) = bool (\_ -> False) (\_ -> True)

-- Would an F-algebra style cata be useful here?
scottNatToNat :: ScottRep'' Nat -> Nat
scottNatToNat (ScottRep'' (Proxy, nat)) = nat (\_ -> Z) (S . scottNatToNat)

scottExampleToExample :: ScottRep'' Example -> Example
scottExampleToExample (ScottRep'' (Proxy, ex)) =
  ex (N . scottNatToNat) (B . scottBoolToBool)

