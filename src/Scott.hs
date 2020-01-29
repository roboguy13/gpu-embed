{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE AllowAmbiguousTypes #-} -- XXX: Is this ok? (used for 'scottElim')
{-# LANGUAGE FunctionalDependencies #-}

module Scott where

import           GHC.Generics
import           Data.Data

import           Data.Void
import           Data.Proxy


data Example2 = B2 Bool | I2 Int deriving (Generic, Show)

scott_Example2B2 :: ScottRep'' Bool -> ScottRep'' Example2
scott_Example2B2 bool = ScottRep'' (Proxy, \f _g -> f bool)

scott_Example2I2 :: Int -> ScottRep'' Example2
scott_Example2I2 int = ScottRep'' (Proxy, \_f g -> g int)



type family ScottRep rec rep r where
  ScottRep rec (M1 i c f p) r  = ScottRep rec (f p) r

  -- "Base types" go here
  ScottRep rec (Rec0 Int p) r  = Int
  --

  ScottRep rec (Rec0 rec p) r  = rec
  ScottRep rec (Rec0 t p) r    = ScottRep'' t
  ScottRep rec ((f :+: g) x) r = (ScottRep rec (f x) r -> r) -> (ScottRep rec (g x) r -> r) -> r
  ScottRep rec ((f :*: g) x) r = (ScottRep rec (f x) r -> ScottRep rec (g x) r -> r) -> r
  ScottRep rec (U1 p) r        = U1 p

-- In the ScottEncode instance for (:+:):
-- Need: ScottRep (ScottRep'' a) (p Void) r
-- Have: ScottRep'' pt
-- Where: Rep pt Void ~ p Void
-- The "pt" recs need to be replaced with "(ScottRep'' a)" recs, I think...
type ScottRep' t rep r =
  (Proxy r, (ScottRep (ScottRep'' t) rep r))

data ScottRep'' t = ScottRep'' (forall r. ScottRep' t (Rep t Void) r)

-- transportScottRep ::
--   (rep1 -> rep2) ->
--   ScottRep t rep1 r -> ScottRep t rep2 r
-- transportScottRep = undefined


data Nat = Z | S Nat deriving (Generic, Show)

data Example = N Nat | B Bool deriving (Generic, Show)

scottElim :: forall a r. ScottRep'' a -> ScottRep (ScottRep'' a) (Rep a Void) r
scottElim (ScottRep'' (Proxy :: Proxy r, rep)) = rep

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

-- scottElim_Bool :: ScottRep'' Bool -> (U1 Void -> r) -> (U1 Void -> r) -> r
-- scottElim_Bool = scottElim
-- -- scottElim_Bool (ScottRep'' (Proxy, bool)) = bool

-- scottElim_Nat :: ScottRep'' Nat -> (U1 Void -> r) -> (ScottRep'' Nat -> r) -> r
-- -- scottElim_Nat (ScottRep'' (Proxy, nat)) = nat
-- scottElim_Nat = scottElim


-- scottElim_Example :: ScottRep'' Example -> (ScottRep'' Nat -> r) -> (ScottRep'' Bool -> r) -> r
-- scottElim_Example = scottElim

scottBoolToBool :: ScottRep'' Bool -> Bool
scottBoolToBool (ScottRep'' (Proxy, bool)) = bool (\_ -> False) (\_ -> True)

-- Would an F-algebra style cata be useful here?
scottNatToNat :: ScottRep'' Nat -> Nat
scottNatToNat (ScottRep'' (Proxy, nat)) = nat (\_ -> Z) (S . scottNatToNat)

scottExampleToExample :: ScottRep'' Example -> Example
scottExampleToExample (ScottRep'' (Proxy, ex)) =
  ex (N . scottNatToNat) (B . scottBoolToBool)


scottExample :: Example -> ScottRep'' Example
scottExample (N n) = scott_ExampleN (scott_Nat n)
scottExample (B b) = scott_ExampleB (scott_Bool b)

scott_Nat :: Nat -> ScottRep'' Nat
scott_Nat Z = scott_Z
scott_Nat (S n) = scott_S (scott_Nat n)

scott_Bool :: Bool -> ScottRep'' Bool
scott_Bool False = scott_False
scott_Bool True = scott_True

exampleFn :: Example -> Example
exampleFn (N Z) = B False
exampleFn (N (S n)) = N n
exampleFn (B b) = B (not b)

scott_exampleFn :: ScottRep'' Example -> ScottRep'' Example
scott_exampleFn ex =
  scottElim ex natPart boolPart
  where
    natPart :: ScottRep'' Nat -> ScottRep'' Example
    natPart nat0 =
      scottElim
        nat0
        (\U1 -> scott_ExampleN scott_Z)
        (\nat -> scott_ExampleN nat)

    boolPart :: ScottRep'' Bool -> ScottRep'' Example
    boolPart bool =
      scott_ExampleB $ scottElim bool (const scott_True) (const scott_False)

overScottEx :: (ScottRep'' Example -> ScottRep'' Example) -> Example -> Example
overScottEx f ex = scottExampleToExample (f (scottExample ex))

retranslated_scott_exampleFn :: Example -> Example
retranslated_scott_exampleFn = overScottEx scott_exampleFn

class (Generic t, Rep t Void ~ repr) =>
  ScottEncode t repr where

  scottEncode :: repr -> ScottRep' t rep r

instance (ScottEncode t (f Void), Rep t Void ~ M1 i c f Void, Generic t)
    => ScottEncode t (M1 i c f Void) where

  scottEncode (M1 x) =
    let (Proxy, r) = (scottEncode :: f Void -> _) x
    in (Proxy, r)

{-
class (Generic a, Rep a Void ~ repr) => ScottEncode a repr where -- | a -> repr where
  scottEncode :: repr -> ScottRep'' a

instance (ScottEncode a (f Void), Rep a Void ~ M1 i c f Void, Generic a)
    => ScottEncode a (M1 i c f Void) where

  scottEncode (M1 x) = scottEncode x

-}


{-
instance forall pt p a q. (Rep pt Void ~ p Void, ScottEncode pt (p Void)
                          ,Generic a, ((p :+: q) Void) ~ (Rep a Void))
    => ScottEncode a ((p :+: q) Void) where

  scottEncode (L1 x) =
    let ScottRep'' (prxy@Proxy, s) = (scottEncode :: p Void -> ScottRep'' pt) x
    in ScottRep'' (Proxy, \z w -> z _)
-}



-- instance (ScottEncode a (f Void), Rep a Void ~ M1 i c f Void, Generic a)

-- scottEncode :: forall a. (Generic a, Data a) => Rep a Void -> ScottRep'' a
-- scottEncode rep = gfoldl undefined ScottRep'' rep --ScottRep'' (Proxy, gfoldl undefined go pure rep)
--   where
--     go :: x -> Rep a Void -> x
--     go = undefined

-- scottEncode :: (Generic a, ScottEncodeRep a (Rep a Void)) => a -> ScottRep'' a
-- scottEncode = scottEncodeRep . from

-- class (Generic a, Rep a Void ~ repr) => ScottEncodeRep a repr where
--   scottEncodeRep :: repr -> ScottRep'' a

-- instance (ScottEncodeRep a (f Void), Rep a Void ~ M1 i c f Void, Generic a) =>
--     ScottEncodeRep a (M1 i c f Void) where
--   scottEncodeRep (M1 x) = scottEncodeRep x

-- instance forall a. (Generic a, Rep a Void ~ Rec0 a Void) =>
--     ScottEncodeRep a (Rec0 a Void) where

--   scottEncodeRep :: Rec0 a Void -> ScottRep'' a
--   scottEncodeRep (K1 x) = scottEncodeRep (from x)



