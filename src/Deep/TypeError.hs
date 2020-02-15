{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}

import GHC.Types (Constraint, Type)
import Data.Type.Equality

data Proxy a = Proxy

data Tagged2 (h :: k) (t :: *) (a :: *) = Tagged { unTagged :: a }

type KindOf (t :: k) = k

type family GetType x where
  GetType (Tagged2 h t x) = t
  GetType t            = t

type family TagWith t x where
  TagWith t (Tagged2 h t' x) = Tagged2 (TypeHead t) t x
  TagWith t x                = Tagged2 (TypeHead t) t x

data ProdMatch s t where
  ProdMatch :: (C a, C b) =>
     (E (GetType a) -> ProdMatch b r) -> ProdMatch (Tagged2 (TypeHead t) t (a, b)) r

  OneProdMatch :: C a => (E (GetType a) -> E r) -> ProdMatch a r

data SumMatch s t where
  SumMatch :: (C a, C b, RepType b ~ b) =>
      ProdMatch a r -> SumMatch b r -> SumMatch (Tagged2 (TypeHead t) t (Either a b)) r

  OneSumMatch :: (C a, C b, RepType a ~ a) => ProdMatch a b -> SumMatch a b

data SafeSumMatch origType s t where
  SafeSumMatch :: TagMatches origType s => Proxy (TypeHead s) -> SumMatch s t -> SafeSumMatch origType s t

data E t where
  LitE :: C t => t -> E t
  CaseE :: C t => E t -> SafeSumMatch t (RepType t) r -> E r
  -- TODO: Try adding TailRec

type family TagMatches t x :: Constraint where
  TagMatches t (Tagged2 h t x) = TypeHead t ~ h

data IntPair = IntPair Int Int

class C t where
  type family TypeHead t :: k

  type family RepType t



instance (C t, RepType t ~ Tagged2 h t a) => C (Tagged2 h t a) where
  type TypeHead (Tagged2 h t a) = h

  type RepType (Tagged2 h t a) = Tagged2 h t a


instance C IntPair where
  type TypeHead IntPair = IntPair :: *

  type RepType IntPair = TagWith IntPair (Tagged2 (,) (Int, Int) (RepType Int, RepType Int))



instance C (a, b) where
  type TypeHead (a, b) = (,)

  type RepType (a, b) = Tagged2 (,) (a, b) (RepType a, RepType b)

instance C Int where
  type TypeHead Int = Int
  type RepType Int = Int

instance C Char where
  type TypeHead Char = Char
  type RepType Char = Char

instance C Bool where
  type TypeHead Bool = Bool
  type RepType Bool = Bool

evalSafeSumMatch :: C a => SafeSumMatch a (RepType a) b -> a -> b
evalSafeSumMatch = undefined

eval :: E a -> a
eval = undefined

-- TypeHead (Tagged2 (TypeHead IntPair) IntPair (Int, Int))

test_works :: (TypeHead (Tagged2 ((TypeHead :: * -> *) IntPair) IntPair (Int, Int))) :~: IntPair
test_works =
  undefined

test :: (TypeHead (Tagged2 ((TypeHead @(KindOf IntPair)) IntPair) IntPair (Int, Int))) :~: IntPair
test =
  undefined

thIP :: (TypeHead IntPair) :~: IntPair
thIP = Refl

test2 :: (TypeHead (Tagged2 IntPair IntPair (Int, Int))) :~: IntPair
test2 = Refl

-- test :: Bool
test_ :: Bool
test_ = 
  -- case HRefl :: (TypeHead (Tagged2 (TypeHead IntPair) IntPair (Int, Int))) :~: IntPair of
    eval (CaseE (LitE (IntPair 1 2)) (SafeSumMatch (Proxy @((TypeHead (Tagged2 (TypeHead IntPair) IntPair (Int, Int))))) (OneSumMatch (ProdMatch (\x -> (OneProdMatch (\y -> LitE True)))))))

-- evalTest :: Bool
-- evalTest = evalSafeSumMatch test (IntPair 1 2)

