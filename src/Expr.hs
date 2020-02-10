{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Expr where

import           Data.Void
import           Data.Tagged
import           Data.Proxy
import           Data.Constraint (Constraint)

import           Data.Bifunctor

import           GHC.Generics
import           Language.Haskell.TH (Name)

import           Data.Complex

-- Idea: Represent a pattern match of a particular type as
--    KnownSymbol name => Proxy name -> MatchType name
-- with 'MatchType' being a type family that gives the type of the match
-- associated to matching on the constructor named 'name'. Maybe these
-- could be stored in a heterogenous list.

-- | Idea: Deep embedding for a pattern match (possibly using a non-regular
-- type?). Convert types to a "canonical form" to use this (like 'Either's
-- and '(,)'s)

-- TODO: Should we have a phantom type argument with the original type to preserve (possibly) more type safety?

-- TODO: Should this just be a function type? Maybe it could be a function
-- from s -> t, where is a nested pair type, and we use projection
-- combinators to extract the values inside the function.
data ProdMatch s t where
  ProdMatch ::
    (GPURep a, GPURep b)
       => (GPUExp (GetType a) -> ProdMatch b r) -> ProdMatch (Tagged t (a, b)) r

  OneProdMatch :: (GPURep a) => (GPUExp (GetType a) -> GPUExp r) -> ProdMatch a r
  NullaryMatch :: GPURep r => GPUExp r -> ProdMatch a r

data SumMatch s t where
  SumMatch ::
    (GPURep a, GPURep b, GPURepTy b ~ b)
        => ProdMatch a r -> SumMatch b r -> SumMatch (Tagged t (Either a b)) r

  EmptyMatch :: SumMatch Void r

  OneSumMatch :: (GPURep a, GPURep b, GPURepTy a ~ a) => ProdMatch a b -> SumMatch a b


type family TagMatches t x :: Constraint where
  TagMatches t (Tagged t x) = ()

data SafeSumMatch origType s t where
  SafeSumMatch :: TagMatches origType s => SumMatch s t -> SafeSumMatch origType s t

  SafeEmptyMatch :: SafeSumMatch origType Void r
  SafeOneMatch :: (GPURep a, GPURep b, GPURepTy a ~ a) => ProdMatch a b -> SafeSumMatch origType a b


type family TagWith t x where
  TagWith t (Tagged t' x) = Tagged t x
  TagWith t x             = Tagged t x

type family GetType x where
  GetType (Tagged t x) = t
  GetType t            = t

type family Untag x where
  Untag (Tagged t x) = x
  Untag x            = x

-- Done (case ... of A -> x; B -> y)  ==>  (case ... of A -> Done x; B -> Done y)
data Iter a b
  = Step b
  | Done a
  deriving (Functor, Generic)

data GPUExp t where
  CaseExp :: (GPURep t) => GPUExp t -> SafeSumMatch t (GPURepTy t) r -> GPUExp r

  FalseExp :: GPUExp Bool
  TrueExp :: GPUExp Bool

  Repped :: GPURep a => GPURepTy a -> GPUExp a

  Lam :: GPURep a => Name -> GPUExp b -> GPUExp (a -> b)
  Var :: Proxy a -> Name -> GPUExp a -- Constructed internally

  -- Lam :: GPURep a =>  -> GPUExp (a -> b)

  Apply :: GPUExp (a -> b) -> GPUExp a -> GPUExp b

  Lit :: Num a => a -> GPUExp a

  Add :: Num a => GPUExp a -> GPUExp a -> GPUExp a
  Sub :: Num a => GPUExp a -> GPUExp a -> GPUExp a
  Mul :: Num a => GPUExp a -> GPUExp a -> GPUExp a

  Twice :: GPUExp (a -> a) -> GPUExp a -> GPUExp a

  FromEnum :: Enum a => GPUExp a -> GPUExp Int
  FromIntegral :: (Integral a, Num b) => GPUExp a -> GPUExp b

  Sqrt :: Floating a => GPUExp a -> GPUExp a

  Equal :: Eq a => GPUExp a -> GPUExp a -> GPUExp Bool
  Lte :: Ord a => GPUExp a -> GPUExp a -> GPUExp Bool
  Gt :: Ord a => GPUExp a -> GPUExp a -> GPUExp Bool

  Not :: GPUExp Bool -> GPUExp Bool

  LeftExp :: GPUExp a -> GPUExp (Either a b)
  RightExp :: GPUExp b -> GPUExp (Either a b)

  PairExp :: GPUExp a -> GPUExp b -> GPUExp (a, b)

  StepExp :: GPUExp b -> GPUExp (Iter a b)
  DoneExp :: GPUExp a -> GPUExp (Iter a b)

  IfThenElse :: GPUExp Bool -> GPUExp a -> GPUExp a -> GPUExp a

  TailRec :: (GPURep a, GPURep b) => (GPUExp b -> GPUExp (Iter a b)) -> GPUExp (b -> a)

  Construct :: a -> GPUExp a
  ConstructAp :: (GPURep a) => GPUExp (a -> b) -> GPUExp a -> GPUExp b

class GPURep t where
    -- Should we wrap these types in a 'Tagged t' in order to preserve more
    -- type safety?
  type GPURepTy t
  type GPURepTy t = TagWith t (GPURepTy (Rep t Void))

  rep :: t -> GPUExp t
  rep = Repped . rep'

  rep' :: t -> GPURepTy t

  default rep' :: (Generic t, GenericRep (Rep t Void), GPURepTy t ~ Tagged t (GenericRepTy (Rep t Void)))
    => t -> GPURepTy t
  rep' = Tagged . genericRep' . (from :: t -> Rep t Void)


  unrep' :: GPURepTy t -> t

  default unrep' :: (Generic t, GenericRep (Rep t Void), GPURepTy t ~ Tagged t (GenericRepTy (Rep t Void)))
    => GPURepTy t -> t
  unrep' = (to :: Rep t Void -> t) . genericUnrep' . unTagged

  repGetType :: t -> GPUExp (GetType t)

  default repGetType :: GetType t ~ t => t -> GPUExp (GetType t)
  repGetType = rep

instance (GPURep t, GPURepTy t ~ Tagged t x) => GPURep (Tagged t x) where
  type GPURepTy (Tagged t x) = Tagged t x

  rep' = id
  unrep' = id

  -- repGetType :: Tagged t x -> GPUExp (GetType (Tagged t x))
  repGetType = rep . unrep'

instance GPURep Int where
  type GPURepTy Int = Int
  rep = Lit
  rep' = id
  unrep' = id
instance GPURep Integer where
  type GPURepTy Integer = Integer
  rep = Lit
  rep' = id
  unrep' = id
instance GPURep Float where
  type GPURepTy Float = Float
  rep = Lit
  rep' = id
  unrep' = id
instance GPURep Double where
  type GPURepTy Double = Double
  rep = Lit
  rep' = id
  unrep' = id

instance GPURep Bool where
  type GPURepTy Bool = Bool
  rep False = FalseExp
  rep True  = TrueExp
  rep' = id
  unrep' = id


instance GPURep a => GPURep (Complex a)

instance GPURep a => GPURep (Maybe a)


instance (GPURep a, GPURep b) => GPURep (Either a b) where
  type GPURepTy (Either a b) = Tagged (Either a b) (Either (GPURepTy a) (GPURepTy b))
  rep (Left x) = LeftExp (rep x)
  rep (Right y) = RightExp (rep y)

  rep' (Left x) = Tagged . Left $ rep' x
  rep' (Right y) = Tagged . Right $ rep' y

  unrep' (Tagged (Left x)) = Left $ unrep' x
  unrep' (Tagged (Right y)) = Right $ unrep' y

instance (GPURep a, GPURep b) => GPURep (a, b) where
  type GPURepTy (a, b) = Tagged (a, b) (GPURepTy a, GPURepTy b)
  rep (x, y) = PairExp (rep x) (rep y)
  rep' (x, y) = Tagged (rep' x, rep' y)
  unrep' (Tagged (x, y)) = (unrep' x, unrep' y)

instance (GPURep a, GPURep b, GPURep c) => GPURep (a, b, c)
instance (GPURep a, GPURep b, GPURep c, GPURep d) => GPURep (a, b, c, d)

-- XXX: Should this instance exist?
instance (GPURep a, GPURep b) => GPURep (Iter a b) where


-- Generics instances
instance GPURep (f p) => GPURep (M1 i c f p) where
  type GPURepTy (M1 i c f p) = GPURepTy (f p)

  rep = Repped . rep'
  rep' (M1 x) = rep' x
  unrep' = M1 . unrep'

instance (GPURep (p x), GPURep (q x)) => GPURep ((p :+: q) x) where
  type GPURepTy ((p :+: q) x) = Tagged (Either (p x) (q x)) (Either (GPURepTy (p x)) (GPURepTy (q x)))

  rep = Repped . rep'

  rep' (L1 x) = Tagged $ Left (rep' x)
  rep' (R1 y) = Tagged $ Right (rep' y)

  unrep' (Tagged (Left x)) = L1 (unrep' x)
  unrep' (Tagged (Right y)) = R1 (unrep' y)

instance (GPURep (p x), GPURep (q x)) => GPURep ((p :*: q) x) where
  type GPURepTy ((p :*: q) x) = Tagged (p x, q x) (GPURepTy (p x), GPURepTy (q x))

  rep' (x :*: y) = Tagged (rep' x, rep' y)
  unrep' (Tagged (x, y)) = (unrep' x :*: unrep' y)

instance GPURep c => GPURep (K1 i c p) where
  type GPURepTy (K1 i c p) = GPURepTy c

  rep = Repped . rep'

  rep' (K1 x) = rep' x
  unrep' = K1 . unrep'

instance GPURep (U1 p) where
  type GPURepTy (U1 p) = ()

  rep' U1 = ()
  unrep' () = U1


class GenericRep repr where
    type GenericRepTy repr

    genericRep' :: repr -> GenericRepTy repr
    genericUnrep' :: GenericRepTy repr -> repr

instance forall p q. (GPURep (p Void), GPURep (q Void)) =>
  GenericRep ((p :+: q) Void) where

    type GenericRepTy ((p :+: q) Void) = Either (GPURepTy (p Void)) (GPURepTy (q Void))

    genericRep' = bimap rep' rep' . toCanonical
    genericUnrep' = fromCanonical . bimap unrep' unrep'

instance (GPURep (p Void), GPURep (q Void)) =>
  GenericRep ((p :*: q) Void) where

    type GenericRepTy ((p :*: q) Void) = (GPURepTy (p Void), GPURepTy (q Void))

    genericRep' = bimap rep' rep' . toCanonical
    genericUnrep' = fromCanonical . bimap unrep' unrep'

instance (GenericRep (f Void)) =>
  GenericRep (M1 i c f Void) where
    type GenericRepTy (M1 i c f Void) = GenericRepTy (f Void)

    genericRep' = genericRep' . unM1
    genericUnrep' = M1 . genericUnrep'

the :: a -> a
the = id

the_repr :: GPUExp a -> GPUExp a
the_repr = id

type family LiftedFn t where
  LiftedFn (a -> b) = GPUExp a -> LiftedFn b
  LiftedFn b = GPUExp b

construct :: (Construct t)
  => t -> LiftedFn t
construct = construct' . Construct

class Construct t where
    construct' :: GPUExp t -> LiftedFn t

instance (GPURep a, Construct b) => Construct (a -> b) where
    construct' :: GPUExp (a -> b) -> GPUExp a -> LiftedFn b
    construct' c = construct' . ConstructAp c

instance {-# INCOHERENT #-} (LiftedFn b ~ GPUExp b) => Construct b where
    construct' :: GPUExp b -> GPUExp b
    construct' = id

-- Should this just produce an error?
sumMatchAbs :: GPURep s => SafeSumMatch s (GPURepTy s) t -> s -> t
sumMatchAbs (SafeSumMatch s) = go s
  where
    go :: GPURep s => SumMatch (GPURepTy s) t -> s -> t
    go (SumMatch p q) =
      \x0 ->
        let Tagged x = rep' x0
        in
        case x of
          Left  a -> prodMatchAbs p a
          Right b -> go q b
    go EmptyMatch = \_ -> error "Non-exhaustive match"
    go (OneSumMatch f) = prodMatchAbs f . unrep' . rep' -- TODO: Is this reasonable?

prodMatchAbs :: GPURep s => ProdMatch s t -> s -> t
prodMatchAbs (ProdMatch f) =
  \(Tagged pair) ->
    case pair of
      (x, y) -> prodMatchAbs (f (repGetType x)) y

prodMatchAbs (OneProdMatch f) = \x -> gpuAbs (f (repGetType x))
prodMatchAbs (NullaryMatch x) = \_ -> gpuAbs x

gpuAbs :: GPUExp t -> t
gpuAbs (CaseExp x f) = sumMatchAbs f (gpuAbs x)
gpuAbs FalseExp = False
gpuAbs TrueExp  = True
gpuAbs (Repped x) = unrep' x
-- gpuAbs (Lam f) = gpuAbs . f . rep
-- gpuAbs (Apply f x) = gpuAbs f (gpuAbs x)
gpuAbs (Lit x)  = x
gpuAbs (Add x y) = gpuAbs x + gpuAbs y
gpuAbs (Sub x y) = gpuAbs x - gpuAbs y
gpuAbs (Mul x y) = gpuAbs x * gpuAbs y
gpuAbs (FromEnum x) = fromEnum (gpuAbs x)
gpuAbs (FromIntegral x) = fromIntegral (gpuAbs x)
gpuAbs (Sqrt x) = sqrt (gpuAbs x)
gpuAbs (Equal x y) = gpuAbs x == gpuAbs y
gpuAbs (Lte x y) = gpuAbs x <= gpuAbs y
gpuAbs (Gt x y) = gpuAbs x > gpuAbs y
gpuAbs (Not x) = not (gpuAbs x)
gpuAbs (LeftExp x) = Left (gpuAbs x)
gpuAbs (RightExp y) = Right (gpuAbs y)
gpuAbs (PairExp x y) = (gpuAbs x, gpuAbs y)
gpuAbs (StepExp x) = Step $ gpuAbs x
gpuAbs (DoneExp y) = Done $ gpuAbs y
gpuAbs (TailRec f) = \x ->
  case gpuAbs (f (rep x)) of
    Step x' -> gpuAbs (TailRec f) x'
    Done r  -> r
gpuAbs (IfThenElse cond t f)
  | gpuAbs cond = gpuAbs t
  | otherwise = gpuAbs f
gpuAbs (Construct x) = x
gpuAbs (ConstructAp f x) = gpuAbs f (gpuAbs x)


class Canonical t where
  type GenericOp t :: (* -> *) -> (* -> *) -> * -> *

  toCanonical :: GenericOp t p q x -> t (p x) (q x)
  fromCanonical :: t (p x) (q x) -> GenericOp t p q x

instance Canonical Either where
  type GenericOp Either = (:+:)

  toCanonical (L1 x) = Left x
  toCanonical (R1 y) = Right y

  fromCanonical (Left x) = L1 x
  fromCanonical (Right y) = R1 y

instance Canonical (,) where
  type GenericOp (,) = (:*:)

  toCanonical (x :*: y) = (x, y)
  fromCanonical (x, y) = x :*: y


