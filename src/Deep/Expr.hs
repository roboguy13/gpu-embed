{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wall #-}

module Deep.Expr where

import           Data.Void
import           Data.Proxy
import           Data.Constraint (Constraint)

import           Data.Bifunctor

import           GHC.Generics
-- import           Language.Haskell.TH (Name)

import           Data.Complex

import           Control.Monad.State

import           Data.Type.Equality
import           Data.Typeable

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

-- data ProdMatch s t where
--   ProdMatch :: forall a b r.
--     (GPURep a, GPURep b)
--        => (GPUExp a -> ProdMatch b r) -> ProdMatch  (a, b) r

--   OneProdMatch :: forall a r. (GPURep a) => (GPUExp a -> GPUExp r) -> ProdMatch a r
--   NullaryMatch :: forall a r. GPURep r => GPUExp r -> ProdMatch a r

-- data SumMatch s t where
--   SumMatch :: forall a b r.
--     (GPURep a, GPURep b, GPURepTy b ~ b)
--         => ProdMatch a r -> SumMatch b r -> SumMatch (Either a b) r

--   EmptyMatch :: forall r. SumMatch Void r

--   OneSumMatch :: forall a b. (GPURep a, GPURep b, GPURepTy a ~ a) => ProdMatch a b -> SumMatch a b

-- | The function this contains just is used to provide a semantics for
-- interpreting a GPUExp
newtype SumMatch  a b = MkSumMatch  { runSumMatch  :: a -> b }
newtype ProdMatch a b = MkProdMatch { runProdMatch :: a -> b }

-- Done (case ... of A -> x; B -> y)  ==>  (case ... of A -> Done x; B -> Done y)
data Iter a b
  = Step b
  | Done a
  deriving (Functor, Generic)

data Name a = Name Int deriving (Eq, Show)

data EnvMapping =
  forall a. Typeable a => (Name a) :=> GPUExp a

newtype Env = Env [EnvMapping]

emptyEnv :: Env
emptyEnv = Env []

extendEnv :: Env -> EnvMapping -> Env
extendEnv (Env maps) m = Env (m:maps)

envLookup :: forall a. Typeable a => Env -> Name a -> Maybe (GPUExp a)
envLookup (Env maps) n@(Name _) = go maps
  where
    go [] = Nothing
    go ((n'@(Name _) :=> e):rest) =
      case namesEq n n' of
        Just Refl -> Just e
        Nothing   -> go rest

namesEq :: forall a b. (Typeable a, Typeable b) => Name a -> Name b -> Maybe (a :~: b)
namesEq (Name n) (Name n') =
  case eqT :: Maybe (a :~: b) of
    Just Refl
      | n == n' -> Just Refl
      | otherwise -> Nothing
    Nothing   -> Nothing

data GPUExp t where
  CaseExp :: forall t x r. (GPURep t, GPURepTy x ~ x, GPURepTy t ~ x) => GPUExp t -> GPUExp (SumMatch x r) -> GPUExp r

  SumMatchExp :: forall a b r.
    (GPURep a, GPURep b, GPURepTy b ~ b)
      => GPUExp (ProdMatch a r) -> GPUExp (SumMatch b r) -> GPUExp (SumMatch (Either a b) r)

  ProdMatchExp :: forall a b r.
    (GPURep a, GPURep b)
      => GPUExp (a -> ProdMatch b r) -> GPUExp (ProdMatch (a, b) r)

  NullaryMatch :: forall a r.
    GPURep a
      => GPUExp r -> GPUExp (ProdMatch a r)

  OneSumMatch :: forall a b.
    (GPURep a, GPURep b, GPURepTy a ~ a)
      => GPUExp (ProdMatch a b) -> GPUExp (SumMatch a b)

  OneProdMatch :: forall a b.
    (GPURep a)
      => GPUExp (a -> b) -> GPUExp (ProdMatch a b)

  EmptyMatch :: forall b. GPUExp (SumMatch Void b)

  FalseExp :: GPUExp Bool
  TrueExp :: GPUExp Bool

  Repped :: GPURep a => GPURepTy a -> GPUExp a

  -- Lam :: GPURep a => Int -> GPUExp b -> GPUExp (a -> b)
  Lam :: forall a b. (GPURep a, Typeable a) => Name a -> GPUExp b -> GPUExp (a -> b)
  Var :: forall a. Typeable a => Name a -> GPUExp a -- Constructed internally

  -- Apply :: GPUExp (a -> b) -> GPUExp a -> GPUExp b

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
  FstExp :: GPUExp (a, b) -> GPUExp a
  SndExp :: GPUExp (a, b) -> GPUExp b

  StepExp :: forall a b. GPUExp b -> GPUExp (Iter a b)
  DoneExp :: forall a b. GPUExp a -> GPUExp (Iter a b)

  IfThenElse :: GPUExp Bool -> GPUExp a -> GPUExp a -> GPUExp a

  TailRec :: forall a b. (GPURep a, GPURep b) => GPUExp (b -> Iter a b) -> GPUExp (b -> a)

  Construct :: a -> GPUExp a
  ConstructAp :: forall a b. (GPURep a) => GPUExp (a -> b) -> GPUExp a -> GPUExp b

-- -- Used for intermediate transformations
-- unLam :: GPUExp (a -> b) -> GPUExp a -> GPUExp b
-- unLam (Lam name body) = go
--   where
--     -- | go x   ==>  body[name|->x]
--     go x = undefined
-- unLam _ = error "unLam: Expected a 'Lam'"

-- subst :: Name -> a -> GPUExp b -> GPUExp b
-- subst name x = go
--   where
--     go = error "subst"

-- For convenience in Core transformation
deepFromInteger :: Num b => Integer -> GPUExp b
deepFromInteger = FromIntegral . Lit

-- lam :: forall a b. (GPURep a, Typeable a) => Name a -> (GPUExp a -> GPUExp b) -> GPUExp (a -> b)
-- lam name f = Lam name (f (Var name))

runIter :: forall a b. (GPURep a, GPURep b) => (a -> Iter b a) -> a -> b
runIter f = go
  where
    go x =
      case f x of
        Done r -> r
        Step x' -> go x'

class GPURep t where
    -- Should we wrap these types in a 'Tagged t' in order to preserve more
    -- type safety?
  type GPURepTy t
  type GPURepTy t = GPURepTy (Rep t Void)

  -- | This should be unapplied type (without type arguments)

  rep :: t -> GPUExp t
  rep = Repped . rep'

  rep' :: t -> GPURepTy t

  default rep' :: (Generic t, GenericRep (Rep t Void), GPURepTy t ~ (GenericRepTy (Rep t Void)))
    => t -> GPURepTy t
  rep' = genericRep' . (from :: t -> Rep t Void)


  unrep' :: GPURepTy t -> t

  default unrep' :: (Generic t, GenericRep (Rep t Void), GPURepTy t ~ (GenericRepTy (Rep t Void)))
    => GPURepTy t -> t
  unrep' = (to :: Rep t Void -> t) . genericUnrep'


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


instance GPURep a => GPURep (Complex a) where

instance GPURep a => GPURep (Maybe a) where


instance (GPURep a, GPURep b) => GPURep (Either a b) where
  -- type GPURepTy (Either a b) = Either (GPURepTy a) (GPURepTy b)
  type GPURepTy (Either a b) = Either a b

  rep (Left x) = LeftExp (Construct x)
  rep (Right y) = RightExp (Construct y)

  rep' = id
  unrep' = id

  -- rep (Left x) = LeftExp (rep x)
  -- rep (Right y) = RightExp (rep y)

  -- rep' (Left x) = Left $ rep' x
  -- rep' (Right y) = Right $ rep' y

  -- unrep' (Left x) = Left $ unrep' x
  -- unrep' (Right y) = Right $ unrep' y

instance (GPURep a, GPURep b) => GPURep (a, b) where
  -- type GPURepTy (a, b) =  (GPURepTy a, GPURepTy b)
  type GPURepTy (a, b) =  (a, b)

  rep (x, y) = PairExp (Construct x) (Construct y) --uncurry PairExp
  rep' = id
  unrep' = id

  -- rep (x, y) = PairExp (rep x) (rep y)
  -- rep' (x, y) = (rep' x, rep' y)
  -- unrep' (x, y) = (unrep' x, unrep' y)

instance (GPURep a, GPURep b, GPURep c) => GPURep (a, b, c) where
instance (GPURep a, GPURep b, GPURep c, GPURep d) => GPURep (a, b, c, d) where

-- XXX: Should this instance exist?
instance (GPURep a, GPURep b) => GPURep (Iter a b) where

-- XXX: Should this instance exist?
instance (GPURep a, GPURep b) => GPURep (a -> b) where
  type GPURepTy (a -> b) = GPURepTy a -> GPURepTy b

  rep = Construct
  rep' f x = rep' (f (unrep' x))
  unrep' = undefined

-- Generics instances
instance GPURep (f p) => GPURep (M1 i c f p) where
  type GPURepTy (M1 i c f p) = GPURepTy (f p)

  rep = Repped . rep'
  rep' (M1 x) = rep' x
  unrep' = M1 . unrep'

instance (GPURep (p x), GPURep (q x)) => GPURep ((p :+: q) x) where
  type GPURepTy ((p :+: q) x) =  Either (GPURepTy (p x)) (GPURepTy (q x))

  rep = Repped . rep'

  rep' (L1 x) = Left (rep' x)
  rep' (R1 y) = Right (rep' y)

  unrep' (Left x) = L1 (unrep' x)
  unrep' (Right y) = R1 (unrep' y)

instance (GPURep (p x), GPURep (q x)) => GPURep ((p :*: q) x) where
  type GPURepTy ((p :*: q) x) =  (GPURepTy (p x), GPURepTy (q x))

  rep' (x :*: y) = (rep' x, rep' y)
  unrep' (x, y) = (unrep' x :*: unrep' y)

-- instance GPURep c => GPURep (K1 R c p)

instance GPURep c => GPURep (K1 i c p) where
  type GPURepTy (K1 i c p) = c --GPURepTy c

  rep = Repped . rep'

  rep' (K1 x) = x --rep' x
  unrep' = K1
  -- unrep' = K1 . unrep'

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

construct :: forall t. (ConstructC t)
  => t -> LiftedFn t
construct = construct' . Construct

class ConstructC t where
    construct' :: GPUExp t -> LiftedFn t

instance (GPURep a, ConstructC b) => ConstructC (a -> b) where
    construct' :: GPUExp (a -> b) -> GPUExp a -> LiftedFn b
    construct' c = construct' . ConstructAp c

instance {-# INCOHERENT #-} (LiftedFn b ~ GPUExp b) => ConstructC b where
    construct' :: GPUExp b -> GPUExp b
    construct' = id

-- Should this just produce an error?
sumMatchAbs :: forall s t. (GPURepTy (GPURepTy s) ~ GPURepTy s, GPURep s) => Env -> GPUExp (SumMatch (GPURepTy s) t) -> s -> t
sumMatchAbs env (SumMatchExp p q) =
  \x0 ->
    let x = rep' x0
    in
    case x of
      Left  a -> prodMatchAbs env p a
      Right b -> sumMatchAbs env q b
sumMatchAbs env EmptyMatch = \_ -> error "Non-exhaustive match"
sumMatchAbs env (OneSumMatch f) =
    prodMatchAbs env f . rep'

prodMatchAbs :: GPURep s => Env -> GPUExp (ProdMatch s t) -> s -> t
prodMatchAbs env (ProdMatchExp f) =
  \pair ->
    case pair of
      (x, y) -> runProdMatch (gpuAbsEnv env f x) y --prodMatchAbs (f (rep x)) y

prodMatchAbs env (OneProdMatch f) = \x -> gpuAbsEnv env f x --gpuAbs (f (rep x))
prodMatchAbs env (NullaryMatch x) = \_ -> gpuAbsEnv env x

gpuAbs :: forall t. GPUExp t -> t
gpuAbs = gpuAbsEnv emptyEnv

gpuAbsEnv :: forall t. Env -> GPUExp t -> t
gpuAbsEnv env (Var v) =
  case envLookup env v of
    Just x -> gpuAbsEnv env x
    Nothing -> error $ "No binding for var " ++ show v
gpuAbsEnv env (CaseExp x f) = sumMatchAbs env f (gpuAbsEnv env x)
gpuAbsEnv env FalseExp = False
gpuAbsEnv env TrueExp  = True
gpuAbsEnv env (Repped x) = unrep' x
-- gpuAbs (Lam f) = gpuAbs . f . rep
-- gpuAbs (Apply f x) = gpuAbs f (gpuAbs x)
gpuAbsEnv env (Lit x)  = x
gpuAbsEnv env (Add x y) = gpuAbsEnv env x + gpuAbsEnv env y
gpuAbsEnv env (Sub x y) = gpuAbsEnv env x - gpuAbsEnv env y
gpuAbsEnv env (Mul x y) = gpuAbsEnv env x * gpuAbsEnv env y
gpuAbsEnv env (FromEnum x) = fromEnum (gpuAbsEnv env x)
gpuAbsEnv env (FromIntegral x) = fromIntegral (gpuAbsEnv env x)
gpuAbsEnv env (Sqrt x) = sqrt (gpuAbsEnv env x)
gpuAbsEnv env (Equal x y) = gpuAbsEnv env x == gpuAbsEnv env y
gpuAbsEnv env (Lte x y) = gpuAbsEnv env x <= gpuAbsEnv env y
gpuAbsEnv env (Gt x y) = gpuAbsEnv env x > gpuAbsEnv env y
gpuAbsEnv env (Not x) = not (gpuAbsEnv env x)
gpuAbsEnv env (LeftExp x) = Left (gpuAbsEnv env x)
gpuAbsEnv env (RightExp y) = Right (gpuAbsEnv env y)
gpuAbsEnv env (PairExp x y) = (gpuAbsEnv env x, gpuAbsEnv env y)
gpuAbsEnv env (StepExp x) = Step $ gpuAbsEnv env x
gpuAbsEnv env (DoneExp y) = Done $ gpuAbsEnv env y
gpuAbsEnv env (TailRec f) = \x ->
  case gpuAbsEnv env f x of
    Step x' -> gpuAbsEnv env (TailRec f) x'
    Done r  -> r
gpuAbsEnv env (IfThenElse cond t f)
  | gpuAbsEnv env cond = gpuAbsEnv env t
  | otherwise = gpuAbsEnv env f
gpuAbsEnv env (Construct x) = x
gpuAbsEnv env (ConstructAp f x) = gpuAbsEnv env f (gpuAbsEnv env x)

gpuAbsEnv env e@(SumMatchExp {}) = MkSumMatch (sumMatchAbs env e)
gpuAbsEnv env e@(OneSumMatch {}) = MkSumMatch (sumMatchAbs env e)
gpuAbsEnv env EmptyMatch = MkSumMatch absurd

gpuAbsEnv env e@(ProdMatchExp {}) = MkProdMatch (prodMatchAbs env e)
gpuAbsEnv env e@(OneProdMatch {}) = MkProdMatch (prodMatchAbs env e)
gpuAbsEnv env e@(NullaryMatch {}) = MkProdMatch (prodMatchAbs env e)

gpuAbsEnv env (FstExp x) = fst (gpuAbsEnv env x)
gpuAbsEnv env (SndExp x) = snd (gpuAbsEnv env x)

gpuAbsEnv env (Lam (name :: Name a) (body :: GPUExp b)) = \(arg :: a) ->

    let go :: forall x. GPUExp x -> GPUExp x
        go expr@(Var name2 :: GPUExp t') =
          case eqT :: Maybe (t' :~: a) of
            Just Refl
              | name == name2 -> rep arg
            _   ->
              case envLookup env name2 of
                Just v -> v
                Nothing -> expr

        go (CaseExp x f) = CaseExp (go x) (go f)

        go (Add x y) = Add (go x) (go y)
        go (Sub x y) = Sub (go x) (go y)
        go (Mul x y) = Mul (go x) (go y)
        go (FromEnum x) = FromEnum (go x)
        go (FromIntegral x) = FromIntegral (go x)
        go (Sqrt x) = Sqrt (go x)
        go (Equal x y) = Equal (go x) (go y)
        go (Lte x y) = Lte (go x) (go y)
        go (Gt x y) = Gt (go x) (go y)
        go (Not x) = Not (go x)
        go (LeftExp x) = LeftExp (go x)
        go (RightExp y) = RightExp (go y)
        go (PairExp x y) = PairExp (go x) (go y)

        go (StepExp x) = StepExp (go x)
        go (DoneExp y) = DoneExp (go y)
        go (TailRec f) = TailRec  (go f)

        go (IfThenElse cond t f) = IfThenElse (go cond) (go t) (go f)

        go (Construct x) = Construct x
        go (ConstructAp f x) = ConstructAp f x

        go (SumMatchExp f g) = SumMatchExp (go f) (go g)
        go (OneSumMatch f) = OneSumMatch (go f)
        go EmptyMatch = EmptyMatch
        go (ProdMatchExp f) = ProdMatchExp (go f)
        go (OneProdMatch x) = OneProdMatch (go x)
        go (NullaryMatch x) = NullaryMatch (go x)

        go (Lam name2 body2) = Lam name2 (go body2) -- Names should be unique, so this should be ok

        go FalseExp = FalseExp
        go TrueExp = TrueExp
        go (Repped x) = Repped x
        go (Lit x) = Lit x
        go (FstExp x) = FstExp (go x)
        go (SndExp x) = SndExp (go x)
    in

    gpuAbsEnv (extendEnv env (name :=> rep arg)) $ go body

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


