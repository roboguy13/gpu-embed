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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RoleAnnotations #-}

module Deep.Expr where

import           Data.Void
import           Data.Proxy
import           Data.Constraint (Constraint, Dict(..))

import           Data.Bifunctor

import           GHC.Generics
import           Data.Generics.Uniplate.Direct
-- import           Language.Haskell.TH (Name)

import           Data.Complex

import           Control.Monad.State

import           Data.Type.Equality
import           Data.Typeable

import           Data.Char

import           GHC.Prim
import           Data.Coerce

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
-- type role SumMatch nominal nominal
newtype SumMatch  a b = MkSumMatch  { runSumMatch  :: a -> b }
-- type role ProdMatch nominal nominal
newtype ProdMatch a b = MkProdMatch { runProdMatch :: a -> b }

-- Done (case ... of A -> x; B -> y)  ==>  (case ... of A -> Done x; B -> Done y)
data Iter a b
  = Step b
  | Done a
  deriving (Functor, Generic)

-- | NOTE: The unique identifiers start at 1
-- type role Name nominal
newtype Name a = Name { getNameIdent :: Int } deriving (Eq, Show)

getNameUniq :: Name a -> Int
getNameUniq = getNameIdent

data EnvMapping where
  (:=>) :: forall a. Typeable a => (Name a) -> GPUExp a -> EnvMapping

newtype Env = Env [EnvMapping]

emptyEnv :: Env
emptyEnv = Env []

extendEnv :: Env -> EnvMapping -> Env
extendEnv (Env maps) m = Env (m:maps)

envLookup :: Typeable a => Env -> Name a -> Maybe (GPUExp a)
envLookup (Env maps) n = go maps
  where
    go [] = Nothing
    go ((n' :=> e):rest) =
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

  Repped :: (GPURep a, GPURep (GPURepTy a)) => GPURepTy a -> GPUExp a

  Lam :: forall a b. (GPURep a, Typeable a) => Name a -> GPUExp b -> GPUExp (a -> b)
  Var :: forall a. Typeable a => Name a -> GPUExp a -- Constructed internally
  App :: forall a b. (GPURep a) => GPUExp (a -> b) -> GPUExp a -> GPUExp b

  -- Apply :: GPUExp (a -> b) -> GPUExp a -> GPUExp b

  CharLit :: Char -> GPUExp Char
  Lit :: (Typeable a, Show a, Num a) => a -> GPUExp a

  Ord :: GPUExp Char -> GPUExp Int

  Add :: Num a => GPUExp a -> GPUExp a -> GPUExp a
  Sub :: Num a => GPUExp a -> GPUExp a -> GPUExp a
  Mul :: Num a => GPUExp a -> GPUExp a -> GPUExp a

  -- Twice :: GPUExp (a -> a) -> GPUExp a -> GPUExp a

  FromEnum :: Enum a => GPUExp a -> GPUExp Int
  FromIntegral :: forall a b. (Typeable a, Typeable b, Integral a, Num b) => GPUExp a -> GPUExp b

  Sqrt :: Floating a => GPUExp a -> GPUExp a

  Equal :: Eq a => GPUExp a -> GPUExp a -> GPUExp Bool
  Lte :: Ord a => GPUExp a -> GPUExp a -> GPUExp Bool
  Gt :: Ord a => GPUExp a -> GPUExp a -> GPUExp Bool

  Not :: GPUExp Bool -> GPUExp Bool

  LeftExp :: forall a b. GPUExp a -> GPUExp (Either a b)
  RightExp :: forall a b. GPUExp b -> GPUExp (Either a b)

  PairExp :: forall a b. GPUExp a -> GPUExp b -> GPUExp (a, b)
  FstExp :: forall a b. GPUExp (a, b) -> GPUExp a
  SndExp :: forall a b. GPUExp (a, b) -> GPUExp b

  StepExp :: forall a b. GPUExp b -> GPUExp (Iter a b)
  DoneExp :: forall a b. GPUExp a -> GPUExp (Iter a b)

  UnitExp :: GPUExp ()

  IfThenElse :: GPUExp Bool -> GPUExp a -> GPUExp a -> GPUExp a

  TailRec :: forall a b. (GPURep a, GPURep b) => GPUExp (b -> Iter a b) -> GPUExp (b -> a)

    -- Typeable allows us to inspect the types. This can be useful if we
    -- want to, for instance, treat 'Complex Double' values differently
    -- than '(Double, Double)' values in a backend
  ConstructRep :: forall a. (Typeable a, GPURep a) => GPUExp (GPURepTy a) -> GPUExp a

  Construct :: a -> GPUExp a
  ConstructAp :: forall a b. (GPURep a) => GPUExp (a -> b) -> GPUExp a -> GPUExp b

  CastExp :: forall (a :: *) (b :: *). a ~ b => GPUExp a -> GPUExp b -- Inspiration from a mailing list posting from Conal Elliott

  UnconstructRep :: GPUExp a -> GPUExp (GPURepTy (M1 S ('MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy) (Rec0 a) Void))

-- (GPURepTy
--     (M1
--        S
--        ('MetaSel
--           'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
--        (Rec0 Int)
--        Void))

tailRecApp :: forall a b. (GPURep a, GPURep b) => GPUExp (b -> Iter a b) -> GPUExp b -> GPUExp a
tailRecApp body = App (TailRec body)

transformE :: (forall r. GPUExp r -> GPUExp r) -> GPUExp a -> GPUExp a
transformE tr0 = tr
  where
    tr :: forall s. GPUExp s -> GPUExp s
    tr = go . tr0

    go :: forall s. GPUExp s -> GPUExp s
    go (CaseExp x f) = CaseExp (tr x) (tr f)
    go (SumMatchExp x y) = SumMatchExp (tr x) (tr y)
    go (ProdMatchExp f) = ProdMatchExp (tr f)
    go (NullaryMatch x) = NullaryMatch (tr x)
    go (OneSumMatch p) = OneSumMatch (tr p)
    go (OneProdMatch f) = OneProdMatch (tr f)
    go EmptyMatch = EmptyMatch
    go FalseExp = FalseExp
    go TrueExp = TrueExp
    go e@(Repped _) = e
    go (Lam n x) = Lam n (tr x)
    go e@(Var _) = e
    go e@(Lit _) = e
    go (Add x y) = Add (tr x) (tr y)
    go (Sub x y) = Sub (tr x) (tr y)
    go (Mul x y) = Mul (tr x) (tr y)
    -- go (Twice f x) = Twice
    go (FromEnum x) = FromEnum (tr x)
    go (FromIntegral x) = FromIntegral (tr x)
    go (Sqrt x) = Sqrt (tr x)
    go (Equal x y) = Equal (tr x) (tr y)
    go (Lte x y) = Lte (tr x) (tr y)
    go (Gt x y) = Gt (tr x) (tr y)
    go (Not x) = Not (tr x)
    go (LeftExp x) = LeftExp (tr x)
    go (RightExp y) = RightExp (tr y)
    go (PairExp x y) = PairExp (tr x) (tr y)
    go (FstExp x) = FstExp (tr x)
    go (SndExp x) = SndExp (tr x)
    go (StepExp x) = StepExp (tr x)
    go (DoneExp y) = DoneExp (tr y)
    go (IfThenElse x y z) = IfThenElse (tr x) (tr y) (tr z)
    go (TailRec f) = TailRec (tr f)
    go e@(Construct _) = e
    go (ConstructAp f x) = ConstructAp (tr f) (tr x)
    go (Ord x) = Ord (tr x)
    go e@(CharLit _) = e
    go e@UnitExp = e
    go e@(ConstructRep _) = e
    go (CastExp x) = CastExp (tr (coerce x))

transformEA :: forall a m. Monad m
  => (forall r. GPUExp r -> m (GPUExp r)) -> GPUExp a -> m (GPUExp a)
transformEA tr0 = tr
  where
    tr :: forall s. GPUExp s -> m (GPUExp s)
    tr = go <=< tr0

    go :: forall s. GPUExp s -> m (GPUExp s)
    go (CaseExp x f) = CaseExp <$> (tr x) <*> (tr f)
    go (SumMatchExp x y) = SumMatchExp <$> (tr x) <*> (tr y)
    go (ProdMatchExp f) = ProdMatchExp <$> (tr f)
    go (NullaryMatch x) = NullaryMatch <$> (tr x)
    go (OneSumMatch p) = OneSumMatch <$> (tr p)
    go (OneProdMatch f) = OneProdMatch <$> (tr f)
    go EmptyMatch = pure EmptyMatch
    go FalseExp = pure FalseExp
    go TrueExp = pure TrueExp
    go e@(Repped _) = pure e
    go (Lam n x) = Lam n <$> (tr x)
    go e@(Var _) = pure e
    go e@(Lit _) = pure e
    go (Add x y) = Add <$> (tr x) <*> (tr y)
    go (Sub x y) = Sub <$> (tr x) <*> (tr y)
    go (Mul x y) = Mul <$> (tr x) <*> (tr y)
    -- go (Twice f x) = Twice
    go (FromEnum x) = FromEnum <$> (tr x)
    go (FromIntegral x) = FromIntegral <$> (tr x)
    go (Sqrt x) = Sqrt <$> (tr x)
    go (Equal x y) = Equal <$> (tr x) <*> (tr y)
    go (Lte x y) = Lte <$> (tr x) <*> (tr y)
    go (Gt x y) = Gt <$> (tr x) <*> (tr y)
    go (Not x) = Not <$> (tr x)
    go (LeftExp x) = LeftExp <$> (tr x)
    go (RightExp y) = RightExp <$> (tr y)
    go (PairExp x y) = PairExp <$> (tr x) <*> (tr y)
    go (FstExp x) = FstExp <$> (tr x)
    go (SndExp x) = SndExp <$> (tr x)
    go (StepExp x) = StepExp <$> (tr x)
    go (DoneExp y) = DoneExp <$> (tr y)
    go (IfThenElse x y z) = IfThenElse <$> (tr x) <*> (tr y) <*> (tr z)
    go (TailRec f) = TailRec <$> (tr f)
    go e@(Construct _) = pure e
    go (ConstructAp f x) = ConstructAp <$> (tr f) <*> (tr x)
    go (Ord x) = Ord <$> (tr x)
    go e@(CharLit _) = pure e
    go e@UnitExp = pure e
    go e@(ConstructRep _) = pure e
    go (CastExp x) = CastExp <$> tr (coerce x)

-- convertE :: Coercible a b => GPUExp a -> GPUExp b
-- convertE (CaseExp x f) = CaseExp x (convertE f)
-- convertE (SumMatchExp x y) = SumMatchExp _ _


-- foldEM :: forall a b m. Monad m => (forall x. GPUExp x -> b -> m b) -> b -> GPUExp a -> m b
-- foldEM f z = go
--   where
--     go :: forall s. GPUExp s -> m b
--     go (CaseExp x y) = f x =<< go y
--     go (SumMatchExp x y) = f x =<< go y
--     go (ProdMatchExp x) = f x z
--     go (NullaryMatch x) = f x z
--     go (OneSumMatch x) = f x z
--     go (OneProdMatch x) = f x z
--     go e@EmptyMatch = return z
--     go e@FalseExp = return z
--     go e@TrueExp = return z
--     go e@(Repped _) = return z
--     go (Lam n x) = f x z
--     go (Add x y) = f x =<< go y

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
deepFromInteger :: (Typeable b, Num b) => Integer -> GPUExp b
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

-- Typeable constraint is for ConstructRep
class Typeable t => GPURep t where
    -- Should we wrap these types in a 'Tagged t' in order to preserve more
    -- type safety?
  type GPURepTy t
  type GPURepTy t = GPURepTy (Rep t Void)

  -- | This should be unapplied type (without type arguments)

  construct :: t -> GPUExp (GPURepTy t)

  -- NOTE: The INLINABLE pragmas make the unfoldings available to the Core
  -- plugin

  default construct :: (Generic t, GPURep (Rep t Void), GPURep (GPURepTy t), GPURepTy (Rep t Void) ~ GPURepTy t) => t -> GPUExp (GPURepTy t)
  construct = construct . (from :: t -> Rep t Void)
  {-# INLINABLE construct #-}

  rep :: t -> GPUExp t

  default rep :: (GPURep (GPURepTy t)) => t -> GPUExp t
  rep x = ConstructRep (construct x)
  {-# INLINABLE rep #-}

  rep' :: t -> GPURepTy t

  default rep' :: (Generic t, GPURepTy t ~ GPURepTy (Rep t Void), GPURep (Rep t Void))
    => t -> GPURepTy t
  rep' = rep' . (from :: t -> Rep t Void)
  {-# INLINABLE rep' #-}


  unrep' :: GPURepTy t -> t

  default unrep' :: (Generic t, GPURepTy t ~ GPURepTy (Rep t Void), GPURep (Rep t Void))
    => GPURepTy t -> t
  unrep' = (to :: Rep t Void -> t) . unrep'
  {-# INLINABLE unrep' #-}

-- TODO: Does this work for what we need (dealing with constructors for
-- user defined types)?

-- construct :: forall a x. (GPURep a, GPURep x, GPURepTy a ~ x) => a -> GPUExp a
-- construct = _ . rep . rep'

-- construct :: a -> GPUExp a
-- construct = Repped . rep'

-- construct :: (GPURep a, GPURep (GPURepTy a)) => GPUExp a -> GPUExp (GPURepTy a)
-- construct (Repped e) = rep e
-- construct _ = error "construct: Given non-Repped argument"

-- constructAp' :: forall a b. (GPURep a) => GPUExp (a -> b) -> GPUExp a -> GPUExp b
-- constructAp' f x = _

instance GPURep Int where
  type GPURepTy Int = Int
  construct = Lit
  rep = Lit
  rep' = id
  unrep' = id
instance GPURep Integer where
  type GPURepTy Integer = Integer
  construct = Lit
  rep = Lit
  rep' = id
  unrep' = id
instance GPURep Float where
  type GPURepTy Float = Float
  construct = Lit
  rep = Lit
  rep' = id
  unrep' = id
instance GPURep Double where
  type GPURepTy Double = Double
  construct = Lit
  rep = Lit
  rep' = id
  unrep' = id

instance GPURep Bool where
  type GPURepTy Bool = Bool

  construct True = TrueExp
  construct False = FalseExp

  rep False = FalseExp
  rep True  = TrueExp
  rep' = id
  unrep' = id

instance GPURep Char where
  type GPURepTy Char = Char

  construct = CharLit

  rep c = CharLit c
  rep' = id
  unrep' = id

instance GPURep a => GPURep (Complex a) where

instance GPURep a => GPURep (Maybe a) where


instance (GPURep a, GPURep b) => GPURep (Either a b) where
  -- type GPURepTy (Either a b) = Either (GPURepTy a) (GPURepTy b)
  type GPURepTy (Either a b) = Either a b

  construct (Left x) = LeftExp (rep x)
  construct (Right y) = RightExp (rep y)

  rep (Left x) = LeftExp (rep x)
  rep (Right y) = RightExp (rep y)

  rep' = id
  unrep' = id

instance (GPURep a, GPURep b) => GPURep (a, b) where
  -- type GPURepTy (a, b) =  (GPURepTy a, GPURepTy b)
  type GPURepTy (a, b) =  (a, b)

  construct (x, y) = PairExp (rep x) (rep y)

  rep (x, y) = PairExp (rep x) (rep y) --uncurry PairExp
  rep' = id
  unrep' = id

instance (GPURep a, GPURep b, GPURep c) => GPURep (a, b, c) where
instance (GPURep a, GPURep b, GPURep c, GPURep d) => GPURep (a, b, c, d) where

-- XXX: Should this instance exist?
instance (GPURep a, GPURep b) => GPURep (Iter a b) where

-- XXX: Should this instance exist?
instance (GPURep a, GPURep b) => GPURep (a -> b) where
  type GPURepTy (a -> b) = GPURepTy a -> GPURepTy b

  construct = error "construct for (a->b) instance called"

  rep = Construct
  rep' f x = rep' (f (unrep' x))
  unrep' = error "unrep' for (a->b) instance called"

-- Generics instances
instance (Typeable (M1 i c f p), GPURep (f p), GPURep (GPURepTy (f p))) => GPURep (M1 i c f p) where
  type GPURepTy (M1 i c f p) = GPURepTy (f p)

  construct = construct . unM1

  rep' (M1 x) = rep' x
  unrep' = M1 . unrep'

instance (Typeable ((p :+: q) x), GPURep (p x), GPURep (q x), GPURep (GPURepTy (p x)), GPURep (GPURepTy (q x))) => GPURep ((p :+: q) x) where
  type GPURepTy ((p :+: q) x) =  Either (GPURepTy (p x)) (GPURepTy (q x))

  construct (L1 x) = LeftExp (construct x)
  construct (R1 x) = RightExp (construct x)

  rep' (L1 x) = Left (rep' x)
  rep' (R1 y) = Right (rep' y)

  unrep' (Left x) = L1 (unrep' x)
  unrep' (Right y) = R1 (unrep' y)

instance (Typeable ((p :*: q) x), GPURep (p x), GPURep (q x), GPURep (GPURepTy (p x)), GPURep (GPURepTy (q x))) => GPURep ((p :*: q) x) where
  type GPURepTy ((p :*: q) x) =  (GPURepTy (p x), GPURepTy (q x))

  construct (x :*: y) = PairExp (construct x) (construct y)

  rep' (x :*: y) = (rep' x, rep' y)
  unrep' (x, y) = (unrep' x :*: unrep' y)

instance (Typeable (K1 i c p), GPURep c) => GPURep (K1 i c p) where
  type GPURepTy (K1 i c p) = c --GPURepTy c

  -- construct = construct . unK1

  construct = rep . unK1

  -- rep = _

  rep' (K1 x) = x
  unrep' = K1

instance Typeable (U1 p) => GPURep (U1 p) where
  type GPURepTy (U1 p) = ()

  construct _ = UnitExp

  rep' U1 = ()
  unrep' () = U1

instance GPURep () where
  type GPURepTy () = ()

  rep () = UnitExp

  rep' = id
  unrep' = id

class GenericRep repr where
    type GenericRepTy repr

    genericRep :: repr -> GPUExp (GenericRepTy repr)

    genericRep' :: repr -> GenericRepTy repr
    genericUnrep' :: GenericRepTy repr -> repr

instance forall p q. (GPURep (p Void), GPURep (q Void), GenericRep (p Void), GenericRep (q Void), GPURepTy (p Void) ~ GenericRepTy (p Void), GPURepTy (q Void) ~ GenericRepTy (q Void)) =>
  GenericRep ((p :+: q) Void) where

    type GenericRepTy ((p :+: q) Void) = Either (GPURepTy (p Void)) (GPURepTy (q Void))

    genericRep (L1 x) = LeftExp (genericRep x)
    genericRep (R1 x) = RightExp (genericRep x)

    genericRep' = bimap rep' rep' . toCanonical
    genericUnrep' = fromCanonical . bimap unrep' unrep'

instance (GPURep (p Void), GPURep (q Void), GenericRep (p Void), GenericRep (q Void), GPURepTy (p Void) ~ GenericRepTy (p Void), GPURepTy (q Void) ~ GenericRepTy (q Void)) =>
  GenericRep ((p :*: q) Void) where

    type GenericRepTy ((p :*: q) Void) = (GPURepTy (p Void), GPURepTy (q Void))

    genericRep (x :*: y) = PairExp (genericRep x) (genericRep y)

    genericRep' = bimap rep' rep' . toCanonical
    genericUnrep' = fromCanonical . bimap unrep' unrep'

instance (GenericRep (f Void)) =>
  GenericRep (M1 i c f Void) where
    type GenericRepTy (M1 i c f Void) = GenericRepTy (f Void)

    genericRep = genericRep . unM1

    genericRep' = genericRep' . unM1
    genericUnrep' = M1 . genericUnrep'

instance GenericRep (U1 x) where
    type GenericRepTy (U1 x) = ()

    genericRep _ = UnitExp

    genericRep' _ = ()
    genericUnrep' () = U1

instance GenericRep (K1 i c f) where
    type GenericRepTy (K1 i c f) = c

    genericRep = error "genericRep called for K1 instance"

    genericRep' = unK1
    genericUnrep' = K1

the :: a -> a
the = id

the_repr :: GPUExp a -> GPUExp a
the_repr = id

-- coerceWith :: Dict (Coercible a b) -> a -> b
-- coerceWith Dict x = coerce x

-- Should this just produce an error?
sumMatchAbs :: forall s t. (GPURepTy (GPURepTy s) ~ GPURepTy s, GPURep s) => Env -> GPUExp (SumMatch (GPURepTy s) t) -> s -> t
-- sumMatchAbs env (CastExp d e) = sumMatchAbs env (coerceWith d e)
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
-- prodMatchAbs env (CastExp e) = prodMatchAbs env (coerce e)
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
    Nothing -> error $ "No binding for name " ++ show v
gpuAbsEnv env (CaseExp x f) = sumMatchAbs env f (gpuAbsEnv env x)
gpuAbsEnv env FalseExp = False
gpuAbsEnv env TrueExp  = True
gpuAbsEnv env UnitExp  = ()
gpuAbsEnv env (Repped x) = unrep' x
-- gpuAbs (Lam f) = gpuAbs . f . rep
-- gpuAbs (Apply f x) = gpuAbs f (gpuAbs x)
gpuAbsEnv env (Lit x) = x
gpuAbsEnv env (Ord x) = ord (gpuAbsEnv env x)
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

gpuAbsEnv env (ConstructRep x) = unrep' $ gpuAbsEnv env x

gpuAbsEnv env (Lam (name :: Name a) (body :: GPUExp b)) = \(arg :: a) ->

    let go0 :: forall x. GPUExp x -> GPUExp x
        go0 expr@(Var name2 :: GPUExp t') =
          case namesEq name name2 of
            Just Refl -> rep arg
            _ ->
              case envLookup env name2 of
                Just v  -> v
                Nothing -> expr
        go0 expr = expr

        go = transformE go0
    in

    gpuAbsEnv (extendEnv env (name :=> rep arg)) $ go body

gpuAbsEnv env (App f x) = gpuAbsEnv env f (gpuAbsEnv env x)
gpuAbsEnv env (CharLit c) = c
gpuAbsEnv env (CastExp x) = gpuAbsEnv env (coerce x)

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


