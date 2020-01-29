-- NOTE: Found some ideas around page 85 of this PhD thesis for getting
-- this stuff to type check ("Theoretical Foundations for 'Totally Functional Programming'", Colin John Morris Kemp, 2007): https://ia600202.us.archive.org/11/items/TheoreticalFoundationsForPracticaltotallyFunctionalProgramming/33429551_PHD_totalthesis.pdf
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}

{-# LANGUAGE AllowAmbiguousTypes #-}


{-# OPTIONS_GHC -ddump-splices #-}

module Case
  where

import           GHC.Generics

import           Data.Proxy
import           Data.Void

import           Data.Coerce

import           Language.Haskell.TH

import           Data.Generics.Uniplate.Operations
-- import           Data.Generics.Uniplate.Data
import           Data.Generics.Uniplate.Direct ((|-), (|*), plate)
import qualified Data.Generics.Uniplate.Direct as Direct
import qualified Data.Generics.Uniplate.DataOnly as Data

import           Data.Data

import           Data.List

import           Control.Monad.Identity
import           Control.Monad.Writer
import           Control.Monad.State
import           Data.Monoid

import           Data.Ord

import           Data.Functor.Const

import           Data.Bifunctor

import           GHC.TypeLits hiding (Nat)

import           Data.Singletons
import           Data.Singletons.TH

import           Language.Haskell.TH.Syntax (OccName, NameFlavour)

import           GHC.TypeLits
import           Data.Type.Bool

import           DSMap
import           Type.Set

import Data.Char

-- $(genSingletons [''Char])

-- $(genSingletons [''OccName])

-- $(genSingletons [''Name])

nameToSymbol :: Name -> SomeSymbol
nameToSymbol = someSymbolVal . show

infixl 0 :@
pattern f :@ x = AppE f x

type Case = (Exp, [Match])

data Nu f where 
  Nu :: (a -> f a) -> a -> Nu f

data ListF a r where
  NilF :: ListF a r
  ConsF :: a -> r -> ListF a r
  deriving (Functor)

newtype Fix f = Fix {unFix :: f (Fix f)}

type List a = Nu (ListF a)

conv :: Functor f => Nu f -> Fix f
conv (Nu f x) =
  Fix (fmap (conv . (\y -> Nu (const y) x) . f) (f x))

fix2list :: Fix (ListF Int) -> [Int]
fix2list (Fix NilF) = []
fix2list (Fix (ConsF x xs)) = x : fix2list xs

  -- conv (Nu _ (f x))

  -- Fix $ _ $ f x

-- listConv :: List a -> Fix (ListF a)
-- listConv (Nu f x) =
--   Fix $ case f x of
--           NilF -> NilF
--           ConsF y ys -> ConsF y $ listConv $ Nu f ys

-- listConv2 :: List a -> [a]
-- listConv2 (Nu f x) =
--   case f x of
--     NilF -> []
--     ConsF y ys -> y : listConv2 (Nu f ys)

testList :: List Int
testList =
  Nu (\x -> ConsF 1 x) NilF
  -- Nu (\x -> (ConsF 1 x)) (ConsF 2 (Nu (\y -> ConsF 3 y) NilF))

-- Idea: Represent a pattern match of a particular type as
--    KnownSymbol name => Proxy name -> MatchType name
-- with 'MatchType' being a type family that gives the type of the match
-- associated to matching on the constructor named 'name'. Maybe these
-- could be stored in a heterogenous list.

-- | Idea: Deep embedding for a pattern match (possibly using a non-regular
-- type?). Convert types to a "canonical form" to use this (like 'Either's
-- and '(,)'s)


-- Should this give back a `Maybe *`, representing the constructor product
-- type (if it exists)?
type family HasConstr0 t (c :: Symbol) where
  HasConstr0 (M1 x (MetaCons c y z) r p) c' =
    c == c' || HasConstr0 (r p) c'
  HasConstr0 ((x :+: y) p) c' = HasConstr0 (x p) c' || HasConstr0 (y p) c'
  HasConstr0 (U1 p) c' = False
  HasConstr0 ((x :*: y) p) c' = False
  HasConstr0 (K1 x y z) c' = False -- TODO: Is this correct?

type HasConstr t c = HasConstr0 t c ~ True

-- data Symbols t symbol where
--   ThisName :: Sing Symbol -> Symbols t symbol


-- -- ProdMatch (FindConstr t s) r
-- data SumMatch2 t r where
--   SumMatch2 :: (forall s. (KnownSymbol s, HasConstr t s) => Sing s -> GPUExp r) -> SumMatch2 t r

-- SumMatch :: Proxy t -> (Symbols t symbol -> ProdMatch symbol r -> GPUExp r) -> SumMatch t r

data Skeleton t name x where
  SkLeft :: Sing name -> Skeleton a name0 x -> Skeleton (Either a b) name x
  SkRight :: Sing name -> Skeleton b name0 x -> Skeleton (Either a b) name x
  SkLeaf :: BaseTy x => Skeleton x name x

-- test1 :: Skeleton (Either Int Char) Int
-- test1 = SkLeft SkLeaf

-- test2 :: Skeleton (Either Int Char) Char
-- test2 = SkRight SkLeaf

-- test3 :: SumMatch2 (Either Int (Either Bool Float)) Float
-- test3 = SumMatch2
--   (\sk ->
--     case sk of
--       SkLeft _name SkLeaf -> OneProdMatch (\int -> FromIntegral int)
--       SkRight _name (SkLeft _name' SkLeaf) -> OneProdMatch (\bool -> FromIntegral (FromEnum bool))
--       SkRight _name (SkRight _name' SkLeaf) -> OneProdMatch (\float -> Sub float (Lit 1.0))
--   )

type family BaseTy0 t where
  BaseTy0 (Either a b) = False
  BaseTy0 (a, b) = False
  BaseTy0 t = True

type BaseTy t = BaseTy0 t ~ True

toSkeleton :: (GPURep t, Generic t) =>
  (t -> r) -> (Skeleton t name x -> r)
toSkeleton = undefined

-- nameToSkeleton :: (GPURep t, Generic t, HasConstr t name)
--   => Proxy t -> (Sing name -> f name r) -> (Skeleton (GPURepTy t) r -> f name r)
-- nameToSkeleton Proxy f = go
--   where
--     go SkLeaf = _

-- data SumMatch2 s t where
--   SumMatch2 :: (Skeleton t name x -> ProdMatch x r) -> SumMatch2 t r

-- TODO: Should we have a phantom type argument with the original type to preserve (possibly) more type safety?
data ProdMatch origType s t where
  ProdMatch ::
       (GPUExp (ConstrType origType b) -> r) -> ProdMatch origType r b


-- exampleSM :: SumMatch (Either Int (Either Bool Float)) Float
-- exampleSM =
--   SumMatch (OneProdMatch (\int -> FromIntegral int))
--            (SumMatch (OneProdMatch (\bool -> FromIntegral (FromEnum bool)))
--                      (OneSumMatch (OneProdMatch (\float -> Sub float (Lit 1.0)))))

type family GetFirst x y where
  GetFirst (Just x) y = Just x
  GetFirst x (Just y) = Just y

type family RemoveJust x where
  RemoveJust (Just x) = x

type family ConstrType0 t (name :: Symbol) where
  ConstrType0 (M1 x ('MetaCons name y z) r p) name = Just (GPURepTy (r p))
  ConstrType0 (M1 x m r p) name2 =
    ConstrType0 (r p) name2

  ConstrType0 ((x :+: y) p) name =
    GetFirst (ConstrType0 (x p) name)
             (ConstrType0 (y p) name)

  ConstrType0 x name = Nothing

type ConstrType t name = RemoveJust (ConstrType0 t name)

type family ConstrNames t where
  ConstrNames (M1 x ('MetaCons name y z) r p) = Insert name (ConstrNames (r p))
  ConstrNames (M1 x m r p) = ConstrNames (r p)
  ConstrNames ((x :+: y) p) = Merge (ConstrNames (x p)) (ConstrNames (y p))


data SumMatch origType r where
  SumMatch ::
    (GPURep a, GPURep b, GPURepTy b ~ b)
      => SetSing (ProdMatch origType r) (ConstrNames origType) -> SumMatch origType r


  -- SumMatch ::
  --   -- (GPURep a, GPURep b, GPURepTy b ~ b)
  --   (GPURep a, GPURep t)
  --       => Sing name -> SetSing (ProdMatch r) ns -> SumMatch origType t r -> SumMatch origType t r

  -- EmptyMatch :: SumMatch origType () r -- TODO: This should probably be Void instead of ()

  -- OneSumMatch ::
  --   (GPURep a, GPURep t)
  --       => Sing name -> ProdMatch (ConstrType t name) r -> SumMatch origType t r

  -- OneSumMatch :: (GPURep a, GPURep b, GPURepTy a ~ a) => ProdMatch a b -> SumMatch origType a b


-- deriving instance (Data t, Data r, GPURepTy r ~ r) => Data (SumMatch t r)

-- deriving instance (Data s, Data t) => Data (ProdMatch s t)

-- Done (case ... of A -> x; B -> y)  ==>  (case ... of A -> Done x; B -> Done y)
data Iter a b
  = Step b
  | Done a
  deriving (Functor, Generic)

data GPUExp t where
  CaseExp :: (GPURep a) => GPUExp a -> SumMatch a t -> GPUExp t

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

  Equal :: Eq a => GPUExp a -> GPUExp a -> GPUExp Bool
  Lte :: Ord a => GPUExp a -> GPUExp a -> GPUExp Bool

  Not :: GPUExp Bool -> GPUExp Bool

  LeftExp :: GPUExp a -> GPUExp (Either a b)
  RightExp :: GPUExp b -> GPUExp (Either a b)

  PairExp :: GPUExp a -> GPUExp b -> GPUExp (a, b)

  StepExp :: GPUExp b -> GPUExp (Iter a b)
  DoneExp :: GPUExp a -> GPUExp (Iter a b)

  IfThenElse :: GPUExp Bool -> GPUExp a -> GPUExp a -> GPUExp a

  TailRec :: (GPURep a, GPURep b) => (GPUExp b -> GPUExp (Iter a b)) -> GPUExp (b -> a)

  Construct :: (a -> b) -> GPUExp (a -> b) -- This is like a specialized 'pure'
  ConstructAp :: (GPURep a) => GPUExp (a -> b) -> GPUExp a -> GPUExp b -- This is like '(<*>)'


-- deriving instance Generic (GPUExp a)

-- deriving instance Data a => Data (GPUExp a)

-- | For lambda demonstration purposes
twice :: (a -> a) -> a -> a
twice f x = f (f x)

lam :: GPURep a => Name -> (GPUExp a -> GPUExp b) -> Q (GPUExp (a -> b))
lam name0 f = do
  name <- newName (show name0)
  return $ Lam name (f (Var Proxy name))

-- TODO: I believe all names should be unique, but this should be verified
apply :: GPUExp (a -> b) -> GPUExp a -> GPUExp b
apply (Lam arg body) x = undefined --transform go body
  where
    go (Var Proxy name)
      | arg == name = x

class GPURep t where
    -- Should we wrap these types in a 'Const t' in order to preserve more
    -- type safety?
  type GPURepTy t
  type GPURepTy t = GPURepTy (Rep t Void)

  rep :: t -> GPUExp t
  rep = Repped . rep'

  rep' :: t -> GPURepTy t

  default rep' :: (Generic t, GenericRep (Rep t Void), GPURepTy t ~ GenericRepTy (Rep t Void))
    => t -> GPURepTy t
  rep' = genericRep' . (from :: t -> Rep t Void)


  unrep' :: GPURepTy t -> t

  default unrep' :: (Generic t, GenericRep (Rep t Void), GPURepTy t ~ GenericRepTy (Rep t Void))
    => GPURepTy t -> t
  unrep' = (to :: Rep t Void -> t) . genericUnrep'

instance GPURep Int where
  type GPURepTy Int = Int
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

instance (GPURep a, GPURep b) => GPURep (Either a b) where
  type GPURepTy (Either a b) = Either a b
  rep (Left x) = LeftExp (rep x)
  rep (Right y) = RightExp (rep y)
  rep' = id
  unrep' = id

instance (GPURep a, GPURep b) => GPURep (a, b) where
  type GPURepTy (a, b) = (a, b)
  rep (x, y) = PairExp (rep x) (rep y)
  rep' = id
  unrep' = id

-- XXX: Should this instance exist?
-- instance (GPURep a, GPURep b) => GPURep (Iter a b) where


-- Generics instances
instance GPURep (f p) => GPURep (M1 D c f p) where
  type GPURepTy (M1 D c f p) = GPURepTy (f p)

  rep = Repped . rep'
  rep' (M1 x) = rep' x
  unrep' = M1 . unrep'

instance (IsSetSing (SetSingMerge (GPURepTy (p x)) (GPURepTy (q x))), IsSetSing (GPURepTy (p x)), IsSetSing (GPURepTy (q x)), GPURep (p x), GPURep (q x)) => GPURep (M1 C (MetaCons name y z) (p :+: q) x) where
  type GPURepTy (M1 C (MetaCons name y z) (p :+: q) x) = SetSingMerge (GPURepTy (p x)) (GPURepTy (q x))

  rep = Repped . rep'

  rep' (M1 (L1 x)) = SetSingInsert _ (rep' x) _
  rep' (M1 (R1 y)) = undefined --Right (rep' y)

  unrep' (Left x) = M1 $ L1 (unrep' x)
  unrep' (Right y) = M1 $ R1 (unrep' y)

instance (GPURep (p x), GPURep (q x)) => GPURep ((p :*: q) x) where
  type GPURepTy ((p :*: q) x) = (GPURepTy (p x), GPURepTy (q x))

  rep' (x :*: y) = (rep' x, rep' y)
  unrep' (x, y) = (unrep' x :*: unrep' y)

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

type family LiftedFn t where
  LiftedFn (a -> b) = GPUExp a -> LiftedFn b
  LiftedFn b = GPUExp b

construct :: forall a b. (Construct (a -> b))
  => (a -> b) -> LiftedFn (a -> b)
construct = construct' . Construct

class Construct t where
    construct' :: GPUExp t -> LiftedFn t

instance (GPURep a, Construct b) => Construct (a -> b) where
    construct' :: GPUExp (a -> b) -> GPUExp a -> LiftedFn b
    construct' c = construct' . ConstructAp c

instance {-# INCOHERENT #-} (LiftedFn b ~ GPUExp b) => Construct b where
    construct' :: GPUExp b -> GPUExp b
    construct' = id

-- -- Should this just produce an error?
-- sumMatchAbs :: forall origType s t. GPURep s => Proxy origType -> SumMatch origType (GPURepTy s) t -> s -> t
-- sumMatchAbs Proxy (SumMatch name p q) =
--   \x0 ->
--     let x = rep' x0
--     in
--     case x of
--       Left  a -> prodMatchAbs p a
--       Right b -> sumMatchAbs (Proxy @origType) q b
-- sumMatchAbs Proxy EmptyMatch = \_ -> error "Non-exhaustive match"
-- sumMatchAbs Proxy (OneSumMatch name f) = prodMatchAbs f . unrep' . rep' -- TODO: Is this reasonable?

-- prodMatchAbs :: GPURep s => ProdMatch s t -> s -> t
-- prodMatchAbs (ProdMatch f) =
--   \pair ->
--     case pair of
--       (x, y) -> prodMatchAbs (f (rep x)) y

-- prodMatchAbs (OneProdMatch f) = \x -> gpuAbs (f (rep x))
-- prodMatchAbs (NullaryMatch x) = \_ -> gpuAbs x

gpuAbs :: GPUExp t -> t
gpuAbs (CaseExp (x :: GPUExp a) f) = sumMatchAbs (Proxy @a) f (gpuAbs x)
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
gpuAbs (Equal x y) = gpuAbs x == gpuAbs y
gpuAbs (Lte x y) = gpuAbs x <= gpuAbs y
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


transformPrims :: [Name] -> Exp -> Exp
transformPrims skipFns = Data.transform go
  where
    builtin :: Name -> Maybe Exp
    builtin x
      | x == 'not = Just $ ConE 'Not
      | x == 'fromEnum = Just $ ConE 'FromEnum
      | x == 'fromIntegral = Just $ ConE 'FromIntegral
      | otherwise = Nothing

    go expr@(LitE _) = ConE 'Lit :@ expr
    go expr@(ConE c)
      | c == 'True = ConE 'TrueExp
      | c == 'False = ConE 'FalseExp

    go expr@(ConE _) = VarE 'construct :@ expr
    go expr@(TupE [x, y]) = VarE 'construct :@ ConE '(,) :@ x :@ y
    go expr@(TupE [x, y, z]) = VarE 'construct :@ ConE '(,,) :@ x :@ y :@ z
    go expr@(TupE [x, y, z, w]) = VarE 'construct :@ ConE '(,,,) :@ x :@ y :@ z :@ w
    go expr@(VarE fn :@ ConE _)
      | fn == 'construct = expr

    go (InfixE (Just x0) (VarE op) (Just y0))
      | op == '(+) = ConE 'Add :@ x :@ y
      | op == '(*) = ConE 'Mul :@ x :@ y
      | op == '(-) = ConE 'Sub :@ x :@ y
      | op == '(==) = ConE 'Equal :@ x :@ y
      | op == '(<=) = ConE 'Lte :@ x :@ y
      where
        x = go x0
        y = go y0

    go (VarE x)
      | Just r <- builtin x = r

    go expr@(VarE f :@ x)
      | Just r <- builtin f = r :@ x

    go expr@(VarE f :@ x) =
        if f `elem` skipFns
        then expr
        else VarE 'construct :@ VarE f :@ x

    go (CondE cond t f) = ConE 'IfThenElse :@ cond :@ t :@ f
    go expr = expr

-- Looks for a 'ConP' get the type info
-- TODO: Make this work in more circumstances
getMatchType :: Case -> Q Type
getMatchType (_, matches) = do
  Just r <- fmap (getFirst . mconcat) $ mapM go matches
  return r
  where
    go (Match (ConP name _) _ _) = do
      DataConI _ ty _ <- reify name
      return (First (Just ty))
    go _ = return (First Nothing)

-- e  ==>  (\x -> e)     {where x is a free variable in e}
abstractOver :: Name -> Exp -> Exp
abstractOver name = LamE [VarP name]

transformProdMatch :: Match -> Exp
transformProdMatch (Match match (NormalB body) _) =
  go vars0
  where
    -- go [] = ConE 'NullaryMatch :@ body --(VarE 'rep :@ body)
    -- go [var] = ConE 'OneProdMatch :@ abstractOver var body --(VarE 'rep :@ body)
    go (var:vars) = ConE 'ProdMatch :@ abstractOver var (go vars)

    vars0 =
      case match of
        ConP _ args -> map getVar args
        TupP args -> map getVar args

    getVar (VarP var) = var

-- Does not necessarily preserve type argument order (sorts matches by
-- constructor name)
-- NOTE: Requires at least one match to find the type
-- NOTE: This must be used in a splice, not in something like runQ
-- evaluated in the IO monad (this is because 'transformCase' uses 'reify')
transformCase0 :: Exp -> Q Exp
transformCase0 (CaseE scrutinee matches0@(firstMatch:_)) = do
    reifiedFirstMatchMaybe <- sequence $ fmap reify firstMatchConMaybe

    conIxMaybe <- case reifiedFirstMatchMaybe of
      Just (DataConI _ _ parentName) -> do
        parent <- reify parentName
        case parent of
          TyConI (DataD _ _ _ _ constrs _) ->
            return $ Just $ \conName -> conName `elemIndex` map getConName constrs
      Nothing -> return Nothing

    let sortedMatches =
          case conIxMaybe of
            Nothing -> matches0
            Just conIx -> sortBy (comparing (conIx . getMatchPatName)) matches0

    return (ConE 'CaseExp :@ scrutinee
              :@ sumMatches sortedMatches)
  where
    firstMatchConMaybe =
      case firstMatch of
        Match (ConP name _) _ _ -> Just name
        Match (TupP _) _ _ -> Nothing
        _ -> Nothing

    -- sumMatches [] = ConE 'EmptyMatch
    -- sumMatches [x] = ConE 'OneSumMatch :@ transformProdMatch x
    sumMatches (x:xs) =
      ConE 'SumMatch :@ transformProdMatch x :@ sumMatches xs
transformCase0 exp = return exp

-- | `skipFns` is for internal `transformPrims` call
transformCase' :: [Name] -> Exp -> Q Exp
transformCase' skipFns = Data.transformM transformCase0 . transformPrims skipFns

transformCase :: Exp -> Q Exp
transformCase = transformCase' []

getConName :: Con -> Name
getConName (NormalC name _) = name
getConName (RecC name _) = name
getConName (InfixC _ name _) = name
getConName (ForallC _ _ con) = getConName con

getMatchPatName :: Match -> Name
getMatchPatName (Match (ConP name _) _ _) = name

getMatchPat :: Match -> Pat
getMatchPat (Match pat _ _) = pat

patHasName :: Name -> Pat -> Bool
patHasName name1 (ConP name2 _) = name1 == name2
patHasName _ _ = False

toEither :: (p :+: q) x -> Either (p x) (q x)
toEither (L1 x) = Left x
toEither (R1 y) = Right y

fromEither :: Either (p x) (q x) -> (p :+: q) x
fromEither (Left x) = L1 x
fromEither (Right y) = R1 y

hasRec :: Name -> Exp -> Bool
hasRec recName = getAny . execWriter . Data.transformM hasRec0
  where
    -- | See if the argument has a recursive call
    hasRec0 :: Exp -> Writer Any Exp
    hasRec0 expr@(AppE (VarE fn) _) | fn == recName = do
      tell (Any True)
      pure expr
    hasRec0 expr = do
      pure expr

transformTailRec :: Name -> [Name] -> Exp -> Exp
transformTailRec recName args =
    (VarE 'gpuAbs :@) . (ConE 'TailRec :@) . stepIntro . LamE (map VarP args) . (Data.transform go)
  where
    stepIntro x = LamE [VarP recName] x :@ ConE 'StepExp


    -- Look for expressions that do not contain a recursive call in
    -- a subexpression, and wrap them in a 'Done'
    go :: Exp -> Exp
    go exp@(CaseE scrutinee branches) =
      CaseE scrutinee
        $ map (\branch@(Match pat (NormalB matchExp) decs) ->
                  if hasRec recName matchExp
                  then branch
                  else Match pat (NormalB (ConE 'DoneExp :@ matchExp)) decs)
              branches
    go exp@(ConE fn :@ cond :@ true :@ false)
      | fn == 'IfThenElse =
        ConE 'IfThenElse :@ cond
              :@ (if hasRec recName true
               then true
               else ConE 'DoneExp :@ true)
              :@ (if hasRec recName false
               then false
               else ConE 'DoneExp :@ false)
    go exp = exp

transformDecTailRec0 :: Dec -> Q Dec
transformDecTailRec0 sig@SigD{} = return sig
transformDecTailRec0 (FunD fnName [Clause [VarP arg] (NormalB body) []]) = do
  body' <- transformCase' [fnName] body
  if not (hasRec fnName body')
    then return (FunD fnName [Clause [VarP arg] (NormalB (VarE 'gpuAbs :@ (LamE [VarP arg] body' :@ (VarE 'rep :@ VarE arg)))) []])
    else
      return $ FunD fnName [Clause [VarP arg] (NormalB (transformTailRec fnName [arg] body' :@ VarE arg)) []]
transformDecTailRec0 expr = error ("transformDecTailRec0: " ++ show expr)

transformExpr :: Exp -> Q Exp
transformExpr = fmap (VarE 'gpuAbs :@) . transformCase

transformDecTailRec :: Q [Dec] -> Q [Dec]
transformDecTailRec qdecs = do
  decs <- qdecs
  mapM transformDecTailRec0 decs

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

