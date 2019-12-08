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
-- {-# LANGUAGE AllowAmbiguousTypes #-}
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

module Case
  where

import           GHC.Generics

import           Data.Proxy
import           Data.Void

import           Data.Coerce

import           Language.Haskell.TH

import           Data.Generics.Uniplate
import           Data.Generics.Uniplate.Data

import           Data.Data

import           Data.List

import           Control.Monad.Identity
import           Control.Monad.Writer
import           Data.Monoid

import           Data.Ord

import           Data.Functor.Const

import           Data.Bifunctor

import           GHC.TypeLits hiding (Nat)

infixl 0 :@
pattern f :@ x = AppE f x

type Case = (Exp, [Match])


-- Idea: Represent a pattern match of a particular type as
--    KnownSymbol name => Proxy name -> MatchType name
-- with 'MatchType' being a type family that gives the type of the match
-- associated to matching on the constructor named 'name'. Maybe these
-- could be stored in a heterogenous list.

-- | Idea: Deep embedding for a pattern match (possibly using a non-regular
-- type?). Convert types to a "canonical form" to use this (like 'Either's
-- and '(,)'s)

data ProdMatch s t where
  ProdMatch :: (GPURep a, GPURep b)
                  => (GPUExp a -> ProdMatch b r)
                      -> ProdMatch (a, b) r

  OneProdMatch :: (GPURep a) => (GPUExp a -> GPUExp r) -> ProdMatch a r
  NullaryMatch :: GPURep r => GPUExp r -> ProdMatch a r

data SumMatch s t where
  SumMatch ::
    (GPURep a, GPURep b, GPURepTy b ~ b)
        => ProdMatch a r -> SumMatch b r
            -> SumMatch (Either a b) r

  EmptyMatch :: SumMatch () r

  OneSumMatch :: (GPURep a, GPURep b, GPURepTy a ~ a) => ProdMatch a b -> SumMatch (GPURepTy a) b

-- Done (case ... of A -> x; B -> y)  ==>  case ... of A -> Done x; B -> y)
data Iter a b
  = Step b
  | Done a
  deriving (Functor)
  

data GPUExp t where
  CaseExp :: GPURep t => GPUExp t -> SumMatch (GPURepTy t) r -> GPUExp r

  FalseExp :: GPUExp Bool
  TrueExp :: GPUExp Bool

  Repped :: GPURep a => GPURepTy a -> GPUExp a

  Lit :: Num a => a -> GPUExp a
  Add :: Num a => GPUExp a -> GPUExp a -> GPUExp a
  Sub :: Num a => GPUExp a -> GPUExp a -> GPUExp a

  Equal :: Eq a => GPUExp a -> GPUExp a -> GPUExp Bool
  Lte :: Ord a => GPUExp a -> GPUExp a -> GPUExp Bool

  Not :: GPUExp Bool -> GPUExp Bool

  LeftExp :: GPUExp a -> GPUExp (Either a b)
  RightExp :: GPUExp b -> GPUExp (Either a b)

  PairExp :: GPUExp a -> GPUExp b -> GPUExp (a, b)

  StepExp :: GPURep b => GPUExp b -> GPUExp (Iter a b)
  DoneExp :: GPURep a => GPUExp a -> GPUExp (Iter a b)

  TailRec :: (GPURep a, GPURep b) => (GPUExp b -> GPUExp (Iter a b)) -> GPUExp (b -> a)

-- rep :: t -> GPUExp t
-- rep = error "rep"

class GPURep t where
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

-- Generics instances
instance GPURep (f p) => GPURep (M1 i c f p) where
  type GPURepTy (M1 i c f p) = GPURepTy (f p)

  rep = Repped . rep'
  rep' (M1 x) = rep' x
  unrep' = M1 . unrep'

instance (GPURep (p x), GPURep (q x)) => GPURep ((p :+: q) x) where
  type GPURepTy ((p :+: q) x) = Either (GPURepTy (p x)) (GPURepTy (q x))

  rep = Repped . rep'

  rep' (L1 x) = Left (rep' x)
  rep' (R1 y) = Right (rep' y)

  unrep' (Left x) = L1 (unrep' x)
  unrep' (Right y) = R1 (unrep' y)

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

-- Should this just produce an error?
sumMatchAbs :: GPURep s => SumMatch (GPURepTy s) t -> s -> t
sumMatchAbs (SumMatch p q) =
  \x0 ->
    let x = rep' x0
    in
    case x of
      Left  a -> prodMatchAbs p a
      Right b -> sumMatchAbs q b
sumMatchAbs EmptyMatch = \_ -> error "Non-exhaustive match"
sumMatchAbs (OneSumMatch f) = prodMatchAbs f . unrep' . rep' -- TODO: Is this reasonable?

prodMatchAbs :: GPURep s => ProdMatch s t -> s -> t
prodMatchAbs (ProdMatch f) =
  \pair ->
    case pair of
      (x, y) -> prodMatchAbs (f (rep x)) y

prodMatchAbs (OneProdMatch f) = \x -> gpuAbs (f (rep x))
prodMatchAbs (NullaryMatch x) = \_ -> gpuAbs x

gpuAbs :: GPUExp t -> t
gpuAbs (CaseExp x f) = sumMatchAbs f (gpuAbs x)
gpuAbs FalseExp = False
gpuAbs TrueExp  = True
gpuAbs (Repped x) = unrep' x
gpuAbs (Lit x)  = x
gpuAbs (Add x y) = gpuAbs x + gpuAbs y
gpuAbs (Sub x y) = gpuAbs x - gpuAbs y
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

-- e  ==>  (\x -> (\x -> e) (gpuAbs x))    {where x is a free variable in e)
abstractOver :: Name -> Exp -> Exp
abstractOver name exp = LamE [VarP name] (LamE [VarP name] exp :@ (VarE 'gpuAbs :@ VarE name))

transformProdMatch :: Match -> Exp
transformProdMatch (Match match (NormalB body) _) =
  go vars0
  where
    go [] = ConE 'NullaryMatch :@ (VarE 'rep :@ body)
    go [var] = ConE 'OneProdMatch :@ abstractOver var (VarE 'rep :@ body)
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
transformCase :: Exp -> Q Exp
transformCase (CaseE scrutinee matches0@(firstMatch:_)) = do
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

    return (VarE 'gpuAbs :@ (ConE 'CaseExp :@ (VarE 'rep :@ scrutinee)
              :@ sumMatches sortedMatches))
  where
    firstMatchConMaybe =
      case firstMatch of
        Match (ConP name _) _ _ -> Just name
        Match (TupP _) _ _ -> Nothing
        _ -> Nothing

    sumMatches [] = ConE 'EmptyMatch
    sumMatches [x] = ConE 'OneSumMatch :@ transformProdMatch x
    sumMatches (x:xs) =
      ConE 'SumMatch :@ transformProdMatch x :@ sumMatches xs

getConName :: Con -> Name
getConName (NormalC name _) = name
getConName (RecC name _) = name
getConName (InfixC _ name _) = name
getConName (ForallC _ _ con) = getConName con

-- TODO: Match constructors that don't have exactly one field
abstractSimpleMatch :: Match -> Exp
abstractSimpleMatch (Match (ConP _ [VarP var]) (NormalB body) _) =
  abstractOver var (VarE 'rep :@ body)
abstractSimpleMatch x = error ("abstractSimpleMatch: " ++ show x)

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

