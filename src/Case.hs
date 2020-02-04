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

import           Data.Tagged

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


-- deriving instance (Data t, Data r, GPURepTy r ~ r) => Data (SumMatch t r)

-- deriving instance (Data s, Data t) => Data (ProdMatch s t)

-- Done (case ... of A -> x; B -> y)  ==>  (case ... of A -> Done x; B -> Done y)
data Iter a b
  = Step b
  | Done a
  deriving (Functor, Generic)

data GPUExp t where
  CaseExp :: (GPURep t) => GPUExp t -> SumMatch (GPURepTy t) r -> GPUExp r

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

  Construct :: a -> GPUExp a
  ConstructAp :: (GPURep a) => GPUExp (a -> b) -> GPUExp a -> GPUExp b


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

type family TagWith t x where
  TagWith t (Tagged t' x) = Tagged t x
  TagWith t x             = Tagged t x

type family GetType x where
  GetType (Tagged t x) = t
  GetType t            = t

type family Untag x where
  Untag (Tagged t x) = x
  Untag x            = x

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

the :: GPUExp a -> GPUExp a
the = id

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
sumMatchAbs :: GPURep s => SumMatch (GPURepTy s) t -> s -> t
sumMatchAbs (SumMatch p q) =
  \x0 ->
    let Tagged x = rep' x0
    in
    case x of
      Left  a -> prodMatchAbs p a
      Right b -> sumMatchAbs q b
sumMatchAbs EmptyMatch = \_ -> error "Non-exhaustive match"
sumMatchAbs (OneSumMatch f) = prodMatchAbs f . unrep' . rep' -- TODO: Is this reasonable?

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
    go [] = ConE 'NullaryMatch :@ body --(VarE 'rep :@ body)
    go [var] = ConE 'OneProdMatch :@ abstractOver var body --(VarE 'rep :@ body)
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

    sumMatches [] = ConE 'EmptyMatch
    sumMatches [x] = ConE 'OneSumMatch :@ transformProdMatch x
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

