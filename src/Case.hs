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
  let Done r = gpuAbs (f (rep x))
  in r

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

-- matchAbs = error "matchAbs"

-- TODO: Implement this idea for a deep embedding of pattern matching:
-- (case e of A () -> a; B () -> b)   ==>   matchAbs ((\f -> f (const a) (const b)) SumMatch) e
--                                    ==>   matchAbs (SumMatch (const a) (const b)) e
--                                    ==>   caseAbs (CaseExp e (SumMatch (const a) (const b)))



-- (case e of A () -> a; B () -> b)   ==>   (\f -> f (const a) (const b)) (\x y -> case e of A p -> x p; B q -> y q)
-- match :: t

countCases :: Q Exp -> Q Int
countCases = fmap (getSum . execWriter . transformBiM go)
  where
    go :: Exp -> Writer (Sum Int) Exp
    go e@(CaseE _ _) = do
      tell $ Sum 1
      return e
    go e = return e

-- | (case e of A -> a; B -> b)   ==>   (\f -> f a b) (\x y -> case e of A -> x; B -> y)
--
-- This is just for simple enumerations right now
factorOutCase :: Case -> Q Exp
factorOutCase (scrutinee, matches) =
  return undefined
  where
    lam1Q :: Q Exp
    lam1Q = do
      f <- newName "f"
      return (LamE [VarP f]
               (foldl1 AppE (VarE f:map matchBody matches)))

    lam2Q :: Q Exp
    lam2Q = do
      matchArgs <- mapM newName (map (('x':) . show) [1..length matches])
      return (LamE (map VarP matchArgs)
                (CaseE
                   scrutinee
                   (zipWith (\m name -> Match (matchPat m) (NormalB (VarE name)) [])
                            matches
                            matchArgs)))

    matchPat :: Match -> Pat
    matchPat (Match pat _ _) = pat

    matchBody :: Match -> Exp
    matchBody (Match _ (NormalB b) _) = b
    matchBody _ = error "factorOutCase.matchBody"


-- Get the first 'case' expression
getFirstCase :: Q Exp -> Q Case
getFirstCase exp0 = do
  Just r <- fmap (getFirst . execWriter . transformBiM go) exp0
  return r
  where
    go :: Exp -> Writer (First Case) Exp
    go e@(CaseE scrutinee matches) = do
      tell $ First (Just (scrutinee, matches))
      return e
    go e = return e

-- Get the list of matches from the first 'case' encountered
getCaseMatchesFirst :: Q Exp -> Q [Match]
getCaseMatchesFirst = fmap snd . getFirstCase

-- Represent 'case' alternatives as a list of functions (taking in the
-- variables from each pattern match) with the associated constructor name.
-- Assumes that the alternatives are in 'C v0 v1 ... vn' form, where the
-- v's are variables
gatherCaseAlts :: [Match] -> Q [(Name, Exp)]
gatherCaseAlts = mapM go
  where
    go (Match (ConP name pats) (NormalB body) []) =
      return (name, LamE (getPatVars pats) body)
    go _ = error "gatherCaseAlts: Currently no support 'where' clauses or for guards in 'case'"

    getPatVars [] = []
    getPatVars (VarP v:pats) = VarP v : getPatVars pats
    getPatVars _ = error "gatherCaseAlts: Each alternative of the case must be in 'C v0 v1 ... vn' form"

-- TODO: Write a 'caseExpand' TH function which turns each 'case'
-- expression into "simplified" case expressions where each alternative
-- only has one pattern match.

-- caseExpandOne :: Q Case -> Q Exp
-- caseExpandOne = undefined





newtype NatScott = NatScott (forall r. (() -> r) -> (NatScott -> r) -> r)
type BoolScott = forall r. BBBool r
newtype ExampleScott = ExampleScott (forall r. (BoolScott -> r) -> (NatScott -> r) -> r)

scott_exampleBool :: BoolScott -> ExampleScott
scott_exampleBool bool = ExampleScott $ \f _g -> f bool

scott_exampleNat :: NatScott -> ExampleScott
scott_exampleNat nat = ExampleScott $ \_f g -> g nat

scottElim_Bool :: BoolScott -> (() -> r) -> (() -> r) -> r
scottElim_Bool = match_bool

scottElim_Nat :: NatScott -> (() -> r) -> (NatScott -> r) -> r
scottElim_Nat (NatScott nat) = nat

scottElim_Example :: ExampleScott -> (BoolScott -> r) -> (NatScott -> r) -> r
scottElim_Example (ExampleScott ex) = ex

scott_false :: BoolScott
scott_false = bbfalse

scott_true :: BoolScott
scott_true = bbtrue

scott_Z :: NatScott
scott_Z = NatScott $ \f _g -> f ()

scott_S :: NatScott -> NatScott
scott_S nat = NatScott $ \_f g -> g nat

scottBoolToBool :: BoolScott -> Bool
scottBoolToBool = bbboolToBool

scottNatToNat :: NatScott -> Nat
scottNatToNat (NatScott nat) = nat (const Z) (S . scottNatToNat)

scottBool :: Bool -> BoolScott
scottBool False = scott_false
scottBool True  = scott_true

scottNat :: Nat -> NatScott
scottNat Z     = scott_Z
scottNat (S n) = scott_S (scottNat n)

-- TODO: When attempting to make a 'Generic' Scott encoder, see if the
-- lifting can be generalized to functions that take in or produce Scott
-- encoded types.
--
-- Also, these lifts could mark places where the transformation may
-- still need to be applied.
scottLift_Bool :: (Bool -> Bool) -> BoolScott -> BoolScott
scottLift_Bool f bool =
  case f (scottElim_Bool bool (const False) (const True)) of
    False -> scott_false
    True  -> scott_true

exampleFn_scott :: ExampleScott -> ExampleScott
exampleFn_scott ex0 =
  scottElim_Example ex0 boolPart natPart
  where
    boolPart :: BoolScott -> ExampleScott
    boolPart bool = scott_exampleBool $ scottLift_Bool not bool

    natPart :: NatScott -> ExampleScott
    natPart nat0 =
      scottElim_Nat nat0 (\()  -> scott_exampleNat scott_Z)
                         (\nat -> scott_exampleNat nat)


scottExampleToExample :: ExampleScott -> Example
scottExampleToExample (ExampleScott ex) =
  ex (\bool -> B $ scottBoolToBool bool) (\nat -> N $ scottNatToNat nat)

scottExample :: Example -> ExampleScott
scottExample (N n) = scott_exampleNat (scottNat n)
scottExample (B b) = scott_exampleBool (scottBool b)

overScottEx :: (ExampleScott -> ExampleScott) -> Example -> Example
overScottEx f ex = scottExampleToExample (f (scottExample ex))

retranslated_scott_exampleFn :: Example -> Example
retranslated_scott_exampleFn = overScottEx exampleFn_scott


data Nat = Z | S Nat deriving (Generic, Show, Data)

data Example = N Nat | B Bool deriving (Generic, Show, Data)


exampleFn :: Example -> Example
exampleFn (N Z)     = B False
exampleFn (N (S n)) = N n
exampleFn (B b)     = B (not b)

type End f = forall r. f r

newtype WrapEnd f = WrapEnd (End f)

type BBBool r = (() -> r) -> (() -> r) -> r
type BBNat r = (() -> r) -> (r -> r) -> r
-- type BBExample r = (BBNat r -> r) -> (BBBool r -> r) -> r
type BBExample r = (End BBNat -> r) -> (End BBBool -> r) -> r
-- type BBExampleEnd f = (End BBNat -> End f) -> (End BBBool -> End f) -> End f

bbnatZ :: BBNat r
bbnatZ f _g = f ()

bbnatS :: BBNat r -> BBNat r
bbnatS nat f g = nat (g . f) g

bbfalse :: BBBool r
bbfalse f _g = f ()

bbtrue :: BBBool r
bbtrue _f g = g ()

bbboolToBool :: (forall r. BBBool r) -> Bool
bbboolToBool bool = bool (const False) (const True)

bbnatToNat :: (forall r. BBNat r) -> Nat
bbnatToNat nat = nat (const Z) S

exampleNat :: (forall x. BBNat x) -> BBExample r
exampleNat nat f _g = f nat

exampleBool :: (forall x. BBBool x) -> BBExample r
exampleBool bool _f g = g bool

bbexampleToExample :: (forall x. BBExample x) -> Example
bbexampleToExample ex =
  ex (\nat -> N $ bbnatToNat nat) (\bool -> B $ bbboolToBool bool)

match_bool :: BBBool r -> (() -> r) -> (() -> r) -> r
match_bool bool f g = bool f g

-- match_nat :: BBNat x -> (() -> r) -> (x -> r) -> r
-- match_nat nat f g = nat f g

match_bbexample :: BBExample r -> (End BBNat -> r) -> (End BBBool -> r) -> r
match_bbexample ex f g = ex f g

-- See 'typeconvert' from [Kemp, 2007]
bbexampleConvert :: BBExample (End BBExample) -> End BBExample
bbexampleConvert ex = ex exampleNat exampleBool

-- -- exampleFn' :: BBExample (BBExample ()) -> BBExample (BBExample ())
-- exampleFn' :: End BBExample -> End BBExample
-- -- exampleFn' :: End BBExample -> _
-- exampleFn' ex f g = undefined
--   -- match_bbexample ex (\nat -> natPart nat) _
--   -- match_bbexample ex (\nat -> match_nat nat (\() -> undefined ) undefined) (\bool -> undefined)
--   where
--     -- natPart :: End BBNat -> BBExample (End BBExample) --(forall y. BBExample y)
--     natPart :: End BBNat -> (BBNat p -> r1) -> (BBBool p -> r1) -> r1
--     natPart nat =
--       match_nat nat (\() (x :: BBNat p -> r) (y :: BBBool p -> r) -> exampleBool bbfalse x y)
--                     (\n (x :: BBNat p -> r)(y :: BBBool p -> r)-> exampleNat n x y)


-- exampleFn' :: (forall x. BBExample x) -> _
-- exampleFn' ex f g =
--   -- ex (\nat p q -> f nat) undefined
--   ex (\nat p q -> f $ nat (\() -> exampleBool bbfalse p q :: BBExample (BBNat r)) (\n -> n)) undefined
--   -- ex natPart undefined
--   -- undefined --ex natPart boolPart

  -- where
  --   -- natPart :: (forall x. BBNat x) -> BBExample b
  --   -- natPart :: End BBNat -> BBExample b
  --   natPart nat f g = nat (\() -> exampleBool bbfalse f g) (\n -> n)
  --   boolPart bool = undefined

-- exampleFn' :: Example -> Example
-- exampleFn' = runIdentity . gfoldl go Identity
--   where
--     go :: Data d => Identity (d -> b) -> d -> Identity b
--     go (Identity f) x =
--       case cast (f x) :: Maybe Bool of
--         Nothing -> undefined

type family BBRep rep r :: * where
  BBRep (M1 i c f p) r = BBRep (f p) r
  BBRep ((f :+: g) x) r = (BBRep (f x) r -> r) -> (BBRep (g x) r -> r) -> r
  BBRep ((f :*: g) x) r = (BBRep (f x) r -> BBRep (g x) r -> r) -> r
  BBRep (U1 p) r = ()
  BBRep (K1 i c p) r = BBRep c r
  -- BBRep (K1 i c p) r = BBRep (Rep c ()) r
  BBRep t r = t

class BBEncode t r where
  bbencode :: Proxy (r,p) -> t -> BBRep (Rep t p) r

-- class BBEncode rep r where
--   bbencode :: Proxy r -> rep -> BBRep rep r

-- instance (BBEncode (f p) r) => BBEncode (M1 i c f p) r where
--   bbencode proxy = bbencode proxy . unM1

-- instance forall f g x r. (forall a. BBEncode (f a) r, forall b. BBEncode (g b) r) =>
--     BBEncode ((f :+: g) x) r where
--   bbencode :: Proxy r -> ((f :+: g) x) -> BBRep ((f :+: g) x) r
--   bbencode proxy (L1 x) = \p q -> p (bbencode proxy x)
--   bbencode proxy (R1 y) = \p q -> q (bbencode proxy y)
    

-- instance forall f g x r. (forall a. BBEncode (f a) r, forall b. BBEncode (g b) r) =>
--     BBEncode ((f :*: g) x) r where
--   bbencode :: Proxy r -> ((f :*: g) x) -> BBRep ((f :*: g) x) r
--   bbencode proxy (x :*: y) = \p -> p (bbencode proxy x) (bbencode proxy y)

-- instance BBEncode (U1 p) r where
--   bbencode _ U1 = ()

-- instance BBEncode c r => BBEncode (K1 i c p) r where
--   bbencode proxy (K1 x) = bbencode proxy x

-- -- instance {-# INCOHERENT #-}  => BBEncode t r where
-- --   bbencode _ x = x

-- instance {-# INCOHERENT #-} BBRep t r ~ t => BBEncode t r where
--   bbencode _ x = x

-- -- extractCases :: Exp -> Q (Maybe [


-- genId' :: Q Exp
-- genId' = [| \x -> x |]

-- iHateDelete :: Q [Dec] -> Q [Dec]
-- iHateDelete = fmap (transformBi f)
--     where
--         f :: Exp -> Exp
--         f (VarE x) | x == 'delete = VarE 'deleteBy `AppE` VarE '(==)
--         f x = x


-- -- demo :: Int
-- -- demo = bbencode (Proxy :: Proxy Int) (from (Left 'a' :: Either Char Bool)) (const 1) (const 2)

-- -- type family BBRep t r where
-- --   BBRep (M1 i c f p)  r = BBRep (f p) r
-- --   BBRep ((f :+: g) x) r = (BBRep (f x) r -> r) -> (BBRep (g x) r -> r) -> r
-- --   BBRep ((f :*: g) x) r = BBRep (f x) r -> BBRep (g x) r -> r
-- --   BBRep (Rec0 t x)    r = t
-- --   -- BBRep 

-- -- class rep ~ Rep t => BBEncode t x rep | t x -> rep where
-- --   bbencode :: Proxy r -> t -> BBRep (rep x) r

-- -- instance BBEncode (M1 i c f p) where
-- --   bbencode Proxy = bbencode Proxy . unM1

-- -- instance BBEncode (

-- -- -- | Boehm-Berarducci encoding
-- -- class Generic t => BBEncode t where
-- --   type BBRep t x :: Type

-- --   bbencode :: Proxy r -> t -> BBRep t r

-- -- -- | (Ignore metadata)
-- -- instance BBEncode (f p) => BBEncode (M1 i c f p) where
-- --   type BBRep (M1 i c f p) r = BBRep (f p) r

-- --   bbencode Proxy = bbencode Proxy . unM1

-- -- instance (forall p. BBEncode (f p), forall q. BBEncode (g q)) =>
-- --     BBEncode ((f :+: g) x) where

-- --   type BBRep ((f :+: g) x) r = f x -> g x -> r


-- -- -- class Generic t => Inductive t where
-- -- --   patterns :: t

-- -- -- match :: [(a, Destruct a -> b)] -> a -> b
-- -- -- match = undefined

