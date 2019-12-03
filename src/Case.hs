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

infixl 0 :@
pattern f :@ x = AppE f x

type Case = (Exp, [Match])


-- | Idea: Deep embedding for a pattern match (possibly using a non-regular
-- type?). Convert types to a "canonical form" to use this (like 'Either's
-- and '(,)'s)
data MatchExp s t where
  SumMatch  :: (GPURep a, GPURep b) => (GPUExp a -> GPUExp r) -> (GPUExp b -> GPUExp r) -> MatchExp (Either a b) r
  ProdMatch :: (GPURep a, GPURep b) => (GPUExp a -> GPUExp b -> GPUExp r) -> MatchExp (a, b) r

-- TODO: Figure out how these types should be related to each other or
-- combined with each other
data GPUExp t where
  CaseExp :: GPURep t => GPUExp t -> MatchExp (GPURepTy t) r -> GPUExp r

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

-- rep :: t -> GPUExp t
-- rep = error "rep"

class GPURep t where
  type GPURepTy t
  type GPURepTy t = t

  rep :: t -> GPUExp t

  rep' :: t -> GPURepTy t
  default rep' :: GPURepTy t ~ t => t -> GPURepTy t
  rep' = id

  unrep' :: GPURepTy t -> t
  default unrep' :: GPURepTy t ~ t => GPURepTy t -> t
  unrep' = id

instance GPURep Int where rep = Lit

instance GPURep Float where rep = Lit
instance GPURep Double where rep = Lit

instance GPURep Bool where
  rep False = FalseExp
  rep True  = TrueExp

instance (GPURep a, GPURep b) => GPURep (Either a b) where
  rep (Left x) = LeftExp (rep x)
  rep (Right y) = RightExp (rep y)

instance (GPURep a, GPURep b) => GPURep (a, b) where
  rep (x, y) = PairExp (rep x) (rep y)

-- Generics instances
instance GPURep (f Void) => GPURep (M1 i c f Void) where
  type GPURepTy (M1 i c f Void) = GPURepTy (f Void)

  rep = Repped . rep'
  rep' (M1 x) = rep' x
  unrep' = M1 . unrep'

instance (GPURep (p Void), GPURep (q Void)) => GPURep ((p :+: q) Void) where
  type GPURepTy ((p :+: q) Void) = Either (GPURepTy (p Void)) (GPURepTy (q Void))

  rep = Repped . rep'

  rep' (L1 x) = Left (rep' x)
  rep' (R1 y) = Right (rep' y)

  unrep' (Left x) = L1 (unrep' x)
  unrep' (Right y) = R1 (unrep' y)

instance GPURep c => GPURep (K1 i c p) where
  type GPURepTy (K1 i c p) = GPURepTy c

  rep = Repped . rep'

  rep' (K1 x) = rep' x
  unrep' = K1 . unrep'

-- Should this just produce an error?
matchAbs :: GPURep s => MatchExp (GPURepTy s) t -> s -> t
matchAbs (SumMatch p q) =
  \x0 ->
    let x = rep' x0
    in
    case x of
      Left  a -> gpuAbs (p (rep a))
      Right b -> gpuAbs (q (rep b))
matchAbs (ProdMatch f) = \p0 ->
  let p = rep' p0
  in
  case p of
    (x, y) -> gpuAbs $ f (rep x) (rep y)

gpuAbs :: GPUExp t -> t
gpuAbs (CaseExp x f) = matchAbs f (gpuAbs x)
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

-- Assumes "simple match" form
transformEitherMatch :: Exp -> Q Exp
transformEitherMatch (CaseE scrutinee matches) =
    return (VarE 'gpuAbs :@ (VarE 'CaseExp :@ (VarE 'rep :@ scrutinee)
              :@ (VarE 'SumMatch :@ leftFn :@ rightFn)))
  where
    leftFn = abstractOver leftVar (VarE 'rep :@ leftBody)
    rightFn = abstractOver rightVar (VarE 'rep :@ rightBody)

    Match (ConP _ [VarP leftVar]) _ _ = leftMatch
    Match (ConP _ [VarP rightVar]) _ _ = rightMatch

    Match _ (NormalB leftBody) _ = leftMatch
    Match _ (NormalB rightBody) _ = rightMatch

    leftMatch, rightMatch :: Match
    Just leftMatch = find (patHasName 'Left . getMatchPat) matches
    Just rightMatch = find (patHasName 'Right . getMatchPat) matches

-- Assumes "simple match" form
transformPairMatch :: Exp -> Q Exp
transformPairMatch (CaseE scrutinee [Match (TupP [VarP var1, VarP var2]) (NormalB body) _]) =
    return (VarE 'gpuAbs :@ (VarE 'CaseExp :@ (VarE 'rep :@ scrutinee)
                :@ (VarE 'ProdMatch :@ abstractOver var1 (abstractOver var2 (VarE 'rep :@ body)))))

-- Does not necessarily preserve type argument order (sorts matches by
-- constructor name)
transformSumMatch :: Exp -> Q Exp
transformSumMatch (CaseE scrutinee matches0) =
    return (VarE 'gpuAbs :@ (VarE 'CaseExp :@ (VarE 'rep :@ scrutinee)
              :@ sumMatches (map abstractSimpleMatch sortedMatches)))
  where
    -- TODO: This needs to sort to the order listed in the data declaration
    sortedMatches = sortBy (comparing getMatchPatName) matches0

    sumMatches [m] = m
    sumMatches [m1,m2] = VarE 'SumMatch :@ m1 :@ m2
    sumMatches (m1:m2:rest) = VarE 'SumMatch :@ m1 :@ (VarE 'SumMatch :@ m2 :@ (sumMatches rest))

abstractSimpleMatch :: Match -> Exp
abstractSimpleMatch (Match (ConP _ [VarP var]) (NormalB body) _) =
  abstractOver var (VarE 'rep :@ body)

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

