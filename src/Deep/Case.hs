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
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TupleSections #-}

module Deep.Case
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

import           Data.Complex

import           Data.Constraint (Constraint)

import           Deep.Expr

infixl 0 :@
pattern f :@ x = AppE f x

type Case = (Exp, [Match])





-- deriving instance (Data t, Data r, GPURepTy r ~ r) => Data (SumMatch t r)

-- deriving instance (Data s, Data t) => Data (ProdMatch s t)


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



transformPrims :: [Name] -> Exp -> Exp
transformPrims skipFns = Data.transform go
  where
    builtin :: Name -> Maybe Exp
    builtin x
      | x == 'not = Just $ ConE 'Not
      | x == 'fromEnum = Just $ ConE 'FromEnum
      | x == 'fromIntegral = Just $ ConE 'FromIntegral
      | x == 'sqrt = Just $ ConE 'Sqrt
      | x == 'the = Just $ VarE 'the_repr
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
      | op == '(>) = ConE 'Gt :@ x :@ y
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


tyVarBndrName :: TyVarBndr -> Name
tyVarBndrName (PlainTV name) = name
tyVarBndrName (KindedTV name _) = name


-- TODO: Check constructor types in case matches to make sure they fit the
-- type


-- Does not necessarily preserve type argument order (sorts matches by
-- constructor name)
-- NOTE: Requires at least one match to find the type
-- NOTE: This must be used in a splice, not in something like runQ
-- evaluated in the IO monad (this is because 'transformCase' uses 'reify')
transformCase0 :: Exp -> Q Exp
transformCase0 (CaseE scrutinee matches0@(firstMatch:_)) = do
    reifiedFirstMatchMaybe <- sequence $ fmap reify firstMatchConMaybe

      -- TODO: See if this needs to be generalized
    infoMaybe <- case reifiedFirstMatchMaybe of
      Just (DataConI _ _ name) -> fmap (fmap ([], )) $ dataCon name
      Just (TyConI (DataD _ name tyCons _ _ _)) -> fmap (fmap (tyCons, )) $ dataCon name
      Nothing -> return Nothing
      -- a -> error $ show reifiedFirstMatchMaybe

    let sortedMatches =
          case infoMaybe of
            Nothing -> matches0
            Just (_, (_, conIx)) -> sortBy (comparing (conIx . getMatchPatName)) matches0

    let Just (_, (name, _)) = infoMaybe
        Just (tyCons, _) = infoMaybe

    return (ConE 'CaseExp :@ scrutinee
              :@ (ConE 'SafeSumMatch :@ (AppTypeE (ConE 'Proxy) (ConT name))  :@ sumMatches sortedMatches))
  where
    dataCon name = do
      parent <- reify name
      case parent of
        TyConI (DataD _ name _ _ constrs _) ->
          return $ Just $ (name, \conName -> conName `elemIndex` map getConName constrs)

    firstMatchConMaybe =
      case firstMatch of
        Match (ConP name _) _ _ -> Just name
        Match (TupP xs) _ _ -> Just (tupleTypeName (length xs))
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

