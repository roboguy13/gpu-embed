{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Plugin.MatchPlugin (plugin) where

import           Deep.GHCUtils

import           Deep.Expr hiding (Var, Lit, Lam, (:@))
import qualified Deep.Expr as Expr
import           Deep.Delineate

import           Data.Data hiding (TyCon (..), tyConName)
import           Data.Generics.Uniplate.Operations
import qualified Data.Generics.Uniplate.DataOnly as Data

import           GhcPlugins

import           InstEnv

import           FamInstEnv

import           TcSMonad


import           Control.Monad

import           Control.Arrow ((&&&), (***), first, second)

-- import           GHCUtils

-- Just for TH Names:
import qualified Language.Haskell.TH.Syntax as TH



import           TcRnTypes
import           TcSimplify
import           TcMType
import           TcRnMonad
import           TcSMonad
import           TcEvidence
import           TcType

import           Finder
import           LoadIface

import           DsBinds
import           DsMonad

import           HsBinds
import           HsDecls

import           CostCentreState

import           Bag
import           VarSet

import           Encoding

import           ErrUtils

import           Data.IORef

import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Char
import           Data.List

infixl 0 :@
pattern f :@ x = App f x

plugin :: Plugin
plugin =
  defaultPlugin
    { installCoreToDos = install
    }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ coreToDos = do
  return (CoreDoPluginPass "Pattern matching plugin" pass : coreToDos)

pass :: ModGuts -> CoreM ModGuts
pass guts = do
  primMap <- forM primMapTH
                 (\(fromTH, toTH) -> do
                  fromName <- thNameToGhcName_ fromTH
                  toName <- thNameToGhcName_ toTH

                  from <- findId guts fromName emptyVarSet
                  to <- findId guts toName emptyVarSet
                  return (from, to))

  constrNames <- mapM (\n -> fmap (,n) (thNameToGhcName_ n)) constrNamesTH

  gpuExprNamedMap <- forM constrNames
                       (\(name, nameTH) -> do
                          named <- findNamed guts name emptyVarSet
                          return (nameTH, named))

  -- bindsOnlyPass return guts
  bindsOnlyPass (mapM (transformBind guts (mg_inst_env guts) primMap (getGPUExprNamedsFrom gpuExprNamedMap))) guts

transformBind :: ModGuts -> InstEnv -> [(Id, Id)] -> (TH.Name -> Named) -> CoreBind -> CoreM CoreBind
transformBind guts instEnv primMap lookupVar (NonRec name e) =
  fmap (NonRec name) (transformExpr guts Nothing primMap lookupVar e)
transformBind guts instEnv primMap lookupVar (Rec bnds) = Rec <$> mapM go bnds
  where
    go (name, e) =
      (name,) <$> transformExpr guts (Just name) primMap lookupVar e

-- TODO: Add support for recursive functions

transformExpr :: ModGuts -> Maybe Var -> [(Id, Id)] -> (TH.Name -> Named) -> Expr Var -> CoreM (Expr Var)
transformExpr guts recName primMap lookupVar = Data.transformM go
  where
    go expr@(Var f :@ _ty :@ _dict :@ x) = do
      externalizeId <- findIdTH guts 'externalize

      if f ==  externalizeId
        then transformSumMatches guts recName primMap lookupVar x
        else return expr
    go expr = return expr

-- XXX: The delineation marker probably has to be floated in (or maybe the
-- transformation can just go through the AST at that marker without
-- floating in the marker itself)

-- | Transform primitives and constructor/function calls. Skips the
-- function call transformation on the given 'recName' argument (if
-- a 'Just').
transformPrims :: ModGuts -> Maybe Var -> [(Id, Id)] -> (TH.Name -> Named) -> Expr Var -> CoreM (Expr Var)
transformPrims guts recName primMap lookupVar = Data.transformM go
  where
    builtin :: Id -> Maybe (Expr Var)
    builtin v = Var <$> lookup v primMap

    -- Numeric literals
    go expr@(Lit x :@ ty :@ dict) = do
      litId <- findIdTH guts 'Lit
      return (Var litId :@ ty :@ dict :@ expr)

    go (Var v)
      | Just b <- builtin v = return b

    go (Var f :@ tyA@(Type{}) :@ tyB@(Type{}) :@ dictA@(Type{}) :@ dictB@(Type{}) :@ x)
      | Just b <- builtin f = return (b :@ tyA :@ tyB :@ dictA :@ dictB :@ x)

    go (Var f :@ ty@(Type{}) :@ dict@(Type{}) :@ x)
      | Just b <- builtin f = return (b :@ ty :@ dict :@ x)

    go (Var f :@ ty@(Type{}) :@ dict@(Type{}) :@ x :@ y)
      | Just b <- builtin f = return (b :@ ty :@ dict :@ x :@ y)

    go expr@(Var v) = do
      tupleIds <- mapM (findIdTH guts) ['(,), '(,,), '(,,,)]
      if v `elem` tupleIds
        then do
          let vType = varType v
          constructId <- findIdTH guts 'construct
          tyCon <- findTyConTH guts ''ConstructC
          -- tyCon <- findTyCon' guts (varName (lookupVar ''ConstructC))

          return (Var constructId :@ Type vType :@ Type (mkTyConApp tyCon [vType]) :@ expr)
        else return expr

    go expr@(Var fn :@ _) = do
      return expr

    go expr@(Case e wild ty alts@((altCon1, _, _):_))
      | DataAlt d <- altCon1 = do
          falseId <- findIdTH guts 'False
          trueId <- findIdTH guts 'True
          iteId <- findIdTH guts 'IfThenElse
          if getName d == getName falseId || getName d == getName trueId
          then -- This is an if-then-else
            let iteAlts = map (\(DataAlt constr, _, body) -> (getName constr, body)) alts
                Just falseBody = lookup (getName falseId) iteAlts
                Just trueBody = lookup (getName trueId) iteAlts
            in
            return (Var iteId :@ Type ty :@ e :@ trueBody :@ falseBody)
          else
            return expr

    go expr = return expr

transformProdMatch :: ModGuts -> (TH.Name -> Named) -> Type -> Alt a -> CoreM (Expr a)
transformProdMatch guts lookupVar ty0 (altCon@(DataAlt dataAlt), vars0, body) = do
  repTyCon <- findTyConTH guts ''GPURep

  repType <- computeRepType guts (dataConOrigResTy dataAlt)

  pairTyCon <- findTyConTH guts ''(,)
  prodTypes <- listTypesWith (getName pairTyCon) repType


  go pairTyCon repTyCon prodTypes vars0
  where
    go pairTyCon repTyCon (ty1:_) [] = do
      nullaryMatchId <- findIdTH guts 'NullaryMatch
      return (Var nullaryMatchId :@ Type ty1 :@ Type ty0 :@ Type (mkTyConApp repTyCon [ty0]) :@ body)

    go pairTyCon repTyCon (ty1:_) [x] = do
      oneProdMatchId <- findIdTH guts 'OneProdMatch

      return (Var oneProdMatchId :@ Type ty1 :@ Type ty0 :@ Type (mkTyConApp repTyCon [ty0]) :@ body)

    go pairTyCon repTyCon (ty1:restTys) (x:xs) = do
      prodMatchId <- findIdTH guts 'ProdMatch

      let restTy = mkTyConApp pairTyCon restTys

      rest <- go pairTyCon repTyCon restTys xs

      return (Var prodMatchId
        :@ Type ty1
        :@ Type restTy
        :@ Type ty0
        :@ Type (mkTyConApp repTyCon [ty1])
        :@ Type (mkTyConApp repTyCon [restTy])
        :@ rest)

transformSumMatch :: ModGuts -> (TH.Name -> Named) -> Expr a -> a -> Type -> [Alt a] -> CoreM (Expr a)

transformSumMatch guts lookupVar scrutinee wild ty0 alts@(alt1@(DataAlt dataAlt1, _, _):_) = do
  repTyCon <- findTyConTH guts ''GPURep

  repType <- computeRepType guts (dataConOrigResTy dataAlt1)

  eitherTyCon <- findTyConTH guts ''Either

  sumTypes <- listTypesWith (getName eitherTyCon) repType


  go eitherTyCon repTyCon sumTypes alts
  where
    go eitherTyCon repTyCon (ty1:_) [] = do
      emptyMatchId <- findIdTH guts 'EmptyMatch
      return (Var emptyMatchId :@ Type ty0)

    go eitherTyCon repTyCon (ty1:_) [x] = do
      prod <- transformProdMatch guts lookupVar ty1 x
      co <- repTyCo guts ty1

      oneSumMatchId <- findIdTH guts 'OneSumMatch

      return (Var oneSumMatchId
                :@ Type ty1
                :@ Type ty0
                :@ Type (mkTyConApp repTyCon [ty1])
                :@ Type (mkTyConApp repTyCon [ty0])
                :@ Coercion co
                :@ prod)

    go eitherTyCon repTyCon (ty1:restTys) (x:xs) = do
      prod <- transformProdMatch guts lookupVar ty1 x

      let restTy = mkTyConApp eitherTyCon restTys

      co <- repTyCo guts restTy

      restSum <- go eitherTyCon repTyCon restTys xs

      sumMatchId <- findIdTH guts 'SumMatch

      return (Var sumMatchId
                :@ Type ty1
                :@ Type restTy
                :@ Type ty0
                :@ Coercion co
                :@ prod
                :@ restSum)

transformSumMatches :: ModGuts -> Maybe Var -> [(Id, Id)] -> (TH.Name -> Named) -> Expr Var -> CoreM (Expr Var)
transformSumMatches guts recName primMap lookupVar =
    Data.transformM go <=< transformPrims guts recName primMap lookupVar
  where
    go (Case scrutinee wild ty alts) =
      transformSumMatch guts lookupVar scrutinee wild ty alts
    go expr = return expr

abstractOver :: a -> Expr a -> Expr a
abstractOver = Lam

-- | listTypesWith (lookupVar ''(,)) (a, (b, c))  ==>  [a, b, c]
-- listTypesWith (lookupVar ''Either) (Either a (Either b c))  ==>  [a, b, c]
listTypesWith :: Name -> Type -> CoreM [Type]
listTypesWith n ty =
  case splitTyConApp_maybe ty of
    Nothing -> return [ty]
    Just (tyCon, [a, b])
      | tyConName tyCon /= n -> return [ty]
      | otherwise ->
          fmap (a:) (listTypesWith n b)
    Just _ -> return [ty]
    -- Just x -> error $ "listTypesWith: " ++ show x


thNameToGhcName_ :: TH.Name -> CoreM Name
thNameToGhcName_ thName = do
  nameMaybe <- thNameToGhcName thName
  case nameMaybe of
    Nothing -> error $ "Cannot find name: " ++ show thName
    Just name -> return name

primMapTH :: [(TH.Name, TH.Name)]
primMapTH =
  [('not, 'Not)
  ,('fromEnum, 'FromEnum)
  ,('fromIntegral, 'FromIntegral)
  ,('sqrt, 'Sqrt)
  -- ,('the, 'the_repr)

  ,('False, 'FalseExp)
  ,('True, 'TrueExp)

  ,('(+), 'Add)
  ,('(*), 'Mul)
  ,('(-), 'Sub)
  ,('(==), 'Equal)
  ,('(<=), 'Lte)
  ,('(>), 'Gt)
  ]

getGPUExprNamedsFrom :: [(TH.Name, Named)] -> TH.Name -> Named
getGPUExprNamedsFrom namedMap name =
  case lookup name namedMap of
    Nothing -> error $ "Cannot find Named for: " ++ show name
    Just i  -> i

constrNamesTH :: [TH.Name]
constrNamesTH =
  [
  -- base --
   'False
  ,'True
  ,'(,)
  ,'(,,)
  ,'(,,,)

  ,''Bool

  -- ProdMatch --
  ,'ProdMatch
  ,'OneProdMatch
  ,'NullaryMatch

  -- SumMatch --
  ,'SumMatch
  ,'EmptyMatch
  ,'OneSumMatch

  -- GPUExp --
  ,'CaseExp
  ,'FalseExp
  ,'TrueExp

  ,'Repped

  -- ,'Lam
  -- ,'Var
  -- ,'Apply

  ,'Expr.Lit
  ,'Add
  ,'Sub
  ,'Mul

  ,'Equal
  ,'Lte
  ,'Gt

  ,'LeftExp
  ,'RightExp

  ,'PairExp

  ,'StepExp
  ,'DoneExp

  ,'IfThenElse

  ,''GPURep
  ,''GPURepTy



  -- Construct --
  ,'construct

  -- Delineate functions --
  ,'internalize
  ,'externalize
  ]


-- Try to give a proof that, given a type t, GPURepTy t ~ t
repTyCo :: ModGuts -> Type -> CoreM Coercion
repTyCo guts ty = do
  repType <- computeRepType guts ty

  return (mkNomReflCo repType)

-- | Use GPURepTy to find the canonical representation type
computeRepType :: ModGuts -> Type -> CoreM Type
computeRepType guts ty = do
  gpuRepTy <- thNameToGhcName_ ''GPURepTy

  repTy <- findTyCon' guts gpuRepTy

  runTcM guts . fmap fst . runTcS $ do
    famInstEnvs <- getFamInstEnvs
    return (topNormaliseType famInstEnvs (mkTyConApp repTy [ty]))

findIdTH :: ModGuts -> TH.Name -> CoreM Id
findIdTH guts thName = do
    nameMaybe <- thNameToGhcName thName
    case nameMaybe of
      Nothing -> error $ "findIdTH: Cannot find " ++ show thName
      Just name -> findId guts name emptyVarSet

findVarTH :: ModGuts -> TH.Name -> CoreM Var
findVarTH guts thName = do
    nameMaybe <- thNameToGhcName thName
    case nameMaybe of
      Nothing -> error $ "findVarTH: Cannot find " ++ show thName
      Just name -> findVar guts name emptyVarSet

findTyConTH :: ModGuts -> TH.Name -> CoreM TyCon
findTyConTH guts thName = do
    nameMaybe <- thNameToGhcName thName
    case nameMaybe of
      Nothing -> error $ "findTyConTH: Cannot find " ++ show thName
      Just name -> findTyCon guts name emptyVarSet

findTypeTH :: ModGuts -> TH.Name -> CoreM Type
findTypeTH guts thName = do
    nameMaybe <- thNameToGhcName thName
    case nameMaybe of
      Nothing -> error $ "findTypeTH: Cannot find " ++ show thName
      Just name -> findType guts name emptyVarSet

