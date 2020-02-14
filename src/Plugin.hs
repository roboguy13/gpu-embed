{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}

module Plugin (plugin) where

import           Expr hiding (Var, Lit, (:@))
import qualified Expr

import           Data.Data
import           Data.Generics.Uniplate.Operations
import qualified Data.Generics.Uniplate.DataOnly as Data

import           GhcPlugins

import           Control.Monad

import           Control.Arrow ((&&&), (***))

-- Just for TH Names:
import qualified Language.Haskell.TH.Syntax as TH

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

                  from <- lookupId fromName
                  to <- lookupId toName
                  return (from, to))

  gpuExprConstrNames <- mapM (\n -> fmap (,n) (thNameToGhcName_ n)) gpuExprConstrNamesTH

  gpuExprIdMap <- forM gpuExprConstrNames
                       (\(name, nameTH) -> do
                          theId <- lookupId name
                          return (nameTH, theId))

  bindsOnlyPass (mapM (transformBind primMap (Var . getGPUExprIdsFrom gpuExprIdMap))) guts

transformBind :: [(Id, Id)] -> (TH.Name -> Expr Var) -> CoreBind -> CoreM CoreBind
transformBind primMap dslVar (NonRec name e) =
  fmap (NonRec name) (transformExpr primMap dslVar e)

transformExpr :: [(Id, Id)] -> (TH.Name -> Expr Var) -> Expr Var -> CoreM (Expr Var)
transformExpr = undefined

-- XXX: The delineation marker probably has to be floated in (or maybe the
-- transformation can just go through the AST at that marker without
-- floating in the marker itself)

-- | Transform primitives and constructor/function calls. Skips the
-- function call transformation on the given 'recName' argument (if
-- a 'Just').
transformPrims :: Maybe Var -> [(Id, Id)] -> (TH.Name -> Expr Var) -> Expr Var -> Expr Var
transformPrims recName primMap dslVar = Data.transform go
  where
    builtin :: Id -> Maybe (Expr Var)
    builtin v = Var <$> lookup v primMap

    go expr@(Lit x) = dslVar 'Lit :@ expr

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
  ,('the, 'the_repr)
  ]

getGPUExprIdsFrom :: [(TH.Name, Id)] -> TH.Name -> Id
getGPUExprIdsFrom idMap name =
  case lookup name idMap of
    -- Nothing -> error $ "Cannot find Id for: " ++ show name
    Just i  -> i

gpuExprConstrNamesTH :: [TH.Name]
gpuExprConstrNamesTH =
  [
  -- ProdMatch --
   'ProdMatch
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
  ]

