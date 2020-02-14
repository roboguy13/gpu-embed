{-# LANGUAGE TemplateHaskellQuotes #-}

module Plugin (plugin) where

import           Expr hiding (Var, Lit)
import qualified Expr

import           Data.Data
import           Data.Generics.Uniplate.Operations
import qualified Data.Generics.Uniplate.DataOnly as Data

import           GhcPlugins

import           Control.Monad

-- Just for TH Names:
import qualified Language.Haskell.TH.Syntax as TH

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

  bindsOnlyPass (mapM (transformBind primMap)) guts

transformBind :: [(Id, Id)] -> CoreBind -> CoreM CoreBind
transformBind primMap (NonRec name e) =
  fmap (NonRec name) (transformExpr primMap e)

transformExpr :: [(Id, Id)] -> Expr Var -> CoreM (Expr Var)
transformExpr = undefined

-- XXX: The delineation marker probably has to be floated in (or maybe the
-- transformation can just go through the AST at that marker without
-- floating in the marker itself)

-- | Transform primitives and constructor/function calls. Skips the
-- function call transformation on the given 'recName' argument (if
-- a 'Just').
transformPrims :: Maybe Var -> [(Id, Id)] -> Expr Var -> Expr Var
transformPrims recName primMap = Data.transform go
  where
    builtin :: Id -> Maybe (Expr Var)
    builtin v = Var <$> lookup v primMap

    go expr@(Lit x) = undefined

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

