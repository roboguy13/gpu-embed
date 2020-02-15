{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}

module Plugin (plugin) where

import           Expr hiding (Var, Lit, Lam, (:@))
import qualified Expr

import           Data.Data hiding (TyCon (..), tyConName)
import           Data.Generics.Uniplate.Operations
import qualified Data.Generics.Uniplate.DataOnly as Data

import           GhcPlugins

import           InstEnv

import           FamInstEnv

import           TcSMonad


import           Control.Monad

import           Control.Arrow ((&&&), (***), first, second)

import           GHCUtils

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

  constrNames <- mapM (\n -> fmap (,n) (thNameToGhcName_ n)) constrNamesTH

  gpuExprIdMap <- forM constrNames
                       (\(name, nameTH) -> do
                          theId <- lookupId name
                          return (nameTH, theId))

  bindsOnlyPass (mapM (transformBind guts (mg_inst_env guts) primMap (getGPUExprIdsFrom gpuExprIdMap))) guts

transformBind :: ModGuts -> InstEnv -> [(Id, Id)] -> (TH.Name -> Var) -> CoreBind -> CoreM CoreBind
transformBind guts instEnv primMap lookupVar (NonRec name e) =
  fmap (NonRec name) (transformExpr guts primMap lookupVar e)

transformExpr :: ModGuts -> [(Id, Id)] -> (TH.Name -> Var) -> Expr Var -> CoreM (Expr Var)
transformExpr guts primMap lookupVar = undefined

-- XXX: The delineation marker probably has to be floated in (or maybe the
-- transformation can just go through the AST at that marker without
-- floating in the marker itself)

-- | Transform primitives and constructor/function calls. Skips the
-- function call transformation on the given 'recName' argument (if
-- a 'Just').
transformPrims :: ModGuts -> Maybe Var -> [(Id, Id)] -> (TH.Name -> Var) -> Expr Var -> CoreM (Expr Var)
transformPrims guts recName primMap lookupVar = Data.transformM go
  where
    builtin :: Id -> Maybe (Expr Var)
    builtin v = Var <$> lookup v primMap

    -- Numeric literals
    go expr@(Lit x :@ ty :@ dict) = return (Var (lookupVar 'Lit) :@ ty :@ dict :@ expr)

    go (Var v)
      | Just b <- builtin v = return b

    go (Var f :@ tyA@(Type{}) :@ tyB@(Type{}) :@ dictA@(Type{}) :@ dictB@(Type{}) :@ x)
      | Just b <- builtin f = return (b :@ tyA :@ tyB :@ dictA :@ dictB :@ x)

    go (Var f :@ ty@(Type{}) :@ dict@(Type{}) :@ x)
      | Just b <- builtin f = return (b :@ ty :@ dict :@ x)

    go (Var f :@ ty@(Type{}) :@ dict@(Type{}) :@ x :@ y)
      | Just b <- builtin f = return (b :@ ty :@ dict :@ x :@ y)

    go expr@(Var v)
      | v `elem` map lookupVar ['(,), '(,,), '(,,,)] = do
          let vType = varType v
          tyCon <- findTyCon' guts (varName (lookupVar ''ConstructC))

          return (Var (lookupVar 'construct) :@ Type vType :@ Type (mkTyConApp tyCon [vType]) :@ expr)

    go expr@(Var fn :@ _)
      | fn == lookupVar 'construct = return $ expr

    go expr@(Case e wild ty alts@((altCon1, _, _):_))
      | DataAlt d <- altCon1 =
          if getName d == getName (lookupVar 'False) || getName d == getName (lookupVar 'True)
          then -- This is an if-then-else
            let iteAlts = map (\(DataAlt constr, _, body) -> (getName constr, body)) alts
                Just falseBody = lookup (getName (lookupVar 'False)) iteAlts
                Just trueBody = lookup (getName (lookupVar 'True)) iteAlts
            in
            return (Var (lookupVar 'IfThenElse) :@ Type ty :@ e :@ trueBody :@ falseBody)
          else
            return expr

    go expr = return expr

transformProdMatch :: ModGuts -> (TH.Name -> Var) -> Type -> Alt a -> CoreM (Expr a)
transformProdMatch guts lookupVar ty0 (altCon@(DataAlt dataCon), vars0, body) = do
  repTyCon <- findTyCon' guts (varName (lookupVar ''GPURep))

  repType <- computeRepType guts (dataConOrigResTy dataCon)

  prodTypes <- listTypesWith (lookupVar ''(,)) repType

  pairTyCon <- findTyCon' guts (varName (lookupVar ''(,)))

  return $ go pairTyCon repTyCon prodTypes vars0
  where
    go pairTyCon repTyCon (ty1:_) [] = Var (lookupVar 'NullaryMatch) :@ Type ty1 :@ Type ty0 :@ Type (mkTyConApp repTyCon [ty0]) :@ body
    go pairTyCon repTyCon (ty1:_) [x] =
      Var (lookupVar 'OneProdMatch) :@ Type ty1 :@ Type ty0 :@ Type (mkTyConApp repTyCon [ty0]) :@ body

    go pairTyCon repTyCon (ty1:restTys) (x:xs) =
      let restTy = (mkTyConApp pairTyCon restTys)
      in
      Var (lookupVar 'ProdMatch)
        :@ Type ty1
        :@ Type restTy
        :@ Type ty0
        :@ Type (mkTyConApp repTyCon [ty1])
        :@ Type (mkTyConApp repTyCon [restTy])
        :@ go pairTyCon repTyCon restTys xs

transformSumMatch :: ModGuts -> (TH.Name -> Var) -> Expr b -> b -> Type -> [Alt b] -> CoreM (Expr a)
transformSumMatch guts lookupVar scrutinee wild ty alts@(alt1:_) = do
  undefined

abstractOver :: a -> Expr a -> Expr a
abstractOver = Lam

-- | listTypesWith (lookupVar ''(,)) (a, (b, c))  ==>  [a, b, c]
-- listTypesWith (lookupVar ''Either) (Either a (Either b c))  ==>  [a, b, c]
listTypesWith :: Var -> Type -> CoreM [Type]
listTypesWith tyConVar ty =
  case splitTyConApp_maybe ty of
    Nothing -> return [ty]
    Just (tyCon, [a, b])
      | tyConName tyCon /= getName tyConVar -> return [ty]
      | otherwise ->
          fmap (a:) (listTypesWith tyConVar b)


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

getGPUExprIdsFrom :: [(TH.Name, Id)] -> TH.Name -> Id
getGPUExprIdsFrom idMap name =
  case lookup name idMap of
    Nothing -> error $ "Cannot find Id for: " ++ show name
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



  -- Construct --
  ,'construct
  ]


-- | Use GPURepTy to find the canonical representation type
computeRepType :: ModGuts -> Type -> CoreM Type
computeRepType guts ty = do
  gpuRepTy <- thNameToGhcName_ ''GPURepTy

  repTy <- findTyCon' guts gpuRepTy

  runTcM guts . fmap fst . runTcS $ do
    famInstEnvs <- getFamInstEnvs
    return (topNormaliseType famInstEnvs (mkTyConApp repTy [ty]))

