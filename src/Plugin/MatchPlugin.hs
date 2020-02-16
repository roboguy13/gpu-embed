{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MagicHash #-}

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

import           TyCon

import           Inst

import           Pair


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

import           DynFlags

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

constructExpr :: ModGuts -> Id -> CoreM CoreExpr
constructExpr guts fId = do
  constructDC <- findIdTH guts 'Construct

  return (Var constructDC :@ Type (varType fId) :@ Var fId)

-- XXX: The delineation marker probably has to be floated in (or maybe the
-- transformation can just go through the AST at that marker without
-- floating in the marker itself)

-- | Transform primitives and constructor/function calls. Skips the
-- function call transformation on the given 'recName' argument (if
-- a 'Just').
transformPrims :: ModGuts -> Maybe Var -> [(Id, Id)] -> (TH.Name -> Named) -> Expr Var -> CoreM (Expr Var)
transformPrims guts recName primMap lookupVar = Data.transformM (transformPrims0 guts recName primMap lookupVar)

transformPrims0 :: ModGuts -> Maybe Var -> [(Id, Id)] -> (TH.Name -> Named) -> Expr Var -> CoreM (Expr Var)
transformPrims0 guts recName primMap lookupVar = go
  where
    builtin :: Id -> Maybe (Expr Var)
    builtin v = Var <$> lookup v primMap

    -- Numeric literals
    go expr@(Lit x :@ ty :@ dict) = do
      dflags <- getDynFlags
      liftIO $ putStrLn ("found Lit: " ++ showPpr dflags expr) 
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

    go expr@(Var f :@ x)
      | "I#" <- occNameString (occName f) = do
        numTyCon <- findTyConTH guts ''Num
        intTy <- findTypeTH guts ''Int
        numDict <- buildDictionaryT guts (mkTyConApp numTyCon [intTy])

        litId <- findIdTH guts 'Expr.Lit
        return (Var litId :@ Type intTy :@ numDict :@ expr)
    
    go (Var f :@ x)
      | not (isTypeArg x) && 
        not (isDerivedOccName (occName f)) && last (occNameString (occName f)) /= '#' = do

        repTyCon <- findTyConTH guts ''GPURep

        let (aTy, bTy) = splitFunTy (varType f)


        dflags <- getDynFlags
        liftIO $ putStrLn ("(aTy, bTy) = " ++ showPpr dflags (aTy, bTy))

        repDict <- buildDictionaryT guts (mkTyConApp repTyCon [aTy])

        constructAp <- findIdTH guts 'ConstructAp

        f' <- constructExpr guts f

        return  (Var constructAp :@ Type aTy :@ Type bTy :@ repDict :@ f' :@ x)

    -- go expr@(Var v)
    --   | not (isDerivedOccName (occName v)) && last (occNameString (occName v)) /= '#'
    --       && occNameString (occName v) /= "construct"
    --       = do
    --         -- Not an internal name (like a dictionary) and not
    --         -- a constructor taking an unboxed type

    --       constructId <- findIdTH guts 'construct
    --       tyCon <- findTyConTH guts ''ConstructC

    --       dflags <- getDynFlags
    --       liftIO $ putStrLn ("ConstructC tyCon: " ++ showPpr dflags tyCon)
    --       liftIO $ putStrLn ("   arity: " ++ show (tyConArity tyCon))

    --       let vType = varType v

    --       liftIO $ putStrLn ("   at type: " ++ showPpr dflags vType)

    --       tyConDict <- buildDictionaryT guts (mkTyConApp tyCon [vType])
    --       liftIO $ putStrLn "after buildDictionaryT"

    --       liftIO $ putStrLn ("constructId type: " ++
    --                           showPpr dflags (varType constructId))

    --       return (Var constructId :@ Type vType :@ tyConDict :@ expr)

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

transformProdMatch :: ModGuts -> (Expr Var -> CoreM (Expr Var)) -> (TH.Name -> Named) -> Type -> Type -> Alt Var -> CoreM (Expr Var)
transformProdMatch guts transformPrims' lookupVar resultTy ty0 (altCon@(DataAlt dataAlt), vars0, body0) = do
  repTyCon <- findTyConTH guts ''GPURep

  repType <- computeRepType guts ty0 --(dataConOrigResTy dataAlt)

  pairTyCon <- findTyConTH guts ''(,)
  prodTypes <- listTypesWith guts (getName pairTyCon) repType

  dflags <- getDynFlags

  liftIO $ putStrLn $ "*** prodTypes = " ++ showPpr dflags prodTypes

  body <- transformPrims' body0


  go body pairTyCon repTyCon prodTypes vars0
  where
    go body pairTyCon repTyCon (ty1:_) [] = do
      nullaryMatchId <- findIdTH guts 'NullaryMatch

      resultTyDict <- buildDictionaryT guts (mkTyConApp repTyCon [resultTy])

      return (Var nullaryMatchId :@ Type ty1 :@ Type resultTy :@ resultTyDict :@ body)

    go body pairTyCon repTyCon (ty1:_) [x] = do
      oneProdMatchId <- findIdTH guts 'OneProdMatch

      ty1Dict <- buildDictionaryT guts (mkTyConApp repTyCon [ty1])

      abs'd <- abstractOver guts x body

      return (Var oneProdMatchId :@ Type ty1 :@ Type resultTy :@ ty1Dict :@ abs'd)

    go body pairTyCon repTyCon (ty1:restTys) (x:xs) = do
      prodMatchId <- findIdTH guts 'ProdMatch

      let restTy = mkTyConApp pairTyCon restTys

      rest <- go body pairTyCon repTyCon restTys xs

      ty1Dict <- buildDictionaryT guts (mkTyConApp repTyCon [ty1]) 
      restTyDict <- buildDictionaryT guts (mkTyConApp repTyCon [restTy])

      abs'd <- abstractOver guts x rest

      return (Var prodMatchId
        :@ Type ty1
        :@ Type restTy
        :@ Type resultTy
        :@ ty1Dict
        :@ restTyDict
        :@ abs'd)

transformSumMatch :: ModGuts -> (Expr Var -> CoreM (Expr Var)) -> (TH.Name -> Named) -> Expr Var -> Var -> Type -> [Alt Var] -> CoreM (Expr Var)

transformSumMatch guts transformPrims' lookupVar scrutinee wild resultTy alts@(alt1@(DataAlt dataAlt1, _, _):_) = do

  dynFlags <- getDynFlags

  repTyCon <- findTyConTH guts ''GPURep
  repTyTyCon <- findTyConTH guts ''GPURepTy

  liftIO $ putStrLn $ showSDoc dynFlags $ ppr resultTy
  liftIO $ putStrLn $ showSDoc dynFlags $ ppr wild

  -- repType <- computeRepType guts (dataConOrigResTy dataAlt1)
  -- repType <- computeRepType guts (exprType scrutinee)

  eitherTyCon <- findTyConTH guts ''Either

  sumTypes <- listTypesWith guts (getName eitherTyCon) (exprType scrutinee)

  liftIO $ putStrLn ("sumTypes = " ++ showPpr dynFlags sumTypes)

  nRepType <- normaliseType' guts (exprType scrutinee)
  liftIO $ putStrLn $ showSDoc dynFlags $ ppr nRepType

  liftIO $ putStrLn $ showSDoc dynFlags $ ppr sumTypes
  liftIO $ putStrLn $ showSDoc dynFlags $ ppr scrutinee
  
  sumMatch <- go eitherTyCon repTyCon sumTypes alts


  caseExpId <- findIdTH guts 'CaseExp

  let scrRepTy = mkTyConApp repTyCon [exprType scrutinee]
      scrRepTyTy = mkTyConApp repTyTyCon [exprType scrutinee]

  repTypeDict <- buildDictionaryT guts scrRepTy

  scrutinee' <- transformPrims' scrutinee

  (scrTyCo, scrTyNorm) <- normaliseTypeCo guts scrRepTyTy

  return (Var caseExpId
           :@ Type (exprType scrutinee)
           :@ Type scrTyNorm
           :@ Type resultTy
           :@ repTypeDict
           :@ mkEqBox scrTyCo
           :@ scrutinee'
           :@ sumMatch)

  where
    go eitherTyCon repTyCon (ty1:_) [] = do
      emptyMatchId <- findIdTH guts 'EmptyMatch
      return (Var emptyMatchId :@ Type resultTy)

    go eitherTyCon repTyCon (ty1:_) [x] = do
      prod <- transformProdMatch guts transformPrims' lookupVar resultTy ty1 x
      co <- repTyCo guts ty1

      oneSumMatchId <- findIdTH guts 'OneSumMatch

      ty1Dict <- buildDictionaryT guts (mkTyConApp repTyCon [ty1])
      resultTyDict <- buildDictionaryT guts (mkTyConApp repTyCon [resultTy])


      return (Var oneSumMatchId
                :@ Type ty1
                :@ Type resultTy
                :@ ty1Dict
                :@ resultTyDict
                :@ mkEqBox co
                :@ prod)

    go eitherTyCon repTyCon allTys@(ty1:restTys) (x:xs) = do
      dflags <- getDynFlags

      prod <- transformProdMatch guts transformPrims' lookupVar resultTy ty1 x

      let restTy = eitherWrap eitherTyCon restTys

      co <- repTyCo guts restTy

      restSum <- go eitherTyCon repTyCon restTys xs

      sumMatchId <- findIdTH guts 'SumMatch


      let Pair coB coA = coercionKind co

      -- let coA = restTy

      -- repTyTyCon <- findTyConTH guts ''GPURepTy

      -- let coB = mkTyConApp repTyTyCon [coA]

      -- liftIO $ putStrLn $ "#### (coA, coB) = "  ++ showPpr dflags (coA, coB)

      liftIO $ putStrLn $ "restTy = " ++ showPpr dflags restTy

      -- let tyA = eitherWrap eitherTyCon allTys


      dictA <- buildDictionaryT guts (mkTyConApp repTyCon [ty1])
      dictB <- buildDictionaryT guts (mkTyConApp repTyCon [restTy])

      -- eqTy <- runTcM guts $ do 
      --   mkEqBoxTy co coB coA

      -- eqDict <- buildDictionaryT guts (mkTyConApp eqTyCon [coA, coB, mkCoercionTy co])
      -- constraint3Tuple <- lookupTyCon (cTupleTyConName 3)
      return (Var sumMatchId
                :@ Type ty1
                -- :@ Type ty1
                :@ Type restTy
                :@ Type resultTy
                :@ dictA
                :@ dictB
                -- :@ Coercion co
                :@ mkEqBox co --coB coA --Type eqTy
                :@ prod
                :@ restSum)


    eitherWrap eitherTyCon = foldr1 (\x acc -> mkTyConApp eitherTyCon [x, acc])

transformSumMatches :: ModGuts -> Maybe Var -> [(Id, Id)] -> (TH.Name -> Named) -> Expr Var -> CoreM (Expr Var)
transformSumMatches guts recName primMap lookupVar =
    Data.transformM go -- <=< transformPrims guts recName primMap lookupVar
  where
    go (Case scrutinee wild ty alts) =
      transformSumMatch guts (transformPrims guts recName primMap lookupVar) lookupVar scrutinee wild ty alts
    go expr = return expr --transformPrims0 guts recName primMap lookupVar expr

-- e  ==>  (\x -> e)     {where x is a free variable in e}
-- Also transforms the type of x :: T to x :: GPUExp T
-- TODO: Make sure there aren't any issues with this type transformation
-- and foralls, etc.
abstractOver :: ModGuts -> Var -> Expr Var -> CoreM (Expr Var)
abstractOver guts v e = do
  expTyCon <- findTyConTH guts ''GPUExp

  let origTy = varType v
      newTy = mkTyConApp expTyCon [origTy]

  return $ Lam (setVarType v newTy) (Data.transform (go newTy) e)
  where
    -- Set var type in rest of expression
    go newTy (Var v')
      | varName v' == varName v = Var $ setVarType v' newTy
    go _newty expr = expr

-- | listTypesWith (lookupVar ''(,)) (a, (b, c))  ==>  [a, b, c]
-- listTypesWith (lookupVar ''Either) (Either a (Either b c))  ==>  [a, b, c]
listTypesWith :: ModGuts -> Name -> Type -> CoreM [Type]
listTypesWith guts n = go <=< normaliseType' guts
  where
    go ty =
      case splitTyConApp_maybe ty of
        Nothing -> return [ty]
        Just (tyCon, [a, b])
          | tyConName tyCon /= n -> return [ty]
          | otherwise ->
              fmap (a:) (go b)
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
  (co, _repType) <- computeRepTypeCo guts ty

  return co

-- | Use GPURepTy to find the canonical representation type
computeRepType :: ModGuts -> Type -> CoreM Type
computeRepType guts = fmap snd . computeRepTypeCo guts

computeRepTypeCo :: ModGuts -> Type -> CoreM (Coercion, Type)
computeRepTypeCo guts ty = do
  gpuRepTy <- thNameToGhcName_ ''GPURepTy

  repTy <- findTyCon' guts gpuRepTy

  normaliseTypeCo guts (mkTyConApp repTy [ty])

normaliseType' :: ModGuts -> Type -> CoreM Type
normaliseType' guts = fmap snd . normaliseTypeCo guts

normaliseTypeCo :: ModGuts -> Type -> CoreM (Coercion, Type)
normaliseTypeCo guts ty =
  runTcM guts . fmap fst . runTcS $ do
    famInstEnvs <- getFamInstEnvs
    return (normaliseType famInstEnvs Nominal ty)


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

-- Modified from 'Inst':

mkEqBox :: TcCoercion -> CoreExpr
mkEqBox co = 
    Var (dataConWorkId eqDataCon) :@ Type k :@ Type ty1 :@ Type ty2 :@ Coercion co

    -- Var (dataConWorkId eqDataCon) :@ Type k :@ Type ty1 :@ Type ty2 :@ Type (mkCoercionTy co)

    -- mkTyConApp eqTyCon [k, ty1, ty2, mkCoercionTy co]
    -- mkTyConApp (promoteDataCon eqDataCon) [k, ty1, ty2, mkCoercionTy co]
  where
    k = tcTypeKind ty1
    Pair ty1 ty2 = coercionKind co

