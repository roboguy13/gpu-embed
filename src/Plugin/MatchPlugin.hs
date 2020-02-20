{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Plugin.MatchPlugin (plugin) where

import           Deep.GHCUtils

import           Deep.Expr hiding (Var, Lit, Lam, (:@), Name)
import qualified Deep.Expr as Expr
import           Deep.Delineate

import           Data.Data hiding (TyCon (..), tyConName, mkFunTy)
import           Data.Typeable hiding (TyCon (..), tyConName, mkFunTy)

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
import           Control.Monad.Writer hiding (pass, Alt)
import           Control.Monad.State

import           Control.Arrow ((&&&), (***), first, second)

import           GHC.Generics
import           GHC.Types (Int(..))

-- import           GHCUtils

-- Just for TH Names:
import qualified Language.Haskell.TH.Syntax as TH



import           TcRnTypes
import           TcSimplify
import           TcMType
import           TcSMonad
import           TcEvidence
import           TcType

import           Finder
import           LoadIface

import           DsBinds

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

newtype UniqueSupply m a = UniqueSupply (StateT Int m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

instance HasDynFlags (UniqueSupply CoreM) where
  getDynFlags = lift getDynFlags

newUnique :: Monad m => UniqueSupply m Int
newUnique = UniqueSupply (modify (+1) *> get)

runUniqueSupply :: Monad m => UniqueSupply m a -> m a
runUniqueSupply (UniqueSupply us) = evalStateT us 0

type MatchM = UniqueSupply CoreM

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
                  return (from, Var to))


  dflags <- getDynFlags


  runUniqueSupply $ bindsOnlyPass_match (mapM (transformBind guts (mg_inst_env guts) primMap)) guts

-- TODO: Figure out what, specifically, this is a workaround for and
-- actually fix the underlying problem.
hasExternalize :: ModGuts -> Expr Var -> MatchM Bool
hasExternalize guts e = do
  (_, a) <- runWriterT (Data.transformM go e)
  case a of
    Any b -> return b
  where
    go :: Expr Var -> WriterT Any MatchM (Expr Var)
    go expr@(Var f) = do
      externalizeId <- lift $ lift $ findIdTH guts 'externalize

      if f == externalizeId
        then tell (Any True) >> return expr
        else return expr
    go expr = return expr

transformBind :: ModGuts -> InstEnv -> [(Id, CoreExpr)] -> CoreBind -> MatchM CoreBind
transformBind guts instEnv primMap (NonRec name e) =
  fmap (NonRec name) (transformExpr guts Nothing primMap e)
transformBind guts instEnv primMap (Rec bnds) = Rec <$> mapM go bnds
  where
    go :: (Var, Expr Var) -> MatchM (Var, Expr Var)
    go (name, e) = do
      hasEx <- hasExternalize guts e
      if hasEx
        then do
          dflags <- lift getDynFlags
          e' <- transformTailRec guts name e
          (name,) <$> transformExpr guts (Just name) primMap e'
        else return (name, e)

-- TODO: Add support for recursive functions

changed :: Monad m => WriterT Any m ()
changed = tell (Any True)

returnChanged :: Monad m => a -> WriterT Any m a
returnChanged x = do
  changed
  return x

-- | 'Nothing' indicates that no changes were made
transformExprMaybe :: ModGuts -> Maybe Var -> [(Id, CoreExpr)] -> Expr Var -> MatchM (Maybe (Expr Var))
transformExprMaybe guts  recName primMap e = do
  (r, progress) <- runWriterT (Data.transformM go e)
  case progress of
    Any False -> return Nothing
    Any True  -> return $ Just r
  where

    go :: CoreExpr -> WriterT Any MatchM CoreExpr
    go expr@(Var f :@ _ty :@ _dict :@ x) = do
      dflags <- lift getDynFlags
      externalizeId <- lift $ lift $ findIdTH guts 'externalize

      if f == externalizeId
        then do
          changed
          lift $ transformPrims guts recName primMap x
        else return expr
    go expr = return expr

untilNothingM :: Monad m => (a -> m (Maybe a)) -> a -> m a
untilNothingM f = go
  where
    go x = do
      fx <- f x
      case fx of
        Just r  -> go r
        Nothing -> return x

transformExpr :: ModGuts -> Maybe Var -> [(Id, CoreExpr)] -> Expr Var -> MatchM (Expr Var)
transformExpr guts recNameM primMap =
  untilNothingM (transformExprMaybe guts recNameM primMap)

constructExpr :: ModGuts -> Id -> MatchM CoreExpr
constructExpr guts fId = do
  constructDC <- lift $ findIdTH guts 'Construct

  return (Var constructDC :@ Type (varType fId) :@ Var fId)

-- XXX: The delineation marker probably has to be floated in (or maybe the
-- transformation can just go through the AST at that marker without
-- floating in the marker itself)

-- | Transform primitives and constructor/function calls. Skips the
-- function call transformation on the given 'recName' argument (if
-- a 'Just').
transformPrims :: ModGuts -> Maybe Var -> [(Id, CoreExpr)] -> Expr Var -> MatchM (Expr Var)
transformPrims guts recName primMap = tr
  where
    tr = transformPrims0 guts recName primMap []

isDictVar :: Var -> Bool
isDictVar v =
  let str = occNameString (occName v)
  in
  take 2 str == "$f" || take 2 str == "$d"

isDict :: CoreExpr -> Bool
isDict (Var v) = isDictVar v
isDict e       = tcIsConstraintKind (tcTypeKind (exprType e))

-- | Does the expression already have a type of the form GPUExp (...)?
hasExprType :: ModGuts -> CoreExpr -> MatchM Bool
hasExprType guts e = do
  expTyCon <- lift $ findTyConTH guts ''GPUExp

  return $ hasExprTy' expTyCon e

hasExprTy' :: TyCon -> CoreExpr -> Bool
hasExprTy' expTyCon e = isExprTy expTyCon (exprType e)

isExprTy :: TyCon -> Type -> Bool
isExprTy expTyCon ty =
  case splitTyConApp_maybe ty of
    Nothing -> False
    Just (t, _) -> t == expTyCon

whenNotExprTyped :: ModGuts -> CoreExpr -> MatchM CoreExpr -> MatchM CoreExpr
whenNotExprTyped guts e m = do
  eType <- hasExprType guts e
  if eType
    then return e
    else m

isVar :: Expr a -> Bool
isVar (Var _) = True
isVar _ = False

-- Mark for further transformation
mark0 :: ModGuts -> Expr Var -> MatchM (Expr Var)
mark0 guts x = do
  eType <- hasExprType guts x
  if eType
    then return x
    else do
      varId <- lift $ findIdTH guts 'Expr.Var

      let xTy = exprType x

      case x of
        -- Var v :@ Type {} :@ _dict :@ _n
        --   | v == varId -> return x
        _ -> do

          externalizeName <- lift $ findIdTH guts 'externalize

          repTyCon <- lift $ findTyConTH guts ''GPURep
          dflags <- getDynFlags

          liftIO $ putStrLn $ "mark0: xTy = " ++ showPpr dflags xTy
          liftIO $ putStrLn $ "mark0: x   = {{" ++ showPpr dflags x ++ "}}"
          dict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [xTy])

          return (Var externalizeName :@ Type xTy :@ dict :@ x)

-- 'exprVars' are already of GPUExp type and do not need to be modified
transformPrims0 :: ModGuts -> Maybe Var -> [(Id, CoreExpr)] -> [Expr Var] -> Expr Var -> MatchM (Expr Var)
transformPrims0 guts recName primMap exprVars e = {- transformLams guts mark <=< -} do
  lamId <- lift $ findIdTH guts 'Expr.Lam
  go0 (== lamId) e
  where
    mark = mark0 guts

    builtin :: Id -> Maybe (Expr Var)
    builtin v = lookup v primMap



    replaceVarType0 v ty expr@(Var v')
      | varName v == varName v' = Var $ setVarType v' ty
      | otherwise = expr
    replaceVarType0 v ty expr = expr

    replaceVarType v ty = Data.transform (replaceVarType0 v ty)

    go0 isLam = go
      where

        go :: Expr Var -> MatchM (Expr Var)
        go (Case scrutinee wild ty alts) = do
          liftIO $ putStrLn "saw a case"
          dflags <- getDynFlags

          falseId <- lift $ findIdTH guts 'False
          trueId <- lift $ findIdTH guts 'True
          iteId <- lift $ findIdTH guts 'IfThenElse
     
          boolTyCon <- lift $ findTyConTH guts ''Bool

          let (DataAlt d, _, _) : _ = alts

          if dataConTyCon d == boolTyCon
          then do
            -- This is an if-then-else
            let [falseBody, trueBody] = map (\(DataAlt constr, _, body) -> body) alts

            scrutineeMarked <- mark scrutinee
            falseBodyMarked <- mark falseBody
            trueBodyMarked <- mark trueBody
            return (Var iteId :@ Type ty :@ scrutineeMarked :@ trueBodyMarked :@ falseBodyMarked)
          else
            transformSumMatch guts mark scrutinee wild ty alts

        go expr@(Lam v body) = do
          expTyCon <- lift $ findTyConTH guts ''GPUExp

          let ty = mkTyConApp expTyCon [varType v]

          bodyMarked <- mark (replaceVarType v ty body)

          return (Lam (setVarType v ty) bodyMarked)

        -- Numeric literals
        go expr@(Lit x :@ ty :@ dict) = do
          dflags <- lift $ getDynFlags
          litId <- lift $ findIdTH guts 'Lit
          return (Var litId :@ ty :@ dict :@ expr)

        go (Var v)
          | Just b <- builtin v = return b

        go expr@(Var v :@ tyA@(Type {}) :@ tyB@(Type {}) :@ dict1 :@ dict2 :@ name :@ body)
          | isLam v = do
              markedBody <- mark body
              return (Var v:@ tyA :@ tyB :@ dict1 :@ dict2 :@ name :@ markedBody)

        go expr@(Var v)
          | False <- isFunTy (varType v) = whenNotExprTyped guts expr $ do
              constructId <- lift $ findIdTH guts 'Construct
              return (Var constructId :@ Type (varType v) :@ expr)

        go expr@(Var f :@ tyA@(Type{}) :@ tyB@(Type{}) :@ dictA :@ dictB :@ x)
          | Just b <- builtin f,
            True <- isDict dictA,
            True <- isDict dictB = whenNotExprTyped guts expr $ do

              markedX <- mark x
              return (b :@ tyA :@ tyB :@ dictA :@ dictB :@ markedX)

        go expr@(Var f :@ ty@(Type{}) :@ dict :@ x)
          | Just b <- builtin f,
            True <- isDict dict = whenNotExprTyped guts expr $ do
              markedX <- mark x
              return (b :@ ty :@ dict :@ markedX)

        go expr@(Var f :@ ty@(Type{}) :@ dict :@ x :@ y)
          | Just b <- builtin f,
            True <- isDict dict = whenNotExprTyped guts expr $ do
              markedX <- mark x
              markedY <- mark y
              return (b :@ ty :@ dict :@ markedX :@ markedY)

        go expr@(Var f :@ tyA@(Type{}) :@ tyB@(Type{}) :@ x)
          | Just b <- builtin f = whenNotExprTyped guts expr $ do
              markedX <- mark x
              return (b :@ tyA :@ tyB :@ markedX)

        -- TODO: Handle other literals
        go expr@(Var f :@ x)
          | "I#" <- occNameString (occName f) = do
            numTyCon <- lift $ findTyConTH guts ''Num
            intTy <- lift $ findTypeTH guts ''Int
            numDict <- lift $ buildDictionaryT guts (mkTyConApp numTyCon [intTy])

            litId <- lift $ findIdTH guts 'Expr.Lit
            return (Var litId :@ Type intTy :@ numDict :@ expr)

          | "D#" <- occNameString (occName f) = do
            numTyCon <- lift $ findTyConTH guts ''Num
            doubleTy <- lift $ findTypeTH guts ''Double
            numDict <- lift $ buildDictionaryT guts (mkTyConApp numTyCon [doubleTy])

            litId <- lift $ findIdTH guts 'Expr.Lit
            return (Var litId :@ Type doubleTy :@ numDict :@ expr)
        
          | "F#" <- occNameString (occName f) = do
            numTyCon <- lift $ findTyConTH guts ''Num
            floatTyCon <- lift $ findTyConTH guts ''Float
            dflags <- lift $ getDynFlags
            let floatTy = mkTyConApp floatTyCon []
            numDict <- lift $ buildDictionaryT guts (mkTyConApp numTyCon [floatTy])

            litId <- lift $ findIdTH guts 'Expr.Lit
            return (Var litId :@ Type floatTy :@ numDict :@ expr)

        go expr@(Var f :@ x)
          | not (isTypeArg x) && 
            not (isDerivedOccName (occName f)) && last (occNameString (occName f)) /= '#',
            Just (aTy, bTy) <- splitFunTy_maybe (varType f) = 
              whenNotExprTyped guts expr $ do

            repTyCon <- lift $ findTyConTH guts ''GPURep


            dflags <- lift $ getDynFlags

            repDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [aTy])

            constructAp <- lift $ findIdTH guts 'ConstructAp

            f' <- constructExpr guts f

            markedX <- mark x

            return  (Var constructAp :@ Type aTy :@ Type bTy :@ repDict :@ f' :@ markedX)

        go expr@(lhs :@ arg)
          | not (isVar lhs) && not (isDict lhs) && not (isDict arg),
            Just (aTy, bTy) <- splitFunTy_maybe (exprType lhs) = whenNotExprTyped guts expr $ do
              constructAp <- lift $ findIdTH guts 'ConstructAp

              repTyCon <- lift $ findTyConTH guts ''GPURep

              dflags <- lift $ getDynFlags

              repDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [aTy])

              markedLhs <- mark lhs
              markedArg <- mark arg

              return (Var constructAp :@ Type aTy :@ Type bTy :@ repDict :@ markedLhs :@ markedArg)

        -- go expr@(Var f :@ tyA@(Type{}) :@ tyB@(Type{}) :@ dict1 :@ dict2 :@ nval
        --            :@ ((Lam v e) :@ x)) = do
        --     markedE <- 

  -- return (Var lamId :@ Type origTy :@ Type eTy' :@ repDict :@ typeableDict :@ nameVal
  --           :@ ((Lam v' (Data.transform (go varId newTy) e)) :@ (Var varId :@ Type origTy :@ typeableDict :@ nameVal)))

        go expr
          | Just (fId, tyArgs, dicts) <- splitTypeApps_maybe expr = whenNotExprTyped guts expr $ do
              constructId <- lift $ findIdTH guts 'Construct

              let expr' = mkTyApps (Var fId) tyArgs
                  expr'' = mkApps expr' (map Var dicts)

              return (Var constructId :@ Type (exprType expr'') :@ expr'')

        go expr = return expr

transformProdMatch :: ModGuts -> (Expr Var -> MatchM (Expr Var)) -> Type -> Type -> Alt Var -> MatchM (Expr Var)
transformProdMatch guts mark resultTy ty0_ (altCon@(DataAlt dataAlt), vars0, body0) = do
  dflags <- lift $ getDynFlags
  repTyCon <- lift $ findTyConTH guts ''GPURep

  ty0 <- lift $ (unwrapExpType guts <=< unwrapExpType guts) ty0_
  liftIO $ putStrLn $ "ty0 = " ++ showPpr dflags ty0

  repType <- lift $ computeRepType guts ty0

  pairTyCon <- lift $ findTyConTH guts ''(,)
  prodTypes <- listTypesWith guts (getName pairTyCon) repType



  body <- mark body0


  go body pairTyCon repTyCon prodTypes vars0
  where
    go :: Expr Var -> TyCon -> TyCon -> [Type] -> [Var] -> MatchM (Expr Var)
    go body pairTyCon repTyCon (ty1:_) [] = do
      nullaryMatchId <- lift $ findIdTH guts 'NullaryMatch

      resultTyDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [resultTy])

      return (Var nullaryMatchId :@ Type ty1 :@ Type resultTy :@ resultTyDict :@ body)

    go body pairTyCon repTyCon allTys@(ty1:_) [x] = do
      dflags <- getDynFlags

      let ty = pairWrap pairTyCon allTys

      oneProdMatchId <- lift $ findIdTH guts 'OneProdMatch

      tyDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [ty])

      abs'd <- abstractOver guts x body

      return (Var oneProdMatchId :@ Type ty :@ Type resultTy :@ tyDict :@ abs'd)

    go body pairTyCon repTyCon (ty1:restTys) (x:xs) = do
      dflags <- lift $ getDynFlags

      prodMatchId <- lift $ findIdTH guts 'ProdMatchExp

      let restTy = pairWrap pairTyCon restTys

      rest <- go body pairTyCon repTyCon restTys xs

      ty1Dict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [ty1]) 
      restTyDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [restTy])

      abs'd <- abstractOver guts x rest

      return (Var prodMatchId
        :@ Type ty1
        :@ Type restTy
        :@ Type resultTy
        :@ ty1Dict
        :@ restTyDict
        :@ abs'd)

    go body pairTyCon repTyCon tys xs = do
      dflags <- lift $ getDynFlags

      error $ "transformProdMatch.go: (" ++ showPpr dflags tys ++ ", " ++ showPpr dflags xs ++ ")\n" -- ++ showPpr dflags body

    pairWrap pairTyCon = foldr1 (\x acc -> mkTyConApp pairTyCon [x, acc])

-- | GPUExp t  ==>  t
-- and GPURepTy t  ==>  t
-- otherwise, it stays the same
unwrapExpType :: ModGuts -> Type -> CoreM Type
unwrapExpType guts ty = do
  expTyCon <- findTyConTH guts ''GPUExp
  repTyTyCon <- findTyConTH guts ''GPURepTy

  let ty' = case splitTyConApp_maybe ty  of
              Nothing -> ty
              Just (tyCon, args) ->
                if tyCon == expTyCon
                  then head args
                  else ty

  case splitTyConApp_maybe ty' of
    Just (tyCon, args)
      | tyCon == repTyTyCon -> return (head args)
    _ -> return ty'



transformSumMatch :: ModGuts -> (Expr Var -> MatchM (Expr Var)) -> Expr Var -> Var -> Type -> [Alt Var] -> MatchM (Expr Var)

transformSumMatch guts mark scrutinee wild resultTy alts@(alt1@(DataAlt dataAlt1, _, _):_) = do

  dynFlags <- lift $ getDynFlags

  repTyCon <- lift $ findTyConTH guts ''GPURep

  eitherTyCon <- lift $ findTyConTH guts ''Either

  scrTy <- lift $ unwrapExpType guts (exprType scrutinee)

  let scrRepTy = mkTyConApp repTyCon [scrTy]

  scrRepTyTy <- lift $ repTyWrap guts scrTy

  (scrTyCo, scrTyNorm) <- lift $ normaliseTypeCo guts scrRepTyTy

  sumTypes <- listTypesWith guts (getName eitherTyCon) scrTyNorm

  nRepType <- lift $ normaliseType' guts scrTy

  sumMatch <- go eitherTyCon repTyCon sumTypes alts


  caseExpId <- lift $ findIdTH guts 'CaseExp


  repTypeDict <- lift $ buildDictionaryT guts scrRepTy

  scrutinee' <- mark scrutinee

  repTyTyCon <- lift $ findTyConTH guts ''GPURepTy

  let scrTyNormRepTy = mkTyConApp repTyTyCon [scrTyNorm]

  (scrTyNormRepTyCo, _) <- lift $ normaliseTypeCo guts scrTyNormRepTy


  return (Var caseExpId
           :@ Type scrTy
           :@ Type scrTyNorm
           :@ Type resultTy
           :@ repTypeDict
           :@ mkEqBox scrTyNormRepTyCo
           :@ mkEqBox scrTyCo
           :@ scrutinee'
           :@ sumMatch)

  where
    go :: TyCon -> TyCon -> [Type] -> [Alt Var] -> MatchM (Expr Var)
    go eitherTyCon repTyCon (ty1:_) [] = do
      emptyMatchId <- lift $ findIdTH guts 'EmptyMatch
      return (Var emptyMatchId :@ Type resultTy)

    go eitherTyCon repTyCon (ty1:_) [x] = do
      prod <- transformProdMatch guts mark resultTy ty1 x
      co <- lift $ repTyCo guts ty1

      oneSumMatchId <- lift $ findIdTH guts 'OneSumMatch

      ty1Dict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [ty1])
      resultTyDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [resultTy])


      return (Var oneSumMatchId
                :@ Type ty1
                :@ Type resultTy
                :@ ty1Dict
                :@ resultTyDict
                :@ mkEqBox co
                :@ prod)

    go eitherTyCon repTyCon allTys@(ty1:restTys) (x:xs) = do
      dflags <- lift $ getDynFlags

      prod <- transformProdMatch guts mark resultTy ty1 x

      let restTy = eitherWrap eitherTyCon restTys

      co <- lift $ repTyCo guts restTy

      restSum <- go eitherTyCon repTyCon restTys xs

      sumMatchId <- lift $ findIdTH guts 'SumMatchExp


      let Pair coB coA = coercionKind co


      dictA <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [ty1])
      dictB <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [restTy])

      ty1' <- lift $ repTyUnwrap guts ty1
      restTy' <- lift $ repTyUnwrap guts restTy

      return (Var sumMatchId
                :@ Type ty1'
                :@ Type restTy'
                :@ Type resultTy
                :@ dictA
                :@ dictB
                :@ mkEqBox co
                :@ prod
                :@ restSum)


    eitherWrap eitherTyCon = foldr1 (\x acc -> mkTyConApp eitherTyCon [x, acc])

noDoneOrStep :: ModGuts -> CoreExpr -> MatchM Bool
noDoneOrStep guts e = do
  (_, an) <- runWriterT (Data.transformM go e)
  case an of
    Any b -> return $ not b
  where
    go :: CoreExpr -> WriterT Any MatchM CoreExpr
    go expr@(Var f) = do
      doneId <- lift $ lift $ findIdTH guts 'Done
      stepId <- lift $ lift $ findIdTH guts 'Step

      tell (Any (f == doneId || f == stepId))
      return expr
    go expr = return expr

-- TODO: Handle polymorphic functions
transformTailRec :: ModGuts -> Var -> CoreExpr -> MatchM CoreExpr
transformTailRec guts recVar e0 = do
    dflags <- getDynFlags
    go0 e0
  where
    recName = varName recVar

    go0 :: CoreExpr -> MatchM CoreExpr
    go0 (Lam v body) = go1 (varType v) v body
    go0 e = return e

    go1 :: Type -> Var -> CoreExpr -> MatchM CoreExpr
    go1 ty lamV expr@(Var f :@ Type fTyArg :@ fDict :@ x) = do
      dflags <- lift $ getDynFlags
      internalizeId <- lift $ findIdTH guts 'internalize

      if f == internalizeId
        then do
          x' <- go2 ty lamV x

          let newTy = mkFunTy ty fTyArg

          repTyCon <- lift $ findTyConTH guts ''GPURep

          newDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [newTy])

          return (Var f :@ Type newTy :@ newDict :@ x')
        else return expr
    go1 ty _ e = return e

    go2 :: Type -> Var -> CoreExpr -> MatchM CoreExpr
    go2 ty lamV expr@(Var f :@ fTyArg :@ fDict :@ x) = do
      dflags <- lift $ getDynFlags
      externalizeId <- lift $ findIdTH guts 'externalize

      if f == externalizeId
        then do
          (x', tyMaybe) <- runWriterT (Data.transformM (go ty) x)
          case tyMaybe of
            First Nothing -> return expr
            First (Just resultTy) -> do
              runIterId <- lift $ findIdTH guts 'runIter
              repTyCon <- lift $ findTyConTH guts ''GPURep

              resultTyDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [resultTy])
              tyDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [ty])

              theLam <- abstractOver guts lamV x'

              return (Var f :@ fTyArg :@ fDict :@
                        (Var runIterId :@ Type resultTy :@ Type ty :@ resultTyDict :@ tyDict :@ theLam))

        else return expr
    go2 ty lamV e = return e

    go :: Type -> CoreExpr -> WriterT (First Type) MatchM CoreExpr
    go argTy (Case scrutinee wild ty alts) = do
      tell (First (Just ty))
      iterTyCon <- lift $ lift $ findTyConTH guts ''Iter
      let ty' = mkTyConApp iterTyCon [ty, argTy]

      alts' <- lift $ mapM (handleAlt ty argTy) alts

      return (Case
                scrutinee
                wild
                ty'
                alts')
    go argTy expr = return expr

    handleAlt :: Type -> Type -> Alt Var -> MatchM (Alt Var)
    handleAlt tyA tyB alt@(altCon, patVars, body)
      | hasRec recName body = do
          body' <- Data.transformM (replaceRecName tyA tyB) body
          return (altCon, patVars, body')
      | otherwise = do
          doneId <- lift $ findIdTH guts 'Done

          isValid <- noDoneOrStep guts body
          if isValid
            then return (altCon, patVars, Var doneId :@ Type tyA :@ Type tyB :@ body)
            else return alt

    replaceRecName tyA tyB (Var v)
       | varName v == recName = do
          stepId <- lift $ findIdTH guts 'Step

          return (Var stepId :@ Type tyA :@ Type tyB)
    replaceRecName tyA tyB e = return e

-- TODO: Does this correctly handle shadowing?
hasRec :: Name -> CoreExpr -> Bool
hasRec recName = getAny . execWriter . Data.transformM go
  where
    go :: CoreExpr -> Writer Any CoreExpr
    go expr@(Var f :@ _)
      | varName f == recName = do
        tell (Any True)
        pure expr
    go expr = pure expr


transformLams :: ModGuts -> (Expr Var -> MatchM (Expr Var)) -> Expr Var -> MatchM (Expr Var)
transformLams guts mark e0 = Data.transformM go e0
  where
    go :: Expr Var -> MatchM (Expr Var)
    go expr@(Lam arg body) = do
      dflags <- lift getDynFlags

      exprTyCon <- lift $ findTyConTH guts ''GPUExp

      exprTypedBody <- hasExprType guts body

      let exprTypedArg = isExprTy exprTyCon (varType arg)

      if {- exprTypedBody && -} exprTypedArg
        then do
          uniq <- newUnique

          lamName <- lift $ findIdTH guts 'Expr.Lam

          body' <- lift $ subst arg uniq body

          argTy' <- lift $ unwrapExpType guts (varType arg)
          bodyTy' <- lift $ unwrapExpType guts (exprType body')

          -- liftIO $ putStrLn $ "(argTy', bodyTy') = " ++ showPpr dflags (argTy', bodyTy')

          iHash <- lift $ findIdTH guts 'GHC.Types.I#

          let nameInt =  (Lit (LitNumber LitNumInt (fromIntegral uniq) intTy))

          return (Var lamName :@ Type bodyTy' :@ Type argTy' :@ nameInt :@ body')
        else return expr

    go expr = return expr

    subst name uniq = Data.transformM (subst0 name uniq)

    subst0 name uniq (Var name')
      | name' == name = do

        varName <- findIdTH guts 'Expr.Var
        intTy <- findTypeTH guts ''Int

        varTy' <- unwrapExpType guts (varType name)

        iHash <- findIdTH guts 'GHC.Types.I#

        let nameInt =  (Lit (LitNumber LitNumInt (fromIntegral uniq) intTy))

        typeableTyCon <- findTyConTH guts ''Typeable'
        typeableDict <- buildDictionaryT guts (mkTyConApp typeableTyCon [varTy'])

        return (Var varName :@ Type varTy' :@ typeableDict :@ nameInt)
    subst0 _ _ expr = return expr



-- e  ==>  (\x -> e)     {where x is a free variable in e}
-- Also transforms the type of x :: T to x :: GPUExp T
-- TODO: Make sure there aren't any issues with this type transformation
-- and foralls, etc.

abstractOver :: ModGuts -> Var -> Expr Var -> MatchM (Expr Var)
abstractOver guts v e = do
  expTyCon <- lift $ findTyConTH guts ''GPUExp
  repTyCon <- lift $ findTyConTH guts ''GPURep
  typeableTyCon <- lift $ findTyConTH guts ''Typeable'
  intTy <- lift $ findTypeTH guts ''Int

  -- lamFnId <- lift $ findIdTH guts 'Expr.lam

  lamId <- lift $ findIdTH guts 'Expr.Lam
  varId <- lift $ findIdTH guts 'Expr.Var
  nameId <- lift $ findIdTH guts 'Expr.Name

  uniq <- newUnique

  typeableDict <- lift $ buildDictionaryT guts (mkTyConApp typeableTyCon [varType v])

  let origTy = varType v
      newTy = mkTyConApp expTyCon [origTy]
      nameInt = Lit (LitNumber LitNumInt (fromIntegral uniq) intTy)
      nameVal = Var nameId :@ Type origTy :@ nameInt
      v' = setVarType v newTy

  eTy' <- lift $ unwrapExpType guts (exprType e)

  dflags <- getDynFlags
  liftIO $ putStrLn $ "varType v = " ++ showPpr dflags (varType v)

  repDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [varType v])

  markedE' <- mark0 guts (Data.transform (go varId newTy) e)

  return (Var lamId :@ Type origTy :@ Type eTy' :@ repDict :@ typeableDict :@ nameVal
            :@ ((Lam v' markedE') :@ (Var varId :@ Type origTy :@ typeableDict :@ nameVal)))
  where
    go varId newTy (Var v')
      | varName v' == varName v = Var $ setVarType v' newTy
    go varId newTy e = e
    -- -- Set var type in rest of expression
    -- go varId dict name origTy (Var v')
    --   | varName v' == varName v = Var varId :@ Type origTy :@ dict :@ name--Var $ setVarType v' newTy
    -- go varId dict name origTy expr = expr

-- | listTypesWith (lookupVar ''(,)) (a, (b, c))  ==>  [a, b, c]
-- listTypesWith (lookupVar ''Either) (Either a (Either b c))  ==>  [a, b, c]
listTypesWith :: ModGuts -> Name -> Type -> MatchM [Type]
listTypesWith guts n = go <=< (Data.transformM normaliseGenerics) -- <=< (fmap snd . topNormaliseType' guts)
  where
    normaliseGenerics :: Type -> MatchM Type
    normaliseGenerics ty = do

      repTyCon <- lift $ findTyConTH guts ''GPURepTy
      m1TyCon <- lift $ findTyConTH guts ''M1

      case splitTyConApp_maybe ty of
        Just (repTyConPossible, (arg:_))
          | repTyConPossible == repTyCon
            -> case splitTyConApp_maybe arg of
                   Just (m1TyConPossible, _)
                     | m1TyConPossible == m1TyCon
                        || m1TyConPossible == repTyCon -- Collapse GPURepTy's
                          -> lift $ normaliseType' guts ty
                   _ -> return ty
        _ -> return ty


    go ty =
      case splitTyConApp_maybe ty of
        Nothing -> return [ty]
        Just (tyCon, [a, b])
          | tyConName tyCon /= n -> return [ty]
          | otherwise ->
              fmap (a:) (go b)
        Just _ -> return [ty]


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
  ,('fromInteger, 'deepFromInteger)
  ,('sqrt, 'Sqrt)

  ,('False, 'FalseExp)
  ,('True, 'TrueExp)

  ,('(+), 'Add)
  ,('(*), 'Mul)
  ,('(-), 'Sub)
  ,('(==), 'Equal)
  ,('(<=), 'Lte)
  ,('(>), 'Gt)

  ,('runIter, 'TailRec)
  ,('Done, 'DoneExp)
  ,('Step, 'StepExp)
  ]

getGPUExprNamedsFrom :: [(TH.Name, Named)] -> TH.Name -> Named
getGPUExprNamedsFrom namedMap name =
  case lookup name namedMap of
    Nothing -> error $ "Cannot find Named for: " ++ show name
    Just i  -> i


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


topNormaliseType' :: ModGuts -> Type -> CoreM (Coercion, Type)
topNormaliseType' guts ty = (secondM (collapseRepTys guts) =<<) $ do
  dflags <- getDynFlags

  runTcM guts . fmap fst . runTcS $ do
    famInstEnvs <- getFamInstEnvs
    
    case topNormaliseType_maybe famInstEnvs ty of
      Nothing -> return (normaliseType famInstEnvs Nominal ty)
      Just (co, ty')  ->
        case setNominalRole_maybe (coercionRole co) co of
          Just co' -> return (co', ty')
          Nothing -> return (co, ty')

-- | GPURepTy (GPURepTy a)  ==>  GPURepTy a
collapseRepTys :: ModGuts -> Type -> CoreM Type
collapseRepTys guts = Data.transformM go
  where
    go ty = do
      repTyTyCon <- findTyConTH guts ''GPURepTy

      case splitTyConApp_maybe ty of
        Just (tyCon, [arg])
          | tyCon == repTyTyCon ->
              case splitTyConApp_maybe arg of
                Just (tyCon', [arg'])
                  | tyCon' == repTyTyCon -> return arg
                _ -> return ty
        _ -> return ty



-- | Wrap in GPURepTy if it isn't already wrapped in a GPURepTy
repTyWrap :: ModGuts -> Type -> CoreM Type
repTyWrap guts ty = do
  repTyTyCon <- findTyConTH guts ''GPURepTy

  case splitTyConApp_maybe ty of
    Just (tyCon, _)
      | tyCon == repTyTyCon -> return ty
    _                       -> return (mkTyConApp repTyTyCon [ty])

-- | GPURepTy a  ==>  a
repTyUnwrap  :: ModGuts -> Type -> CoreM Type
repTyUnwrap guts ty = do
  repTyTyCon <- findTyConTH guts ''GPURepTy

  case splitTyConApp_maybe ty of
    Just (tyCon, [arg])
      | tyCon == repTyTyCon -> return arg
    _ -> return ty

-- | Splits: fVar @ty1 @ty2 ... @tyN $fdict1 ... $fdictM    (where fVar is a Var)
splitTypeApps_maybe :: Expr a -> Maybe (Var, [Type], [Var])
splitTypeApps_maybe (lhs0 :@ x) =
  case x of
    Type tyN -> do --fmap (second (reverse . (tyN:))) (go lhs0)
          (f, tys, dicts) <- go lhs0
          return (f, reverse (tyN:tys), reverse dicts)
    Var d
      | True <- isDictVar d -> do
          (f, tys, dicts) <- goDicts lhs0
          return (f, reverse tys, reverse (d:dicts))
    _ -> Nothing
  where
    go (Var f)            = Just (f, [], [])
    go (Var f :@ Type ty) = Just (f, [ty], [])

    go (Var f :@ _)       = Nothing

    go (lhs   :@ Type ty) = do
          (f, tys, dicts) <- go lhs
          return (f, ty:tys, dicts)


    go _                  = Nothing


    goDicts (Var f)          = Just (f, [], [])
    goDicts (Var f :@ Var d)
      | True <- isDictVar d  = Just (f, [], [d])
    goDicts (lhs   :@ Var d)
      | True <- isDictVar d  = do
          (f, tys, dicts) <- goDicts lhs
          return (f, tys, d:dicts)

    goDicts expr@(_lhs :@ Type _ty) = go expr

splitTypeApps_maybe _ = Nothing

   

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
  where
    k = tcTypeKind ty1
    Pair ty1 ty2 = coercionKind co

-- Modified from CoreMonad
bindsOnlyPass_match :: (CoreProgram -> MatchM CoreProgram) -> ModGuts -> MatchM ModGuts
bindsOnlyPass_match pass guts
  = do { binds' <- pass (mg_binds guts)
       ; return (guts { mg_binds = binds' }) }

