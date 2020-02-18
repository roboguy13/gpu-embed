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

import           Data.Data hiding (TyCon (..), tyConName, mkFunTy)
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

import           Control.Arrow ((&&&), (***), first, second)

import           GHC.Generics

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
                  return (from, Var to))


  dflags <- getDynFlags


  bindsOnlyPass (mapM (transformBind guts (mg_inst_env guts) primMap)) guts

-- TODO: Figure out what, specifically, this is a workaround for and
-- actually fix the underlying problem.
hasExternalize :: ModGuts -> Expr Var -> CoreM Bool
hasExternalize guts e = do
  (_, a) <- runWriterT (Data.transformM go e)
  case a of
    Any b -> return b
  where
    go :: Expr Var -> WriterT Any CoreM (Expr Var)
    go expr@(Var f) = do
      externalizeId <- lift $ findIdTH guts 'externalize

      if f == externalizeId
        then tell (Any True) >> return expr
        else return expr
    go expr = return expr

transformBind :: ModGuts -> InstEnv -> [(Id, CoreExpr)] -> CoreBind -> CoreM CoreBind
transformBind guts instEnv primMap (NonRec name e) =
  fmap (NonRec name) (transformExpr guts Nothing primMap e)
transformBind guts instEnv primMap (Rec bnds) = Rec <$> mapM go bnds
  where
    go :: (Var, Expr Var) -> CoreM (Var, Expr Var)
    go (name, e) = do
      hasEx <- hasExternalize guts e
      if hasEx
        then do
          dflags <- getDynFlags
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
transformExprMaybe :: ModGuts -> Maybe Var -> [(Id, CoreExpr)] -> Expr Var -> CoreM (Maybe (Expr Var))
transformExprMaybe guts  recName primMap e = do
  (r, progress) <- runWriterT (Data.transformM go e)
  case progress of
    Any False -> return Nothing
    Any True  -> return $ Just r
  where

    go :: CoreExpr -> WriterT Any CoreM CoreExpr
    go expr@(Var f :@ _ty :@ _dict :@ x) = do
      dflags <- getDynFlags
      externalizeId <- lift $ findIdTH guts 'externalize

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

transformExpr :: ModGuts -> Maybe Var -> [(Id, CoreExpr)] -> Expr Var -> CoreM (Expr Var)
transformExpr guts recNameM primMap =
  untilNothingM (transformExprMaybe guts recNameM primMap)

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
transformPrims :: ModGuts -> Maybe Var -> [(Id, CoreExpr)] -> Expr Var -> CoreM (Expr Var)
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
hasExprType :: ModGuts -> CoreExpr -> CoreM Bool
hasExprType guts e = do
  expTyCon <- findTyConTH guts ''GPUExp

  return $ hasExprTy' expTyCon e

hasExprTy' :: TyCon -> CoreExpr -> Bool
hasExprTy' expTyCon e =
  case splitTyConApp_maybe (exprType e) of
    Nothing -> False
    Just (t, _) -> t == expTyCon

whenNotExprTyped :: ModGuts -> CoreExpr -> CoreM CoreExpr -> CoreM CoreExpr
whenNotExprTyped guts e m = do
  eType <- hasExprType guts e
  if eType
    then return e
    else m

isVar :: Expr a -> Bool
isVar (Var _) = True
isVar _ = False

-- 'exprVars' are already of GPUExp type and do not need to be modified
transformPrims0 :: ModGuts -> Maybe Var -> [(Id, CoreExpr)] -> [Expr Var] -> Expr Var -> CoreM (Expr Var)
transformPrims0 guts recName primMap exprVars = go
  where
    builtin :: Id -> Maybe (Expr Var)
    builtin v = lookup v primMap

    -- Mark for further transformation
    mark x = do
      eType <- hasExprType guts x
      if eType
        then return x
        else do
          let xTy = exprType x

          externalizeName <- findIdTH guts 'externalize

          repTyCon <- findTyConTH guts ''GPURep

          dict <- buildDictionaryT guts (mkTyConApp repTyCon [xTy])

          return (Var externalizeName :@ Type xTy :@ dict :@ x)


    replaceVarType0 v ty expr@(Var v')
      | varName v == varName v' = Var $ setVarType v' ty
      | otherwise = expr
    replaceVarType0 v ty expr = expr

    replaceVarType v ty = Data.transform (replaceVarType0 v ty)

    go (Case scrutinee wild ty alts) = do
      dflags <- getDynFlags

      falseId <- findIdTH guts 'False
      trueId <- findIdTH guts 'True
      iteId <- findIdTH guts 'IfThenElse
 
      boolTyCon <- findTyConTH guts ''Bool

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
      expTyCon <- findTyConTH guts ''GPUExp

      let ty = mkTyConApp expTyCon [varType v]

      bodyMarked <- mark (replaceVarType v ty body)

      return (Lam (setVarType v ty) bodyMarked)

    -- Numeric literals
    go expr@(Lit x :@ ty :@ dict) = do
      dflags <- getDynFlags
      litId <- findIdTH guts 'Lit
      return (Var litId :@ ty :@ dict :@ expr)

    go (Var v)
      | Just b <- builtin v = return b

    go expr@(Var v)
      | False <- isFunTy (varType v) = whenNotExprTyped guts expr $ do
          constructId <- findIdTH guts 'Construct
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
        numTyCon <- findTyConTH guts ''Num
        intTy <- findTypeTH guts ''Int
        numDict <- buildDictionaryT guts (mkTyConApp numTyCon [intTy])

        litId <- findIdTH guts 'Expr.Lit
        return (Var litId :@ Type intTy :@ numDict :@ expr)

      | "D#" <- occNameString (occName f) = do
        numTyCon <- findTyConTH guts ''Num
        doubleTy <- findTypeTH guts ''Double
        numDict <- buildDictionaryT guts (mkTyConApp numTyCon [doubleTy])

        litId <- findIdTH guts 'Expr.Lit
        return (Var litId :@ Type doubleTy :@ numDict :@ expr)
    
      | "F#" <- occNameString (occName f) = do
        numTyCon <- findTyConTH guts ''Num
        floatTyCon <- findTyConTH guts ''Float
        dflags <- getDynFlags
        let floatTy = mkTyConApp floatTyCon []
        numDict <- buildDictionaryT guts (mkTyConApp numTyCon [floatTy])

        litId <- findIdTH guts 'Expr.Lit
        return (Var litId :@ Type floatTy :@ numDict :@ expr)

    go expr@(Var f :@ x)
      | not (isTypeArg x) && 
        not (isDerivedOccName (occName f)) && last (occNameString (occName f)) /= '#',
        Just (aTy, bTy) <- splitFunTy_maybe (varType f) = 
          whenNotExprTyped guts expr $ do

        repTyCon <- findTyConTH guts ''GPURep


        dflags <- getDynFlags

        repDict <- buildDictionaryT guts (mkTyConApp repTyCon [aTy])

        constructAp <- findIdTH guts 'ConstructAp

        f' <- constructExpr guts f

        markedX <- mark x

        return  (Var constructAp :@ Type aTy :@ Type bTy :@ repDict :@ f' :@ markedX)

    go expr@(lhs :@ arg)
      | not (isVar lhs) && not (isDict lhs) && not (isDict arg),
        Just (aTy, bTy) <- splitFunTy_maybe (exprType lhs) = whenNotExprTyped guts expr $ do
          constructAp <- findIdTH guts 'ConstructAp

          repTyCon <- findTyConTH guts ''GPURep

          dflags <- getDynFlags

          repDict <- buildDictionaryT guts (mkTyConApp repTyCon [aTy])

          markedLhs <- mark lhs
          markedArg <- mark arg

          return (Var constructAp :@ Type aTy :@ Type bTy :@ repDict :@ markedLhs :@ markedArg)

    go expr
      | Just (fId, tyArgs, dicts) <- splitTypeApps_maybe expr = whenNotExprTyped guts expr $ do
          constructId <- findIdTH guts 'Construct

          let expr' = mkTyApps (Var fId) tyArgs
              expr'' = mkApps expr' (map Var dicts)

          return (Var constructId :@ Type (exprType expr'') :@ expr'')

    go expr = return expr

transformProdMatch :: ModGuts -> (Expr Var -> CoreM (Expr Var)) -> Type -> Type -> Alt Var -> CoreM (Expr Var)
transformProdMatch guts transformPrims' resultTy ty0 (altCon@(DataAlt dataAlt), vars0, body0) = do
  repTyCon <- findTyConTH guts ''GPURep

  repType <- computeRepType guts ty0

  pairTyCon <- findTyConTH guts ''(,)
  prodTypes <- listTypesWith guts (getName pairTyCon) repType

  dflags <- getDynFlags


  body <- transformPrims' body0


  go body pairTyCon repTyCon prodTypes vars0
  where
    go body pairTyCon repTyCon (ty1:_) [] = do
      nullaryMatchId <- findIdTH guts 'NullaryMatch

      resultTyDict <- buildDictionaryT guts (mkTyConApp repTyCon [resultTy])

      return (Var nullaryMatchId :@ Type ty1 :@ Type resultTy :@ resultTyDict :@ body)

    go body pairTyCon repTyCon allTys@(ty1:_) [x] = do
      dflags <- getDynFlags

      let ty = pairWrap pairTyCon allTys

      oneProdMatchId <- findIdTH guts 'OneProdMatch

      tyDict <- buildDictionaryT guts (mkTyConApp repTyCon [ty])

      abs'd <- abstractOver guts x body

      return (Var oneProdMatchId :@ Type ty :@ Type resultTy :@ tyDict :@ abs'd)

    go body pairTyCon repTyCon (ty1:restTys) (x:xs) = do
      dflags <- getDynFlags

      prodMatchId <- findIdTH guts 'ProdMatch

      let restTy = pairWrap pairTyCon restTys

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

    go body pairTyCon repTyCon tys xs = do
      dflags <- getDynFlags

      error $ "(" ++ showPpr dflags tys ++ ", " ++ showPpr dflags xs ++ ")\n" -- ++ showPpr dflags body

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



transformSumMatch :: ModGuts -> (Expr Var -> CoreM (Expr Var)) -> Expr Var -> Var -> Type -> [Alt Var] -> CoreM (Expr Var)

transformSumMatch guts transformPrims' scrutinee wild resultTy alts@(alt1@(DataAlt dataAlt1, _, _):_) = do

  dynFlags <- getDynFlags

  repTyCon <- findTyConTH guts ''GPURep

  eitherTyCon <- findTyConTH guts ''Either

  scrTy <- unwrapExpType guts (exprType scrutinee)

  let scrRepTy = mkTyConApp repTyCon [scrTy]

  scrRepTyTy <- repTyWrap guts scrTy

  (scrTyCo, scrTyNorm) <- normaliseTypeCo guts scrRepTyTy

  sumTypes <- listTypesWith guts (getName eitherTyCon) scrTyNorm

  nRepType <- normaliseType' guts scrTy

  sumMatch <- go eitherTyCon repTyCon sumTypes alts


  caseExpId <- findIdTH guts 'CaseExp


  repTypeDict <- buildDictionaryT guts scrRepTy

  scrutinee' <- transformPrims' scrutinee


  return (Var caseExpId
           :@ Type scrTy
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
      prod <- transformProdMatch guts transformPrims' resultTy ty1 x
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

      prod <- transformProdMatch guts transformPrims' resultTy ty1 x

      let restTy = eitherWrap eitherTyCon restTys

      co <- repTyCo guts restTy

      restSum <- go eitherTyCon repTyCon restTys xs

      sumMatchId <- findIdTH guts 'SumMatch


      let Pair coB coA = coercionKind co


      dictA <- buildDictionaryT guts (mkTyConApp repTyCon [ty1])
      dictB <- buildDictionaryT guts (mkTyConApp repTyCon [restTy])

      ty1' <- repTyUnwrap guts ty1
      restTy' <- repTyUnwrap guts restTy

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

noDoneOrStep :: ModGuts -> CoreExpr -> CoreM Bool
noDoneOrStep guts e = do
  (_, an) <- runWriterT (Data.transformM go e)
  case an of
    Any b -> return $ not b
  where
    go :: CoreExpr -> WriterT Any CoreM CoreExpr
    go expr@(Var f) = do
      doneId <- lift $ findIdTH guts 'Done
      stepId <- lift $ findIdTH guts 'Step

      tell (Any (f == doneId || f == stepId))
      return expr
    go expr = return expr

-- TODO: Handle polymorphic functions
transformTailRec :: ModGuts -> Var -> CoreExpr -> CoreM CoreExpr
transformTailRec guts recVar e0 = do
    dflags <- getDynFlags
    go0 e0
  where
    recName = varName recVar

    go0 :: CoreExpr -> CoreM CoreExpr
    go0 (Lam v body) = go1 (varType v) v body
    go0 e = return e

    go1 :: Type -> Var -> CoreExpr -> CoreM CoreExpr
    go1 ty lamV expr@(Var f :@ Type fTyArg :@ fDict :@ x) = do
      dflags <- getDynFlags
      internalizeId <- findIdTH guts 'internalize

      if f == internalizeId
        then do
          x' <- go2 ty lamV x

          let newTy = mkFunTy ty fTyArg

          repTyCon <- findTyConTH guts ''GPURep


          newDict <- buildDictionaryT guts (mkTyConApp repTyCon [newTy])

          return (Var f :@ Type newTy :@ newDict :@ x')
        else return expr
    go1 ty _ e = return e

    go2 :: Type -> Var -> CoreExpr -> CoreM CoreExpr
    go2 ty lamV expr@(Var f :@ fTyArg :@ fDict :@ x) = do
      dflags <- getDynFlags
      externalizeId <- findIdTH guts 'externalize

      if f == externalizeId
        then do
          (x', tyMaybe) <- runWriterT (Data.transformM (go ty) x)
          case tyMaybe of
            First Nothing -> return expr
            First (Just resultTy) -> do
              runIterId <- findIdTH guts 'runIter
              repTyCon <- findTyConTH guts ''GPURep

              resultTyDict <- buildDictionaryT guts (mkTyConApp repTyCon [resultTy])
              tyDict <- buildDictionaryT guts (mkTyConApp repTyCon [ty])

              return (Var f :@ fTyArg :@ fDict :@
                        (Var runIterId :@ Type resultTy :@ Type ty :@ resultTyDict :@ tyDict :@ Lam lamV x'))

        else return expr
    go2 ty lamV e = return e

    go :: Type -> CoreExpr -> WriterT (First Type) CoreM CoreExpr
    go argTy (Case scrutinee wild ty alts) = do
      tell (First (Just ty))
      iterTyCon <- lift $ findTyConTH guts ''Iter
      let ty' = mkTyConApp iterTyCon [ty, argTy]

      alts' <- lift $ mapM (handleAlt ty argTy) alts

      return (Case
                scrutinee
                wild
                ty'
                alts')
    go argTy expr = return expr

    handleAlt :: Type -> Type -> Alt Var -> CoreM (Alt Var)
    handleAlt tyA tyB alt@(altCon, patVars, body)
      | hasRec recName body = do
          body' <- Data.transformM (replaceRecName tyA tyB) body
          return (altCon, patVars, body')
      | otherwise = do
          doneId <- findIdTH guts 'Done

          isValid <- noDoneOrStep guts body
          if isValid
            then return (altCon, patVars, Var doneId :@ Type tyA :@ Type tyB :@ body)
            else return alt

    replaceRecName tyA tyB (Var v)
       | varName v == recName = do
          stepId <- findIdTH guts 'Step

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
listTypesWith guts n = go <=< (Data.transformM normaliseGenerics) -- <=< (fmap snd . topNormaliseType' guts)
  where
    normaliseGenerics :: Type -> CoreM Type
    normaliseGenerics ty = do

      repTyCon <- findTyConTH guts ''GPURepTy
      m1TyCon <- findTyConTH guts ''M1

      case splitTyConApp_maybe ty of
        Just (repTyConPossible, (arg:_))
          | repTyConPossible == repTyCon
            -> case splitTyConApp_maybe arg of
                   Just (m1TyConPossible, _)
                     | m1TyConPossible == m1TyCon
                        || m1TyConPossible == repTyCon -- Collapse GPURepTy's
                          -> normaliseType' guts ty
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

normaliseType' :: ModGuts -> Type -> CoreM Type
normaliseType' guts = fmap snd . normaliseTypeCo guts

normaliseTypeCo :: ModGuts -> Type -> CoreM (Coercion, Type)
normaliseTypeCo guts ty =
  runTcM guts . fmap fst . runTcS $ do
    famInstEnvs <- getFamInstEnvs
    return (normaliseType famInstEnvs Nominal ty)

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

