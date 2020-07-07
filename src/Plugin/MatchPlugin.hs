{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}

module Plugin.MatchPlugin (plugin) where

import           Deep.GHCUtils

import           Deep.Expr hiding (Var, Lit, Lam, (:@), Name, App)
import qualified Deep.Expr as Expr
import           Deep.Delineate

import           Data.Data hiding (TyCon (..), tyConName, mkFunTy)
import           Data.Typeable hiding (TyCon (..), tyConName, mkFunTy)

import           Data.Generics.Uniplate.Operations
import qualified Data.Generics.Uniplate.DataOnly as Data

import           GhcPlugins

import           InstEnv

-- import           Literal (mkMachInt)

import           FamInstEnv

import           TcSMonad

import           CoreUnfold

import           TyCon

import           Inst

import           Pair

import           Coercion

import qualified Data.Kind as Kind

import           Control.Monad
import           Control.Monad.Writer hiding (pass, Alt)
import           Control.Monad.State
import           Control.Applicative

import           Data.Foldable

import           Data.Maybe

import           Control.Arrow ((&&&), (***), first, second)

import           GHC.Generics
import           GHC.Types (Int(..))

-- import           GHCUtils

-- Just for TH Names:
import qualified Language.Haskell.TH.Syntax as TH


import           OccurAnal

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

import           CoreOpt
import           Id

-- import           Data.Typeable.Internal

import Debug.Trace

data PluginState =
  PluginState
    { currUniq :: Int
    , inlinedNames :: [Name] -- | Names inlined so far
    }

newtype UniqueSupply m a = UniqueSupply (StateT Int m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

instance HasDynFlags (UniqueSupply CoreM) where
  getDynFlags = lift getDynFlags

newUnique :: Monad m => UniqueSupply m Int
newUnique = UniqueSupply (modify (+1) *> get)

runUniqueSupply :: Monad m => UniqueSupply m a -> m a
runUniqueSupply (UniqueSupply us) = evalStateT us 0


type MatchM = UniqueSupply CoreM

-- -- | Keeps a list of inlined names, to prevent infinite inlining
-- newtype InlinerM m a = InlinerM (StateT [Name] m a)

-- type MatchM = InlinerM (UniqueSupply CoreM)

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


  runUniqueSupply $ bindsOnlyPass_match (transformBinds guts (mg_inst_env guts) primMap) guts

-- TODO: Figure out what, specifically, this is a workaround for and
-- actually fix the underlying problem.
hasExternalize :: ModGuts -> Expr Var -> MatchM Bool
hasExternalize guts e = do
  (_, Any a) <- runWriterT (Data.transformM go e)
  return a
  where
    go :: Expr Var -> WriterT Any MatchM (Expr Var)
    go expr@(Var f) = do
      externalizeId <- lift $ lift $ findIdTH guts 'externalize

      if f == externalizeId
        then tell (Any True) >> return expr
        else return expr
    go expr = return expr

-- changeAssoc :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
-- changeAssoc x y [] = [(x, y)]
-- changeAssoc x y ((n, e):rest)
--   | n == x    = (x, y) : rest
--   | otherwise = (n, e) : changeAssoc x y rest

-- lookupBind :: Var -> CoreBind -> Maybe CoreBind
-- lookupBind name b@(NonRec v e)
--   | v == name = Just b
-- lookupBind name 

findBind :: Var -> [CoreBind] -> Maybe CoreBind
findBind v [] = Nothing
findBind v (b@(NonRec n e):bs)
  | v == n = Just b
  | otherwise = findBind v bs
findBind v (b@(Rec rs):bs) =
  case lookup v rs of
    Just _ -> Just b
    Nothing -> findBind v bs

changeBind :: [CoreBind] -> CoreBind -> CoreBind
changeBind newBinds b@(NonRec n e) =
  let x = find (\case
                  NonRec n' e'
                    | n' == n -> True
                  _ -> False) newBinds
  in
  case x of
    Just r -> r
    Nothing -> b

changeBind newBinds b@(Rec rs) = Rec (map go rs)
  where
    go (n, e) =
      let x = mapMaybe (\case
                      Rec rs' ->
                        case lookup n rs' of
                          Just b' -> Just (n, b')
                          _ -> Nothing
                      _ -> Nothing) newBinds
      in
      case x of
        (r:_) -> r
        [] -> (n, e)



transformBinds :: ModGuts -> InstEnv -> [(Id, CoreExpr)] -> [CoreBind] -> MatchM [CoreBind]
transformBinds guts instEnv primMap binds = do
  (binds2, changedBinds) <- runWriterT $ mapM go0 binds

  let new_mg_binds = map (changeBind changedBinds) (mg_binds guts)

  mapM (go1 new_mg_binds) binds2
  where
    go0 :: CoreBind -> WriterT [CoreBind] MatchM CoreBind
    go0 b@(NonRec {}) = pure b
    go0 (Rec r) = do
      (x, bs) <- lift $ runWriterT
                  $ forM r
                  $ \ (name, e) -> do
                      hasEx <- lift $ hasExternalize guts e
                      if hasEx
                        then do
                          r <- (name,) <$> lift (transformTailRec guts name e)
                          tell [r]
                          return r
                        else return (name, e)

      tell [Rec bs]
      return (Rec x)

    go1 new_mg_binds (NonRec name e) = do
      hasEx <- hasExternalize guts e
      if hasEx
        then
          fmap (NonRec name) (transformExpr (guts {mg_binds = new_mg_binds}) name Nothing primMap e)
        else return (NonRec name e)

    go1 new_mg_binds (Rec r) = fmap Rec $
      forM r $ \ (name, e) -> do
        hasEx <- hasExternalize guts e
        if hasEx
          then do
            dflags <- lift getDynFlags
            (name,) <$> transformExpr (guts {mg_binds = new_mg_binds}) name (Just name) primMap e
          else return (name, e)

changed :: Monad m => WriterT Any m ()
changed = tell (Any True)

returnChanged :: Monad m => a -> WriterT Any m a
returnChanged x = do
  changed
  return x

-- -- TODO: Figure out why this is needed to mitigate an out-of-scope type variable issue in a coercion
-- removeExpVarOnlyCoercion :: DynFlags -> Coercion -> Coercion
-- removeExpVarOnlyCoercion dflags = Data.transform go
--   where
--     go co
--       | Just (ty, role) <- isReflCo_maybe co
--       , Just (tyF, tyArg) <- splitAppTy_maybe ty
--       , isTyVarTy tyArg
--         = trace ("coercion type var: " ++ showPpr dflags tyArg) co
--     go co = co


-- | 'Nothing' indicates that no changes were made
transformExprMaybe :: ModGuts -> Var -> Maybe Var -> [(Id, CoreExpr)] -> Expr Var -> MatchM (Maybe (Expr Var))
transformExprMaybe guts currName recName primMap e = do
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
          lift $ transformPrims guts currName recName primMap x
        else return expr
    go expr = return expr

transformExpr :: ModGuts -> Var -> Maybe Var -> [(Id, CoreExpr)] -> Expr Var -> MatchM (Expr Var)
transformExpr guts currName recNameM primMap e = do
  dflags <- lift getDynFlags
  {- Data.transform (onCoercion (removeExpVarOnlyCoercion dflags)) <$> -}

  {- updateUnitTypeProofs guts =<< updateTypeProofs guts =<< updateUnitTypeProofs guts =<< -}
  untilNothingM (transformExprMaybe guts currName recNameM primMap) e


-- XXX: The delineation marker probably has to be floated in (or maybe the
-- transformation can just go through the AST at that marker without
-- floating in the marker itself)

-- | Transform primitives and constructor/function calls. Skips the
-- function call transformation on the given 'recName' argument (if
-- a 'Just').
transformPrims :: ModGuts -> Var -> Maybe Var -> [(Id, CoreExpr)] -> Expr Var -> MatchM (Expr Var)
transformPrims guts currName recName primMap = tr
  where
    tr = transformPrims0 guts currName recName primMap []


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
mark0 :: HasCallStack => ModGuts -> Expr Var -> MatchM (Expr Var)
mark0 _ e@(Type _) = return e
-- mark0 _ e@(Coercion {}) = return e
mark0 guts e@(Var f :@ Type ty :@ dict :@ x) = do
  externalizeName <- lift $ findIdTH guts 'externalize

  if f == externalizeName
    then do
      r <- tryMarkUnrepVar guts x
      case r of
        Just x' -> return x'
        Nothing -> return e
    else do
      r <- tryMarkUnrepVar guts e
      case r of
        Just x' -> return x'
        Nothing -> markIt guts x

mark0 guts x = do
  dflags <- getDynFlags
  -- traceM $ "mark: x = " ++ showPpr dflags x
  r <- tryMarkUnrepVar guts x
  case r of
    Just x' -> return x'
    Nothing -> markIt guts x

tryMarkUnrepVar :: HasCallStack => ModGuts -> Expr Var -> MatchM (Maybe (Expr Var))
-- tryMarkUnrepVar guts e@(Var f :@ Type tyA :@ var@(Var g :@ Type tyB :@ _dict :@ _)) = do
tryMarkUnrepVar guts e@(Var f :@ Type tyA :@ x) = do
  unrepId <- lift $ findIdTH guts 'unrep
  varConId <- lift $ findIdTH guts 'Expr.Var

  dflags <- getDynFlags

  if f == unrepId -- && g == varConId
    then do
      dflags <- getDynFlags

      -- traceM $ "=== mark0 ===> " ++ showPpr dflags var

      -- unconstructRepId <- lift $ findIdTH guts 'UnconstructRep
      -- return (Just (Var unconstructRepId :@ Type tyB :@ var))

      return $ Just x
    else do
      -- traceM $ "=== mark0 ===> " ++ showPpr dflags var
      return Nothing

tryMarkUnrepVar guts e = Just <$> markIt guts e

-- | Mark without special treatment for any 'unrep (Var ...)' expressions
markIt :: HasCallStack => ModGuts -> Expr Var -> MatchM (Expr Var)
markIt guts x = do
  dflags <- getDynFlags
  expTyCon <- lift $ findTyConTH guts ''GPUExp

  -- traceM $ "markIt: " ++ showPpr dflags x

  eType <- hasExprType guts x
  -- traceM $ "markIt x hasExprType: " ++ showPpr dflags eType
  -- liftIO $ putStrLn $ "markIt exprType = " ++ showPpr dflags (exprType x)
  if eType
    then return x
    else
      case splitFunTy_maybe (exprType x) of
        Just (a, b)
          | {- isExprTy expTyCon a && -} isExprTy expTyCon b -> return x
        _ -> markAny guts x

-- | Mark anything that isn't a dictionary
markAny :: HasCallStack => ModGuts -> Expr Var -> MatchM (Expr Var)
markAny guts x = do
  dflags <- getDynFlags
  if isDict x
    then return x
    else do
      let xTy = exprType x

      externalizeName <- lift $ findIdTH guts 'externalize

      repTyCon <- lift $ findTyConTH guts ''GPURep

      dict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [xTy])

      return (Var externalizeName :@ Type xTy :@ dict :@ x)

isConstructor :: Var -> Bool
isConstructor v
  | isId v =
    case idDetails v of
      DataConWorkId {} -> True
      DataConWrapId {} -> True
      _ -> trace ("is not constructor: " ++ occNameString (occName v)) False
  | otherwise = False

getConstructorTyCon_maybe :: Var -> Maybe TyCon
getConstructorTyCon_maybe v
  | isId v = trace ("idDetails: " ++ showSDocUnsafe (ppr (idDetails v))) $
    case idDetails v of
      DataConWorkId dc -> Just $ dataConTyCon dc
      DataConWrapId dc -> Just $ dataConTyCon dc
      -- DataConWorkId dc -> Just $ dataConTyCon dc
      _ -> Nothing
getConstructorTyCon_maybe _ = Nothing

builtinConstructor :: Var -> Bool
builtinConstructor v =
    "I#" == occNameString (occName v)
    || "D#" == occNameString (occName v)
    || "F#" == occNameString (occName v)
    || "C#" == occNameString (occName v)

getConstructorApp_maybe ::
  Expr Var
    -> Maybe
        ( [Expr Var]  -- Type arguments
        , [Expr Var]  -- Dictionary arguments
        , TyCon       -- The TyCon of the type of the constructor
        , Var         -- Constructor name
        , [Expr Var]) -- Constructor arguments
getConstructorApp_maybe e =
  case go e of
    -- Just (_, _, _, []) -> Nothing -- TODO: Do we want this?
    (Just (_, _, _, constr, _))
      | builtinConstructor constr -> Nothing
    r -> r
  where
    go (Var v)
      | Just tyCon <- getConstructorTyCon_maybe v = Just ([], [], tyCon, v, [])
    go (App f x)
      | isTypeArg x = do
          (tys, dicts, tyCon, constr, args) <- go f
          return (x:tys, dicts, tyCon, constr, args)

      | isCoArg x || isDict x = do
          (tys, dicts, tyCon, constr, args) <- go f
          return (tys, x:dicts, tyCon, constr, args)

      | otherwise             = do
          (tys, dicts, tyCon, constr, args) <- go f
          return (tys, dicts, tyCon, constr, x:args)

    go _ = Nothing

isType :: Expr a -> Bool
isType (Type _) = True
isType _ = False

finalResultType :: Type -> Type
finalResultType ty =
  case splitFunTy_maybe ty of
    Nothing -> ty
    Just (_, ty') -> finalResultType ty'

-- | GPUExp (a -> b)  ===>   Just (a, b)
getEmbeddedFnType0 :: TyCon -> ModGuts -> Type -> Maybe (Type, Type)
getEmbeddedFnType0 expTyCon guts t =
    let t' = dropForAlls t
        (_, resultTy0) = splitForAllTys t'
        resultTy = finalResultType resultTy0
    in
    case splitTyConApp_maybe resultTy of
      Just (ex, [fn])
        | ex == expTyCon && isFunTy fn -> Just (splitFunTy fn)
      _ -> Nothing

getEmbeddedFnType :: ModGuts -> Type -> MatchM (Maybe (Type, Type))
getEmbeddedFnType guts t = do
    expTyCon <- lift $ findTyConTH guts ''GPUExp
    return $ getEmbeddedFnType0 expTyCon guts t

isEmbeddedFnType :: ModGuts -> Type -> MatchM Bool
isEmbeddedFnType guts t =
  fmap isJust (getEmbeddedFnType guts t)



-- | mkExprApps f [x, y, z]  =  App (App (App f x') y') z'
-- where x', y', z' are marked versions of x, y and z
mkExprApps :: ModGuts -> CoreExpr -> [CoreExpr] -> MatchM CoreExpr
mkExprApps guts fn0 args0 =
    foldlM go fn0 args0
  where
    go f x = do
      dflags <- getDynFlags
      liftIO $ putStrLn $ "+++++++++ x = " ++ showPpr dflags x
      liftIO $ putStrLn ""
      appId <- lift $ findIdTH guts 'Expr.App

      repTyCon <- lift $ findTyConTH guts ''GPURep

      tyM <- getEmbeddedFnType guts (exprType f)

      case tyM of
        Nothing -> error "mkExprApps"
        Just (tyA, tyB) -> do
          liftIO $ putStrLn $ "(tyA, tyB) = " ++ showPpr dflags (tyA, tyB)
          dictA <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [tyA])

          markedX <- mark0 guts x

          return (Var appId :@ Type tyA :@ Type tyB :@ dictA :@ f :@ markedX)


-- 'exprVars' are already of GPUExp type and do not need to be modified
transformPrims0 :: ModGuts -> Var -> Maybe Var -> [(Id, CoreExpr)] -> [Expr Var] -> Expr Var -> MatchM (Expr Var)
transformPrims0 guts currName recName primMap exprVars e = {- transformLams guts mark <=< -} do

  dflags <- getDynFlags

  -- tailRecId <- lift $ findIdTH guts 'Expr.TailRec
  -- runIterId <- lift $ findIdTH guts 'Expr.runIter
  -- traceM ""
  -- traceM $ "TailRec type: " ++ showPpr dflags (exprType (Var tailRecId))
  -- traceM $ "runIter type: " ++ showPpr dflags (exprType (Var runIterId))
  -- traceM ""

  lamId <- lift $ findIdTH guts 'Expr.Lam
  expTyCon <- lift $ findTyConTH guts ''GPUExp

  fromIntegral <- lift $ findIdTH guts 'fromIntegral
  fromInteger <- lift $ findIdTH guts 'fromInteger
  unrep <- lift $ findIdTH guts 'unrep

  go0 (== unrep) (== fromIntegral) (== fromInteger) expTyCon (== lamId) e
  where
    mark :: HasCallStack => CoreExpr -> MatchM CoreExpr
    mark = mark0 guts

    builtin :: Id -> Maybe (Expr Var)
    builtin v = lookup v primMap



    replaceVarType0 v ty expr@(Var v')
      | varName v == varName v' = Var $ setVarType v' ty
      | otherwise = expr
    replaceVarType0 v ty expr = expr

    replaceVarType v ty = Data.transform (replaceVarType0 v ty)

    go0 isUnrep isFromIntegral isFromInteger expTyCon isLam = go
      where
        hasExprTy = hasExprTy' expTyCon

        mkLit :: TH.Name -> Expr Var -> MatchM (Expr Var)
        mkLit tyName expr = do
            litTy <- lift $ findTypeTH guts tyName
            typeType <- lift $ findTypeTH guts ''Kind.Type

            typeableTyCon <- lift $ findTyConTH guts ''Typeable
            showTyCon <- lift $ findTyConTH guts ''Show
            numTyCon <- lift $ findTyConTH guts ''Num
            intTy <- lift $ findTypeTH guts ''Int

            typeableDict <- lift $ buildDictionaryT guts (mkTyConApp typeableTyCon [typeType, litTy])
            showDict <- lift $ buildDictionaryT guts (mkTyConApp showTyCon [litTy])
            numDict <- lift $ buildDictionaryT guts (mkTyConApp numTyCon [litTy])

            litId <- lift $ findIdTH guts 'Expr.Lit
            return (Var litId :@ Type litTy :@ typeableDict :@ showDict :@ numDict :@ expr)

        go :: Expr Var -> MatchM (Expr Var)
        go (Case scrutinee wild ty alts) = do
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


        -- Numeric literals
        go expr@(Lit x :@ ty@(Type{}) :@ dict)
          | isDict dict = do
          dflags <- lift $ getDynFlags
          litId <- lift $ findIdTH guts 'Lit
          return (Var litId :@ ty :@ dict :@ expr)

        go (Var v)
          | Just b <- builtin v = return b

        go expr@(Lam v e) = abstractOver guts v e

        go expr@(Var v)
          | not (isFunTy (varType v))  -- TODO: Can this be removed?
          , not (hasExprTy expr) = do
              repId <- lift $ findIdTH guts 'rep

              repTyCon <- lift $ findTyConTH guts ''GPURep
              repDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [varType v])

              return (Var repId :@ Type (varType v) :@ repDict :@ expr)

        -- Handle builtins
        go expr@(Var f :@ tyA@(Type{}) :@ tyB@(Type{}) :@ dictA :@ dictB :@ x :@ y)
          | Just b <- builtin f,
            True <- isDict dictA,
            True <- isDict dictB,
            not (hasExprTy expr) = do

              -- TODO: Is the problem that it is ending up as
              -- 'mark (f x) y'? If so, how do we fix it? It is probably
              -- coming in through the inlining.

              runIterId <- lift $ findIdTH guts 'runIter

              tailRecAppId <- lift $ findIdTH guts 'tailRecApp
              dflags <- getDynFlags

              -- x <- unwrapUnconstructRep guts x0
              -- y <- unwrapUnconstructRep guts y0

              markedX <- mark x
              markedY <- mark y

              liftIO $ putStrLn "--------------- Might fire"

              if f == runIterId
                then do
                  liftIO $ putStrLn "+++++++++++++++++++ tailRecApp fired"
                  traceM $ "tyA, tyB: " ++ showPpr dflags (tyA, tyB)
                  return (Var tailRecAppId :@ tyA :@ tyB :@ dictA :@ dictB :@ markedX :@ markedY)
                else
                  return (b :@ tyA :@ tyB :@ dictA :@ dictB :@ markedX :@ markedY)


        go expr@(Var f :@ tyA@(Type{}) :@ tyB@(Type{}) :@ dictA :@ dictB :@ x)
          | Just b <- builtin f,
            True <- isDict dictA,
            True <- isDict dictB,
            not (hasExprTy expr) = do
              markedX <- mark x
              dflags <- getDynFlags

              traceM ""
              traceM $ "here: " ++ showPpr dflags f
              traceM $ "tyA, tyB: " ++ showPpr dflags (tyA, tyB)
              traceM ""

              runIterId <- lift $ findIdTH guts 'runIter
              tailRecAppId <- lift $ findIdTH guts 'tailRecApp

              if f == runIterId
                then
                  -- abstractOver guts
                  return (Var tailRecAppId :@ tyA :@ tyB :@ dictA :@ dictB :@ markedX)
                else
                  return (b :@ tyA :@ tyB :@ dictA :@ dictB :@ markedX)

        go expr@(Var f :@ tyA@(Type tyA') :@ tyB@(Type tyB') :@ dictA :@ dictB :@ x)
           | isFromIntegral f,
             True <- isDict dictA,
             True <- isDict dictB,
             not (hasExprTy expr) = do
               markedX <- mark x

               typeableTyCon <- lift $ findTyConTH guts ''Typeable
               typeType <- lift $ findTypeTH guts ''Kind.Type
               typeableDictA <- lift $ buildDictionaryT guts (mkTyConApp typeableTyCon [typeType, tyA'])
               typeableDictB <- lift $ buildDictionaryT guts (mkTyConApp typeableTyCon [typeType, tyB'])


               fromIntegralConstrId <- lift $ findIdTH guts 'FromIntegral

               return (Var fromIntegralConstrId :@ tyA :@ tyB :@ typeableDictA :@ typeableDictB :@ dictA :@ dictB :@ markedX)

        go expr@(Var f :@ ty@(Type ty') :@ dict :@ x)
          | Just b <- builtin f,
            True <- isDict dict,
            not (hasExprTy expr) = do
              markedX <- mark x
              return (b :@ ty :@ dict :@ markedX)

        go expr@(Var f :@ ty@(Type ty') :@ dict :@ x)
          | isFromInteger f
          , True <- isDict dict
          , not (hasExprTy expr) = do
              fromIntegerId <- lift $ findIdTH guts 'fromInteger
              deepFromIntegerId <- lift $ findIdTH guts 'deepFromInteger


              typeableTyCon <- lift $ findTyConTH guts ''Typeable
              typeType <- lift $ findTypeTH guts ''Kind.Type
              typeableDict <- lift $ buildDictionaryT guts (mkTyConApp typeableTyCon [typeType, ty'])

              markedX <- mark x
              return (Var deepFromIntegerId :@ ty :@ typeableDict :@ dict :@ markedX)

        go expr@(Var f :@ ty@(Type{}) :@ dict :@ x :@ y)
          | Just b <- builtin f,
            True <- isDict dict,
            not (hasExprTy expr) = do
              markedX <- mark x
              markedY <- mark y

              dflags <- getDynFlags
              -- traceM $ "builtin transformed: " ++ showPpr dflags f
              -- traceM $ "===================> " ++ showPpr dflags b

              return (b :@ ty :@ dict :@ markedX :@ markedY)

        go expr@(Var f :@ (Type tyA0) :@ (Type tyB0) :@ x :@ y)
          | Just b <- builtin f,
            not (hasExprTy expr) = do
              markedX <- mark x
              markedY <- mark y

              -- tyA <- lift $ normaliseType' guts tyA0
              -- tyB <- lift $ normaliseType' guts tyB0

              let tyA = tyA0
                  tyB = tyB0

              return (b :@ Type tyA :@ Type tyB :@ markedX :@ markedY)

        go expr@(Var f :@ tyA@(Type{}) :@ tyB@(Type{}) :@ x)
          | Just b <- builtin f,
            not (hasExprTy expr) = do
              dflags <- getDynFlags

              traceM $ "prim: " ++ showPpr dflags f
              traceM $ "^===> " ++ showPpr dflags x

              -- liftIO $ putStrLn ""
              -- liftIO $ putStrLn $ "---------- builtin: " ++ showPpr dflags b
              -- liftIO $ putStrLn $ "---------- arg:     " ++ showPpr dflags x
              -- liftIO $ putStrLn ""
              markedX <- mark x
              return (b :@ tyA :@ tyB :@ markedX)

        -- go expr@(Var f :@ Type tyA :@ (Var g :@ tyB :@ dict :@ x))
        --   | not (hasExprTy expr)
        --   , isDict dict
        --   , Nothing <- getConstructorApp_maybe expr = do
        --       unrepId <- lift $ findIdTH guts 'unrep
        --       when (f == unrepId) $ traceM "found unrep"
        --       return expr

        go expr@(Var f :@ x)
          | Just b <- builtin f
          , not (isDict x)
          , not (isType x)
          , not (hasExprTy expr) = do
              markedX <- mark x
              return (b :@ markedX)

        -- TODO: Handle other literals
        go expr@(Var f :@ x)
          | "I#" <- occNameString (occName f) = mkLit ''Int expr

          | "D#" <- occNameString (occName f) = mkLit ''Double expr

          | "F#" <- occNameString (occName f) = mkLit ''Float expr

          | "C#" <- occNameString (occName f) = do
            charLitId <- lift $ findIdTH guts 'Expr.CharLit

            return (Var charLitId :@ expr)

        -- Handle constructors that are not builtins
        go expr@(_ :@ _)
          | Just (tys, dicts, constrTyCon, constr, args0) <- getConstructorApp_maybe (Data.transform (maybeApply workDataCon_maybe) expr),
            Nothing <- builtin constr,
            not (hasExprTy expr),
            not (isDict (Var constr)) = do

            let args = reverse args0  -- TODO: Why is this necessary?

            dflags <- getDynFlags
            constructRepId <- lift $ findIdTH guts 'ConstructRep
            repTyCon <- lift $ findTyConTH guts ''GPURep

            if constr == constructRepId || constrTyCon == repTyCon
              then return expr
              else do

                liftIO $ putStrLn ""
                liftIO $ putStrLn $ "Handling constructor: " ++ showPpr dflags constr
                liftIO $ putStrLn $ "From expr: " ++ showPpr dflags (Data.transform (maybeApply workDataCon_maybe) expr)

                repTyTyCon <- lift $ findTyConTH guts ''GPURepTy

                dflags <- lift $ getDynFlags

                repDictExpr <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [exprType expr])
                repDictRepTy <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [mkTyConApp repTyTyCon [exprType expr]])
                repId <- lift $ findIdTH guts 'rep
                constructFnId <- lift $ findIdTH guts 'construct
                fromId <- lift $ findIdTH guts 'from

                let tryUnfoldAndReduceDict' = tryUnfoldAndReduceDict guts dflags
                let unfoldAndReduceDict_maybe' = unfoldAndReduceDict_maybe guts dflags

                let constr' = mkApps (Var constr) (tys ++ dicts)
                let constr'Type = exprType constr'

                markedArgs <- mapM mark args

                tc@(co, ty') <- lift $ computeRepTypeCo guts (exprType expr)

                let repUnfolding = getUnfolding guts dflags repId

                let getUnfolding' = getUnfolding guts dflags

                let constructUnfolding = getUnfolding' constructFnId
                    (constructFn0, _) =
                        betaReduceAll
                          constructUnfolding
                          [ Type (exprType expr)
                          , repDictExpr
                          ]
                    constructFn1 = caseInline dflags $ Data.transform letNonRecSubst constructFn0
                    (constructFnE, _) = collectArgs constructFn1

                let constructFn =
                        case constructFnE of
                          Var f -> Just f
                          _ -> Nothing

                -- error $ showPpr dflags expr

                -- liftIO $ putStrLn $ "repUnfolding = {" ++ showPpr dflags repUnfolding ++ "}"
                -- error $ "constructUnfolding = {" ++ showPpr dflags constructUnfolding ++ "}"

                -- traceM $ "rep type: " ++ showPpr dflags (exprType repUnfolding)


                let (fn0, restArgs) = betaReduceAll
                                       repUnfolding --constructUnfolding
                                         [ Type (exprType expr)
                                         , repDictExpr
                                         ]

                let unfoldAndReduceDictT = Data.transform tryUnfoldAndReduceDict'

                let fn = caseInline dflags $ onScrutinee (betaReduce . onAppFun tryUnfoldAndReduceDict') $ Data.transform letNonRecSubst fn0

                let repFn1 = caseInline dflags $ Data.transform letNonRecSubst fn
                    (repFnE, _) = collectArgs repFn1

                    repFn =
                      case repFnE of
                        Var f -> Just f
                        _ -> Nothing

                let e' =
                         -- onScrutinee (Data.transform tryUnfoldAndReduceDict') $
                         onScrutinee (tryUnfoldAndReduceDict guts dflags)
                         --     $ tryUnfoldAndReduceDict'
                             $ Data.transform (caseInline dflags)
                             $ Data.transform letNonRecSubst fn

                let e'' = -- Data.transform letNonRecSubst $ Data.transform betaReduce $ Data.transform tryUnfoldAndReduceDict' $
                      onScrutinee (Data.transform (tryUnfoldAndReduceDict guts dflags)) $
                        Data.transform (caseInline dflags) $ onScrutinee (Data.transform betaReduce) e'

                let (repFnName, _) = collectArgs e''
                traceM $ "repFnName = " ++ showPpr dflags repFnName

                let (Var dictFn, dictArgs) = collectArgs e''

                let reduceConstruct arg
                      = Data.transform betaReduce $ Data.transform (maybeTransform3 targetTheFn constructFn ({- Data.transform -} (tryUnfoldAndReduceDict guts dflags) . unfoldAndReduceDict guts dflags)) $ Data.transform letNonRecSubst $ Data.transform betaReduce $
                      onAppFun (tryUnfoldAndReduceDict guts dflags) $
                      arg


                -- e''' <- Data.transformM (maybeTransform3M targetTheFnM constructFn (\app -> let (cFn, cArgs) = collectArgs app in fmap (mkApps cFn) (mapM (\x -> trace ("unconstructing " ++ showPpr dflags x) $ applyUnconstructRep guts x (exprType x)) cArgs))) e''

                let simplE' = e'' --reduceConstruct e''


                -- traceM $ "simplE' = " ++ showPpr dflags simplE'


                let fnE = Data.transform letNonRecSubst
                            $ untilNothing (unfoldAndReduceDict_maybe guts dflags) simplE'

                -- traceM $ "fnE = " ++ showPpr dflags fnE

                unreppedArgs <- mapM (applyUnrep guts <=< {- applyUnconstructRep' guts <=< -} mark) markedArgs --args
                unrepId <- lift $ findIdTH guts 'unrep

                -- let (newExpr, remainingArgs) = betaReduceAll fnE [mkApps constr' unreppedArgs]

                let fnE' = Data.transform betaReduce $ Data.transform letNonRecSubst $ Data.transform betaReduce $ Data.transform (tryUnfoldAndReduceDict guts dflags) fnE
                let (newExpr, remainingArgs) = betaReduceAll fnE' [mkApps constr' unreppedArgs]


                let internalTypeableModule = Module baseUnitId (mkModuleName "Data.Typeable.Internal")

                -- typeableC <- lift $ findClassTH guts ''Typeable

                typeableTyCon <- lift $ findTyConTH guts ''Typeable
                let newExpr'
                      = Data.transform (caseInline dflags)
                        $ newExpr

                -- traceM $ "newExpr'0 = {" ++ showPpr dflags newExpr'0 ++ "}"

                -- traceM $ "newExpr' = {" ++ showPpr dflags newExpr' ++ "}"

                -- error (showPpr dflags (Data.transform(unfoldAndBetaReduce guts dflags (idIsFrom internalTypeableModule)) newExpr'0))

                newExpr'' <- return newExpr' --Data.transformM (elimRepUnrep guts) newExpr'

                -- error (showPpr dflags newExpr'')

                expType <- lift $ findTypeTH guts ''GPUExp
                externalizeId <- lift $ findIdTH guts 'externalize
                castExpId <- lift $ findIdTH guts 'CastExp

                -- let elimConstruct = fmap (Data.transform (caseInline dflags)
                --                            . Data.transform betaReduce)
                --                     . transformIgnoringClasses_maybe (replaceVarId_maybe constructFnId (getUnfolding' constructFnId))

                -- let elimTheFn fnId = upOneLevel_maybe (Just
                --                                       . transformIgnoringClasses (onAppFun (Data.transform betaReduce
                --                                                                  . Data.transform letNonRecSubst
                --                                                                  . betaReduce
                --                                                                  . onAppFun tryUnfoldAndReduceDict'
                --                                                                  . Data.transform letNonRecSubst
                --                                                                  . tryUnfoldAndReduceDict')))
                --                           (upOneLevel_maybe (Just
                --                                             . Data.transform (caseInline dflags)
                --                                             . transformIgnoringClasses (onScrutinee tryUnfoldAndReduceDict')
                --                                             . Data.transform betaReduce)
                --                               (upOneLevel_maybe (Just)
                --                                 (fmap (Data.transform (caseInline dflags)
                --                                           . Data.transform betaReduce)
                --                                   . transformIgnoringClasses_maybe (replaceVarId_maybe fnId (getUnfolding' fnId)))))


                let elimFrom = fmap (Data.transform (caseInline dflags) . Data.transform betaReduce . Data.transform (onScrutinee (Data.transform tryUnfoldAndReduceDict')) . Data.transform (caseInline dflags . Data.transform (onScrutinee tryUnfoldAndReduceDict') . betaReduce)) . transformMaybe (onScrutinee_maybe (fmap tryUnfoldAndReduceDict' . transformMaybe (replaceVarId_maybe fromId (getUnfolding' fromId))))


                -- traceM $ "fn of newExpr'': " ++ showPpr dflags (fst (collectArgs newExpr''))
                case collectArgs newExpr'' of
                  (Var newExpr''Fn, _)
                    | newExpr''Fn /= constructRepId -> do
                        r <- elimRepUnrep guts newExpr''
                        traceM "already done"
                        traceM $ "^=====> " ++ showPpr dflags r
                        return r
                  _ -> do
                    traceM "not done"

                    -- pairExpWorkId <- lift $ findDataConWorkIdTH guts 'PairExp
                    -- leftExpWorkId <- lift $ findDataConWorkIdTH guts 'LeftExp
                    -- rightExpWorkId <- lift $ findDataConWorkIdTH guts 'RightExp
                    -- constructRepWorkId <- lift $ findDataConWorkIdTH guts 'ConstructRep
                    -- unitExpWorkId <- lift $ findDataConWorkIdTH guts 'UnitExp

                    -- pairExpWrapId <- lift $ findIdTH guts 'PairExp
                    -- rightExpWrapId <- lift $ findIdTH guts 'RightExp
                    -- leftExpWrapId <- lift $ findIdTH guts 'LeftExp
                    -- constructRepWrapId <- lift $ findIdTH guts 'ConstructRep
                    -- unitExpWrapId <- lift $ findIdTH guts 'UnitExp

                    -- let dslConstructorIds = [pairExpWorkId, pairExpWrapId, constructRepWorkId, constructRepWrapId, leftExpWorkId, rightExpWorkId, leftExpWrapId, rightExpWrapId, unitExpWorkId, unitExpWrapId]

                    simplE'' <- return $ (Data.transform betaReduce . Data.transform letNonRecSubst . Data.transform betaReduce . onAppFun tryUnfoldAndReduceDict' . Data.transform letNonRecSubst . onAppFun tryUnfoldAndReduceDict') -- Remove a $crep, try to get this in the form of a ConstructRep application
                                  -- $ Data.transformM (elimRepUnrep guts)
                                  $ Data.transform (caseInline dflags)
                                  $ Data.transform (combineCasts dflags)
                                  $ betaReduce (simplE' :@ mkApps constr' unreppedArgs)
                    -- traceM $ "simplE'' = " ++ showPpr dflags simplE''

                    -- traceM $ "collected: " ++ showPpr dflags (collectArgs simplE'')

                    traceM $ "simplE'' = " ++ showPpr dflags simplE''

                    case collectArgs simplE'' of
                      (r, []) -> return r
                      (simplE''Fn, simplE''Args0@(Type tyArg:_)) -> do

                        let simplE''Arg0 = last simplE''Args0

                            simplE''Arg = {- untilNothing (elimTheFn constructFnId)-} simplE''Arg0 -------------------------------------------
                            prepareResult x = mkApps simplE''Fn (init simplE''Args0 ++ [x])


                        traceM $ "simplE''Arg = " ++ showPpr dflags simplE''Arg

                        -- traceM $ "=== simplE''' ===> " ++ showPpr dflags simplE'''

                        -- return simplE''
{-
                        let newExpr'''0 =
                              -- transformIgnoringClasses_maybe elimConstruct $

                              Data.transform (combineCasts dflags) $
                              Data.transform (caseInline dflags) $
                              Data.transform betaReduce $
                              Data.transform (combineCasts dflags) $
                              Data.transform (maybeApply (elimTheFn fromId)) $

                              untilNothing (upOneLevel_maybe (Just . Data.transform betaReduce . Data.transform (combineCasts dflags)) (transformIgnoringClasses_maybe (elimTheFn constructFnId))) $

                              Data.transform betaReduce $
                              -- Data.transform caseFloatApp $
                              maybeApply (repeatTransform caseFloatApp_maybe) $
                              Data.transform betaReduce $
                              Data.transform (combineCasts dflags) $
                              Data.transform betaReduce $
                              Data.transform (combineCasts dflags) $

                              untilNothing (transformIgnoringClasses_maybe (elimTheFn constructFnId)) $ ---------------

                              Data.transform (caseInline dflags) $
                              Data.transform betaReduce $
                              transformIgnoringClasses (maybeApply (elimTheFn fromId)) $
                              Data.transform letNonRecSubst $
                              -- Data.transform (caseInline dflags) $
                              -- Data.transform betaReduce $
                              untilNothing --maybeApply
                                (fmap (Data.transform betaReduce . maybeApply (repeatTransform caseFloatApp_maybe)) -- Eliminate a $dmconstruct
                                 . upOneLevel_maybe (Just . transformIgnoringClasses (onAppFun (Data.transform betaReduce . Data.transform letNonRecSubst . betaReduce . onAppFun tryUnfoldAndReduceDict' . Data.transform letNonRecSubst . tryUnfoldAndReduceDict')))
                                  (upOneLevel_maybe (Just
                                                    -- . Data.transform (maybeApply ((fmap (\x -> trace ("onAppFun: " ++ showPpr dflags x) $ onAppFun tryUnfoldAndReduceDict' x)) . (onVarWhen_maybe (not . idIsFrom internalTypeableModule) (unfoldAndReduceDict_maybe' . Var))))
                                                    . Data.transform (caseInline dflags)
                                                    . betaReduce)
                                  -- (upOneLevel_maybe (Just . Data.transform (caseInline dflags) . Data.transform (onScrutinee (Data.transform tryUnfoldAndReduceDict')) . betaReduce)
                                    (upOneLevel_maybe
                                      (Just . betaReduce)
                                      (transformIgnoringClasses_maybe elimConstruct))))
                                simplE''Arg
-}

                        let newExpr'''0
                              = maybeApply --untilNothing
                                        ( {-
                                            fmap ( (\x -> trace ("trying " ++ showPpr dflags x) (tryUnfoldAndReduceDict' x))
                                              . Data.transform (caseInline dflags . Data.transform betaReduce)

                                              . Data.transform (onScrutinee (Data.transform tryUnfoldAndReduceDict'))

                                              . Data.transform betaReduce

                                              . maybeApply (repeatTransform caseFloatApp_maybe)
                                              . maybeApply (repeatTransform caseFloatCast_maybe)
                                              . maybeApply (combineCasts_maybe dflags)
                                              . Data.transform letNonRecSubst)
                                              -} id
                                                  . fmap ((\r -> trace ("reduce(" ++ showPpr dflags currName ++ "): " ++ showPpr dflags r) r) {- . Data.transform (onScrutinee tryUnfoldAndReduceDict') . Data.transform (replaceVarId fromId (getUnfolding' fromId)). Data.transform (onScrutinee (onScrutinee tryUnfoldAndReduceDict')) . {- Data.transform caseFloatCase . -} Data.transform betaReduce . Data.transform (combineCasts dflags) . repeatCaseFloat) -} ) . ({- reduceDictFn_maybe guts dflags fromId <=< -} fmap (Data.transform (combineCasts dflags) . reduceUnfolded guts dflags . unfoldAndReduceId guts dflags constructFnId . reduceUnfolded guts dflags . unfoldAndReduceId guts dflags constructFnId . reduceUnfolded guts dflags . unfoldAndReduceId guts dflags fromId . Data.transform (applyWhen (hasExprTy' expTyCon) tryUnfoldAndReduceDict') . Data.transform (onScrutinee (unfoldAndReduceId guts dflags fromId)) . reduceUnfolded guts dflags . unfoldAndReduceId guts dflags constructFnId . Data.transform betaReduce . reduceUnfolded guts dflags . unfoldAndReduceId guts dflags constructFnId . Data.transform betaReduce . reduceUnfolded guts dflags . unfoldAndReduceId guts dflags constructFnId . Data.transform betaReduce . Data.transform (combineCasts dflags) . repeatCaseFloat . Data.transform letNonRecSubst . tryUnfoldAndReduceDict' . Data.transform letNonRecSubst . tryUnfoldAndReduceDict' . Data.transform (caseInline dflags) . Data.transform (onScrutinee tryUnfoldAndReduceDict') . betaReduce) . reduceDictFn_maybe guts dflags constructFnId))
                                                -- . (transformMaybe ( transformIgnoringClasses_maybe (replaceVarId_maybe constructFnId (getUnfolding' constructFnId)))))
                                    simplE''Arg

                        let unfoldAndInlineCase = Data.transform (caseInline dflags) . Data.transform (onScrutinee tryUnfoldAndReduceDict')

                        -- traceM $ "elimRepUnrep: {" ++ showPpr dflags newExpr'''0 ++ "}"
                        newExpr''' <- fmap (Data.transform betaReduce . repeatCaseFloat) $ elimRepUnrep guts $ Data.transform betaReduce  newExpr'''0
                        traceM $ "before elimRepUnrep: " ++ showPpr dflags newExpr'''0
                        traceM "after elimRepUnrep"
                        traceM $ "newExpr''' = " ++ showPpr dflags newExpr'''
                        traceM $ "floated newExpr''' = " ++ showPpr dflags (maybeApply (repeatTransform caseFloatApp_maybe) newExpr''')
                        traceM ""

                        -- TODO: Note: the out-of-scope coercion type variable gets
                        -- introduced somewhere between newExpr and newExpr'0

                        -- traceM $ "newExpr'0 = {" ++ showPpr dflags newExpr'0 ++ "}"
                        -- traceM $ "newExpr''' = {" ++ showPpr dflags newExpr''' ++ "}"

                        -- let toTy = mkTyConApp expTyCon [mkTyConApp repTyTyCon [tyArg]]

                        -- -- newCo <- lift $ buildCo guts (exprType newExpr''') toTy
                        -- (co1, _) <- lift $ normaliseTypeCo_role guts Representational toTy
                        -- (co2, _) <- lift $ normaliseTypeCo_role guts Representational (exprType newExpr''')
                        -- let co3 = mkTransCo co2 (mkSymCo co1)

                        -- -- traceM $ "co1 kind = " ++ showPpr dflags (coercionKind co1)
                        -- -- traceM $ "co2 kind = " ++ showPpr dflags (coercionKind co2)
                        -- traceM $ "co3 kind = " ++ showPpr dflags (coercionKind co3)
                        -- -- traceM $ "exprType newExpr''' = " ++ showPpr dflags (exprType newExpr''')


                        constructedResult <- return $ prepareResult newExpr'''
                        -- constructedResult <- return (Var constructRepId :@ tyExpr :@ dict1 :@ dict2 :@  newExpr''') --return (constructRepFn :@ Type ty :@ dict1' :@ dict2' :@ Cast r' theCo)
                        -- let constructedResult = (constructRepFn :@ Type ty :@ dict1' :@ dict2' :@ r')

                        -- traceM $ "constructRepFn = " ++ showPpr dflags constructRepFn
                        -- traceM $ "dict1' = " ++ showPpr dflags dict1'
                        -- traceM $ "dict2' = " ++ showPpr dflags dict2'

                        -- traceM $ "theCo = {" ++ showPpr dflags theCo ++ "}"
                        -- traceM $ "co'' = {" ++ showPpr dflags co'' ++ "}"
                        -- traceM $ "mkSymCo co' = {" ++ showPpr dflags (mkSymCo co') ++ "}"

                        -- error "debug"

                        -- Data.transformM (fixConstructorCast guts dflags) constructedResult

                        -- traceM $ "getUnfolding' constructFnId: " ++ showPpr dflags (getUnfolding' constructFnId)

                        -- let test = mkEqTypeExpr (exprType constructedResult) (exprType constructedResult)

                        -- testDict <- lift $ buildDictionaryT guts (mkTyConApp eqTyCon [tcTypeKind (exprType constructedResult), exprType constructedResult, exprType constructedResult])
                        -- traceM $ "mkEqTypeExpr: " ++ showPpr dflags testDict

                        -- constructedResult' <-
                        --       case collectArgs constructedResult of
                        --         (Var cFn, cArgs@(Type toTy0:_))
                        --           | cFn == constructRepId -> do
                        --               let transformedArg = last cArgs

                        --               transformedTy0 <- lift $ unwrapExpType guts (exprType transformedArg)

                        --               let transformedTy = mkTyConApp repTyTyCon [transformedTy0]
                        --                   toTy = mkTyConApp repTyTyCon [toTy0]

                        --               traceM $ "types for eq: " ++ showPpr dflags (toTy, transformedTy)

                        --               dict <- lift $ buildDictionaryT guts (mkTyConApp eqTyCon [tcTypeKind toTy, transformedTy, toTy])

                        --               traceM $ "dict = " ++ showPpr dflags dict
                        --               return constructedResult
                        --         (fn, _) -> do
                        --           traceM $ "not ConstructRep: " ++ showPpr dflags fn
                        --           return constructedResult

                        -- traceM $ "args = " ++ showPpr dflags (length (snd (collectArgs constructedResult)))
                        traceM $ "constructedResult = {" ++ showPpr dflags constructedResult ++ "}"

                        -- updateTypeProofs guts constructedResult

                        -- Data.transformM (updateConstructRepCast guts) constructedResult
                        return constructedResult

                        -- traceM $ "before updateTypeProofs: " ++ showPpr dflags r

                    -- error "debug"

                    -- error (showPpr dflags constructedResult)

                    -- TODO: Why does the second updateTypeProofs change
                    -- things?
                    {- updateTypeProofs guts =<< updateUnitTypeProofs guts =<< -}


                    -- r' <- updateTypeProofs guts r

                    -- traceM $ "after updateTypeProofs: " ++ showPpr dflags r'
                    -- return r'

                    -- return r



                    -- error (showPpr dflags r)


                    -- error (showPpr dflags constructedResult)
                    -- return $ Data.transform letNonRecSubst $ simpleOptExpr dflags $ Data.transform betaReduce $ Data.transform letNonRecSubst $ Data.transform (maybeApply (combineCasts_maybe dflags)) $ constructedResult

                    -- error (showPpr dflags (newExpr, remainingArgs))
                    -- return newExpr'''

        go expr@(Var f :@ Type ty :@ x)
          | isUnrep f = do
              -- dflags <- getDynFlags
              -- traceM "isUnrep..."
              -- traceM $ "^--> ty = " ++ showPpr dflags ty
              -- traceM $ "^--> x  = " ++ showPpr dflags x
              return x

        go expr@(_ :@ _)
          | Nothing <- getConstructorApp_maybe expr
          , (Var f, args) <- collectArgs expr
          , not (isConstructor f)
          , not (isUnrep f)
          , Nothing <- builtin f
          , not (isDict expr)
          , not (hasExprTy expr) = do

            internalizeId <- lift $ findIdTH guts 'internalize

            dflags <- getDynFlags

            if f == internalizeId
              then do
                -- liftIO $ putStrLn $ "matching interalize: " ++ showPpr dflags args
                case args of
                  [_, _, x] ->
                    mark x
              else do

                -- liftIO $ putStrLn $ "transforming: " ++ showPpr dflags expr

                when (f == currName) (error "Improper form of recursion (mutual recursion or non-tail recursion")

                let unfoldingF = getUnfolding guts dflags f

                -- markedF <- mark unfoldingF
                traceM $ "marking args: " ++ showPpr dflags args
                markedArgs <- mapM mark args

                let (newF0, newArgs) = betaReduceAll unfoldingF markedArgs --args
                    newF             = caseInlineT dflags $ caseInline dflags (caseInline dflags newF0)

                markedNewF <- mark newF

                mkExprApps guts markedNewF newArgs


        -- go e0@(Cast e co0) = whenNotExprTyped guts e0 $ do
        --   liftIO $ putStrLn "Handling Cast..."
        --   expType <- lift $ findTypeTH guts ''GPUExp

        --   let expTypeRefl = mkReflCo (coercionRole co0) expType

        --   markedE <- mark e

        --   let co = mkAppCo expTypeRefl co0

        --   return (Cast markedE co)

        go expr = return expr


applyUnrep :: ModGuts -> CoreExpr -> MatchM CoreExpr
applyUnrep guts e = do
  dflags <- getDynFlags

  ty <- lift $ unwrapExpType guts (exprType e)

--   when (isDict e) $ error $ "applyUnrep: isDict: " ++ showPpr dflags e

  unrepId <- lift $ findIdTH guts 'unrep

  let result = (Var unrepId :@ Type ty :@ e)

  traceM $ "applyUnrep: exprType e = " ++ showPpr dflags ty
  traceM $ "applyUnrep type: " ++ showPpr dflags (exprType result)

  return result


-- | rep (unrep x)  ==>  x `cast` ...
-- and rep (unrep x) `cast` co  ==>  x `cast` ...
elimRepUnrep :: ModGuts -> CoreExpr -> MatchM CoreExpr
elimRepUnrep guts expr0 = do
  dflags <- getDynFlags

  expr' <- elimRepUnrep_in_cast guts expr0

  -- traceM $ "expr' =" ++ showPpr dflags expr'

  elimRepUnrep_without_cast guts expr'

elimRepUnrep_without_cast :: ModGuts -> CoreExpr -> MatchM CoreExpr
elimRepUnrep_without_cast guts = Data.descendM go' <=< go'
  where
    go (Cast e co) = Cast <$> (go e) <*> pure co
    go e = elimRepUnrep_co go' guts Nothing (exprType e) e

    go' = Data.descendM go

thirdF :: Functor f => (c -> f c') -> (a, b, c) -> f (a, b, c')
thirdF f (x, y, z) = fmap (\z' -> (x, y, z')) (f z)

third :: (a, b, c) -> c
third (_, _, z) = z

-- | rep (unrep x) `cast` co  ==>  x `cast` ...
elimRepUnrep_in_cast :: ModGuts -> CoreExpr -> MatchM CoreExpr
elimRepUnrep_in_cast guts expr0@(Cast e co) = elimRepUnrep_co (elimRepUnrep_in_cast guts) guts (Just co) origType e
  where origType = exprType expr0

elimRepUnrep_in_cast guts expr@(Case s wild ty (alt1:restAlts)) = do
  alt1' <- thirdF (elimRepUnrep_in_cast guts) alt1
  restAlts' <- mapM (thirdF (elimRepUnrep_in_cast guts)) restAlts
  s' <- elimRepUnrep_in_cast guts s

  dflags <- getDynFlags

  -- traceM $ "replacement ty = " ++ showPpr dflags (exprType (third alt1'))

  return $ Case s' wild ty (alt1':restAlts')
  -- return $ Case s' wild (exprType (third alt1')) (alt1':restAlts')

elimRepUnrep_in_cast guts expr = Data.descendM (elimRepUnrep_in_cast guts) expr

elimRepUnrep_co :: (CoreExpr -> MatchM CoreExpr) -> ModGuts -> Maybe Coercion -> Type -> CoreExpr -> MatchM CoreExpr
elimRepUnrep_co rec guts coA_M origType expr@(Var r :@ Type{} :@ dict :@ arg) =
  go0 arg
  where
    go0 e =
      case e of
        Var u :@ Type{} :@ x -> go e u Nothing x
        Cast (Var u :@ Type{} :@ x) coB -> go e u (Just coB) x
        _ -> Data.descendM rec (coerceMaybe coA_M expr)

    go :: CoreExpr -> Id -> Maybe Coercion -> CoreExpr -> MatchM CoreExpr
    go unrepped u coB_M x = do
      dflags <- getDynFlags

      repId <- lift $ findIdTH guts 'rep
      unrepId <- lift $ findIdTH guts 'unrep
      expTyCon <- lift $ findTyConTH guts ''GPUExp
      expType <- lift $ findTypeTH guts ''GPUExp

      -- traceM $ "building coercion: " ++ showPpr dflags (exprType x, origType)
      -- traceM $ "coA_M = " ++ showPpr dflags (fmap coercionKind coA_M)
      -- traceM $ "coB_M = " ++ showPpr dflags (fmap coercionKind coB_M)
      traceM "****** elimRepUnrep_co ******"

      co_M <-
            case (coA_M, coB_M) of
              (Just coA, Just coB0) -> do
                let Pair coB_ty1 coB_ty2 = coercionKind coB0


                coB <- lift $ buildCo guts coB_ty1 coB_ty2

                traceM ("coercion kind coA: " ++ showPpr dflags (coercionKind coA))
                traceM ("coercion kind coB: " ++ showPpr dflags (coercionKind coB))
                let Just coB_N = setNominalRole_maybe (coercionRole coB) coB
                    coB' = mkAppCo (mkReflCo (coercionRole coA) expType) coB_N
                traceM ("coercion kind coA: " ++ showPpr dflags (coercionKind coA))
                traceM ("coercion kind coB': " ++ showPpr dflags (coercionKind coB'))
                traceM ("coercion role coB': " ++ showPpr dflags (coercionRole coB'))

                if not (coercionRKind coB' `eqType` coercionLKind coA)
                  then error "elimRepUnrep_co: not (coercionRKind coB' `eqType` coercionLKind coA)"
                  else return ()

                let co' = mkTransCo coB' coA
                return $ Just co'
                -- Just $ downgradeRole Representational (coercionRole co') co'
              _ -> return (coA_M <|> coB_M)
                -- case coA_M <|> coB_M of
                --   Nothing -> return $ Nothing
                --   Just co0 -> do
                --     case setNominalRole_maybe (coercionRole co0) co0 of
                --       Just co' -> return $ Just co'
                --       Nothing -> do
                --         co <- lift $ buildCo guts (coercionLKind co0) (coercionRKind co0)

                --         let Just co' = setNominalRole_maybe (coercionRole co) co
                --         return $ Just co'

      -- let co_M = do
      --               guard (isJust coA_M || isJust coB_M)
      --               let newCo = fromMaybe (buildCoercion (exprType x) origType) coB_M

      --               -- traceM $ "newCo = {" ++ showPpr dflags newCo ++ "}"

      --               newCo' <- case splitTyConApp_maybe (coercionRKind newCo) of
      --                           Just (tyCon, _)
      --                             | tyCon == expTyCon -> return newCo
      --                           _ -> Just $ buildCoercion (mkTyConApp expTyCon [exprType x]) (mkTyConApp expTyCon [origType])


      --               traceM $ "kinds of coA_M and coB_M: " ++ showPpr dflags (fmap coercionKind coA_M, fmap coercionKind coB_M)
      --               traceM $ "newCo' kind = " ++ showPpr dflags (coercionKind newCo')
      --               -- traceM $ "newCo' = {" ++ showPpr dflags newCo' ++ "}"

      --               let newCo'' =
      --                     case coA_M of
      --                       Nothing -> newCo'
      --                       Just coA -> trace "making trans co" $ mkTransCo newCo' coA

      --               traceM $ "newCo'' kind = " ++ showPpr dflags (coercionKind newCo'')

      --               Just $ downgradeRole Representational (coercionRole newCo'') newCo''


      if r == repId && u == unrepId
        then do

          when (isNothing coA_M || isNothing coB_M)
            $ traceM ("maybe coA_M, coB_M = " ++ showPpr dflags (fmap coercionKind coA_M, fmap coercionKind coB_M))
          -- traceM ""
          -- -- traceM $ "co_M = " ++ showPpr dflags co_M
          -- -- traceM $ "elimRepUnrep_co: origType = " ++ showPpr dflags origType
          -- traceM $ "elimRepUnrep_co: co kinds: " ++ showPpr dflags (fmap coercionKind coA_M, fmap coercionKind coB_M)
          -- -- traceM $ "======================> x =" ++ showPpr dflags x
          -- traceM $ "======================> expr =" ++ showPpr dflags x


          -- traceM ""
          -- traceM $ "co_M = " ++ showPpr dflags (fmap coercionKind co_M)
          -- traceM $ "coA_M = " ++ showPpr dflags (fmap coercionKind coA_M)
          -- traceM $ "coB_M = " ++ showPpr dflags (fmap coercionKind coB_M)
          -- traceM $ "x = " ++ showPpr dflags x

          -- unconstructRepId <- lift $ findIdTH guts 'UnconstructRep
          ty <- lift $ unwrapExpType guts (exprType unrepped)


          -- traceM ""
          -- traceM $ "unrepped type = " ++ showPpr dflags (exprType unrepped)
          -- traceM $ "unrepped = " ++ showPpr dflags unrepped
          -- traceM $ "--->" ++ showPpr dflags x --showPpr dflags (Var unconstructRepId :@ Type ty :@ x')

          if not $ eqType ty (exprType unrepped)
            then traceM "not eqType" >> {- fmap (coerceMaybe co_M) -} (Data.descendM rec (coerceMaybe co_M x))
            else rec (coerceMaybe co_M x)
        -- else Data.descendM (elimRepUnrep guts) expr--return $ coerceMaybe coA_M expr
        else Data.descendM rec $ coerceMaybe co_M expr

elimRepUnrep_co rec guts co_M _ expr = Data.descendM rec (coerceMaybe co_M expr)

-- TODO: Check this
coerceMaybe :: Maybe Coercion -> Expr a -> Expr a
coerceMaybe Nothing e = e
coerceMaybe (Just co) e = Cast e co

applyUnconstructRep :: ModGuts -> CoreExpr -> Type -> MatchM CoreExpr
applyUnconstructRep guts e ty = do
  unconstructRepId <- lift $ findIdTH guts 'UnconstructRep
  return (Var unconstructRepId :@ Type ty :@ e)

applyUnconstructRep' :: ModGuts -> CoreExpr -> MatchM CoreExpr
applyUnconstructRep' guts e = do
  ty <- lift $ unwrapExpType guts (exprType e)
  applyUnconstructRep guts e ty

unwrapUnconstructRep_maybe :: ModGuts -> CoreExpr -> MatchM (Maybe CoreExpr)
unwrapUnconstructRep_maybe guts e@(Var f :@ Type _ :@ x) = do
  unconstructRepId <- lift $ findIdTH guts 'UnconstructRep
  if f == unconstructRepId
    then return (return x)
    else return Nothing
unwrapUnconstructRep_maybe _ _ = return Nothing

transformProdMatch :: ModGuts -> (Expr Var -> MatchM (Expr Var)) -> Type -> Type -> Alt Var -> MatchM (Expr Var)
transformProdMatch guts mark resultTy ty0_ (altCon@(DataAlt dataAlt), vars0, body0) = do
  dflags <- lift $ getDynFlags
  repTyCon <- lift $ findTyConTH guts ''GPURep

  ty0 <- lift $ (unwrapExpType guts <=< unwrapExpType guts) ty0_

  repType <- lift $ computeRepType guts ty0

  pairTyCon <- lift $ findTyConTH guts ''(,)
  prodTypes <- listTypesWith guts (getName pairTyCon) repType



  body <- mark body0


  go body pairTyCon repTyCon prodTypes vars0
  where
    go :: Expr Var -> TyCon -> TyCon -> [Type] -> [Var] -> MatchM (Expr Var)
    go body pairTyCon repTyCon (ty1:_) [] = do
      nullaryMatchId <- lift $ findIdTH guts 'NullaryMatch

      resultTyDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [ty1])

      return (Var nullaryMatchId :@ Type ty1 :@ Type resultTy :@ resultTyDict :@ body)

    go body pairTyCon repTyCon allTys@(ty1:_) [x] = do
      dflags <- getDynFlags

      let ty = pairWrap pairTyCon allTys

      oneProdMatchId <- lift $ findIdTH guts 'OneProdMatch

      tyDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [ty])

      abs'd <- mark =<< abstractOver guts x body

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

    pairWrap _ [] = error "pairWrap"
    pairWrap pairTyCon xs = foldr1 (\x acc -> mkTyConApp pairTyCon [x, acc]) xs

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

      -- traceM $ "transformSumMatch: ty1:restTys = " ++ showPpr dflags (ty1:restTys)
      -- traceM $ "transformSumMatch: x:xs = " ++ showPpr dflags (x:xs)
      let restTy = eitherWrap eitherTyCon restTys

      co <- lift $ repTyCo guts restTy

      restSum <- go eitherTyCon repTyCon restTys xs

      sumMatchId <- lift $ findIdTH guts 'SumMatchExp


      let coPair@(Pair coB coA) = coercionKind co


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


    eitherWrap _ [] = error "eitherWrap"
    eitherWrap eitherTyCon xs = foldr1 (\x acc -> mkTyConApp eitherTyCon [x, acc]) xs

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
    go0 (Lam v body) =
      go1 (varType v) v body
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
    go1 ty lamV e = go2 ty lamV e

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

              -- theLam <- abstractOver guts lamV x'
              let theLam = Lam lamV x'
              outerV <- lift $ mkSysLocalM (occNameFS (occName lamV)) (varType lamV)

              return (Var f :@ fTyArg :@ fDict :@
                        (Lam outerV (Var runIterId :@ Type resultTy :@ Type ty :@ resultTyDict :@ tyDict :@ theLam :@ Var outerV)))

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

          body' <- subst arg uniq body

          argTy' <- lift $ unwrapExpType guts (varType arg)
          bodyTy' <- lift $ unwrapExpType guts (exprType body')

          iHash <- lift $ findIdTH guts 'GHC.Types.I#
          -- intTy <- findTypeTH guts ''Int#

          let nameInt =  Var iHash :@ Lit (mkLitInt dflags (fromIntegral uniq))

          return (Var lamName :@ Type bodyTy' :@ Type argTy' :@ nameInt :@ body')
        else return expr

    go expr = return expr

    subst name uniq = Data.transformM (subst0 name uniq)

    subst0 name uniq (Var name')
      | name' == name = do

        varName <- lift $ findIdTH guts 'Expr.Var
        -- intTy <- findTypeTH guts ''Int#

        varTy' <- lift $ unwrapExpType guts (varType name)

        iHash <- lift $ findIdTH guts 'GHC.Types.I#

        dflags <- getDynFlags
        let nameInt =  Var iHash :@ Lit (mkLitInt dflags (fromIntegral uniq))

        typeableTyCon <- lift $ findTyConTH guts ''Typeable
        typeType <- lift $ findTypeTH guts ''Kind.Type
        typeableDict <- lift $ buildDictionaryT guts (mkTyConApp typeableTyCon [typeType, varTy'])

        -- let result = Var varName :@ Type varTy' :@ typeableDict :@ nameInt
        unreppedVar <- applyUnrep guts (Var varName :@ Type varTy' :@ typeableDict :@ nameInt)
        traceM $ "var result = " ++ showPpr dflags unreppedVar

        return unreppedVar

        -- applyUnconstructRep guts unreppedVar varTy'

        -- liftIO $ putStrLn $ "var result = " ++ showPpr dflags result

        -- return result
    subst0 _ _ expr = return expr


-- TODO: Check if this is needed and implement if it is
-- -- | Turn `unrep (Var ...)`s into `Var ...`s when they are already in
-- -- a `GPUExp` position and also turn application of `GPUExp`s into `App`s
-- simplifyLambda = undefined

-- e  ==>  (\x -> e)     {where x is a free variable in e}
-- Also transforms the type of x :: T to x :: GPUExp T
-- TODO: Make sure there aren't any issues with this type transformation
-- and foralls, etc.

abstractOver :: HasCallStack => ModGuts -> Var -> Expr Var -> MatchM (Expr Var)
abstractOver guts v e = do
  expTyCon <- lift $ findTyConTH guts ''GPUExp
  repTyCon <- lift $ findTyConTH guts ''GPURep
  typeableTyCon <- lift $ findTyConTH guts ''Typeable
  -- intTy <- lift $ findTypeTH guts ''Int#

  -- lamFnId <- lift $ findIdTH guts 'Expr.lam

  -- lamId <- lift $ findIdTH guts 'Expr.Lam

  lamId <- lift $ findDataConWorkIdTH guts 'Expr.Lam

  varId <- lift $ findIdTH guts 'Expr.Var
  nameId <- lift $ findIdTH guts 'Expr.Name

  typeType <- lift $ findTypeTH guts ''Kind.Type

  uniq <- newUnique

  typeableDict <- lift $ buildDictionaryT guts (mkTyConApp typeableTyCon [typeType, varType v])
  iHash <- lift $ findIdTH guts 'GHC.Types.I#

  dflags <- getDynFlags
  -- error (showPpr dflags typeableDict)

  let origTy = varType v
      newTy = mkTyConApp expTyCon [origTy]
      nameInt = Var iHash :@ Lit (mkLitInt dflags (fromIntegral uniq))
      nameVal = Var nameId :@ Type origTy :@ nameInt
      v' = setVarType v newTy

  eTy' <- lift $ unwrapExpType guts (exprType e)

  dflags <- getDynFlags

  -- liftIO $ putStrLn $ "abstractOver: e = " ++ showPpr dflags e
  -- liftIO $ putStrLn $ "abstractOver: v = " ++ showPpr dflags v
  -- liftIO $ putStrLn $ "abstractOver: varType v = " ++ showPpr dflags (varType v)

  repDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [varType v])

  let e' = Data.transform (go varId newTy) e

  unreppedVar <- applyUnrep guts (Var varId :@ Type origTy :@ typeableDict :@ nameVal)

  -- let markedSubstE' = substCoreExpr v' unreppedVar markedE'

  -- let varExp = Data.transform (tryUnfoldAndReduceDict guts dflags) $ Data.transform letNonRecSubst (Var varId :@ Type origTy :@ typeableDict :@ nameVal)
  let varExp = Data.transform (tryUnfoldAndReduceDict guts dflags) $ Data.transform letNonRecSubst unreppedVar

  -- varExp <- applyUnconstructRep guts varExp0 origTy

  -- varExp <- applyUnrep guts varExp0

  -- traceM $ "varExp = " ++ showPpr dflags varExp

  markedSubstE' <- mark0 guts $ substCoreExpr v' varExp e'
  -- traceM $ "marking " ++ showPpr dflags (substCoreExpr v' varExp e)
  -- liftIO $ putStrLn $ "markedSubstE' = " ++ showPpr dflags markedSubstE'

  -- traceM $ "markedSubstE' = " ++ showPpr dflags (Data.transform (go varId newTy) markedSubstE')
  -- markedSubstE'' <- mark0 guts markedSubstE'

  -- traceM $ "lamId = " ++ showPpr dflags lamId

  let funTy = mkFunTy origTy eTy'

  let co = mkReflCo Nominal funTy

  return (Var lamId :@ Type funTy :@ Type origTy :@ Type eTy' :@ Coercion co :@ repDict :@ typeableDict :@ nameVal
            :@ markedSubstE')
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
  ,('ord, 'Ord)
  ,('fromEnum, 'FromEnum)
  -- ,('fromIntegral, 'FromIntegral)
  -- ,('fromInteger, 'deepFromInteger)
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

  -- ,('(), 'UnitExp)
  -- ,('Left, 'LeftExp)
  -- ,('Right, 'RightExp)
  -- ,('(,), 'PairExp)

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

findDataConWorkIdTH :: ModGuts -> TH.Name -> CoreM Id
findDataConWorkIdTH guts thName = do
    nameMaybe <- thNameToGhcName thName
    case nameMaybe of
      Nothing -> error $ "findDataConWorkId: Cannot find " ++ show thName
      Just name -> findDataConWorkId guts name

findTypeTH :: ModGuts -> TH.Name -> CoreM Type
findTypeTH guts thName = do
    nameMaybe <- thNameToGhcName thName
    case nameMaybe of
      Nothing -> error $ "findTypeTH: Cannot find " ++ show thName
      Just name -> findType guts name emptyVarSet


-- Modified from 'Inst':

mkEqTypeExpr :: Type -> Type -> CoreExpr
mkEqTypeExpr ty1 ty2 =
  Var (dataConWrapId eqDataCon) :@ Type k :@ Type ty1 :@ Type ty2
  where
    k = tcTypeKind ty1

mkEqBox :: TcCoercion -> CoreExpr
mkEqBox co =
    Var (dataConWorkId eqDataCon) :@ Type k :@ Type ty1 :@ Type ty2 :@ Coercion co
  where
    k = tcTypeKind ty1
    Pair ty1 ty2 = coercionKind co

mkEqBoxRepr :: TcCoercion -> CoreExpr
mkEqBoxRepr co =
    Var (dataConWorkId eqDataCon) :@ Type k :@ Type ty1 :@ Type ty2 :@ Coercion co
  where
    k = mkReprPrimEqPred ty1 ty2 --tcTypeKind ty1
    Pair ty1 ty2 = coercionKind co

-- Modified from CoreMonad
bindsOnlyPass_match :: (CoreProgram -> MatchM CoreProgram) -> ModGuts -> MatchM ModGuts
bindsOnlyPass_match pass guts
  = do { binds' <- pass (mg_binds guts)
       ; return (guts { mg_binds = binds' }) }

