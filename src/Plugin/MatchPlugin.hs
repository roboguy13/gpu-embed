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
  -- unwrappedM <- unwrapUnconstructRep_maybe guts x
  -- case unwrappedM of
  --   Just x' -> return x'
    -- Nothing -> do
      r <- tryMarkUnrepVar guts x
      case r of
        Just x' -> return x'
        Nothing -> markIt guts x

tryMarkUnrepVar :: HasCallStack => ModGuts -> Expr Var -> MatchM (Maybe (Expr Var))
tryMarkUnrepVar guts e@(Var f :@ Type tyA :@ var@(Var g :@ Type tyB :@ _dict :@ _)) = do
  unrepId <- lift $ findIdTH guts 'unrep
  varConId <- lift $ findIdTH guts 'Expr.Var

  dflags <- getDynFlags

  if f == unrepId && g == varConId
    then do
      dflags <- getDynFlags
      traceM "traceMarkUnrepVar: unrep Var"
      traceM $ "--> unrepType: " ++ showPpr dflags tyA

      -- traceM $ "=== mark0 ===> " ++ showPpr dflags var

      -- unconstructRepId <- lift $ findIdTH guts 'UnconstructRep
      -- return (Just (Var unconstructRepId :@ Type tyB :@ var))

      return Nothing -- $ Just var
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
          | isExprTy expTyCon a && isExprTy expTyCon b -> return x
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

getConstructorTyCon_maybe :: Var -> Maybe TyCon
getConstructorTyCon_maybe v
  | isId v =
    case idDetails v of
      DataConWorkId dc -> Just $ dataConTyCon dc
      DataConWorkId dc -> Just $ dataConTyCon dc
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

-- | Transform 'f x' to 'App f x' when f has a type of the form
-- 'GPUExp (a -> b)'. Performs this transformation recursively.
-- transformApps :: ModGuts -> Expr Var -> MatchM (Expr Var)
-- transformApps guts = Data.descendM go
--   where
--     mark = mark0 guts

--     go expr@(lhs :@ rhs) = do
--         -- let (f, args) = collectArgs expr
--         expTyCon <- lift $ findTyConTH guts ''GPUExp
--         dflags <- getDynFlags

--         when (not (isFunTy (exprType lhs))) $ do
--           liftIO $ putStrLn $ "========= " ++ showPpr dflags (exprType lhs)
--           liftIO $ putStrLn ""

--         case getEmbeddedFnType0 expTyCon guts (exprType lhs) of
--           Nothing -> return expr
--           Just (aTy, bTy) -> do
--             -- let (tyArgs, restArgs0) = span isType args
--             --     (dictArgs, restArgs1) = span isDict restArgs0

--             -- dflags <- getDynFlags
--             -- liftIO $ putStrLn $ "!!!!!!!!!! attempting: " ++ showPpr dflags f
--             -- liftIO $ putStrLn $ "!!!!!!!!!! with rhs = " ++ showPpr dflags rhs
--             -- liftIO $ putStrLn $ "%%%%%%%%%% With type:  " ++ showPpr dflags (exprType (mkApps f (tyArgs ++ dictArgs)))
--             -- liftIO $ putStrLn ""

--             if isFunTy (exprType lhs)
--               then return expr -- Nothing to do here, already typical function application
--               else do


--                     -- liftIO $ putStrLn $ "~~~~~~~~~~~~ App transform: " ++ showPpr dflags expr
--                     -- liftIO $ putStrLn $ "~~~~~~~~~~~~ restArgs1 = " ++ showPpr dflags restArgs1

--                     -- case restArgs1 of
--                     --   [] -> return expr
--                     --   (arg:nextArgs) ->

--                     dflags <- getDynFlags
--                     -- liftIO $ putStrLn $ "App transform: " ++  showPpr dflags expr
--                     appId <- lift $ findIdTH guts 'App

--                     repTyCon <- lift $ findTyConTH guts ''GPURep
--                     repDict <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [aTy])

--                     -- markedLhs <- mark lhs
--                     -- markedRhs <- mark rhs

--                     return (Var appId :@ Type aTy :@ Type bTy :@ repDict :@ lhs :@ rhs)

--     go expr = return expr


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
            -- True <- isDict dictA,
            -- True <- isDict dictB,
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
                  return (Var tailRecAppId :@ tyA :@ tyB :@ dictA :@ dictB :@ markedX :@ markedY)
                else
                  return (b :@ tyA :@ tyB :@ dictA :@ dictB :@ markedX :@ markedY)


        go expr@(Var f :@ tyA@(Type{}) :@ tyB@(Type{}) :@ dictA :@ dictB :@ x)
           | Just b <- builtin f,
             True <- isDict dictA,
             True <- isDict dictB,
             not (hasExprTy expr) = do
               markedX <- mark x
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

              -- dflags <- getDynFlags
              -- traceM $ "builtin transformed: " ++ showPpr dflags f

              return (b :@ ty :@ dict :@ markedX :@ markedY)

        go expr@(Var f :@ (Type tyA0) :@ (Type tyB0) :@ x :@ y)
          | Just b <- builtin f,
            not (hasExprTy expr) = do
              markedX <- mark x
              markedY <- mark y

              tyA <- lift $ normaliseType' guts tyA0
              tyB <- lift $ normaliseType' guts tyB0

              return (b :@ Type tyA :@ Type tyB :@ markedX :@ markedY)

        go expr@(Var f :@ tyA@(Type{}) :@ tyB@(Type{}) :@ x)
          | Just b <- builtin f,
            not (hasExprTy expr) = do
              dflags <- getDynFlags
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
          | Just (tys, dicts, constrTyCon, constr, args0) <- getConstructorApp_maybe expr,
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


                -- liftIO $ putStrLn $ "repUnfolding = {" ++ showPpr dflags repUnfolding ++ "}"

                let (fn0, restArgs) = betaReduceAll
                                       repUnfolding
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
                      = Data.transform betaReduce $ Data.transform (maybeTransform3 targetTheFn constructFn (Data.transform (tryUnfoldAndReduceDict guts dflags) . unfoldAndReduceDict guts dflags)) $ Data.transform letNonRecSubst $ Data.transform betaReduce $
                      onAppFun (tryUnfoldAndReduceDict guts dflags) $
                      arg


                -- e''' <- Data.transformM (maybeTransform3M targetTheFnM constructFn (\app -> let (cFn, cArgs) = collectArgs app in fmap (mkApps cFn) (mapM (\x -> trace ("unconstructing " ++ showPpr dflags x) $ applyUnconstructRep guts x (exprType x)) cArgs))) e''

                let simplE' = reduceConstruct e''




                let fnE = Data.transform letNonRecSubst
                            $ whileRight (unfoldAndReduceDict_either guts dflags) simplE'

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

                newExpr'' <- Data.transformM (elimRepUnrep guts) newExpr'

                -- error (showPpr dflags newExpr'')

                expType <- lift $ findTypeTH guts ''GPUExp
                externalizeId <- lift $ findIdTH guts 'externalize
                castExpId <- lift $ findIdTH guts 'CastExp

                let elimConstruct = fmap (Data.transform (caseInline dflags)
                                           . Data.transform betaReduce)
                                    . transformIgnoringClasses_maybe (replaceVarId_maybe constructFnId (getUnfolding' constructFnId))

                let elimTheFn fnId = upOneLevel_maybe (Just
                                                      . transformIgnoringClasses (onAppFun (Data.transform betaReduce
                                                                                 . Data.transform letNonRecSubst
                                                                                 . betaReduce
                                                                                 . onAppFun tryUnfoldAndReduceDict'
                                                                                 . Data.transform letNonRecSubst
                                                                                 . tryUnfoldAndReduceDict')))
                                          (upOneLevel_maybe (Just
                                                            . Data.transform (caseInline dflags)
                                                            . transformIgnoringClasses (onScrutinee tryUnfoldAndReduceDict')
                                                            . Data.transform betaReduce)
                                              (upOneLevel_maybe (Just)
                                                (fmap (Data.transform (caseInline dflags)
                                                          . Data.transform betaReduce)
                                                  . transformIgnoringClasses_maybe (replaceVarId_maybe fnId (getUnfolding' fnId)))))



                traceM $ "fn of newExpr'': " ++ showPpr dflags (fst (collectArgs newExpr''))
                case collectArgs newExpr'' of
                  (Var newExpr''Fn, _)
                    | newExpr''Fn /= constructRepId -> do
                        traceM "already done"
                        -- traceM $ "^=====> " ++ showPpr dflags newExpr''
                        return newExpr''
                  _ -> do

                    pairExpWorkId <- lift $ findDataConWorkIdTH guts 'PairExp
                    leftExpWorkId <- lift $ findDataConWorkIdTH guts 'LeftExp
                    rightExpWorkId <- lift $ findDataConWorkIdTH guts 'RightExp
                    constructRepWorkId <- lift $ findDataConWorkIdTH guts 'ConstructRep
                    unitExpWorkId <- lift $ findDataConWorkIdTH guts 'UnitExp

                    pairExpWrapId <- lift $ findIdTH guts 'PairExp
                    rightExpWrapId <- lift $ findIdTH guts 'RightExp
                    leftExpWrapId <- lift $ findIdTH guts 'LeftExp
                    constructRepWrapId <- lift $ findIdTH guts 'ConstructRep
                    unitExpWrapId <- lift $ findIdTH guts 'UnitExp

                    let dslConstructorIds = [pairExpWorkId, pairExpWrapId, constructRepWorkId, constructRepWrapId, leftExpWorkId, rightExpWorkId, leftExpWrapId, rightExpWrapId, unitExpWorkId, unitExpWrapId]

                    simplE'' <- fmap (Data.transform betaReduce . Data.transform letNonRecSubst . Data.transform betaReduce . onAppFun tryUnfoldAndReduceDict' . Data.transform letNonRecSubst . onAppFun tryUnfoldAndReduceDict') -- Remove a $crep, try to get this in the form of a ConstructRep application
                                  $ Data.transformM (elimRepUnrep guts)
                                  $ Data.transform (caseInline dflags)
                                  -- $ repeatTransform' (removeCastsOfAppFns_maybe dslConstructorIds)
                                  $ Data.transform (combineCasts dflags)
                                  $ betaReduce (simplE' :@ mkApps constr' unreppedArgs)
                    -- traceM $ "simplE'' = " ++ showPpr dflags simplE''

                    let (simplE''Fn, simplE''Args0@(Type tyArg:_)) = collectArgs simplE''
                        simplE''Arg0 = last simplE''Args0

                        simplE''Arg = untilNothing (elimTheFn constructFnId) simplE''Arg0
                        prepareResult x = mkApps simplE''Fn (init simplE''Args0 ++ [x])


                    traceM $ "simplE''Arg = " ++ showPpr dflags simplE''Arg

                    -- traceM $ "=== simplE''' ===> " ++ showPpr dflags simplE'''

                    -- return simplE''


                    let newExpr'''0 =
                          -- transformIgnoringClasses_maybe elimConstruct $

                          Data.transform (combineCasts dflags) $
                          Data.transform (caseInline dflags) $
                          Data.transform betaReduce $
                          Data.transform (combineCasts dflags) $
                          Data.transform (maybeApply (elimTheFn fromId)) $

                          untilNothing (upOneLevel_maybe (Just . Data.transform betaReduce . Data.transform (combineCasts dflags)) (transformIgnoringClasses_maybe (elimTheFn constructFnId))) $

                          Data.transform betaReduce $
                          Data.transform caseFloatApp $
                          Data.transform betaReduce $
                          Data.transform (combineCasts dflags) $
                          Data.transform betaReduce $
                          Data.transform (combineCasts dflags) $
                          transformIgnoringClasses (maybeApply (elimTheFn constructFnId)) $
                          Data.transform (caseInline dflags) $
                          Data.transform betaReduce $
                          transformIgnoringClasses (maybeApply (elimTheFn fromId)) $
                          Data.transform letNonRecSubst $
                          -- Data.transform (caseInline dflags) $
                          -- Data.transform betaReduce $
                          maybeApply
                            (fmap (Data.transform betaReduce . Data.transform caseFloatApp) -- Eliminate a $dmconstruct
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

                    -- traceM $ "elimRepUnrep: {" ++ showPpr dflags newExpr'''0 ++ "}"
                    newExpr''' <- (elimRepUnrep guts) newExpr'''0
                    traceM "after elimRepUnrep"
                    traceM $ "newExpr''' = " ++ showPpr dflags newExpr'''
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

                    traceM $ "getUnfolding' constructFnId: " ++ showPpr dflags (getUnfolding' constructFnId)

                    -- traceM $ "args = " ++ showPpr dflags (length (snd (collectArgs constructedResult)))
                    -- traceM $ "constructedResult = {" ++ showPpr dflags constructedResult ++ "}"

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
          | isUnrep f = return x

        go expr@(_ :@ _)
          | Nothing <- getConstructorApp_maybe expr
          , (Var f, args) <- collectArgs expr
          , not (isConstructor f)
          , not (isUnrep f)
          , Nothing <- builtin f
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

                let (newF0, newArgs) = betaReduceAll unfoldingF args --markedArgs
                    newF             = caseInlineT dflags $ caseInline dflags (caseInline dflags newF0)

                markedNewF <- mark newF

                -- liftIO $ putStrLn $ "newArgs = " ++ showPpr dflags newArgs

                -- liftIO $ putStrLn $ "inlining (pre-beta reduce): { " ++ showPpr dflags unfoldingF ++ " }"

                -- liftIO $ putStrLn $ "inlining (pre-case inline): { " ++ showPpr dflags newF0 ++ " }"
                -- liftIO $ putStrLn $ "inlining: { " ++ showPpr dflags newF ++ " }"
                -- liftIO $ putStrLn $ "inlining (new args): " ++ showPpr dflags newArgs
                -- liftIO $ putStrLn $ "inlining: { " ++ showPpr dflags (betaReduceAll (caseInlineT dflags newF) args) ++ " }"

                mkExprApps guts markedNewF newArgs


        -- go e0@(Cast e co0) = whenNotExprTyped guts e0 $ do
        --   liftIO $ putStrLn "Handling Cast..."
        --   expType <- lift $ findTypeTH guts ''GPUExp

        --   let expTypeRefl = mkReflCo (coercionRole co0) expType

        --   markedE <- mark e

        --   let co = mkAppCo expTypeRefl co0

        --   return (Cast markedE co)

        go expr = return expr

-- normaliseConstructorType :: ModGuts -> DynFlags -> CoreExpr -> MatchM CoreExpr
-- normaliseConstructorType guts dflags e0@(Var v)
--   | Just _ <- isDataConId_maybe fn
--     = do

dslExprType :: ModGuts -> CoreExpr -> MatchM Type
-- dslExprType e =
--   let ty = exprType e
--   in
--   trace ("dslExprType: " ++ showSDocUnsafe (ppr e) ++ "\n---> ty = " ++ showSDocUnsafe (ppr ty))
--     $ ty

-- dslExprType guts (Cast e _) = dslExprType guts e
dslExprType guts e@(_ :@ _)
  | (Var f, args) <- collectArgs e = do
    pairExpId <- lift $ findDataConWorkIdTH guts 'PairExp
    leftExpId <- lift $ findDataConWorkIdTH guts 'LeftExp
    rightExpId <- lift $ findDataConWorkIdTH guts 'RightExp

    pairExpWrapId <- lift $ findIdTH guts 'PairExp
    rightExpWrapId <- lift $ findIdTH guts 'RightExp

    expTyCon <- lift $ findTyConTH guts ''GPUExp
    pairTyCon <- lift $ findTyConTH guts ''(,)
    eitherTyCon <- lift $ findTyConTH guts ''Either

    if | f == pairExpId || f == pairExpWrapId ->
          case args of
            (Type resTy:Type ty1:Type ty2:Coercion co:x1:x2:rest) ->
              return $ mkTyConApp expTyCon [resTy]
            _ -> return $ exprType e
       | f == rightExpId || f == rightExpWrapId ->
          case args of
            (Type ty1:Type ty2:x:rest) ->
              return $ mkTyConApp expTyCon [mkTyConApp eitherTyCon [ty1, ty2]]
            _ -> return $ exprType e
       | otherwise -> return $ exprType e
dslExprType guts e = return $ exprType e

updateUnitTypeProofs :: ModGuts -> CoreExpr -> MatchM CoreExpr
updateUnitTypeProofs guts e@(Cast (Var x) co) = do
  unitExpId <- lift $ findDataConWorkIdTH guts 'UnitExp
  unitExpWrapId <- lift $ findIdTH guts 'UnitExp

  dflags <- getDynFlags
  if {- x == unitExpId || -} x == unitExpWrapId
    then do
      traceM "unitExp found"

      (co'0, ty') <- lift $ normaliseTypeCo guts (coercionLKind co)

      let co' = downgradeRole Representational (coercionRole co'0) co'0

      traceM $ "unit: co' kinds = " ++ showPpr dflags (coercionKind co')
      traceM $ "unit: co kinds  = " ++ showPpr dflags (coercionKind co)


      traceM $ "unit: co role = " ++ showPpr dflags (coercionRole co)

      let co'' = mkTransCo (mkSymCo co') co

      traceM $ "unit: trans co kinds = " ++ showPpr dflags (coercionKind co'')

      return $ Cast (Var x) co''
    else
      Data.descendM (updateUnitTypeProofs guts) e
updateUnitTypeProofs guts e =
  Data.descendM (updateUnitTypeProofs guts) e

updateTypeProofs :: ModGuts -> CoreExpr -> MatchM CoreExpr
updateTypeProofs guts e = do
  dflags <- getDynFlags
  Data.transformM (updateTypeProofs0 guts) e
  -- updateUnitTypeProofs guts =<< fmap (repeatCaseFloat . Data.transform (combineCasts dflags) . Data.transform letNonRecSubst) (updateTypeProofs0 guts =<< updateUnitTypeProofs guts e)

updateTypeProofs0 :: ModGuts -> CoreExpr -> MatchM CoreExpr
updateTypeProofs0 guts e@(_ :@ _)
  | (Var f, args) <- collectArgs e = do
      pairExpId <- lift $ findDataConWorkIdTH guts 'PairExp
      leftExpId <- lift $ findDataConWorkIdTH guts 'LeftExp
      rightExpId <- lift $ findDataConWorkIdTH guts 'RightExp
      constructRepId <- lift $ findDataConWorkIdTH guts 'ConstructRep

      pairExpWrapId <- lift $ findIdTH guts 'PairExp
      rightExpWrapId <- lift $ findIdTH guts 'RightExp
      leftExpWrapId <- lift $ findIdTH guts 'LeftExp

      typeableTyCon <- lift $ findTyConTH guts ''Typeable
      expTyCon <- lift $ findTyConTH guts ''GPUExp
      repTyTyCon <- lift $ findTyConTH guts ''GPURepTy

      unitExpId <- lift $ findDataConWorkIdTH guts 'UnitExp

      pairExpWorkId <- lift $ findDataConWorkIdTH guts 'PairExp
      leftExpWorkId <- lift $ findDataConWorkIdTH guts 'LeftExp
      rightExpWorkId <- lift $ findDataConWorkIdTH guts 'RightExp
      constructRepWorkId <- lift $ findDataConWorkIdTH guts 'ConstructRep
      unitExpWorkId <- lift $ findDataConWorkIdTH guts 'UnitExp

      constructRepWrapId <- lift $ findIdTH guts 'ConstructRep
      unitExpWrapId <- lift $ findIdTH guts 'UnitExp

      let dslConstructorIds = [pairExpWorkId, pairExpWrapId, constructRepWorkId, constructRepWrapId, leftExpWorkId, rightExpWorkId, leftExpWrapId, rightExpWrapId, unitExpWorkId, unitExpWrapId]

      unitExpWrapId <- lift $ findIdTH guts 'UnitExp

      dflags <- getDynFlags

      -- traceM $ "checking " ++ showPpr dflags f ++ " vs " ++ showPpr dflags pairExpId

      if | f == pairExpId || f == pairExpWrapId -> do
            traceM $ "pairExpId transform, length args = " ++ show (length args)
            traceM $ "args = " ++ showPpr dflags args

            case args of
              (Type resTy:Type ty1:Type ty2:Coercion co:x1:x2:rest)
                  | noFreeVarsOfType resTy && noFreeVarsOfType ty1 && noFreeVarsOfType ty2 -> do

                -- ty1' <- lift $ normaliseType' guts ty1
                -- ty2' <- lift $ normaliseType' guts ty2

                (co', resTy') <- lift $ normaliseTypeCo guts resTy

                -- let co' = mkReflCo Nominal resTy
                -- traceM $ "ty1' = " ++ showPpr dflags ty1'

                -- traceM $ "resTy = " ++ showPpr dflags resTy
                -- traceM $ "x1 = " ++ showPpr dflags x1
                -- traceM $ "x2 = " ++ showPpr dflags x2

                traceM $ "pair co kind: " ++ showPpr dflags (coercionKind co)
                traceM $ "pair co' kind: " ++ showPpr dflags (coercionKind co')


                -- x1' <- {- fmap removeCasts $ -} Data.descendM (updateTypeProofs guts) x1
                -- x2' <- {- fmap removeCasts $ -} Data.descendM (updateTypeProofs guts) x2

                let x1' = maybeApply (removeCastsOfAppFns_maybe dslConstructorIds) x1
                    x2' = maybeApply (removeCastsOfAppFns_maybe dslConstructorIds) x2

                ty1 <- dslExprType guts x1'
                ty2 <- dslExprType guts x2'

                (x1'_co, x1'_ty) <- (lift . (normaliseTypeCo guts)) ty1
                (x2'_co, x2'_ty) <- (lift . (normaliseTypeCo guts)) ty2

                ty1' <- lift $ unwrapExpType guts x1'_ty
                ty2' <- lift $ unwrapExpType guts x2'_ty

                traceM $ "x1' = " ++ showPpr dflags x1'
                traceM $ "x2' = " ++ showPpr dflags x2'

                traceM $ "x1' ty, co: " ++ showPpr dflags (exprType x1', coercionKind x1'_co)
                traceM $ "x2' ty, co: " ++ showPpr dflags (exprType x2', coercionKind x2'_co)
                traceM ""

                let x1'' = x1' --Cast x1' $ downgradeRole Representational (coercionRole x1'_co) x1'_co
                    x2'' = x2' --Cast x2' $ downgradeRole Representational (coercionRole x2'_co) x2'_co

                -- let co'' = mkTransCo co co'
                let co'' = mkReflCo (coercionRole co) resTy'

                traceM $ "trans co: " ++ showPpr dflags (coercionKind (mkTransCo co co'))

                return (foldl (:@) (Var f :@ Type resTy' :@ Type ty1' :@ Type ty2' :@ Coercion co'') (x1'':x2'':rest))
              _ -> return e
         | f == constructRepId -> do
            traceM $ "constructRepId, length args = " ++ show (length args)
            case args of
              (Type ty:dict1:dict2:x:rest)
                | noFreeVarsOfType ty -> do

                  traceM $ "constructRepId case"

                  (co'0, ty') <- lift $ normaliseTypeCo guts (mkTyConApp expTyCon [mkTyConApp repTyTyCon [ty]])
                  let co' = mkSymCo co'0

                  -- x' <- Data.descendM (updateTypeProofs guts) x
                  let x' = maybeApply (removeCastsOfAppFns_maybe dslConstructorIds) x

                  dslTy <- dslExprType guts x'
                  -- let dslTy = dslExprType x'

                  (x'_co, x'_ty) <- (lift . (normaliseTypeCo guts)) dslTy

                  let co'' = mkTransCo x'_co co'

                  let x'' = updateCast x' $ downgradeRole Representational (coercionRole x'_co) co' --co'' --x'_co


                  traceM ""
                  traceM $ "dslExprType of " ++ showPpr dflags x'

                  traceM ""
                  traceM "---"
                  traceM $ "x'_co = " ++ showPpr dflags (coercionKind x'_co)
                  traceM $ "co' = " ++ showPpr dflags (coercionKind co')
                  traceM $ "co'' = " ++ showPpr dflags (coercionKind co'')
                  traceM $ "dslTy = " ++ showPpr dflags dslTy
                  -- traceM $ "exprTy = " ++ showPpr dflags (exprType x')
                  traceM $ "x' = " ++ showPpr dflags x'
                  traceM $ "dict1 = " ++ showPpr dflags dict1
                  traceM "---"
                  traceM ""

                  -- ty' <- (lift . unwrapExpType guts) =<< (dslExprType guts x')

                  typeType <- lift $ findTypeTH guts ''Kind.Type
                  -- dict1' <- lift $ buildDictionaryT guts (mkTyConApp typeableTyCon [typeType, ty'])
                  -- dict2' <- lift $ buildDictionaryT guts (mkTyConApp expTyCon [ty'])

                  return (foldl (:@) (Var f :@ Type ty) (dict1:dict2:x'':rest))
              _ -> return e --Data.descendM (updateTypeProofs guts) e
         | {- f == rightExpId || -} f == rightExpWrapId ->
            case args of
              (Type ty1:Type ty2:x:rest)
                | noFreeVarsOfType ty1 && noFreeVarsOfType ty2 -> do
                  (_co1', ty1') <- lift $ normaliseTypeCo guts ty1
                  (co2', ty2') <- lift $ normaliseTypeCo guts ty2

                  when (f == rightExpId) (traceM ("rightExp: e = " ++ showPpr dflags e))

                  -- x' <- Data.descendM (updateTypeProofs guts) x
                  let x' = maybeApply (removeCastsOfAppFns_maybe dslConstructorIds) x

                  (coX', tyX') <- (lift . normaliseTypeCo guts) (exprType x')

                  let x'' = x' --updateCast x' $ downgradeRole Representational (coercionRole co2') coX'

                  return $ foldl (:@) (Var f :@ Type ty1' :@ Type ty2') (x'':rest)
              _ -> return e

         | {- f == leftExpId || -} f == leftExpWrapId -> do --Data.descendM (updateTypeProofs guts) e --undefined
            case args of
              (Type ty1:Type ty2:x:rest)
                | noFreeVarsOfType ty1 && noFreeVarsOfType ty2 -> do
                  (co1', ty1') <- lift $ normaliseTypeCo guts ty1
                  (_co2', ty2') <- lift $ normaliseTypeCo guts ty2

                  -- x' <- Data.descendM (updateTypeProofs guts) x
                  let x' = maybeApply (removeCastsOfAppFns_maybe dslConstructorIds) x

                  (coX', tyX') <- (lift . normaliseTypeCo guts) (exprType x')

                  let x'' = x' --updateCast x' $ downgradeRole Representational (coercionRole co1') coX'

                  return $ foldl (:@) (Var f :@ Type ty1' :@ Type ty2') (x'':rest)
              _ -> return e

         | otherwise -> return e
{-
updateTypeProofs0 guts e@(Cast (Var x) co) = do
  unitExpId <- lift $ findDataConWorkIdTH guts 'UnitExp
  unitExpWrapId <- lift $ findIdTH guts 'UnitExp

  dflags <- getDynFlags
  if x == unitExpId || x == unitExpWrapId
    then do

      (co', ty') <- lift $ normaliseTypeCo guts (coercionLKind co)
      traceM $ "unit: co' kinds = " ++ showPpr dflags (coercionKind co')
      traceM $ "unit: co kinds  = " ++ showPpr dflags (coercionKind co)
      Data.descendM (updateTypeProofs guts) e
    else do
      traceM $ "not unit: " ++ showPpr dflags x
      Data.descendM (updateTypeProofs guts) e
-}

updateTypeProofs0 guts e = return e
  -- Data.descendM (updateTypeProofs guts) e

updateCast :: CoreExpr -> Coercion -> CoreExpr
updateCast (Cast e _) co = updateCast e co
updateCast e co = Cast e co

-- -- TODO: Maybe the coercionEnv should be something where you "use up"
-- -- coercions, like popping off of a stack (kind of linear in a way)
-- updateTypeProofs :: ModGuts -> [Coercion] -> Maybe CoreType -> CoreExpr -> MatchM CoreExpr
-- updateTypeProofs guts coercionEnv thisType_M e@(_ :@ _)

{-
updateTypeProofs :: ModGuts -> CoreExpr -> MatchM CoreExpr
updateTypeProofs guts e@(_ :@ _)
  | (Var f, args) <- collectArgs e = do
      pairExpId <- lift $ findDataConWorkIdTH guts 'PairExp
      leftExpId <- lift $ findDataConWorkIdTH guts 'LeftExp
      rightExpId <- lift $ findDataConWorkIdTH guts 'RightExp
      constructRepId <- lift $ findDataConWorkIdTH guts 'ConstructRep

      rightExpWrapId <- lift $ findIdTH guts 'RightExp

      dflags <- getDynFlags

      -- traceM $ "checking " ++ showPpr dflags f ++ " vs " ++ showPpr dflags pairExpId

      if | f == pairExpId -> do
            -- traceM $ "pairExpId transform, length args = " ++ show (length args)
            -- traceM $ "args = " ++ showPpr dflags args

            case args of
              (Type resTy:Type ty1:Type ty2:Coercion co:x1:x2:rest)
                  | noFreeVarsOfType resTy && noFreeVarsOfType ty1 && noFreeVarsOfType ty2 -> do
                ty1' <- lift $ normaliseType' guts ty1
                ty2' <- lift $ normaliseType' guts ty2

                (co', resTy') <- lift $ normaliseTypeCo guts resTy

                -- let co' = mkReflCo Nominal resTy
                -- traceM $ "ty1' = " ++ showPpr dflags ty1'

                traceM $ "x1 = " ++ showPpr dflags x1
                traceM $ "x2 = " ++ showPpr dflags x2
                traceM $ "pair co kind: " ++ showPpr dflags (coercionKind co)
                traceM $ "pair co' kind: " ++ showPpr dflags (coercionKind co')

                (x1_co, _) <- lift $ normaliseTypeCo guts (exprType x1)
                (x2_co, _) <- lift $ normaliseTypeCo guts (exprType x2)

                let x1'
                      | noFreeVarsOfType (exprType x1) = Cast x1 $ downgradeRole Representational (coercionRole x1_co) x1_co
                      | otherwise = x1
                    x2'
                      | noFreeVarsOfType (exprType x2) = Cast x2 $ downgradeRole Representational (coercionRole x2_co) x2_co
                      | otherwise = x2

                -- let co'' = mkTransCo co co'
                let co'' = mkReflCo (coercionRole co) resTy'

                return (foldl (:@) (Var f :@ Type resTy' :@ Type ty1' :@ Type ty2' :@ Coercion co'') (x1':x2':rest))
              _ -> return e
         | f == constructRepId -> do
            traceM $ "constructRepId, length args = " ++ show (length args)
            case args of
              (Type ty:dict1:dict2:rest) -> do

                  traceM $ "constructRepId case"

                  ty' <- lift $ normaliseType' guts ty

                  return (foldl (:@) (Var f :@ Type ty') (dict1:dict2:rest))
              _ -> return e
         | f == rightExpId || f == rightExpWrapId ->
            case args of
              (Type ty1:Type ty2:rest) -> do
                (_co1', ty1') <- lift $ normaliseTypeCo guts ty1
                (_co2', ty2') <- lift $ normaliseTypeCo guts ty2


                return $ foldl (:@) (Var f :@ Type ty1' :@ Type ty2') rest
              _ -> return e
         | f == leftExpId -> return e --undefined
         | otherwise -> return e
updateTypeProofs guts e@(Cast app@(_ :@ _) co)
  | noFreeVarsOfType (exprType app) && not (exprType app `eqType` coercionLKind co) = do -- TODO: Make sure this works ok with polymorphic types

      dflags <- getDynFlags

      let (fn, _) = collectArgs app

      traceM $ "updateTypeProofs: fn = " ++ showPpr dflags fn

      traceM $ "updateTypeProofs: tys = " ++ showPpr dflags (exprType app, coercionLKind co, coercionRKind co)

      (coL, tyL) <- lift $ normaliseTypeCo guts (coercionLKind co)

      (coApp, tyApp) <- lift $ normaliseTypeCo guts (exprType app)

      (co'0, ty') <- lift $ normaliseTypeCo guts (coercionRKind co)

      let co' = mkSymCo $ downgradeRole (coercionRole co) (coercionRole co'0) co'0

      traceM $ "updateTypeProofs: coL: " ++ showPpr dflags (coercionKind coL)
      traceM $ "updateTypeProofs: coApp: " ++ showPpr dflags (coercionKind coApp)
      traceM $ "updateTypeProofs: co'0: " ++ showPpr dflags (coercionKind co'0)
      traceM $ "exprType app: " ++ showPpr dflags (exprType app)
      traceM ""

      return (Cast app co')
      -- return app
      -- return e
updateTypeProofs _ e@(Case s wild ty alts@((_, _, rhs):rest))
  | noFreeVarsOfType (exprType rhs) && not (ty `eqType` exprType rhs) = -- TODO: Make sure this works ok with polymorphic types
      return (Case s wild (exprType rhs) alts)

updateTypeProofs _ e = return e
-}

applyUnrep :: ModGuts -> CoreExpr -> MatchM CoreExpr
applyUnrep guts e = do
  dflags <- getDynFlags

  ty <- lift $ unwrapExpType guts (exprType e)

  unrepId <- lift $ findIdTH guts 'unrep

  let result = (Var unrepId :@ Type ty :@ e)

  traceM $ "applyUnrep: exprType e = " ++ showPpr dflags ty
  traceM $ "applyUnrep type: " ++ showPpr dflags (exprType result)
  return result


-- | rep (unrep x)  ==>  x
elimRepUnrep :: ModGuts -> CoreExpr -> MatchM CoreExpr
elimRepUnrep guts expr0@(Cast e co) = elimRepUnrep_co guts (Just co) origType e
  where origType = exprType expr0
-- elimRepUnrep guts (Cast e co) = do
--   e' <- elimRepUnrep_co guts Nothing e
--   return $ Cast e' co
elimRepUnrep guts expr = elimRepUnrep_co guts Nothing (exprType expr) expr

elimRepUnrep_co :: ModGuts -> Maybe Coercion -> Type -> CoreExpr -> MatchM CoreExpr
elimRepUnrep_co guts coA_M origType expr@(Var r :@ Type{} :@ dict :@ arg) =
  go0 arg
  where
    go0 e =
      case e of
        Var u :@ Type{} :@ x -> go e u Nothing x
        Cast (Var u :@ Type{} :@ x) coB -> go e u (Just coB) x
        _ -> Data.descendM (elimRepUnrep guts) expr

    go :: CoreExpr -> Id -> Maybe Coercion -> CoreExpr -> MatchM CoreExpr
    go unrepped u coB_M x = do
      dflags <- getDynFlags

      repId <- lift $ findIdTH guts 'rep
      unrepId <- lift $ findIdTH guts 'unrep
      expTyCon <- lift $ findTyConTH guts ''GPUExp

      -- traceM $ "building coercion: " ++ showPpr dflags (exprType x, origType)
      -- traceM $ "coA_M = " ++ showPpr dflags (fmap coercionKind coA_M)
      -- traceM $ "coB_M = " ++ showPpr dflags (fmap coercionKind coB_M)

      let co_M = do
                    guard (isJust coA_M || isJust coB_M)
                    let newCo = buildCoercion (exprType x) origType

                    -- traceM $ "newCo = {" ++ showPpr dflags newCo ++ "}"

                    newCo' <- case splitTyConApp_maybe (coercionRKind newCo) of
                                Just (tyCon, _)
                                  | tyCon == expTyCon -> return newCo
                                _ -> Just $ buildCoercion (mkTyConApp expTyCon [exprType x]) (mkTyConApp expTyCon [origType])


                    traceM $ "kinds of coA_M and coB_M: " ++ showPpr dflags (fmap coercionKind coA_M, fmap coercionKind coB_M)
                    traceM $ "newCo' kind = " ++ showPpr dflags (coercionKind newCo')
                    -- traceM $ "newCo' = {" ++ showPpr dflags newCo' ++ "}"

                    let newCo'' =
                          case coA_M of
                            Nothing -> newCo'
                            Just coA -> mkTransCo newCo' coA

                    traceM $ "newCo'' kind = " ++ showPpr dflags (coercionKind newCo'')

                    Just $ downgradeRole Representational (coercionRole newCo'') newCo''


      if r == repId && u == unrepId
        then do

          traceM ""
          -- traceM $ "co_M = " ++ showPpr dflags co_M
          -- traceM $ "elimRepUnrep_co: origType = " ++ showPpr dflags origType
          traceM $ "elimRepUnrep_co: co kinds: " ++ showPpr dflags (fmap coercionKind coA_M, fmap coercionKind coB_M)
          -- traceM $ "======================> x =" ++ showPpr dflags x
          traceM $ "======================> expr =" ++ showPpr dflags x

          let x' = x  --coerceMaybe co_M x

          unconstructRepId <- lift $ findIdTH guts 'UnconstructRep
          ty <- lift $ unwrapExpType guts (exprType unrepped)


          traceM ""
          traceM $ "unrepped type = " ++ showPpr dflags (exprType unrepped)
          traceM $ "unrepped = " ++ showPpr dflags unrepped
          traceM $ "--->" ++ showPpr dflags (Var unconstructRepId :@ Type ty :@ x')

          if not $ eqType ty (exprType unrepped)
            then traceM "not eqType" >> Data.descendM (elimRepUnrep guts) x'
            else {- fmap (Var unconstructRepId :@ Type ty :@) -} (elimRepUnrep guts x')
        else Data.descendM (elimRepUnrep guts) expr--return $ coerceMaybe coA_M expr

    composeCos = mkTransCo

elimRepUnrep_co guts co_M _ expr = Data.descendM (elimRepUnrep guts) $ coerceMaybe co_M expr

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

  lamId <- lift $ findIdTH guts 'Expr.Lam
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

  traceM $ "markedSubstE' = " ++ showPpr dflags (Data.transform (go varId newTy) markedSubstE')
  -- markedSubstE'' <- mark0 guts markedSubstE'

  return (Var lamId :@ Type origTy :@ Type eTy' :@ repDict :@ typeableDict :@ nameVal
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

mkAppCo' :: Coercion -> Coercion -> Coercion
mkAppCo' coA coB =
      mkTransAppCo
        (coercionRole coA)
        coA
        (coercionLKind coA)
        (coercionRKind coA)

        (coercionRole coB)
        coB
        (coercionLKind coB)
        (coercionRKind coB)

        (coercionRole coA)


-- Taken from an older version of Coercion in the GHC API:

-- | Like 'mkAppCo', but allows the second coercion to be other than
-- nominal. See Note [mkTransAppCo]. Role r3 cannot be more stringent
-- than either r1 or r2.
mkTransAppCo :: Role         -- ^ r1
             -> Coercion     -- ^ co1 :: ty1a ~r1 ty1b
             -> Type         -- ^ ty1a
             -> Type         -- ^ ty1b
             -> Role         -- ^ r2
             -> Coercion     -- ^ co2 :: ty2a ~r2 ty2b
             -> Type         -- ^ ty2a
             -> Type         -- ^ ty2b
             -> Role         -- ^ r3
             -> Coercion     -- ^ :: ty1a ty2a ~r3 ty1b ty2b
mkTransAppCo r1 co1 ty1a ty1b r2 co2 ty2a ty2b r3
-- How incredibly fiddly! Is there a better way??
  = case (r1, r2, r3) of
      (_,                _,                Phantom)
        -> mkPhantomCo kind_co (mkAppTy ty1a ty2a) (mkAppTy ty1b ty2b)
        where -- ty1a :: k1a -> k2a
              -- ty1b :: k1b -> k2b
              -- ty2a :: k1a
              -- ty2b :: k1b
              -- ty1a ty2a :: k2a
              -- ty1b ty2b :: k2b
              kind_co1 = mkKindCo co1        -- :: k1a -> k2a ~N k1b -> k2b
              kind_co  = mkNthCo Nominal 1 kind_co1  -- :: k2a ~N k2b

      (_,                _,                Nominal)
        -> --ASSERT( r1 == Nominal && r2 == Nominal )
           mkAppCo co1 co2
      (Nominal,          Nominal,          Representational)
        -> mkSubCo (mkAppCo co1 co2)
      (_,                Nominal,          Representational)
        -> --ASSERT( r1 == Representational )
           mkAppCo co1 co2
      (Nominal,          Representational, Representational)
        -> go (mkSubCo co1)
      (_               , _,                Representational)
        -> --ASSERT( r1 == Representational && r2 == Representational )
           go co1
  where
    go co1_repr
      | Just (tc1b, tys1b) <- splitTyConApp_maybe ty1b
      , nextRole ty1b == r2
      = (mkAppCo co1_repr (mkNomReflCo ty2a)) `mkTransCo`
        (mkTyConAppCo Representational tc1b
           (zipWith mkReflCo (tyConRolesRepresentational tc1b) tys1b
            ++ [co2]))

      | Just (tc1a, tys1a) <- splitTyConApp_maybe ty1a
      , nextRole ty1a == r2
      = (mkTyConAppCo Representational tc1a
           (zipWith mkReflCo (tyConRolesRepresentational tc1a) tys1a
            ++ [co2]))
        `mkTransCo`
        (mkAppCo co1_repr (mkNomReflCo ty2b))

      | otherwise
      = pprPanic "mkTransAppCo" (vcat [ ppr r1, ppr co1, ppr ty1a, ppr ty1b
                                      , ppr r2, ppr co2, ppr ty2a, ppr ty2b
                                      , ppr r3 ])

