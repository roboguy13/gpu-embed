{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

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

import qualified Data.Kind as Kind

import           Control.Monad
import           Control.Monad.Writer hiding (pass, Alt)
import           Control.Monad.State

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

    go1 new_mg_binds (NonRec name e) =
      fmap (NonRec name) (transformExpr (guts {mg_binds = new_mg_binds}) name Nothing primMap e)

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

untilNothingM :: Monad m => (a -> m (Maybe a)) -> a -> m a
untilNothingM f = go
  where
    go x = do
      fx <- f x
      case fx of
        Just r  -> go r
        Nothing -> return x

transformExpr :: ModGuts -> Var -> Maybe Var -> [(Id, CoreExpr)] -> Expr Var -> MatchM (Expr Var)
transformExpr guts currName recNameM primMap =
  {- transformApps guts <=< -} untilNothingM (transformExprMaybe guts currName recNameM primMap)


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

-- whenNotExprTyped :: ModGuts -> CoreExpr -> MatchM CoreExpr -> MatchM CoreExpr
-- whenNotExprTyped guts e m = do
--   eType <- hasExprType guts e
--   if eType
--     then return e
--     else m

isVar :: Expr a -> Bool
isVar (Var _) = True
isVar _ = False

-- Mark for further transformation
mark0 :: HasCallStack => ModGuts -> Expr Var -> MatchM (Expr Var)
mark0 guts x = do
  dflags <- getDynFlags
  expTyCon <- lift $ findTyConTH guts ''GPUExp

  eType <- hasExprType guts x
  -- liftIO $ putStrLn $ "mark0 exprType = " ++ showPpr dflags (exprType x)
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
      varId <- lift $ findIdTH guts 'Expr.Var

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
        , Var         -- Constructor name
        , [Expr Var]) -- Constructor arguments
getConstructorApp_maybe e = 
  case go e of
    -- Just (_, _, _, []) -> Nothing -- TODO: Do we want this?
    (Just (_, _, constr, _))
      | builtinConstructor constr -> Nothing
    r -> r
  where
    go (Var v)
      | isConstructor v = Just ([], [], v, [])
    go (App f x)
      | isTypeArg x = do
          (tys, dicts, constr, args) <- go f
          return (x:tys, dicts, constr, args)

      | isCoArg x || isDict x = do
          (tys, dicts, constr, args) <- go f
          return (tys, x:dicts, constr, args)

      | otherwise             = do
          (tys, dicts, constr, args) <- go f
          return (tys, dicts, constr, x:args)

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

  go0 (== fromIntegral) (== fromInteger) expTyCon (== lamId) e
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

    go0 isFromIntegral isFromInteger expTyCon isLam = go
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
              return (b :@ ty :@ dict :@ markedX :@ markedY)

        go expr@(Var f :@ tyA@(Type{}) :@ tyB@(Type{}) :@ x :@ y)
          | Just b <- builtin f,
            not (hasExprTy expr) = do
              markedX <- mark x
              markedY <- mark y
              return (b :@ tyA :@ tyB :@ markedX :@ markedY)

        go expr@(Var f :@ tyA@(Type{}) :@ tyB@(Type{}) :@ x)
          | Just b <- builtin f,
            not (hasExprTy expr) = do
              dflags <- getDynFlags
              liftIO $ putStrLn ""
              liftIO $ putStrLn $ "---------- builtin: " ++ showPpr dflags b
              liftIO $ putStrLn $ "---------- arg:     " ++ showPpr dflags x
              liftIO $ putStrLn ""
              markedX <- mark x
              return (b :@ tyA :@ tyB :@ markedX)

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
          | Just (tys, dicts, constr, args0) <- getConstructorApp_maybe expr,
            Nothing <- builtin constr,
            not (hasExprTy expr),
            not (isDict (Var constr)) = do

            let args = reverse args0  -- TODO: Why is this necessary?

            dflags <- getDynFlags
            constructRepId <- lift $ findIdTH guts 'ConstructRep

            if constr == constructRepId
              then return expr
              else do

                liftIO $ putStrLn ""
                liftIO $ putStrLn $ "Handling constructor: " ++ showPpr dflags constr
                -- liftIO $ putStrLn $ "  ==> with args:      " ++ showPpr dflags args
                -- liftIO $ putStrLn ""

                repTyCon <- lift $ findTyConTH guts ''GPURep
                repTyTyCon <- lift $ findTyConTH guts ''GPURepTy

                dflags <- lift $ getDynFlags

                repDictExpr <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [exprType expr])
                repDictRepTy <- lift $ buildDictionaryT guts (mkTyConApp repTyCon [mkTyConApp repTyTyCon [exprType expr]])
                repId <- lift $ findIdTH guts 'rep
                constructFnId <- lift $ findIdTH guts 'construct

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


                liftIO $ putStrLn $ "repUnfolding = {" ++ showPpr dflags repUnfolding ++ "}"

                let (fn, restArgs) = betaReduceAll
                                       repUnfolding
                                         [ Type (exprType expr)
                                         , repDictExpr
                                         -- , (mkApps constr' args)
                                         ]

                let repFn1 = caseInline dflags $ Data.transform letNonRecSubst fn
                    (repFnE, _) = collectArgs repFn1

                    repFn =
                      case repFnE of
                        Var f -> Just f
                        _ -> Nothing

                let expr2' = Data.transform letNonRecSubst fn

                let e' =
                         onScrutinee (unfoldAndReduceDict guts dflags) --(Data.transform (tryUnfoldAndReduceDict guts dflags))
                             $ Data.transform letNonRecSubst fn

                -- let e' = Data.transform letNonRecSubst $ Data.transform (tryUnfoldAndReduceDict guts dflags) fn
                let e'' =
                      onScrutinee (Data.transform (tryUnfoldAndReduceDict guts dflags)) $
                        Data.transform (caseInlineT dflags) $ onScrutinee (Data.transform betaReduce) e'

                let (Var dictFn, dictArgs) = collectArgs e''

                let reduceConstruct arg
                      = Data.transform betaReduce $ Data.transform (maybeTransform3 targetTheFn constructFn (Data.transform (tryUnfoldAndReduceDict guts dflags) . unfoldAndReduceDict guts dflags)) $ Data.transform letNonRecSubst $ Data.transform betaReduce $
                      onAppFun (tryUnfoldAndReduceDict guts dflags) $
                      arg


                let simplE' = reduceConstruct e''


                let fnE = Data.transform letNonRecSubst
                            $ whileRight (unfoldAndReduceDict_either guts dflags) simplE'
                               -- $ Data.transform (targetTheFnMaybe repFn (Data.transform (tryUnfoldAndReduceDict guts dflags))) simplE'

                unreppedArgs <- mapM (applyUnrep guts <=< mark) args
                unrepId <- lift $ findIdTH guts 'unrep

                let (newExpr, remainingArgs) = betaReduceAll fnE [mkApps constr' unreppedArgs]
                let newExpr' = (Data.transform betaReduce . Data.transform letNonRecSubst)
                              $ caseInlineT dflags (mkApps newExpr remainingArgs)

                let transformUnrepParent = targetParentOfFnApp dflags unrepId (applyWhen (isDictNotClassApp dflags) (unfoldAndReduceDict guts dflags))

                let newExpr''0 = Data.transform (whileRight (castFloatAppEither dflags)) . Data.transform transformUnrepParent $ onAppFun (tryUnfoldAndReduceDict guts dflags) $ Data.transform (caseInlineT dflags) newExpr'

                newExpr''1 <- Data.transformM (elimRepUnrep guts) $ Data.transform betaReduce newExpr''0

                liftIO $ putStrLn $ "constructUnfolding = " ++ showPpr dflags constructUnfolding

                -- Unfold a 'construct'
                let newExpr''2
                      = -- Data.transform betaReduce $ Data.transform (maybeApply (fmap (Data.transform (caseInline dflags) . betaReduce . Data.transform (caseInline dflags)) . unfoldTheFn_maybe guts dflags constructFnId))
                        Data.transform betaReduce $ Data.transform (tryCastFloatApp dflags) $ caseInlineT dflags $ Data.transform betaReduce $ Data.transform (maybeApply (fmap betaReduce . unfoldTheFn_maybe guts dflags constructFnId))
                        $ Data.transform betaReduce $ targetLastAppArg (Data.transform letNonRecSubst . Data.transform caseInlineDefault . betaReduce . onAppFun (tryUnfoldAndReduceDict guts dflags)) $ Data.transform (maybeApply (fmap (Data.transform letNonRecSubst . tryUnfoldAndReduceDict guts dflags . caseInlineT dflags) . onScrutinee_maybe (unfoldAndReduceDict_maybe guts dflags)))
                        $ targetAppArgs betaReduce
                        $ betaReduce
                        $ targetAppArgs betaReduce
                        $ Data.transform
                          (maybeApply (fmap (Data.transform (tryUnfoldAndReduceDict guts dflags) . betaReduce) . unfoldTheFn_maybe guts dflags constructFnId))
                          $ Data.transform letNonRecSubst newExpr''1

                fromFnId <- lift $ findIdTH guts 'from

                -- Unfold a 'from'
                let newExpr''3
                        =
                          Data.transform (caseInline dflags) $
                          Data.transform betaReduce $
                          Data.transform (maybeApply (fmap (unfoldAndReduceDict guts dflags . caseInline dflags) . onScrutinee_maybe (unfoldAndReduceDict_maybe guts dflags))) $
                          Data.transform betaReduce $
                          Data.transform (maybeApply (unfoldTheFn_maybe guts dflags fromFnId)) $
                          newExpr''2

                -- Unfold a 'construct'
                let newExpr''4
                        =
                          Data.transform betaReduce $
                          Data.transform (caseInline dflags) $
                          Data.transform (maybeApply (onScrutinee_maybe (unfoldAndReduceDict_maybe guts dflags))) $
                          Data.transform betaReduce $
                          Data.transform (maybeApply (unfoldTheFn_maybe guts dflags constructFnId)) $
                          newExpr''3

                repClassName <- fmap tyConName $ lift $ findTyConTH guts ''GPURep

                constructRepConstructorId <- lift $ findIdTH guts 'ConstructRep

                -- Unfold another 'construct'
                -- TODO: Automate these 'construct' unfolding steps
                -- (including the next 'let')
                let newExpr''5
                        =
                          -- Data.transform (targetTheFnApp constructRepConstructorId (targetLastAppArg (descendAppLhs (onAppFunId (getUnfolding guts dflags))))) $
                          -- Data.transform (maybeApply (whenVarHasClassName_maybe repClassName (tryUnfoldAndReduceDict guts dflags))) $
                          Data.transform (caseInline dflags) $
                          Data.transform betaReduce $
                          Data.transform (maybeApply (fmap (tryUnfoldAndReduceDict guts dflags) . caseInline_maybe dflags)) $
                          -- Data.transform (maybeApply (onScrutinee_maybe (unfoldAndReduceDict_maybe guts dflags))) $
                          Data.transform betaReduce $
                          Data.transform (maybeApply (unfoldTheFn_maybe guts dflags constructFnId)) $
                          newExpr''4

                let newExpr''6
                      =
                          Data.transform combineCasts $

                          Data.transform (caseInline dflags) $
                          Data.transform betaReduce $
                          Data.transform (maybeApply (fmap (tryUnfoldAndReduceDict guts dflags) . caseInline_maybe dflags)) $
                          -- Data.transform (maybeApply (onScrutinee_maybe (unfoldAndReduceDict_maybe guts dflags))) $
                          Data.transform betaReduce $
                          Data.transform (maybeApply (unfoldTheFn_maybe guts dflags constructFnId)) $



                          Data.transform (caseInline dflags) $
                          Data.transform betaReduce $
                          Data.transform (maybeApply (fmap (tryUnfoldAndReduceDict guts dflags) . caseInline_maybe dflags)) $
                          -- Data.transform (maybeApply (onScrutinee_maybe (unfoldAndReduceDict_maybe guts dflags))) $
                          Data.transform betaReduce $
                          Data.transform (maybeApply (unfoldTheFn_maybe guts dflags constructFnId)) $
                          newExpr''5

                newExpr'' <- Data.transformM (targetCastM (elimRepUnrep guts)) $ newExpr''6

                -- case newExpr'' of
                --   App{} ->
                --     let (f, _) = collectArgs newExpr''
                --     in
                --     liftIO $ putStrLn $ "newExpr'' f = " ++ showPpr dflags f
                --   _ -> return ()

                -- let newExpr''
                --       = Data.transform ((maybeTransform3 targetTheFn constructFn (tryUnfoldAndReduceDict guts dflags))) newExpr''2

                -- newExpr'' <- return $ Data.transform (caseInlineT dflags) $ Data.transform betaReduce $ Data.transform (tryUnfoldAndReduceDict guts dflags) $ Data.transform (caseInlineT dflags) $ Data.transform (tryUnfoldAndReduceDict guts dflags) $ Data.transform betaReduce $ Data.transform (targetTheFn constructFnId (const constructUnfolding)) $ Data.transform betaReduce $ Data.transform letNonRecSubst newExpr''1 --Data.transformM (elimUnrepExternalize guts) newExpr''1

                -- let newExpr'' = Data.transform (targetTheFnMaybe constructFn (Data.transform (tryUnfoldAndReduceDict guts dflags))) newExpr''1

                -- liftIO $ putStrLn $ "fn = " ++ showPpr dflags fn ++ "\n"
                -- liftIO $ putStrLn $ "e' = " ++ showPpr dflags e' ++ "\n"
                -- liftIO $ putStrLn $ "e'' = " ++ showPpr dflags e' ++ "\n"
                -- liftIO $ putStrLn $ "simplE' = " ++ showPpr dflags simplE' ++ "\n"
                -- liftIO $ putStrLn $ "fnE     = " ++ showPpr dflags fnE ++ "\n"
                -- liftIO $ putStrLn $ "args    = " ++ showPpr dflags args ++ "\n"
                liftIO $ putStrLn $ "===converting to==> " ++ showPpr dflags newExpr''

                return newExpr''

        go expr@(_ :@ _)
          | Nothing <- getConstructorApp_maybe expr
          , (Var f, args) <- collectArgs expr
          , not (isConstructor f)
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
                markedArgs <- mapM mark args

                let (newF0, newArgs) = betaReduceAll unfoldingF args --markedArgs
                    newF             = caseInlineT dflags $ caseInline dflags (caseInline dflags newF0)

                markedNewF <- mark newF

                -- liftIO $ putStrLn $ "newArgs = " ++ showPpr dflags newArgs

                liftIO $ putStrLn $ "inlining (pre-beta reduce): { " ++ showPpr dflags unfoldingF ++ " }"
                -- liftIO $ putStrLn $ "inlining (pre-case inline): { " ++ showPpr dflags newF0 ++ " }"
                -- liftIO $ putStrLn $ "inlining: { " ++ showPpr dflags newF ++ " }"
                -- liftIO $ putStrLn $ "inlining (new args): " ++ showPpr dflags newArgs
                -- liftIO $ putStrLn $ "inlining: { " ++ showPpr dflags (betaReduceAll (caseInlineT dflags newF) args) ++ " }"

                mkExprApps guts markedNewF newArgs


        go expr = return expr

applyUnrep :: ModGuts -> CoreExpr -> MatchM CoreExpr
applyUnrep guts e = do
  unrepId <- lift $ findIdTH guts 'unrep
  return (Var unrepId :@ Type (exprType e) :@ e)

-- | rep (unrep x)  ==>  x
elimRepUnrep :: ModGuts -> CoreExpr -> MatchM CoreExpr
elimRepUnrep guts (Cast e co) = elimRepUnrep_co guts (Just co) e
elimRepUnrep guts expr = elimRepUnrep_co guts Nothing expr

elimRepUnrep_co :: ModGuts -> Maybe Coercion -> CoreExpr -> MatchM CoreExpr
elimRepUnrep_co guts coA_M expr@(Var r :@ Type{} :@ dict :@ arg) =
  go0 arg
  where
    go0 e =
      case e of
        (Var u :@ Type{} :@ x) -> go u Nothing x
        (Cast (Var u :@ Type{} :@ x) coB) -> go u (Just coB) x
        _ -> return expr

    go u coB_M x = do
      repId <- lift $ findIdTH guts 'rep
      unrepId <- lift $ findIdTH guts 'unrep

      if r == repId && u == unrepId
        then
          case (coA_M, coB_M) of
            (Nothing, Just coB)  -> do
              liftIO $ putStrLn "Casting..."
              return $ Cast x coB
            (Just coA, Nothing)  -> do
              liftIO $ putStrLn "Casting..."
              return $ Cast x coA
            (Nothing, Nothing)   -> do
              return $ x
            (Just coA, Just coB) -> do
              liftIO $ putStrLn "Casting..."
              return $ Cast x (composeCos coA coB)
        else return expr

    composeCos = mkTransCo

elimRepUnrep_co _guts _co expr = return expr
-- elimRepUnrep guts (Cast e _) = elimRepUnrep guts e

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

          body' <- lift $ subst arg uniq body

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

        varName <- findIdTH guts 'Expr.Var
        -- intTy <- findTypeTH guts ''Int#

        varTy' <- unwrapExpType guts (varType name)

        iHash <- findIdTH guts 'GHC.Types.I#

        dflags <- getDynFlags
        let nameInt =  Var iHash :@ Lit (mkLitInt dflags (fromIntegral uniq))

        typeableTyCon <- findTyConTH guts ''Typeable
        typeType <- findTypeTH guts ''Kind.Type
        typeableDict <- buildDictionaryT guts (mkTyConApp typeableTyCon [typeType, varTy'])

        return (Var varName :@ Type varTy' :@ typeableDict :@ nameInt)
    subst0 _ _ expr = return expr



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

  markedE' <- mark0 guts (Data.transform (go varId newTy) e)

  -- unreppedVar <- applyUnrep guts (Var varId :@ Type origTy :@ typeableDict :@ nameVal)
  -- let markedSubstE' = substCoreExpr v' unreppedVar markedE'

  let markedSubstE' = substCoreExpr v' (Var varId :@ Type origTy :@ typeableDict :@ nameVal) markedE'
  -- liftIO $ putStrLn $ "markedSubstE' = " ++ showPpr dflags markedSubstE'

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

  ,('(), 'UnitExp)
  ,('Left, 'LeftExp)
  ,('Right, 'RightExp)
  ,('(,), 'PairExp)
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

