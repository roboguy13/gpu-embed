{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Plugin.MatchPlugin (plugin) where

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

                  from <- lookupId fromName
                  to <- lookupId toName
                  return (from, to))

  constrNames <- mapM (\n -> fmap (,n) (thNameToGhcName_ n)) constrNamesTH

  gpuExprIdMap <- forM constrNames
                       (\(name, nameTH) -> do
                          theId <- lookupId name
                          return (nameTH, theId))

  -- bindsOnlyPass return guts
  bindsOnlyPass (mapM (transformBind guts (mg_inst_env guts) primMap (getGPUExprIdsFrom gpuExprIdMap))) guts

transformBind :: ModGuts -> InstEnv -> [(Id, Id)] -> (TH.Name -> Var) -> CoreBind -> CoreM CoreBind
transformBind guts instEnv primMap lookupVar (NonRec name e) =
  fmap (NonRec name) (transformExpr guts Nothing primMap lookupVar e)
transformBind guts instEnv primMap lookupVar (Rec bnds) = Rec <$> mapM go bnds
  where
    go (name, e) =
      (name,) <$> transformExpr guts (Just name) primMap lookupVar e

-- TODO: Add support for recursive functions

transformExpr :: ModGuts -> Maybe Var -> [(Id, Id)] -> (TH.Name -> Var) -> Expr Var -> CoreM (Expr Var)
transformExpr guts recName primMap lookupVar = Data.transformM go
  where
    go (Var f :@ _ty :@ _dict :@ x)
      | f == lookupVar 'externalize = transformSumMatches guts recName primMap lookupVar x
    go expr = return expr

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
transformProdMatch guts lookupVar ty0 (altCon@(DataAlt dataAlt), vars0, body) = do
  repTyCon <- findTyCon' guts (varName (lookupVar ''GPURep))

  repType <- computeRepType guts (dataConOrigResTy dataAlt)

  prodTypes <- listTypesWith (lookupVar ''(,)) repType

  pairTyCon <- findTyCon' guts (varName (lookupVar ''(,)))

  return $ go pairTyCon repTyCon prodTypes vars0
  where
    go pairTyCon repTyCon (ty1:_) [] = Var (lookupVar 'NullaryMatch) :@ Type ty1 :@ Type ty0 :@ Type (mkTyConApp repTyCon [ty0]) :@ body

    go pairTyCon repTyCon (ty1:_) [x] =
      Var (lookupVar 'OneProdMatch) :@ Type ty1 :@ Type ty0 :@ Type (mkTyConApp repTyCon [ty0]) :@ body

    go pairTyCon repTyCon (ty1:restTys) (x:xs) =
      let restTy = mkTyConApp pairTyCon restTys
      in
      Var (lookupVar 'ProdMatch)
        :@ Type ty1
        :@ Type restTy
        :@ Type ty0
        :@ Type (mkTyConApp repTyCon [ty1])
        :@ Type (mkTyConApp repTyCon [restTy])
        :@ go pairTyCon repTyCon restTys xs

transformSumMatch :: ModGuts -> (TH.Name -> Var) -> Expr a -> a -> Type -> [Alt a] -> CoreM (Expr a)

transformSumMatch guts lookupVar scrutinee wild ty0 alts@(alt1@(DataAlt dataAlt1, _, _):_) = do
  repTyCon <- findTyCon' guts (varName (lookupVar ''GPURep))

  repType <- computeRepType guts (dataConOrigResTy dataAlt1)

  sumTypes <- listTypesWith (lookupVar ''Either) repType

  eitherTyCon <- findTyCon' guts (varName (lookupVar ''Either))

  go eitherTyCon repTyCon sumTypes alts
  where
    go eitherTyCon repTyCon (ty1:_) [] =
      return (Var (lookupVar 'EmptyMatch) :@ Type ty0)

    go eitherTyCon repTyCon (ty1:_) [x] = do
      prod <- transformProdMatch guts lookupVar ty1 x
      co <- repTyCo guts ty1

      return (Var (lookupVar 'OneSumMatch)
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

      return (Var (lookupVar 'SumMatch)
                :@ Type ty1
                :@ Type restTy
                :@ Type ty0
                :@ Coercion co
                :@ prod
                :@ restSum)

transformSumMatches :: ModGuts -> Maybe Var -> [(Id, Id)] -> (TH.Name -> Var) -> Expr Var -> CoreM (Expr Var)
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








--
-- Slightly modified from HERMIT:
--

-- | Build a dictionary for the given
buildDictionary :: ModGuts -> Id -> CoreM (Id, [CoreBind])
buildDictionary guts evar = do
    (i, bs) <- runTcM guts $ do
#if __GLASGOW_HASKELL__ > 710 
        loc <- getCtLocM (GivenOrigin UnkSkol) Nothing
#else
        loc <- getCtLoc $ GivenOrigin UnkSkol
#endif
        let predTy = varType evar
#if __GLASGOW_HASKELL__ > 710 
            nonC = mkNonCanonical $ CtWanted { ctev_pred = predTy, ctev_dest = EvVarDest evar, ctev_loc = loc }
            wCs = mkSimpleWC [cc_ev nonC]
        -- TODO: Make sure solveWanteds is the right function to call.
        (_wCs', bnds) <- second evBindMapBinds <$> runTcS (solveWanteds wCs)
#else
            nonC = mkNonCanonical $ CtWanted { ctev_pred = predTy, ctev_evar = evar, ctev_loc = loc }
            wCs = mkSimpleWC [nonC]
        (_wCs', bnds) <- solveWantedsTcM wCs
#endif
        -- reportAllUnsolved _wCs' -- this is causing a panic with dictionary instantiation
                                  -- revist and fix!
        return (evar, bnds)
    bnds <- runDsM guts $ dsEvBinds bs
    return (i,bnds)

buildDictionaryT :: ModGuts -> Type -> CoreM CoreExpr
buildDictionaryT guts = \ ty -> do
    dflags <- getDynFlags
    binder <- newIdH ("$d" ++ zEncodeString (filter (not . isSpace) (showPpr dflags ty))) ty
    (i,bnds) <- buildDictionary guts binder
    when (notNull bnds) (error "no dictionary bindings generated.")
    -- guardMsg (notNull bnds) "no dictionary bindings generated."
    return $ case bnds of
                [NonRec v e] | i == v -> e -- the common case that we would have gotten a single non-recursive let
                _ -> mkCoreLets bnds (varToCoreExpr i)


runTcM :: ModGuts -> TcM a -> CoreM a
runTcM guts m = do
    env <- getHscEnv
    dflags <- getDynFlags
    -- What is the effect of HsSrcFile (should we be using something else?)
    -- What should the boolean flag be set to?
    (msgs, mr) <- liftIO $ initTcFromModGuts env guts HsSrcFile False m
    let showMsgs (warns, errs) = showSDoc dflags $ vcat
                                                 $    text "Errors:" : pprErrMsgBagWithLoc errs
                                                   ++ text "Warnings:" : pprErrMsgBagWithLoc warns
    maybe (error $ showMsgs msgs) return mr

runDsM :: ModGuts -> DsM a -> CoreM a
runDsM guts = runTcM guts . initDsTc

-- | Make a unique identifier for a specified type, using a provided name.
newIdH :: MonadUnique m => String -> Type -> m Id
newIdH nm ty = mkLocalId <$> newName' nm <*> return ty

-- | Make a 'Name' from a string.
newName' :: MonadUnique m => String -> m Name
newName' nm = mkSystemVarName <$> getUniqueM <*> return (mkFastString nm)

-- | Re-Setup the typechecking environment from a ModGuts
initTcFromModGuts
    :: HscEnv
    -> ModGuts
    -> HscSource
    -> Bool          -- True <=> retain renamed syntax trees
    -> TcM r
    -> IO (Messages, Maybe r) -- Nothing => error thrown by the thing inside
                              -- (error messages should have been printed already)
initTcFromModGuts hsc_env guts hsc_src keep_rn_syntax do_this
 = do { let { type_env = mk_type_env guts } ;
        errs_var     <- newIORef (emptyBag, emptyBag) ;
        tvs_var      <- newIORef emptyVarSet ;
        keep_var     <- newIORef emptyNameSet ;
#if __GLASGOW_HASKELL__ > 710 
        used_gre_var <- newIORef [] ;
#else
        used_rdr_var <- newIORef Set.empty ;
#endif
        th_var       <- newIORef False ;
        th_splice_var<- newIORef False ;
#if __GLASGOW_HASKELL__ > 710 
        infer_var    <- newIORef (True, emptyBag) ;
#else
        infer_var    <- newIORef True ;
#endif
        lie_var      <- newIORef emptyWC ;
        dfun_n_var   <- newIORef (mk_dfun_n guts) ;
        type_env_var <- newIORef type_env ;

        dependent_files_var <- newIORef [] ;
        static_wc_var       <- newIORef emptyWC ;

        th_topdecls_var      <- newIORef [] ;
        th_topnames_var      <- newIORef emptyNameSet ;
        th_modfinalizers_var <- newIORef [] ;
        th_state_var         <- newIORef Map.empty ;
#if __GLASGOW_HASKELL__ > 710 
        th_remote_state_var  <- newIORef Nothing ;
#endif


        th_top_level_locs_var <- newIORef (Set.fromList []) ;
        th_foreign_files_var <- newIORef [] ;
        th_coreplugins_var <- newIORef [] ;

{- TODO: Verify implementations are correct for:
           tcg_semantic_mod,
           tcg_th_top_level_locs, tcg_merged, tcg_th_foreign_files,
           tcg_th_coreplugins, tcg_top_loc, tcg_complete_matches,
           tcg_cc_st
 -}

        costCentreState_var <- newIORef newCostCentreState ;

        let {
             dflags = hsc_dflags hsc_env ;
             mod = mg_module guts ;
             realSrcLoc = realSrcLocSpan $ mkRealSrcLoc (fsLit "Top level") 1 1 ;

             maybe_rn_syntax :: forall a. a -> Maybe a ;
             maybe_rn_syntax empty_val
                | keep_rn_syntax = Just empty_val
                | otherwise      = Nothing ;

             gbl_env = TcGblEnv {
                tcg_semantic_mod = mod, -- TODO: Is this ok?

                tcg_th_top_level_locs = th_top_level_locs_var,
                tcg_merged = [],
                tcg_th_foreign_files = th_foreign_files_var,
                tcg_th_coreplugins = th_coreplugins_var,
                tcg_top_loc = realSrcLoc,
                tcg_complete_matches = [],
                tcg_cc_st = costCentreState_var,

                -- these first four are CPP'd in GHC itself, but we include them here
                tcg_th_topdecls      = th_topdecls_var,
                tcg_th_topnames      = th_topnames_var,
                tcg_th_modfinalizers = th_modfinalizers_var,
                tcg_th_state         = th_state_var,

                -- queried during tcrnif
                tcg_mod            = mod,
                tcg_src            = hsc_src,
                -- tcg_sig_of         = getSigOf dflags (moduleName mod),
                -- tcg_impl_rdr_env   = Nothing,
                tcg_rdr_env        = mg_rdr_env guts,
                tcg_default        = Nothing,
                tcg_fix_env        = mg_fix_env guts,
                tcg_field_env      = mk_field_env guts,
                tcg_type_env       = type_env,
                tcg_type_env_var   = type_env_var,
                tcg_inst_env       = mg_inst_env guts,
                tcg_fam_inst_env   = mg_fam_inst_env guts,
                tcg_ann_env        = emptyAnnEnv,
#if __GLASGOW_HASKELL__ <= 710 
                tcg_visible_orphan_mods = mkModuleSet [mod],
#endif
                tcg_dfun_n         = dfun_n_var,

                -- accumulated, not queried, during tcrnif
                tcg_dependent_files = dependent_files_var,
                tcg_tc_plugins     = [],
                tcg_static_wc      = static_wc_var,
                tcg_exports        = [],
                tcg_warns          = NoWarnings,
                tcg_anns           = [],
                tcg_tcs            = [],
                tcg_insts          = [],
                tcg_fam_insts      = [],
                tcg_rules          = [],
                tcg_th_used        = th_var,
                tcg_imports        = emptyImportAvails,
                tcg_dus            = emptyDUs,
                tcg_ev_binds       = emptyBag,
                tcg_fords          = [],
                -- tcg_vects          = [],
                tcg_patsyns        = [],
                tcg_doc_hdr        = Nothing,
                tcg_hpc            = False,
                tcg_main           = Nothing,
                tcg_safeInfer      = infer_var,
                tcg_binds          = emptyLHsBinds,
                tcg_sigs           = emptyNameSet,
                tcg_imp_specs      = [],
                tcg_rn_decls       = maybe_rn_syntax emptyRnGroup,
#if __GLASGOW_HASKELL__ <= 710 
                tcg_used_rdrnames  = used_rdr_var,
#endif
                tcg_rn_imports     = [],
                tcg_rn_exports     = maybe_rn_syntax [],
                tcg_keep           = keep_var,
#if __GLASGOW_HASKELL__ > 710 
                tcg_self_boot      = NoSelfBoot, -- Assume there are no hsboot files
                tcg_used_gres       = used_gre_var,
                tcg_th_remote_state = th_remote_state_var,
                tcg_tr_module       = Nothing,
#endif
                tcg_th_splice_used = th_splice_var
             } ;
             lcl_env = TcLclEnv {
                tcl_errs       = errs_var,
                tcl_loc        = realSrcLoc,
                tcl_ctxt       = [],
                tcl_rdr        = emptyLocalRdrEnv,
                tcl_th_ctxt    = topStage,
                tcl_th_bndrs   = emptyNameEnv,
                tcl_arrow_ctxt = NoArrowCtxt,
                tcl_env        = emptyNameEnv,
                tcl_bndrs      = [],
                -- tcl_tidy       = emptyTidyEnv,
                tcl_tyvars     = tvs_var,
                tcl_lie        = lie_var,
                tcl_tclvl      = topTcLevel
             } ;
        } ;

        -- OK, here's the business end!
        maybe_res <- initTcRnIf 'a' hsc_env gbl_env lcl_env $
                     do { r <- tryM do_this
                        ; case r of
                          Right res -> return (Just res)
                          Left _    -> return Nothing } ;

        -- Check for unsolved constraints
        lie <- readIORef lie_var ;
        if isEmptyWC lie
           then return ()
           else pprPanic "initTc: unsolved constraints" (ppr lie) ;

        -- Collect any error messages
        msgs <- readIORef errs_var ;

        let { final_res | errorsFound dflags msgs = Nothing
                        | otherwise               = maybe_res } ;

        return (msgs, final_res)
    }

mk_type_env :: ModGuts -> TypeEnv
-- copied from GHC.compileCore
mk_type_env guts = typeEnvFromEntities (bindersOfBinds (mg_binds guts))
                                           (mg_tcs guts)
                                           (mg_fam_insts guts)
mk_field_env :: ModGuts -> RecFieldEnv
-- TODO
#if __GLASGOW_HASKELL__ > 710
mk_field_env _ = emptyNameEnv 
#else
mk_field_env _ = RecFields emptyNameEnv emptyNameSet
#endif

mk_dfun_n :: ModGuts -> OccSet
-- TODO
mk_dfun_n _ = emptyOccSet

findTyCon' :: ModGuts -> Name -> CoreM TyCon
findTyCon' guts nm = findTyCon guts nm emptyVarSet

findTyCon :: ModGuts -> Name -> VarSet -> CoreM TyCon
findTyCon guts nm c =
    findTyConInNameSpaces guts [tcClsName] nm c

--------------------------------------------------------------------------------------------------

findTyConInNameSpaces :: ModGuts -> [NameSpace] -> Name -> VarSet -> CoreM TyCon
findTyConInNameSpaces guts nss nm c = do --setFailMsg "Variable not in scope." -- because catchesM clobbers failure messages.
  rs <- sequence [ findTyConInNameSpace guts ns nm c | ns <- nss ]
  case rs of
    [] -> error "Variable not in scope"
    (r:_) -> return r

findTyConInNameSpace :: ModGuts -> NameSpace -> Name -> VarSet -> CoreM TyCon
findTyConInNameSpace guts ns nm c =
    case nonDetEltsUniqSet $ filterVarSet ((== ns) . occNameSpace . getOccName) $ findBoundVars ((== nm) . varName) c of
        _ : _ : _ -> error "multiple matching variables in scope."
        [v]       -> error "not a TyCon" --return (varToNamed v)
        []        -> findTyConInNSModGuts guts ns nm

-- | List all variables bound in the context that match the given predicate.
findBoundVars :: (Var -> Bool) -> VarSet -> VarSet
findBoundVars p = filterVarSet p

-- | Looks for TyCon in current GlobalRdrEnv. If not present, calls 'findInNSPackageDB'.
findTyConInNSModGuts :: ModGuts -> NameSpace -> Name -> CoreM TyCon
findTyConInNSModGuts guts ns nm = do
    let rdrEnv = mg_rdr_env guts
    case lookupGRE_RdrName (toRdrName ns nm) rdrEnv of
        [gre] -> lookupTyCon $ gre_name gre
        []    -> findTyConInNSPackageDB guts ns nm
        _     -> error "findInNSModGuts: multiple names returned"

-- | Make a RdrName for the given NameSpace and HermitName
toRdrName :: NameSpace -> Name -> RdrName
toRdrName ns nm = maybe (mkRdrUnqual onm) (flip mkRdrQual onm) (Just mnm)
    where onm = nameOccName nm
          mnm = moduleName $ nameModule nm

-- | Looks for Named in package database, or built-in packages.
findTyConInNSPackageDB :: ModGuts -> NameSpace -> Name -> CoreM TyCon
findTyConInNSPackageDB guts ns nm = do
    mnm <- lookupName guts ns nm
    case mnm of
        Nothing -> findTyConBuiltIn ns nm
        Just n  -> lookupTyCon n

-- | Helper to call lookupRdrNameInModule
lookupName :: ModGuts -> NameSpace -> Name -> CoreM (Maybe Name)
lookupName guts ns nm = case isQual_maybe rdrName of
                    Nothing    -> return Nothing -- we can't use lookupName on the current module
                    Just (m,_) -> do
                        hscEnv <- getHscEnv
                        liftIO $ lookupRdrNameInModule hscEnv guts m rdrName
    where rdrName = toRdrName ns nm

-- | Looks for Named amongst GHC's built-in DataCons/TyCons.
findTyConBuiltIn :: Monad m => NameSpace -> Name -> m TyCon
findTyConBuiltIn ns nm
    | isValNameSpace ns = error "not a TyCon"
        -- case [ dc | tc <- wiredInTyCons, dc <- tyConDataCons tc, nm == (getName dc) ] of
        --     [] -> fail "name not in scope."
        --     [dc] -> return $ NamedDataCon dc
        --     dcs -> fail $ "multiple DataCons match: " ++ intercalate ", " (map unqualifiedName dcs)
    | isTcClsNameSpace ns =
        case [ tc | tc <- wiredInTyCons, nm == (getName tc) ] of
            [] -> error "type name not in scope."
            [tc] -> return tc
            tcs -> error $ "multiple TyCons match: " ++ intercalate ", " (map getOccString tcs)
    | otherwise = error "findNameBuiltIn: unusable NameSpace"

-- | Finds the 'Name' corresponding to the given 'RdrName' in the context of the 'ModuleName'. Returns @Nothing@ if no
-- such 'Name' could be found. Any other condition results in an exception:
--
-- * If the module could not be found
-- * If we could not determine the imports of the module
--
-- This is adapted from GHC's function called lookupRdrNameInModuleForPlugins,
-- but using initTcFromModGuts instead of initTcInteractive. Also, we ImportBySystem
-- instead of ImportByPlugin, so the EPS gets populated with RULES and instances from
-- the loaded module.
--
-- TODO: consider importing by plugin first, then only importing by system when a name
-- is successfully found... as written we will load RULES/instances if the module loads
-- successfully, even if the name is not found.
lookupRdrNameInModule :: HscEnv -> ModGuts -> ModuleName -> RdrName -> IO (Maybe Name)
lookupRdrNameInModule hsc_env guts mod_name rdr_name = do
    -- First find the package the module resides in by searching exposed packages and home modules
    found_module <- findImportedModule hsc_env mod_name Nothing
    case found_module of
        Found _ mod -> do
            -- Find the exports of the module
            (_, mb_iface) <- initTcFromModGuts hsc_env guts HsSrcFile False $
                             initIfaceTcRn $
                             loadSysInterface doc mod

            case mb_iface of
                Just iface -> do
                    -- Try and find the required name in the exports
                    let decl_spec = ImpDeclSpec { is_mod = mod_name, is_as = mod_name
                                                , is_qual = False, is_dloc = noSrcSpan }
#if __GLASGOW_HASKELL__ <= 710 
                        provenance = Imported [ImpSpec decl_spec ImpAll]
#else
                        provenance = Just $ ImpSpec decl_spec ImpAll
#endif
                        env = mkGlobalRdrEnv (gresFromAvails provenance (mi_exports iface))
                    case lookupGRE_RdrName rdr_name env of
                        [gre] -> return (Just (gre_name gre))
                        []    -> return Nothing
                        _     -> panic "lookupRdrNameInModule"

                Nothing -> error $ "Could not determine the exports of the module " ++ moduleNameString mod_name --throwCmdLineErrorS dflags $ hsep [ptext (sLit "Could not determine the exports of the module"), ppr mod_name]
        err -> --throwCmdLineErrorS dflags $ cannotFindModule dflags mod_name err
          error $ "Cannot find module: " ++ moduleNameString mod_name -- ++ "\n" ++ show err
  where
    dflags = hsc_dflags hsc_env
    doc = ptext (sLit "contains a name used in an invocation of lookupRdrNameInModule")

