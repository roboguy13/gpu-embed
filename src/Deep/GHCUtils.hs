--
-- Slightly modified from HERMIT:
--

{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}

module Deep.GHCUtils where

import           GhcPlugins hiding (freeVarsBind)

import           TcRnTypes
import           TcSimplify
import           TcMType
import           TcRnMonad
import           TcSMonad
import           TcEvidence
import           TcType

import           TyCoRep

import           TcErrors

import           InstEnv
import           FamInstEnv

import           Class

import           MkId

import           Packages

import           Coercion

import           Finder
import           LoadIface

import           DsBinds
import           DsMonad

import           HsBinds
import           HsDecls

import qualified OccName

import           CostCentreState

import           Bag
import           VarSet

import           Encoding

import           CoreOpt

import           ErrUtils

import           Data.IORef

import qualified Data.Map as Map
import qualified Data.Set as Set

import           Control.Monad

import           Control.Arrow (first, second)


import           Data.Char
import           Data.List

import           Data.Generics.Uniplate.Operations
import qualified Data.Generics.Uniplate.DataOnly as Data

import Debug.Trace

-- | Build a dictionary for the given
buildDictionary :: HasCallStack => ModGuts -> Id -> CoreM (Id, [CoreBind])
buildDictionary guts evar = do
    dflags <- getDynFlags
    hsc_env <- getHscEnv
    eps <- liftIO $ hscEPS hsc_env

    (i, bs) <- runTcM guts $ do
#if __GLASGOW_HASKELL__ > 710
        loc <- getCtLocM (GivenOrigin UnkSkol) Nothing
#else
        loc <- getCtLoc $ GivenOrigin UnkSkol
#endif
        let predTy = varType evar
#if __GLASGOW_HASKELL__ > 710
            wanted =  CtWanted { ctev_pred = predTy, ctev_dest = EvVarDest evar, ctev_loc = loc, ctev_nosh = WDeriv }
            -- nonC = mkNonCanonical wanted
            -- wCs = mkSimpleWC [cc_ev nonC]
            wCs = mkSimpleWC [wanted]
        -- TODO: Make sure solveWanteds is the right function to call.
        (wCs', bnds) <- second evBindMapBinds <$> runTcS (solveWanteds wCs)
        -- (wCs'', bnds') <- second evBindMapBinds <$> runTcS (solveWanteds wCs')
        -- liftIO $ putStrLn (showPpr dflags bnds)
#else
            nonC = mkNonCanonical $ CtWanted { ctev_pred = predTy, ctev_evar = evar, ctev_loc = loc }
            wCs = mkSimpleWC [nonC]
        (_wCs', bnds) <- solveWantedsTcM wCs
#endif
        reportAllUnsolved wCs' -- this is causing a panic with dictionary instantiation
                                  -- revist and fix!
        return (evar, bnds)
    bnds <- runDsM guts $ dsEvBinds bs
    -- bnds2 <- mapM (tryToFillCoHoles guts) bnds
    return (i,bnds)


buildDictionaryT :: HasCallStack => ModGuts -> Type -> CoreM CoreExpr
buildDictionaryT guts = \ ty0 -> do

    dflags <- getDynFlags

    ty <- case splitTyConApp_maybe ty0 of
            Just (tyCon, tyArgs) -> do
                tyArgs' <- mapM (normaliseType' guts) tyArgs
                let r = mkTyConApp tyCon tyArgs'
                return r
            Nothing -> return ty0

    binder <- newIdH ("$d" ++ zEncodeString (filter (not . isSpace) (showPpr dflags ty))) ty
    (i,bnds) <- buildDictionary guts binder
    when (null bnds) (error ("no dictionary bindings generated for " ++ showPpr dflags ty))
    -- guardMsg (notNull bnds) "no dictionary bindings generated."
    return $ case bnds of
                [NonRec v e] | i == v -> e -- the common case that we would have gotten a single non-recursive let
                _ -> mkCoreLets bnds (varToCoreExpr i)

normaliseType' :: ModGuts -> Type -> CoreM Type
normaliseType' guts = fmap snd . normaliseTypeCo guts

normaliseTypeCo :: ModGuts -> Type -> CoreM (Coercion, Type)
normaliseTypeCo guts ty =
  runTcM guts . fmap fst . runTcS $ do
    famInstEnvs <- getFamInstEnvs
    return (normaliseType famInstEnvs Nominal ty)

-- TODO: This is a stop-gap measure. Try to figure out why some of the
-- coercion holes are not getting filled by the GHC API (particularly for
-- the equality constraint in the incoherent instance of ConstructC).
tryToFillCoHoles :: ModGuts -> CoreBind -> CoreM CoreBind
tryToFillCoHoles guts bind =
    case bind of
      NonRec n e -> NonRec n <$> Data.transformM go e
      Rec recBinds -> Rec <$> mapM (secondM (Data.transformM go)) recBinds

  where
    go :: CoreExpr -> CoreM CoreExpr
    go expr@(Coercion (HoleCo coHole@(CoercionHole {ch_co_var}))) = do
      dflags <- getDynFlags
      -- liftIO $ putStrLn ("got to a co hole named " ++ showPpr dflags ch_co_var)
      -- liftIO $ putStrLn ("    with type " ++ showPpr dflags (varType ch_co_var))
      case varType ch_co_var of
        CoercionTy co -> do
          let mkCo r t = mkReflCo r t
          case co of
            GRefl role ty _ -> do
              let co' = mkCo role (varType ch_co_var)
              -- runTcM guts $ do
              --   fillCoercionHole coHole co'
              return (Coercion co')
            Refl ty -> do
              let co' = mkCo Nominal (varType ch_co_var)
              -- runTcM guts $ do
              --   fillCoercionHole coHole co'
              return (Coercion co')
            _ -> do
              liftIO $ putStrLn "    cannot fill (inner)"
              return expr
        CastTy{} -> do
          liftIO $ putStrLn "    kind coercion"
          return expr
        AppTy{} -> do
          liftIO $ putStrLn "    AppTy"
          return expr
        TyConApp tyCon lst@(_:_:ty:_) -> do
          return (Coercion (mkReflCo Nominal ty))
        _ -> do
          liftIO $ putStrLn "    cannot fill (outer)"
          return expr

      -- return (Coercion (mkNomReflCo (varType ch_co_var)))

      -- runTcM guts $ do
      --   fillCoercionHole coHole (mkNomReflCo (varType ch_co_var))
      --   return expr
    go expr = return expr

runTcM :: HasCallStack => ModGuts -> TcM a -> CoreM a
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

-- initTcFromModGuts
--   :: HscEnv
--   -> ModGuts
--   -> HscSource
--   -> Bool
--   -> TcM r
--   -> IO (Messages, Maybe r)
-- initTcFromModGuts hsc_env guts hsc_src keep_rn_syntax do_this
--   = let realSrcLoc = realSrcLocSpan $ mkRealSrcLoc (fsLit "Top level") 1 1
--     in
--     initTc hsc_env hsc_src keep_rn_syntax (mg_module guts) realSrcLoc do_this

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
        eps <- hscEPS hsc_env ;



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
                -- tcg_inst_env       = extendInstEnvList (mg_inst_env guts)
                --                       (filter (\eps_inst ->
                --                                   not (memberInstEnv (mg_inst_env guts) eps_inst))
                --                         (instEnvElts (eps_inst_env eps))),
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
                tcg_imports        = emptyImportAvails {imp_orphs = dep_orphs (mg_deps guts)},
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

-- | Possible results from name lookup.
-- Invariant: One constructor for each NameSpace.
data Named = NamedId Id
           | NamedDataCon DataCon
           | NamedTyCon TyCon
           | NamedTyVar Var

instance Show Named where
    show (NamedId _) = "NamedId"
    show (NamedDataCon _) = "NamedDataCon"
    show (NamedTyCon _) = "NamedTyCon"
    show (NamedTyVar _) = "NamedTyVar"

instance NamedThing Named where
  getOccName (NamedId x) = getOccName x
  getOccName (NamedDataCon x) = getOccName x
  getOccName (NamedTyCon x) = getOccName x
  getOccName (NamedTyVar x) = getOccName x

  getName (NamedId x) = getName x
  getName (NamedDataCon x) = getName x
  getName (NamedTyCon x) = getName x
  getName (NamedTyVar x) = getName x

tyConClassNS :: NameSpace
tyConClassNS = tcClsName

dataConNS :: NameSpace
dataConNS = dataName

tyVarNS :: NameSpace
tyVarNS = tvName

varNS :: NameSpace
varNS = varNameNS

-- | Rename this namespace, as 'varName' is already a function in Var.
varNameNS :: NameSpace
varNameNS = OccName.varName

allNameSpaces :: [NameSpace]
allNameSpaces = [varNS, dataConNS, tyConClassNS, tyVarNS]

findId :: ModGuts -> Name -> VarSet -> CoreM Id
findId guts nm c = do
    nmd <- findInNameSpaces guts [varNS, dataConNS] nm c
    case nmd of
        NamedId i -> return i
        NamedDataCon dc -> return $ dataConWrapId dc
        other -> error $ "findId: impossible Named returned: " ++ show other

findVar :: ModGuts -> Name -> VarSet -> CoreM Var
findVar guts nm c = do
    nmd <- findInNameSpaces guts [varNS, tyVarNS, dataConNS] nm c
    case nmd of
        NamedId i -> return i
        NamedTyVar v -> return v
        NamedDataCon dc -> return $ dataConWrapId dc
        other -> error $ "findVar: impossible Named returned: " ++ show other

findTyCon' :: ModGuts -> Name -> CoreM TyCon
findTyCon' guts nm = findTyCon guts nm emptyVarSet

findTyCon :: ModGuts -> Name -> VarSet -> CoreM TyCon
findTyCon guts nm c = do
    nmd <- findInNameSpace guts tyConClassNS nm c
    case nmd of
        NamedTyCon tc -> return tc
        other -> error $ "findTyCon: impossible Named returned: " ++ show other

findType :: ModGuts -> Name -> VarSet -> CoreM Type
findType guts nm c = do
    nmd <- findInNameSpaces guts [tyVarNS, tyConClassNS] nm c
    case nmd of
        NamedTyVar v -> return $ mkTyVarTy v
        NamedTyCon tc -> return $ mkTyConTy tc
        other -> error $ "findType: impossible Named returned: " ++ show other

findNamed :: ModGuts -> Name -> VarSet -> CoreM Named
findNamed guts nm c =
    findInNameSpaces guts allNameSpaces nm c

--------------------------------------------------------------------------------------------------

findInNameSpaces :: ModGuts -> [NameSpace] -> Name -> VarSet -> CoreM Named
findInNameSpaces guts nss nm c = do --setFailMsg "Variable not in scope." -- because catchesM clobbers failure messages.
  rs <- sequence [ findInNameSpace guts ns nm c | ns <- nss ]
  case rs of
    [] -> error "Variable not in scope"
    (r:_) -> return r

findInNameSpace :: ModGuts -> NameSpace -> Name -> VarSet -> CoreM Named
findInNameSpace guts ns nm c =
    case nonDetEltsUniqSet $ filterVarSet ((== ns) . occNameSpace . getOccName) $ findBoundVars ((== nm) . varName) c of
        _ : _ : _ -> error "multiple matching variables in scope."
        [v]       -> return (varToNamed v)
        []        -> findInNSModGuts guts ns nm

varToNamed :: Var -> Named
varToNamed v | isVarOcc onm = NamedId v
             | isTvOcc onm  = NamedTyVar v
             | otherwise = error "varToNamed: impossible Var namespace"
    where onm = getOccName v

-- | List all variables bound in the context that match the given predicate.
findBoundVars :: (Var -> Bool) -> VarSet -> VarSet
findBoundVars p = filterVarSet p

-- | Looks for TyCon in current GlobalRdrEnv. If not present, calls 'findInNSPackageDB'.
findInNSModGuts :: ModGuts -> NameSpace -> Name -> CoreM Named
findInNSModGuts guts ns nm = do
    let rdrEnv = mg_rdr_env guts
    case lookupGRE_RdrName (toRdrName ns nm) rdrEnv of
        [gre] -> nameToNamed $ gre_name gre
        []    -> findInNSPackageDB guts ns nm
        _     -> error "findInNSModGuts: multiple names returned"

-- | We have a name, find the corresponding Named.
nameToNamed :: MonadThings m => Name -> m Named
nameToNamed n | isVarName n     = liftM NamedId $ lookupId n
              | isDataConName n = liftM NamedDataCon $ lookupDataCon n
              | isTyConName n   = liftM NamedTyCon $ lookupTyCon n
              | isTyVarName n   = error "nameToNamed: impossible, TyVars are not exported and cannot be looked up."
              | otherwise       = error "nameToNamed: unknown name type"

-- | Make a RdrName for the given NameSpace and HermitName
toRdrName :: NameSpace -> Name -> RdrName
toRdrName ns nm = maybe (mkRdrUnqual onm) (flip mkRdrQual onm) (Just mnm)
    where onm = nameOccName nm
          mnm = moduleName $ nameModule nm

-- | Looks for Named in package database, or built-in packages.
findInNSPackageDB :: ModGuts -> NameSpace -> Name -> CoreM Named
findInNSPackageDB guts ns nm = do
    mnm <- lookupName guts ns nm
    case mnm of
        Nothing -> findNamedBuiltIn ns nm
        Just n  -> nameToNamed n

-- | Helper to call lookupRdrNameInModule
lookupName :: ModGuts -> NameSpace -> Name -> CoreM (Maybe Name)
lookupName guts ns nm = case isQual_maybe rdrName of
                    Nothing    -> return Nothing -- we can't use lookupName on the current module
                    Just (m,_) -> do
                        hscEnv <- getHscEnv
                        liftIO $ lookupRdrNameInModule hscEnv guts m rdrName
    where rdrName = toRdrName ns nm
          --
-- | Looks for Named amongst GHC's built-in DataCons/TyCons.
findNamedBuiltIn :: Monad m => NameSpace -> Name -> m Named
findNamedBuiltIn ns n
    | isValNameSpace ns =
        case [ dc | tc <- wiredInTyCons, dc <- tyConDataCons tc, n == (getName dc) ] of
            [] -> error "name not in scope."
            [dc] -> return $ NamedDataCon dc
            dcs -> error $ "multiple DataCons match: " ++ intercalate ", " (map unqualifiedName dcs)
    | isTcClsNameSpace ns =
        case [ tc | tc <- wiredInTyCons, n == (getName tc) ] of
            [] -> error "type name not in scope."
            [tc] -> return $ NamedTyCon tc
            tcs -> error $ "multiple TyCons match: " ++ intercalate ", " (map unqualifiedName tcs)
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

    let go mod = do
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

    case found_module of
        Found _ mod -> go mod
        NotFound {} ->
          case lookupModuleWithSuggestions dflags mod_name Nothing of
            LookupHidden _ ((mod, _):_) ->  go mod
            _ -> error "Cannot find module"
          -- error $ "Cannot find module: " ++ showPpr dflags fr_mods_hidden ++ "\n===>" ++ showPpr dflags fr_unusables
        err -> --throwCmdLineErrorS dflags $ cannotFindModule dflags mod_name err
          error $ "Cannot find module: " ++ moduleNameString mod_name
                  ++ showSDoc dflags (cannotFindModule dflags mod_name err)
                  -- ++ "\n" ++ show err
  where
    dflags = hsc_dflags hsc_env
    doc = ptext (sLit "contains a name used in an invocation of lookupRdrNameInModule")

-- | Get the unqualified name from a 'NamedThing'.
unqualifiedName :: NamedThing nm => nm -> String
unqualifiedName = getOccString

-- Adapted from getUnfoldingsT in HERMIT:
getUnfolding_either :: ModGuts -> DynFlags -> Id -> Either String CoreExpr
getUnfolding_either guts dflags i =
  case lookup i (flattenBinds (mg_binds guts)) of
    Nothing ->
      case unfoldingInfo (idInfo i) of
        CoreUnfolding { uf_tmpl = uft } -> Right uft
        dunf@(DFunUnfolding {})         -> Right $ dFunExpr dunf
        _ -> case idDetails i of
              ClassOpId cls -> do
                let selectors = zip [ idName s | s <- classAllSelIds cls] [0..]
                    msg = getOccString i ++ " is not a method of " ++ getOccString cls ++ "."
                    idx = maybe (error msg) id $ lookup (idName i) selectors
                    r = mkDictSelRhs cls idx
                -- trace ("mkDictSelRhs = "  ++ showPpr dflags r)
                (Right r)
              idDet           -> Left $ "Cannot find unfolding for " ++ showPpr dflags i
                                        ++ "  (idDetails=" ++ showPpr dflags idDet ++ ")"
    Just e -> Right e
  where
    flattenBinds [] = []
    flattenBinds (NonRec b e:rest) = (b, e) : flattenBinds rest
    flattenBinds (Rec bs:rest) = bs ++ flattenBinds rest

getUnfolding :: ModGuts -> DynFlags -> Id -> CoreExpr
getUnfolding guts dflags i =
  case getUnfolding_either guts dflags i of
    Left e -> error e
    Right x -> x

-- | Transform scrutinee of a case. If not a 'case', leave it alone.
onScrutinee :: (CoreExpr -> CoreExpr) -> CoreExpr -> CoreExpr
onScrutinee f (Case scrutinee wild ty alts) = Case (f scrutinee) wild ty alts
onScrutinee _ e = e

isDictVar :: Var -> Bool
isDictVar v =
  let str = occNameString (occName v)
  in
  length str >= 2 && (take 2 str == "$f" || take 2 str == "$d" || take 2 str == "C:")

isDict :: CoreExpr -> Bool
isDict (Var v) = isDictVar v
isDict e       = tcIsConstraintKind (tcTypeKind (exprType e))

isClassVar :: CoreExpr -> Bool
isClassVar (Var v) =
  let str = occNameString (occName v)
  in
  length str >= 2 && take 2 str == "C:"
isClassVar _ = False

isDictNotClass :: DynFlags -> CoreExpr -> Bool
isDictNotClass dflags e =
  isDict e && not (isClassVar e)

-- | For use with Uniplate. Example:
-- transform (applyWhen predicate fn) expr
applyWhen :: (a -> Bool) -> (a -> a) -> a -> a
applyWhen p f x
  | p x       = f x
  | otherwise = x

-- | $fDict x0 x1 ... xN    ==>   [unfolding of $fDict] x0 x1 ... xN
unfoldAndReduceDict_either :: ModGuts -> DynFlags -> CoreExpr -> Either String CoreExpr
unfoldAndReduceDict_either guts dflags e =
  case collectArgs e of
    (fnE@(Var dictFn), dictArgs) ->
      if isDictNotClass dflags fnE
        then
          case getUnfolding_either guts dflags dictFn of
            Left err -> Left err
            Right dictFnUnfolding ->
              case betaReduceAll dictFnUnfolding dictArgs of
                (fn, args) -> Right $ mkApps fn args
        else
          Left "unfoldAndReduceDict_either: not isDictNotClass"
    _ -> Left $ "unfoldAndReduceDict_either: not of form App (... (App (Var v) x) ...) z. Given: " ++ showPpr dflags e

tryUnfoldAndReduceDict :: ModGuts -> DynFlags -> CoreExpr -> CoreExpr
tryUnfoldAndReduceDict guts dflags e =
  case unfoldAndReduceDict_either guts dflags e of
    Right e' -> e'
    _ -> e

unfoldAndReduceDict :: HasCallStack => ModGuts -> DynFlags -> CoreExpr -> CoreExpr
unfoldAndReduceDict guts dflags e =
  case unfoldAndReduceDict_either guts dflags e of
    Right e' -> e'
    Left err -> error ("unfoldAndReduceDict: " ++ err)

-- | This should, among other things, reduce a case-of-known-constructor
simpleOptExpr' :: CoreExpr -> CoreM CoreExpr
simpleOptExpr' e = do
    dflags <- getDynFlags
    return $ simpleOptExpr dflags e

--
-- From HERMIT: --
--

-- | Build a CoreExpr for a DFunUnfolding
dFunExpr :: Unfolding -> CoreExpr
dFunExpr dunf@(DFunUnfolding {}) = mkCoreLams (df_bndrs dunf) $ mkCoreConApps (df_con dunf) (df_args dunf)
dFunExpr _ = error "dFunExpr: not a DFunUnfolding"

-- | @Let (NonRec v e) body@ ==> @body[e/v]@
letNonRecSubst :: CoreExpr -> CoreExpr
letNonRecSubst (Let (NonRec v rhs) body) =
   substCoreExpr v rhs body
letNonRecSubst expr = expr

 -- | Substitute all occurrences of a variable with an expression, in an expression.
substCoreExpr :: Var -> CoreExpr -> (CoreExpr -> CoreExpr)
substCoreExpr v e expr = substExpr (text "substCoreExpr") (extendSubst emptySub v e) expr
    where emptySub = mkEmptySubst (mkInScopeSet (localFreeVarsExpr (Let (NonRec v e) expr)))

-- | Substitute all occurrences of a variable with an expression, in a case alternative.
substCoreAlt :: Var -> CoreExpr -> CoreAlt -> CoreAlt
substCoreAlt v e alt = let (con, vs, rhs) = alt
                           inS            = (flip delVarSet v . unionVarSet (localFreeVarsExpr e) . localFreeVarsAlt) alt
                           subst          = extendSubst (mkEmptySubst (mkInScopeSet inS)) v e
                           (subst', vs')  = substBndrs subst vs
                        in (con, vs', substExpr (text "alt-rhs") subst' rhs)

-- | Beta-reduce as many lambda-binders as possible.
betaReduceAll :: CoreExpr -> [CoreExpr] -> (CoreExpr, [CoreExpr])
betaReduceAll (Lam v body) (a:as) = betaReduceAll (substCoreExpr v a body) as
betaReduceAll e            as     = (e,as)

-- | Find all locally defined free variables in an expression.
localFreeVarsExpr :: CoreExpr -> VarSet
localFreeVarsExpr = filterVarSet isLocalVar . freeVarsExpr


-- | Find all free variables in an expression.
freeVarsExpr :: CoreExpr -> VarSet
freeVarsExpr (Var v) = extendVarSet (freeVarsVar v) v
freeVarsExpr (Lit {}) = emptyVarSet
freeVarsExpr (App e1 e2) = freeVarsExpr e1 `unionVarSet` freeVarsExpr e2
freeVarsExpr (Lam b e) = delVarSet (freeVarsExpr e) b
freeVarsExpr (Let b e) = freeVarsBind b `unionVarSet` delVarSetList (freeVarsExpr e) (bindersOf b)
freeVarsExpr (Case s b ty alts) = let altFVs = delVarSet (unionVarSets $ map freeVarsAlt alts) b
                                  in unionVarSets [freeVarsExpr s, freeVarsType ty, altFVs]
freeVarsExpr (Cast e co) = freeVarsExpr e `unionVarSet` freeVarsCoercion co
freeVarsExpr (Tick t e) = freeVarsTick t `unionVarSet` freeVarsExpr e
freeVarsExpr (Type ty) = freeVarsType ty
freeVarsExpr (Coercion co) = freeVarsCoercion co

freeVarsTick :: Tickish Id -> VarSet
freeVarsTick (Breakpoint _ ids) = mkVarSet ids
freeVarsTick _ = emptyVarSet

-- | Find all free identifiers in a binding group, which excludes any variables bound in the group.
freeVarsBind :: CoreBind -> VarSet
freeVarsBind (NonRec v e) = freeVarsExpr e `unionVarSet` freeVarsVar v
freeVarsBind (Rec defs)   = let (bs,es) = unzip defs
                             in delVarSetList (unionVarSets (map freeVarsVar bs ++ map freeVarsExpr es)) bs

-- | Find all free variables on a binder. Equivalent to idFreeVars, but safe to call on type bindings.
freeVarsVar :: Var -> VarSet
#if __GLASGOW_HASKELL__ > 710
freeVarsVar v = varTypeTyCoVars v `unionVarSet` bndrRuleAndUnfoldingVars v
#else
freeVarsVar v = varTypeTyVars v `unionVarSet` bndrRuleAndUnfoldingVars v
#endif

-- | Find all free variables in a case alternative, which excludes any variables bound in the alternative.
freeVarsAlt :: CoreAlt -> VarSet
freeVarsAlt (_,bs,e) = delVarSetList (freeVarsExpr e `unionVarSet` unionVarSets (map freeVarsVar bs)) bs

-- | Find all free local variables in a case alternative, which excludes any variables bound in the alternative.
localFreeVarsAlt :: CoreAlt -> VarSet
localFreeVarsAlt (_,bs,e) = delVarSetList (localFreeVarsExpr e `unionVarSet` unionVarSets (map freeVarsVar bs)) bs

-- | Find all free variables in a type.
freeVarsType :: Type -> TyVarSet
#if __GLASGOW_HASKELL__ > 710
freeVarsType = tyCoVarsOfType
#else
freeVarsType = tyVarsOfType
#endif

-- | Find all free variables in a coercion.
freeVarsCoercion :: Coercion -> VarSet
freeVarsCoercion = tyCoVarsOfCo

-- This function is copied from GHC, which defines but doesn't expose it.
-- A 'let' can bind a type variable, and idRuleVars assumes
-- it's seeing an Id. This function tests first.
bndrRuleAndUnfoldingVars :: Var -> VarSet
bndrRuleAndUnfoldingVars v | isTyVar v = emptyVarSet
                           | otherwise = idUnfoldingVars v



-- From GHC.Runtime.Eval:

-- Stricter version of isTyVarClassPred that requires all TyConApps to have at least
-- one argument or for the head to be a TyVar. The reason is that we want to ensure
-- that all residual constraints mention a type-hole somewhere in the constraint,
-- meaning that with the correct choice of a concrete type it could be possible for
-- the constraint to be discharged.
isSatisfiablePred :: PredType -> Bool
isSatisfiablePred ty = case getClassPredTys_maybe ty of
    Just (_, tys@(_:_)) -> all isTyVarTy tys
    _                   -> isTyVarTy ty

