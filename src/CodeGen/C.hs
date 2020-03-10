{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}

{-# OPTIONS_GHC -Wall #-}

module CodeGen.C
  where

import           Deep.Expr

import           Data.Typeable

import           Data.Semigroup
import           Control.Monad.Writer
import           Control.Monad.State
import           Data.List

import           Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.Set as Set

import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE

import           Data.Maybe (isNothing)

import           GHC.Stack (HasCallStack)

import           Data.Ord

import           Data.Complex

import Debug.Trace

nub' :: Ord a => [a] -> [a]
nub' = Set.toList . Set.fromList

deleteAll :: Eq a => a -> [a] -> [a]
deleteAll _ [] = []
deleteAll x (y:ys)
  | y == x    =     deleteAll x ys
  | otherwise = y : deleteAll x ys

type CCode = String
type CName = String

data SomeName = forall a. Typeable a => SomeName (Name a)

-- | NOTE: This instance will only take the unique value into account, not
-- the type tag of the 'Name'.
instance Eq SomeName where
  (SomeName (Name a)) == (SomeName (Name b)) = a == b

instance Ord SomeName where
  compare (SomeName (Name a)) (SomeName (Name b)) = compare a b

instance Show SomeName where
  show (SomeName n) = show n

newtype LocalEnv = LocalEnv (Map Int CName) deriving Show

-- Takes a unique from a 'Name a' and gives back the current CName that
-- references it.
le_lookup :: HasCallStack => Int -> LocalEnv -> CName
le_lookup uniq (LocalEnv env) =
  case Map.lookup uniq env of
    Nothing -> error $ "le_lookup: Cannot find " ++ show uniq
    Just x  -> x

le_modifyName :: LocalEnv -> Int -> CName -> LocalEnv
le_modifyName (LocalEnv env) uniq cname = LocalEnv $ Map.insert uniq cname env

le_modifyNames :: LocalEnv -> [(Int, CName)] -> LocalEnv
le_modifyNames le [] = le
le_modifyNames (LocalEnv env) ((uniq, cname):changes) = le_modifyNames (LocalEnv (Map.insert uniq cname env)) changes

le_fromList :: [(Int, CName)] -> LocalEnv
le_fromList = LocalEnv . Map.fromList

le_initial :: Int -> LocalEnv
le_initial varCount = LocalEnv $ Map.fromList $ map (\n -> (n, "vars[" <> show n <> "]")) [0..varCount-1]


data CodeGenState =
  CodeGenState
    { cg_le :: LocalEnv
    , cg_currUniq :: Int
    , cg_lams :: [SomeLambda]
    }

newtype CodeGen a =
  CodeGen (State CodeGenState a)
  deriving (Functor, Applicative, Monad)

deriving instance MonadState CodeGenState CodeGen

cg_modifyName :: Int -> CName -> CodeGen ()
cg_modifyName uniq cname =
  modify (\cg -> cg { cg_le = le_modifyName (cg_le cg) uniq cname })

cg_modifyNames :: [(Int, CName)] -> CodeGen ()
cg_modifyNames changes =
  modify (\cg -> cg { cg_le = le_modifyNames (cg_le cg) changes })

cg_lookup :: HasCallStack => Int -> CodeGen CName
cg_lookup uniq =
  fmap (le_lookup uniq . cg_le) get

withLocalEnv :: LocalEnv -> CodeGen a -> CodeGen a
withLocalEnv newEnv m = do
  oldEnv <- fmap cg_le get
  modify (\cg -> cg { cg_le = newEnv })
  r <- m
  modify (\cg -> cg { cg_le = oldEnv })
  return r

freshCName :: CodeGen CName
freshCName = do
  uniq <- fmap cg_currUniq get

  modify (\cg -> cg { cg_currUniq = uniq+1 })

  return ("x" ++ show uniq)

lookupLambda :: Int -> CodeGen SomeLambda
lookupLambda uniq = do
  lams <- fmap cg_lams get

  case find (\(SomeLambda lam) -> getNameUniq (lambda_name lam) == uniq) lams of
    Nothing -> error "lookupLambda"
    Just x  -> return x

runTopLevelCodeGen :: Int -> [SomeLambda] -> CodeGen a -> a
runTopLevelCodeGen varCount lams (CodeGen m) =
  evalState m (CodeGenState { cg_le = le_initial varCount, cg_currUniq = 0, cg_lams = lams })

data Lambda a b
  = Lambda
    { lambda_fvs :: [SomeName] -- | Free variables. These must remain sorted by unique, in ascending order
    , lambda_name :: Name a -- | Lambdas are named by their argument name
      -- TODO: Should we have a [(SomeName, CName)] (possibly replacing
      -- lambda_fvs?)
    , lambda_body :: GPUExp b
    , lambda_isTailRec :: Bool
    }

data SomeLambda = forall a b. {- Typeable a => -} SomeLambda (Lambda a b)

getFVs :: GPUExp a -> [SomeName]
getFVs = (`execState` []) . go
  where
    go :: forall s. GPUExp s -> State [SomeName] ()
    go (Var n) = modify (SomeName n:)

    go (CaseExp x y) = go x *> go y
    go (ProdMatchExp x) = go x
    go (SumMatchExp x y) = go x *> go y
    go (NullaryMatch x) = go x
    go (OneSumMatch x) = go x
    go (OneProdMatch x) = go x
    go EmptyMatch = pure ()
    go FalseExp = pure ()
    go TrueExp = pure ()
    go (Repped {}) = pure ()
    go (Lam n x) = do
      go x
      modify (deleteAll (SomeName n))
    go (App f x) = go f *> go x
    go (Lit {}) = pure ()
    go (Add x y) = go x *> go y
    go (Sub x y) = go x *> go y
    go (Mul x y) = go x *> go y
    go (FromEnum x) = go x
    go (FromIntegral x) = go x
    go (Sqrt x) = go x
    go (Equal x y) = go x *> go y
    go (Lte x y) = go x *> go y
    go (Gt x y) = go x *> go y
    go (Not x) = go x
    go (LeftExp x) = go x
    go (RightExp x) = go x
    go (PairExp x y) = go x *> go y
    go (FstExp x) = go x
    go (SndExp x) = go x
    go (StepExp x) = go x
    go (DoneExp x) = go x
    go (IfThenElse x y z) = go x *> go y *> go z
    go (TailRec x) = go x
    go (Construct {}) = pure ()
    go (ConstructAp x y) = go x *> go y
    go (Ord x) = go x
    go (CharLit {}) = pure ()
    go UnitExp = pure ()
    go (ConstructRep x) = go x


-- | Precondition: The maximum unique of all the variables must be
-- equal to the number of variables.
--
-- TODO: Eliminate this precondition.
--
getVarCount :: GPUExp a -> Int
getVarCount = getMax . execWriter . go
  where
    -- TODO: Abstract this traversal pattern
    go :: forall s. GPUExp s -> Writer (Max Int) ()
    go (Var (Name n)) = tell (Max n)

    go (CaseExp x y) = go x *> go y
    go (ProdMatchExp x) = go x
    go (SumMatchExp x y) = go x *> go y
    go (NullaryMatch x) = go x
    go (OneSumMatch x) = go x
    go (OneProdMatch x) = go x
    go EmptyMatch = pure ()
    go FalseExp = pure ()
    go TrueExp = pure ()
    go (Repped {}) = pure ()
    go (Lam n x) = go x
    go (App f x) = go f *> go x
    go (Lit {}) = pure ()
    go (Add x y) = go x *> go y
    go (Sub x y) = go x *> go y
    go (Mul x y) = go x *> go y
    go (FromEnum x) = go x
    go (FromIntegral x) = go x
    go (Sqrt x) = go x
    go (Equal x y) = go x *> go y
    go (Lte x y) = go x *> go y
    go (Gt x y) = go x *> go y
    go (Not x) = go x
    go (LeftExp x) = go x
    go (RightExp x) = go x
    go (PairExp x y) = go x *> go y
    go (FstExp x) = go x
    go (SndExp x) = go x
    go (StepExp x) = go x
    go (DoneExp x) = go x
    go (IfThenElse x y z) = go x *> go y *> go z
    go (TailRec x) = go x
    go (Construct {}) = pure ()
    go (ConstructAp x y) = go x *> go y
    go (Ord x) = go x
    go (CharLit {}) = pure ()
    go UnitExp = pure ()
    go (ConstructRep x) = go x

collectLambdas :: GPUExp a -> [SomeLambda]
collectLambdas = execWriter . go
  where
    go :: forall s. GPUExp s -> Writer [SomeLambda] ()
    go (Var {}) = pure ()
    go (CaseExp x y) = go x *> go y
    go (ProdMatchExp x) = go x
    go (SumMatchExp x y) = go x *> go y
    go (NullaryMatch x) = go x
    go (OneSumMatch x) = go x
    go (OneProdMatch x) = go x
    go EmptyMatch = pure ()
    go FalseExp = pure ()
    go TrueExp = pure ()
    go (Repped {}) = pure ()
    go (TailRec lamExp@(Lam n body)) = tell [mkLambda True (SomeName n) body] *> go body
    go (Lam n x) = tell [mkLambda False (SomeName n) x] *> go x
    go (App f x) = go f *> go x
    go (Lit {}) = pure ()
    go (Add x y) = go x *> go y
    go (Sub x y) = go x *> go y
    go (Mul x y) = go x *> go y
    go (FromEnum x) = go x
    go (FromIntegral x) = go x
    go (Sqrt x) = go x
    go (Equal x y) = go x *> go y
    go (Lte x y) = go x *> go y
    go (Gt x y) = go x *> go y
    go (Not x) = go x
    go (LeftExp x) = go x
    go (RightExp x) = go x
    go (PairExp x y) = go x *> go y
    go (FstExp x) = go x
    go (SndExp x) = go x
    go (StepExp x) = go x
    go (DoneExp x) = go x
    go (IfThenElse x y z) = go x *> go y *> go z
    go (TailRec x) = go x
    go (Construct {}) = pure ()
    go (ConstructAp x y) = go x *> go y
    go (Ord x) = go x
    go (CharLit {}) = pure ()
    go UnitExp = pure ()
    go (ConstructRep x) = go x

mkLambda :: Bool -> SomeName -> GPUExp a -> SomeLambda
mkLambda isTailRec (SomeName argName) body =
  SomeLambda $
    Lambda
      { lambda_fvs = trace "lambda_fvs:" $ traceShowId $
          nub' $
          sortBy (comparing (\(SomeName a) -> getNameUniq a)) $
          deleteAll
            (SomeName argName)
            (getFVs body)
      , lambda_name = argName
      , lambda_body = body
      , lambda_isTailRec = isTailRec
      }

genProgram :: HasCallStack => GPUExp a -> CCode
genProgram e =
  let varCount = getVarCount e
      lambdas = collectLambdas e
  in
  runTopLevelCodeGen varCount lambdas $ do

    resultName <- freshCName

    lambdasCode <- genLambdas e
    exprCode <- genExp e resultName
    return $ unlines
      [ prelude varCount
      , unlines
          (map (\(SomeLambda lam) -> "var_t " <> lambdaCName_byInt (getNameUniq (lambda_name lam)) <> "(var_t, struct closure_t*);")
               lambdas)
      , ""
      , lambdasCode
      , "var_t top_level() {"
      , "  var_t " <> resultName <> ";"
      , exprCode
      , "  return " <> resultName <> ";"
      , "}"
      ]


prelude :: Int -> CCode
prelude varCount =
  unlines
    [ "#include <stdio.h>"
    , "#include <stdlib.h>"
    , "#include <stdbool.h>"
    , "#include <string.h>"
    , "#include <assert.h>"
    , "#include <math.h>"
    , ""
    , "typedef enum var_type_tag {"
    , "  EXPR_INT"
    , ", EXPR_FLOAT"
    , ", EXPR_DOUBLE"
    , ", EXPR_CHAR"
    , ", EXPR_BOOL"
    , ", EXPR_CLOSURE"
    , ", EXPR_EITHER_LEFT"
    , ", EXPR_EITHER_RIGHT"
    , ", EXPR_PAIR"
    , ", EXPR_UNIT"
    , ", EXPR_STEP"
    , ", EXPR_DONE"
    , ", EXPR_UNBOXED"
    , ", EXPR_COMPLEX     // Complex numbers"
    , "} var_type_tag;"
    , ""
    , "struct closure_t;"
    , ""
    , "typedef struct var_t {"
    , "  var_type_tag tag;"
    , "  void* value;"
    , "} var_t;"
    , ""
    , "typedef struct closure_t {"
    , "  var_t* fv_env;"
    , "  var_t (*fn)(var_t, struct closure_t*);"
    , "} closure_t;"
    , ""
    , "var_t vars[" <> show varCount <> "];"
    , ""
    , "#define GET_MATH_OP_ADD +"
    , "#define GET_MATH_OP_MUL *"
    , "#define GET_MATH_OP_SUB -"
    , "#define GET_MATH_OP_DIV /"
    , ""
    , "#define GET_COMPARE_OP_LTE <="
    , "#define GET_COMPARE_OP_LT <"
    , "#define GET_COMPARE_OP_GTE >="
    , "#define GET_COMPARE_OP_GT >"
    , "#define GET_COMPARE_OP_EQUAL =="
    , ""
    , "  // Remove any additional wrappers (for instance, a EXPR_COMPLEX wraps a EXPR_PAIR"
    , "#define UNWRAP(result, x)\\"
    , "  do {\\"
    , "    if ((x).tag == EXPR_COMPLEX) {\\"
    , "      result = *((var_t*)((x).value));\\"
    , "    } else {\\"
    , "      result = x;\\"
    , "    }\\"
    , "  } while (0);"
    , ""
    , "#define MATH_OP(op, result, a, b)\\"
    , "  do {\\"
    , "    assert((a).tag == (b).tag);\\"
    , "    (result).tag = (a).tag;\\"
    , "    switch ((a).tag) {\\"
    , "      case EXPR_INT:\\"
    , "        (result).value = malloc(sizeof(int));\\"
    , "        *((int*)(result).value) = *(int*)((a).value) GET_MATH_OP_##op *(int*)((b).value);\\"
    , "        break;\\"
    , "      case EXPR_FLOAT:\\"
    , "        (result).value = malloc(sizeof(float));\\"
    , "        *((float*)(result).value) = *(float*)((a).value) GET_MATH_OP_##op *(float*)((b).value);\\"
    , "        break;\\"
    , "      case EXPR_DOUBLE:\\"
    , "        (result).value = malloc(sizeof(double));\\"
    , "        *((double*)(result).value) = *(double*)((a).value) GET_MATH_OP_##op *(double*)((b).value);\\"
    , "        break;\\"
    , "      default:\\"
    , "        fprintf(stderr, \"%s type tag = %d\\n\", #a, (a).tag);\\"
    , "        assert(0 && \"Attempting to perform arithmetic on non-numeric types\");\\"
    , "    }\\"
    , "  } while (0);"
    , ""
    , "#define COMPARE(op, result, a, b)\\"
    , "  do {\\"
    , "   assert((a).tag == (b).tag);\\"
    , "    switch ((a).tag) {\\"
    , "      case EXPR_INT:\\"
    , "        *((bool*)(result).value) = *(int*)((a).value) GET_COMPARE_OP_##op *(int*)((b).value);\\"
    , "        break;\\"
    , "      case EXPR_FLOAT:\\"
    , "        *((bool*)(result).value) = *(float*)((a).value) GET_COMPARE_OP_##op *(float*)((b).value);\\"
    , "        break;\\"
    , "      case EXPR_DOUBLE:\\"
    , "        *((bool*)(result).value) = *(double*)((a).value) GET_COMPARE_OP_##op *(double*)((b).value);\\"
    , "        break;\\"
    , "      case EXPR_BOOL:\\"
    , "        *((bool*)(result).value) = *(bool*)((a).value) GET_COMPARE_OP_##op *(bool*)((b).value);\\"
    , "        break;\\"
    , "      case EXPR_CHAR:\\"
    , "        *((bool*)(result).value) = *(char*)((a).value) GET_COMPARE_OP_##op *(char*)((b).value);\\"
    , "        break;\\"
    , "      default:\\"
    , "        fprintf(stderr, \"%s type tag = %d\\n\", #a, (a).tag);\\"
    , "        assert(0 && \"Cannot compare given type for equality\");\\"
    , "    }\\"
    , "  } while (0);"
    , ""
    , "#define CAST_TO(result, r_type, a)\\"
    , "  do {\\"
    , "    switch ((a).tag) {\\"
    , "      case EXPR_INT:\\"
    , "        *((r_type*)(result).value) = (r_type) *(int*)((a).value);\\"
    , "        break;\\"
    , "      case EXPR_FLOAT:\\"
    , "        *((r_type*)(result).value) = (r_type) *(float*)((a).value);\\"
    , "        break;\\"
    , "      case EXPR_DOUBLE:\\"
    , "        *((r_type*)(result).value) = (r_type) *(double*)((a).value);\\"
    , "        break;\\"
    , "      default:\\"
    , "        fprintf(stderr, \"%s type tag = %d\\n\", #a, (a).tag);\\"
    , "        assert(0 && \"CAST_FROM: Invalid type tag\");\\"
    , "    }\\"
    , "  } while (0);"
    , ""
    , "#define MATH_SQRT(result, a)\\"
    , "  do {\\"
    , "      case EXPR_FLOAT:\\"
    , "        *((float*)(result).value) = sqrt(*(float*)((a).value));\\"
    , "        break;\\"
    , "      case EXPR_DOUBLE:\\"
    , "        *((double*)(result).value) = sqrt(*(double*)((a).value));\\"
    , "        break;\\"
    , "  } while(0);"
    , ""  -- 
    , "#define INIT_COMPLEX_PAIR(result)\\"
    , "  do {\\"
    , "    (result).tag = EXPR_COMPLEX;\\"
    , "    (result).value = malloc(sizeof(var_t));\\"
    , "    (*((var_t*)(result).value)).tag = EXPR_PAIR;\\"
    , "    (*((var_t*)(result).value)).value = malloc(2*sizeof(var_t));\\"
    , "  } while (0);"
    , ""
    , "#define INIT_COMPLEX(a, type, eTag)\\"
    , "  do {\\"
    , "    (a).tag = EXPR_COMPLEX;\\"
    , "    (a).value = malloc(sizeof(var_t));\\"
    , "    ((var_t*)((a).value))->tag = EXPR_PAIR;\\"
    , "    ((var_t*)((a).value))->value = malloc(2*sizeof(var_t));\\"
    , "    ((var_t*)(((var_t*)((a).value))->value))[0].tag = eTag;\\"
    , "    ((var_t*)(((var_t*)((a).value))->value))[1].tag = eTag;\\"
    , "    ((var_t*)(((var_t*)((a).value))->value))[0].value = malloc(sizeof(type));\\"
    , "    ((var_t*)(((var_t*)((a).value))->value))[1].value = malloc(sizeof(type));\\"
    , "  } while (0);"
    , ""
    , "#define PAIR_FST(result, p)\\"
    , "  do {\\"
    , "    assert((p).tag == EXPR_PAIR);\\"
    , "    (result) = ((var_t*)((p).value))[0];\\"
    , "  } while(0);"
    , ""
    , "#define PAIR_SND(result, p)\\"
    , "  do {\\"
    , "    assert((p).tag == EXPR_PAIR);\\"
    , "    (result) = ((var_t*)((p).value))[1];\\"
    , "  } while(0);"
    , ""
    , "#define PAIR_ASSIGN_FST(result, x)\\"
    , "  do {\\"
    , "    ((var_t*)((result).value))[0] = (x);\\"
    , "  } while(0);"
    , ""
    , "#define PAIR_ASSIGN_SND(result, x)\\"
    , "  do {\\"
    , "    ((var_t*)((result).value))[1] = (x);\\"
    , "  } while(0);"
    , ""
    , "#define COMPLEX_REAL(result, c)\\"
    , "  do {\\"
    , "    assert((p).tag == EXPR_COMPLEX);\\"
    , "    PAIR_FST(result, *((var_t*)((c).value)));\\"
    , "  } while (0);"
    , ""
    , "#define COMPLEX_IMAG(result, c)\\"
    , "  do {\\"
    , "    assert((c).tag == EXPR_COMPLEX);\\"
    , "    PAIR_SND(result, *((var_t*)((c).value)));\\"
    , "  } while (0);"
    , ""
    , "#define COMPLEX_ASSIGN_REAL(result, x)\\"
    , "  do {\\"
    , "    PAIR_ASSIGN_FST(*((var_t*)((result).value)), x);\\"
    , "  } while(0);"
    , ""
    , "#define COMPLEX_ASSIGN_IMAG(result, x)\\"
    , "  do {\\"
    , "    PAIR_ASSIGN_SND(*((var_t*)((result).value)), x);\\"
    , "  } while(0);"
    , ""
    , "bool isIterTag(var_type_tag tag) {"
    , "  return tag == EXPR_STEP || tag == EXPR_DONE;"
    , "}"
    ]

data ShowablePair = forall a. (Typeable a, Show a) => ShowablePair a a

mainCode :: [CCode] -> CCode
mainCode body =
  unlines
    [ "int main(int argc, char* argv[]) {"
    , unlines (map (++"  ") body)
    , "}"
    ]

genExp :: HasCallStack => GPUExp a -> CName -> CodeGen CCode

genExp (ConstructRep x :: GPUExp t) resultName =
  case getComplexType_maybe (Proxy :: Proxy t) of
    Nothing -> do
      r <- genExp x resultName
      return $ unlines
        [ "// ConstructRep (Non-Complex)"
        , r
        ]

    Just _ -> do
      pairName <- freshCName
      pairCode <- genExp x pairName

      return $ unlines
        [ "// Complex ConstructRep"
        , "var_t " <> pairName <> ";"
        , pairCode
        , resultName <> ".tag = EXPR_COMPLEX;"
        , resultName <> ".value = malloc(sizeof(var_t));"
        , "*((var_t*)(" <> resultName <> ".value)) = " <> pairName <> ";"
        ]

genExp (Var (Name n)) resultName = do
  nCName <- cg_lookup n

  return $ unlines
    [ "if (isIterTag(" <> nCName <> ".tag)) {"
    , resultName <> " = " <> "*(var_t*)(" <> nCName <> ".value);"
    , "} else {"
    , resultName <> " = " <> nCName <> ";"
    , "}"
    ]

genExp (CaseExp s body) resultName = do
  sResultName <- freshCName
  computeS <- genExp s sResultName

  caseCode <- genCaseExp sResultName body resultName

  return $ unlines
    [ "var_t " <> sResultName <> ";"
    , computeS
    , caseCode
    ]

genExp (Lam (Name n) body) resultName = do
  closurePtrName <- freshCName

  sLam@(SomeLambda lam) <- lookupLambda n
  closureCode <- buildClosure sLam ("(*" <> closurePtrName <> ")")

  -- let fvs = lambda_fvs lam

  return $ unlines
    [ "closure_t* " <> closurePtrName <> " = malloc(sizeof(closure_t));"
    , closureCode
    , ""
    , resultName <> ".tag = EXPR_CLOSURE;"
    , resultName <> ".value = (void*)" <> closurePtrName <> ";"
    ]

genExp (ProdMatchExp f) resultName = genExp f resultName

genExp (OneProdMatch f) resultName = genExp f resultName

-- TODO: Generalize
genExp (App lamExp@(Lam (Name n) _) x) resultName = do
  xName <- freshCName
  xCode <- genExp x xName

  le <- fmap cg_le get

  traceM $ "/////////// le = " ++ show le
  traceM $ "/////////// le' = " ++ show (le_modifyName le n xName)

  closureName <- freshCName
  closureVarName <- freshCName
  closureCode <- withLocalEnv (le_modifyName le n xName) $ genExp lamExp closureVarName

  lam <- lookupLambda n

  callCode <- callClosure lam closureName xName resultName

  return $ unlines
    [ "var_t " <> xName <> ";"
    , "closure_t " <> closureName <> ";"
    , "var_t " <> closureVarName <> ";"
    , ""
    , xCode
    , closureCode
    , "memcpy(&" <> closureName <> ", (closure_t*)(" <> closureVarName <> ".value), sizeof(closure_t));"
    , callCode
    ]

genExp (App (TailRec lam) x) resultName = genExp (App lam x) resultName

genExp (App _ _) _ = error "genExp: App"

-- genExp (App f x) resultName = do
--   rName <- freshCName
--   xName <- freshCName

--   rCode <- genExp f fName
--   xCode <- genExp x xName

--   callCode <- callClosure 

--   return $ unlines
--     [ "var_t " <> fName <> ";"
--     , "var_t " <> xName <> ";"
--     , 

genExp (Lit x :: GPUExp t) resultName =
    case getComplex_maybe x of
      Just (ShowablePair a b, (ty, tag)) -> do
        aName <- freshCName
        bName <- freshCName

        aCode <- oneDimNumCode a aName ty tag
        bCode <- oneDimNumCode b bName ty tag

        return $ unlines
          [ "var_t " <> aName <> ";"
          , "var_t " <> bName <> ";"
          , aCode
          , bCode
          , "// Complex Lit"
          , "INIT_COMPLEX(" <> resultName <> ", " <> ty <> ", " <> tag <> ");"
          , "COMPLEX_ASSIGN_REAL(" <> resultName <> ", " <> aName <> ");"
          , "COMPLEX_ASSIGN_IMAG(" <> resultName <> ", " <> bName <> ");"
          -- , resultName <> ".value = malloc(sizeof(2*sizeof(var_t)));"
          -- , resultName <> ".tag = " <> tag <> ";"
          -- , resultName <> ".value[0] = " <> "*(" <> ty <> ")(" <> aName <> ".value);"
          -- , resultName <> ".value[1] = " <> "*(" <> ty <> ")(" <> bName <> ".value);"
          ]
      Nothing ->
        uncurry (oneDimNumCode x resultName) (numTypeInfo x)
  where

    oneDimNumCode x' resultName' ty tag =
      return $ unlines
        [ "// oneDimNumCode"
        , resultName' <> ".value = malloc(sizeof(" <> ty <> "));"
        , resultName' <> ".tag = " <> tag <> ";"
        , "*(" <> ty <>"*)(" <> resultName' <> ".value) = " <> show x' <> ";"
        ]

genExp TrueExp resultName =
  return $ unlines
    [ resultName <> ".tag = EXPR_BOOL;"
    , resultName <> ".value = malloc(sizeof(bool));"
    , "*(bool*)(" <> resultName <> ".value) = true;"
    ]

genExp FalseExp resultName =
  return $ unlines
    [ resultName <> ".tag = EXPR_BOOL;"
    , resultName <> ".value = malloc(sizeof(bool));"
    , "*(bool*)(" <> resultName <> ".value) = false;"
    ]

genExp (DoneExp x) resultName = do
  xName <- freshCName

  xCode <- genExp x xName

  return $ unlines
    [ "var_t " <> xName <> ";"
    , xCode
    , resultName <> ".tag = EXPR_DONE;"
    , resultName <> ".value = malloc(sizeof(var_t));"
    , "*(var_t*)(" <> resultName <> ".value) = " <> xName <> ";"
    ]

genExp (StepExp x) resultName = do
  xName <- freshCName

  xCode <- genExp x xName

  return $ unlines
    [ "var_t " <> xName <> ";"
    , xCode
    , resultName <> ".tag = EXPR_STEP;"
    , resultName <> ".value = malloc(sizeof(var_t));"
    , "*(var_t*)(" <> resultName <> ".value) = " <> xName <> ";"
    ]

genExp (Sub x y) resultName = do
  xName <- freshCName
  yName <- freshCName

  xCode <- genExp x xName
  yCode <- genExp y yName

  return $ unlines
    [ "// Sub"
    , "var_t " <> xName <> ";"
    , "var_t " <> yName <> ";"
    , xCode
    , yCode
    , "assert(" <> xName <> ".tag == " <> yName <> ".tag);"
    , ""
    , "if (" <> xName <> ".tag == EXPR_COMPLEX) {"
    , "  INIT_COMPLEX_PAIR(" <> resultName <> ");"
    , "  MATH_OP(SUB, ((var_t*)(" <> resultName <> ".value))[0], ((var_t*)(" <> xName <> ".value))[0], ((var_t*)(" <> yName <> ".value)[0]); "
    , "  MATH_OP(SUB, ((var_t*)(" <> resultName <> ".value))[1], ((var_t*)(" <> xName <> ".value))[1], ((var_t*)(" <> yName <> ".value)[1]); "
    , "} else {"
    , "  MATH_OP(SUB, " <> resultName <> ", " <> xName <> ", " <> yName <> ");"
    , "}"
    ]

genExp (Mul x y) resultName = do
  xName <- freshCName
  yName <- freshCName

  x0y0Name <- freshCName
  x0y1Name <- freshCName
  x1y0Name <- freshCName
  x1y1Name <- freshCName

  realName <- freshCName
  imagName <- freshCName

  xCode <- genExp x xName
  yCode <- genExp y yName

  return $ unlines
    [ "// Mul"
    , "var_t " <> xName <> ";"
    , "var_t " <> yName <> ";"
    , xCode
    , yCode
    -- , "assert(" <> xName <> ".tag == " <> yName <> ".tag);"
    , ""
    , "if (" <> xName <> ".tag == EXPR_COMPLEX) {"
    , "  var_t " <> x0y0Name <> ";"
    , "  var_t " <> x0y1Name <> ";"
    , "  var_t " <> x1y0Name <> ";"
    , "  var_t " <> x1y1Name <> ";"
    , "  var_t " <> realName <> ";"
    , "  var_t " <> imagName <> ";"
    , ""
    , ""
    , "  MATH_OP(MUL, " <> x0y0Name <> ", ((var_t*)(" <> xName <> ".value))[0], ((var_t*)(" <> yName <> ".value))[0]);"
    , "  MATH_OP(MUL, " <> x0y1Name <> ", ((var_t*)(" <> xName <> ".value))[0], ((var_t*)(" <> yName <> ".value))[1]);"
    , "  MATH_OP(MUL, " <> x1y0Name <> ", ((var_t*)(" <> xName <> ".value))[1], ((var_t*)(" <> yName <> ".value))[0]);"
    , "  MATH_OP(MUL, " <> x1y1Name <> ", ((var_t*)(" <> xName <> ".value))[1], ((var_t*)(" <> yName <> ".value))[1]);"
    , ""
    , "  MATH_OP(SUB, " <> realName <> ", " <> x0y0Name <> ", " <> x1y1Name <> ");"
    , "  MATH_OP(ADD, " <> imagName <> ", " <> x0y1Name <> ", " <> x1y0Name <> ");"
    -- , "  assert(*(var_t*)(" <> realName <> ".value).tag == *(var_t*)(" <> imagName <> ".value).tag);"
    , "  INIT_COMPLEX_PAIR(" <> resultName <> ");"
    , "  COMPLEX_ASSIGN_REAL(" <> resultName <> ", " <> realName <> ");"
    , "  COMPLEX_ASSIGN_IMAG(" <> resultName <> ", " <> imagName <> ");"
    -- , "  ((var_t*)(" <> resultName <> ".value))[0] = *((var_t*)(" <> realName <> ".value));"
    -- , "  ((var_t*)(" <> resultName <> ".value))[1] = *((var_t*)(" <> imagName <> ".value));"
    , "} else {"
    , "  MATH_OP(MUL, " <> resultName <> ", " <> xName <> ", " <> yName <> ");"
    , "}"
    ]

genExp (Add x y) resultName = do
  xName <- freshCName
  yName <- freshCName

  xCode <- genExp x xName
  yCode <- genExp y yName

  return $ unlines
    [ "// Add"
    , "var_t " <> xName <> ";"
    , "var_t " <> yName <> ";"
    , xCode
    , yCode
    , "assert(" <> xName <> ".tag == " <> yName <> ".tag);"
    , ""
    , "if (" <> xName <> ".tag == EXPR_COMPLEX) {"
    , "  INIT_COMPLEX_PAIR(" <> resultName <> ");"
    , "  MATH_OP(ADD, ((var_t*)(" <> resultName <> ".value))[0], ((var_t*)(" <> xName <> ".value))[0], ((var_t*)(" <> yName <> ".value))[0]); "
    , "  MATH_OP(ADD, ((var_t*)(" <> resultName <> ".value))[1], ((var_t*)(" <> xName <> ".value))[1], ((var_t*)(" <> yName <> ".value))[1]); "
    , "} else {"
    , "  MATH_OP(ADD, " <> resultName <> ", " <> xName <> ", " <> yName <> ");"
    , "}"
    ]

genExp (FromIntegral (x :: GPUExp a) :: GPUExp b) resultName = do
  xName <- freshCName

  xCode <- genExp x xName

  case getComplexType_maybe (Proxy :: Proxy b) of
    Just (ty, tag) -> do

      let (tyX, tagX) = numTypeInfo (undefined :: a)

      zeroName <- freshCName

      return $ unlines
        [ "// Complex FromIntegral"
        , "var_t " <> xName <> ";"
        , "var_t " <> zeroName <> ";"
        , zeroName <> ".tag = " <> tag <> ";"
        , zeroName <> ".value = malloc(sizeof(" <> ty <> "));"
        , "*((" <> ty <> "*)(" <> zeroName <> ".value)) = 0;"
        , xCode
        , "INIT_COMPLEX(" <> resultName <> ", " <> ty <> ", " <> tag <> ");"
        , "COMPLEX_ASSIGN_REAL(" <> resultName <> ", " <> xName <> ");"
        , "COMPLEX_ASSIGN_IMAG(" <> resultName <> ", " <> zeroName <> ");"
        -- , resultName <> ".value = malloc(2*sizeof(var_t));"
        -- , "((var_t*)(" <> resultName <> ".value))[0] = " <> xName <> ";"
        -- , "*(" <> ty <> "*)(((var_t*)(" <> resultName <> ".value))[1].value) = 0;"
        ]
    Nothing -> do
      let (ty, tag) = numTypeInfo (undefined :: b)

      return $ unlines
        [ "var_t " <> xName <> ";"
        , xCode
        , ""
        , "CAST_TO(" <> resultName <> ", " <> ty <> ", " <> xName <> ");"
        ]

genExp (Sqrt x) resultName = do
  xName <- freshCName

  xCode <- genExp x xName

  return $ unlines
    [ "var_t " <> xName <> ";"
    , xCode
    , ""
    , "MATH_SQRT(" <> resultName <> ", " <> xName <>");"
    ]

genExp (Lte x y) resultName = do
  xName <- freshCName
  yName <- freshCName

  xCode <- genExp x xName
  yCode <- genExp y yName

  return $ unlines
    [ "var_t " <> xName <> ";"
    , "var_t " <> yName <> ";"
    , xCode
    , yCode
    , "assert(" <> xName <> ".tag == " <> yName <> ".tag);"
    , resultName <> ".tag = EXPR_BOOL;"
    , resultName <> ".value = malloc(sizeof(bool));"
    , "COMPARE(LTE, " <> resultName <> ", " <> xName <> ", " <> yName <> ");"
    ]

genExp (Gt x y) resultName = do
  xName <- freshCName
  yName <- freshCName

  xCode <- genExp x xName
  yCode <- genExp y yName
  
  return $ unlines
    [ "var_t " <> xName <> ";"
    , "var_t " <> yName <> ";"
    , xCode
    , yCode
    , "assert(" <> xName <> ".tag == " <> yName <> ".tag);"
    , resultName <> ".tag = EXPR_BOOL;"
    , resultName <> ".value = malloc(sizeof(bool));"
    , "COMPARE(GT, " <> resultName <> ", " <> xName <> ", " <> yName <> ");"
    ]

genExp (Equal x y) resultName = do
  xName <- freshCName
  yName <- freshCName

  xCode <- genExp x xName
  yCode <- genExp y yName

  return $ unlines
    [ "var_t " <> xName <> ";"
    , "var_t " <> yName <> ";"
    , xCode
    , yCode
    , "assert(" <> xName <> ".tag == " <> yName <> ".tag);"
    , ""
    , resultName <> ".tag = EXPR_BOOL;"
    , resultName <> ".value = malloc(sizeof(bool));"
    , "if (" <> resultName <> ".tag == EXPR_COMPLEX) {"
    , "  COMPARE(EQUAL, " <> resultName <> ", ((var_t*)(" <> xName <> ".value))[0], ((var_t*)(" <> yName <> ".value))[0]);"
    , "  COMPARE(EQUAL, " <> resultName <> ", ((var_t*)(" <> xName <> ".value))[1], ((var_t*)(" <> yName <> ".value))[1]);"
    , "} else {"
    , "  COMPARE(EQUAL, " <> resultName <> ", " <> xName <> ", " <> yName <> ");"
    , "}"
    ]

genExp (IfThenElse b t f) resultName = do
  bName <- freshCName
  tName <- freshCName
  fName <- freshCName

  bCode <- genExp b bName
  tCode <- genExp t resultName
  fCode <- genExp f resultName

  return $ unlines
    [ "var_t " <> bName <> ";"
    , "var_t " <> tName <> ";"
    , "var_t " <> fName <> ";"
    , ""
    , bCode
    , ""
    , "if (*(bool*)(" <> bName <> ".value)) {"
    , tCode
    , "} else {"
    , fCode
    , "}"
    ]

genExp (TailRec lamExp@(Lam (Name n) body)) resultName = do
  genExp lamExp resultName

genExp (PairExp x y) resultName = do
  xName <- freshCName
  yName <- freshCName

  xCode <- genExp x xName
  yCode <- genExp y yName

  return $ unlines
    [ "var_t " <> xName <> ";"
    , "var_t " <> yName <> ";"
    , xCode
    , yCode
    , resultName <> ".tag = EXPR_PAIR;"
    , resultName <> ".value = malloc(sizeof(var_t)*2);"
    , "((var_t*)(" <> resultName <> ".value))[0] = " <> xName <> ";"
    , "((var_t*)(" <> resultName <> ".value))[1] = " <> yName <> ";"
    ]

genExp (Repped x) resultName = error "genExp: Repped" --genExp (rep x) resultName

genExp (LeftExp x) resultName = do
  xName <- freshCName

  xCode <- genExp x xName

  return $ unlines
    [ "var_t " <> xName <> ";"
    , xCode
    , resultName <> ".tag = EXPR_EITHER_LEFT;"
    , resultName <> ".value = malloc(sizeof(var_t));"
    , "*(var_t*)(" <> resultName <> ".value) = " <> xName <> ";"
    ]

genExp (RightExp x) resultName = do
  xName <- freshCName

  xCode <- genExp x xName

  return $ unlines
    [ "var_t " <> xName <> ";"
    , xCode
    , resultName <> ".tag = EXPR_EITHER_RIGHT;"
    , resultName <> ".value = malloc(sizeof(var_t));"
    , "*(var_t*)(" <> resultName <> ".value) = " <> xName <> ";"
    ]

genExp UnitExp resultName =
  return $ unlines
    [ resultName <> ".tag = EXPR_UNIT;"
    , resultName <> ".value = 0;"
    ]

genExp (CharLit c) resultName =
  return $ unlines
    [ resultName <> ".tag = EXPR_CHAR;"
    , "*(char*)(" <> resultName <> ".value) = " <> show c <> ";"
    ]

genExp (Ord x) resultName = do
  xName <- freshCName

  xCode <- genExp x xName

  return $ unlines
    [ "var_t " <> xName <> ";"
    , xCode
    , ""
    , resultName <> ".tag = EXPR_INT;"
    , "*(int*)(" <> resultName <> ".value) = *(int*)(" <> xName <> ".value);"
    ]

genExp (FromEnum x) resultName = error "genExp: TODO: implement FromEnum"

genExp (SumMatchExp _ _) _ = error "genExp: SumMatchExp"
genExp (NullaryMatch _) _ = error "genExp: NullaryMatch"
genExp (OneSumMatch _) _ = error "genExp: OneSumMatch"
genExp EmptyMatch _ = error "genExp: EmptyMatch"


genCaseExp :: CName -> GPUExp (SumMatch a r) -> CName -> CodeGen CCode
genCaseExp s (OneSumMatch p) resultName = genProdMatch s p resultName
genCaseExp s (SumMatchExp x y) resultName = do
  s' <- freshCName

  thenPart <- genProdMatch s' x resultName
  elsePart <- genCaseExp s' y resultName

  return $ unlines
    [ "assert(" <> s <> ".tag == EXPR_EITHER_LEFT || " <> s <> ".tag == EXPR_EITHER_RIGHT);"
    , "var_t " <> s' <> " = *(var_t*)(" <> s <> ".value);"

    , "if (" <> s <> ".tag == EXPR_EITHER_LEFT) {"
    , thenPart
    , "} else if (" <> s <> ".tag == EXPR_EITHER_RIGHT) {"
    , elsePart
    , "}"
    ]

-- TODO: Implement with multiple actual function calls?
genProdMatch :: CName -> GPUExp (ProdMatch a r) -> CName -> CodeGen CCode
genProdMatch s p resultName = do
  r <- getProdMatchLams p
  case r of
    Right x ->
      -- Nullary
      genExp x resultName

    Left (argUniqs0, innerLam) -> do
      -- Not nullary
      let lastArg = last argUniqs0
          argUniqs = init argUniqs0

      unwrappedName <- freshCName

      let itemNames = map (\i -> pairCar i unwrappedName) [0..length argUniqs0-1]

      -- TODO: Should the enivronment be saved and restored?
      cg_modifyNames (zip argUniqs itemNames)

      code <- buildAndCall innerLam (pairCar (length argUniqs0-1) unwrappedName) resultName

      return $ unlines
        [ "var_t " <> unwrappedName <> ";"
        , "UNWRAP(" <> unwrappedName <> ", " <> s <> ");"
        , code
        ]


pairCar :: Int -> CName -> CCode
pairCar 0 p = "((var_t*)" <> p <> ".value)[0]"
pairCar 1 p = "((var_t*)" <> p <> ".value)[1]"
pairCar depth p =
  "((var_t*)(" <> (pairCdr (depth-2) p) <> ").value)[1]"

pairCdr :: Int -> CName -> CCode
pairCdr 0 p = "((var_t*)" <> p <> ".value)[1]"
pairCdr depth p =
  "((var_t*)" <> (pairCdr (depth-1) p) <> ".value)[1]"

-- | Get argument uniques for each lambda and also the innermost lambda
getProdMatchLams :: GPUExp (ProdMatch a r) -> CodeGen (Either ([Int], SomeLambda) (GPUExp r))
getProdMatchLams (OneProdMatch (Lam (Name n) _)) = do
  lam <- lookupLambda n
  return $ Left ([n], lam)

getProdMatchLams (ProdMatchExp (Lam (Name n) x)) = do
  r <- getProdMatchLams x
  case r of
    Left (restNs, lam) -> return $ Left (n:restNs, lam)
    Right _ -> error "getProdMatchLams"

getProdMatchLams (NullaryMatch x) = return $ Right x

lambdaCName_byInt :: Int -> CName
lambdaCName_byInt i = "lam_" <> show i

lambdaCName :: SomeLambda -> CName
lambdaCName (SomeLambda cl) = lambdaCName_byInt (getNameIdent (lambda_name cl))

genLambda :: SomeLambda -> CodeGen CCode
genLambda sc@(SomeLambda c) = do
  rName <- freshCName

  currEnv <- fmap cg_le get

  let modifyFvEnv =
            le_modifyName
                (le_modifyNames
                  currEnv
                  (zipWith
                    (\(SomeName fv) i -> (getNameUniq fv, fvEnvItem i))
                    (lambda_fvs c)
                    [0..]))

                    -- (zip (map (\(SomeName n) -> getNameUniq n) (lambda_fvs c)) -- TODO: Does this put things in the correct order?
                    --    fvIxes))

  let localEnv
        | lambda_isTailRec c =
            modifyFvEnv
                (getNameUniq (lambda_name c))
                rName
        | otherwise =
            modifyFvEnv
                (getNameUniq (lambda_name c))
                "arg"

  body <- withLocalEnv localEnv (genExp (lambda_body c) rName)

  tempName <- freshCName

  let body'
        | lambda_isTailRec c =
            unlines
              [ rName <> ".tag = EXPR_STEP;"
              , rName <> ".value = malloc(sizeof(var_t));"
              , "*(var_t*)(" <> rName <> ".value) = arg;"
              , "while (" <> rName <> ".tag != EXPR_DONE) {"
              , body
              , "}"
              , ""
              , "var_t " <> tempName <> " = *(var_t*)(" <> rName <> ".value);"
              , rName <> ".tag = " <> tempName <> ".tag;"
              , rName <> ".value = " <> tempName <> ".value;"
              ]
        | otherwise = body

  return $
    unlines
      [ "var_t " <> lambdaCName sc <> "(var_t arg, struct closure_t* self) {"
      , "  var_t " <> rName <> ";"
      , body'
      , "  return " <> rName <> ";"
      , "}"
      ]
  where
    fvEnvItem i = "self->fv_env[" <> show i <> "]"

    Name n = lambda_name c

genLambdas :: GPUExp a -> CodeGen CCode
genLambdas e = do
  let lambdas = collectLambdas e

  unlines <$> mapM genLambda lambdas

buildAndCall :: SomeLambda -> CName -> CName -> CodeGen CCode
buildAndCall sLam argName resultName = do
  closureVarName <- freshCName

  closureCode <- buildClosure sLam closureVarName
  callCode <- callClosure sLam closureVarName argName resultName

  return $ unlines
    [ "closure_t " <> closureVarName <> ";"
    , closureCode
    , callCode
    ]

buildClosure :: HasCallStack => SomeLambda -> CName -> CodeGen CCode
buildClosure sc@(SomeLambda c) closureVarName = do
  currEnv <- fmap cg_le get


  let fvs = lambda_fvs c
  traceM $ "////////// fvs = " ++ show fvs
  init_fvEnv <- forM (zip [0..] fvs) (\(i, SomeName fv) -> do
                            fvName <- cg_lookup (getNameUniq fv)
                            return (closureVarName <> ".fv_env[" <> show i <> "] = " <> fvName <> ";"))

  return $
    unlines
      [ closureVarName <> ".fv_env = malloc(sizeof(var_t)*" <> show fvCount <> ");"
      , closureVarName <> ".fn = &" <> lambdaCName sc <> ";"
      , unlines init_fvEnv
      ]
  where
    fvCount = length (lambda_fvs c)

callClosure :: SomeLambda -> CName -> CName -> CName -> CodeGen CCode
callClosure (SomeLambda (Lambda { lambda_name })) closureName argName resultName =
  return $
    resultName <> " = " <> closureName <> ".fn(" <> argName <> ", &" <> closureName <> ");"


-- TODO: Determine if the warning this gives is a sign of a problem (it
-- is likely to be, at least, a minor bug in GHC):
--
-- Update: Despite the warning, it seems ok.
numTypeInfo :: forall n a. (HasCallStack, Typeable n) => n -> (CName, CName)
numTypeInfo arg =
 case eqT :: Maybe (n :~: Int) of
   Just _ -> ("int", "EXPR_INT")
   Nothing ->
     case eqT :: Maybe (n :~: Float) of
       Just _ -> ("float", "EXPR_FLOAT")
       Nothing ->
         case eqT :: Maybe (n :~: Double) of
           Just _ -> ("double", "EXPR_DOUBLE")
           Nothing ->
             case eqT :: Maybe (n :~: Integer) of
               Just _ -> trace "Warning: using int to represent Integer" ("int", "EXPR_INT")
               Nothing -> error $ "numTypeInfo: invalid lit type: " ++ show (typeOf arg)


getComplexType_maybe :: forall a. Typeable a => Proxy a -> Maybe (CName, CName)
getComplexType_maybe Proxy =
  case eqT :: Maybe (a :~: Complex Float) of
    Just Refl -> Just ("float", "EXPR_FLOAT")
    Nothing ->
      case eqT :: Maybe (a :~: Complex Double) of
        Just Refl -> Just ("double", "EXPR_DOUBLE")
        Nothing -> Nothing

getComplex_maybe :: Typeable a => a -> Maybe (ShowablePair, (CName, CName))
getComplex_maybe x =
  case cast x :: Maybe (Complex Float) of
    Just (a :+ b) -> Just (ShowablePair a b, ("float", "EXPR_FLOAT"))
    Nothing ->
      case cast x :: Maybe (Complex Double) of
        Just (a :+ b) -> Just (ShowablePair a b, ("double", "EXPR_DOUBLE"))
        Nothing -> Nothing

-- Tests and examples --
cTest :: GPUExp Int
cTest =
  CaseExp (Var (Name 0) :: GPUExp (Either Int Float))
    (SumMatchExp
      (OneProdMatch (Lam (Name 1) (Var (Name 1))))
      (OneSumMatch (OneProdMatch (Lam (Name 2) (Var (Name 0))))))

cTest2 :: GPUExp Int
cTest2 =
  CaseExp (Var (Name 0) :: GPUExp (Int, Float))
    (OneSumMatch
      (ProdMatchExp
        (Lam (Name 1)
          (OneProdMatch
            (Lam (Name 2)
              (Var (Name 1)))))))

cTest3 :: GPUExp Int
cTest3 =
  CaseExp (Var (Name 0) :: GPUExp (Int, Float))
    (OneSumMatch
      (ProdMatchExp
        (Lam (Name 1)
          (OneProdMatch
            (Lam (Name 2)
              (Mul (Var (Name 1)) (Var (Name 1))))))))

cTest4 :: GPUExp Int
cTest4 =
  CaseExp (Var (Name 0) :: GPUExp (Int, Float))
    (OneSumMatch
      (ProdMatchExp
        (Lam (Name 1)
          (OneProdMatch
            (Lam (Name 2)
              (Mul (Var (Name 1)) (Lit 11)))))))

(&) :: GPURep a => GPUExp a -> GPUExp (a -> b) -> GPUExp b
(&) = flip App

-- | isEven 6
cTest5 :: GPUExp Bool
cTest5 = Lit 6 &
  TailRec (Lam (Name 0 :: Name Int)
    (IfThenElse (Equal (Var (Name 0 :: Name Int)) (Lit 0))
      (DoneExp TrueExp)
      (IfThenElse (Equal (Var (Name 0 :: Name Int)) (Lit 1))
        (DoneExp FalseExp)
        (StepExp (Sub (Var (Name 0 :: Name Int)) (Lit 2))))))

-- | factorial 5
cTest6 :: GPUExp Int
cTest6 = --(PairExp (Lit 5) (Lit 1)) &
  (construct ((5,1) :: (Int, Int))) &
    TailRec (Lam (Name 0 :: Name (Int, Int))
      (CaseExp (Var (Name 0 :: Name (Int, Int)))
        (OneSumMatch
          (ProdMatchExp
            (Lam (Name 1 :: Name Int)
              (OneProdMatch
                (Lam (Name 2 :: Name Int)
                  (IfThenElse (Equal (Var (Name 1)) (Lit 0 :: GPUExp Int))
                    (DoneExp (Var (Name 2)))
                    (StepExp (PairExp (Sub (Var (Name 1)) (Lit 1)) (Mul (Var (Name 1)) (Var (Name 2)))))
                    ))))))))

