{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

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

import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE

import           Data.Maybe (isNothing)

import           GHC.Stack (HasCallStack)

import           Data.Ord

import Debug.Trace

type CCode = String
type CName = String

data SomeName = forall a. Typeable a => SomeName (Name a)

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
      modify (deleteBy (\(SomeName n') (SomeName n) -> getNameUniq n' == getNameUniq n) (SomeName n))
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

mkLambda :: Bool -> SomeName -> GPUExp a -> SomeLambda
mkLambda isTailRec (SomeName argName) body =
  SomeLambda $
    Lambda
      { lambda_fvs =
          sortBy (comparing (\(SomeName a) -> getNameUniq a)) $
          deleteBy
            (\(SomeName n) (SomeName n') -> getNameUniq n == getNameUniq n')
            (SomeName argName)
            (getFVs body)
      , lambda_name = argName
      , lambda_body = body
      , lambda_isTailRec = isTailRec
      }

genProgram :: GPUExp a -> CCode
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
    , "#define MATH_OP(op, result, a, b)\\"
    , "  do {\\"
    , "    assert((a).tag == (b).tag);\\"
    , "    (result).tag = (a).tag;\\"
    , "    switch ((a).tag) {\\"
    , "      case EXPR_INT:\\"
    , "        (result).value = malloc(sizeof(int));\\"
    , "        *((int*)(result).value) = *(int*)((a).value) op *(int*)((b).value);\\"
    , "        break;\\"
    , "      case EXPR_FLOAT:\\"
    , "        (result).value = malloc(sizeof(float));\\"
    , "        *((float*)(result).value) = *(float*)((a).value) op *(float*)((b).value);\\"
    , "        break;\\"
    , "      case EXPR_DOUBLE:\\"
    , "        (result).value = malloc(sizeof(double));\\"
    , "        *((double*)(result).value) = *(double*)((a).value) op *(double*)((b).value);\\"
    , "        break;\\"
    , "      default:\\"
    , "       fprintf(stderr, \"type tag = %d\\n\", a.tag);\\"
    , "       assert(0 && \"Attempting to perform arithmetic on non-numeric types\");\\"
    , "    }\\"
    , "  } while (0);"
    ]

mainCode :: [CCode] -> CCode
mainCode body =
  unlines
    [ "int main(int argc, char* argv[]) {"
    , unlines (map (++"  ") body)
    , "}"
    ]

-- varNamed :: Name a -> CCode
-- varNamed (Name n) = "vars[" <> show n <> "]"

genExp :: HasCallStack => GPUExp a -> CName -> CodeGen CCode
genExp (Var (Name n)) resultName = do
  nCName <- cg_lookup n

  return $ unlines
    [ "if (" <> nCName <> ".tag == EXPR_STEP || " <> nCName <> ".tag == EXPR_DONE) {"
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
  closureName <- freshCName
  closurePtrName <- freshCName

  sLam@(SomeLambda lam) <- lookupLambda n
  closureCode <- buildClosure sLam closureName

  let fvs = lambda_fvs lam

  -- init_fvEnv <- forM (zip [0..] fvs) (\(i, SomeName fv) -> do
  --                           fvName <- cg_lookup (getNameUniq fv)
  --                           return (closurePtrName <> "->fv_env[" <> show i <> "] = " <> fvName <> ";"))

  return $ unlines
    [ "closure_t " <> closureName <> ";"
    , closureCode
    , "closure_t* " <> closurePtrName <> " = malloc(sizeof(closure_t));"
    , closurePtrName <> "->fn = " <> closureName <> ".fn;"
    -- , unlines init_fvEnv
    -- , closurePtrName <> "->fv_env = " <> closureName <> ".fv_env;"
    , closurePtrName <> "->fv_env = malloc(sizeof(var_t)*" <> show (length fvs) <> ");"
    , "memcpy(" <> closurePtrName <> "->fv_env, " <> closureName <> ".fv_env, sizeof(var_t)*" <> show (length fvs) <> ");"
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

genExp (Lit x :: GPUExp t) resultName =
  return $ unlines
    [ resultName <> ".value = " <> "malloc(sizeof(" <> ty <> "));"
    , resultName <> ".tag = " <> tag <> ";"
    , "*(" <> ty <>"*)(" <> resultName <> ".value) = " <> show x <> ";"
    ]

  where
    (ty, tag) =
      case eqT :: Maybe (t :~: Int) of
        Just _ -> ("int", "EXPR_INT")
        Nothing ->
          case eqT :: Maybe (t :~: Float) of
            Just _ -> ("float", "EXPR_FLOAT")
            Nothing ->
              case eqT :: Maybe (t :~: Double) of
                Just _ -> ("double", "EXPR_DOUBLE")
                Nothing -> error "Lit: invalid lit type"

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
    -- , "memcpy(" <> resultName <> ".value, " <> xName <> ", sizeof(var_t));"
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
    -- , "memcpy(" <> resultName <> ".value, " <> xName <> ", sizeof(var_t));"
    ]
genExp (Sub x y) resultName = do
  xName <- freshCName
  yName <- freshCName

  xCode <- genExp x xName
  yCode <- genExp y yName

  return $ unlines
    [ "var_t " <> xName <> ";"
    , "var_t " <> yName <> ";"
    , xCode
    , yCode
    , "MATH_OP(-, " <> resultName <> ", " <> xName <> ", " <> yName <> ");"
    ]

genExp (Mul x y) resultName = do
  xName <- freshCName
  yName <- freshCName

  xCode <- genExp x xName
  yCode <- genExp y yName

  return $ unlines
    [ "var_t " <> xName <> ";"
    , "var_t " <> yName <> ";"
    , xCode
    , yCode
    , "MATH_OP(*, " <> resultName <> ", " <> xName <> ", " <> yName <> ");"
    ]

genExp (Equal x y) resultName = do
  xName <- freshCName
  yName <- freshCName

  xCode <- genExp x xName
  yCode <- genExp y yName

  return $ unlines
    [ "var_t " <> xName <> ";"
    , "var_t " <> yName <> ";"
    , ""
    , xCode
    , ""
    , yCode
    , ""
    , resultName <> ".tag = EXPR_BOOL;"
    , resultName <> ".value = malloc(sizeof(bool));"
    , "*(bool*)(" <> resultName <> ".value) = *(int*)(" <> xName <> ".value) == *(int*)(" <> yName <> ".value);"
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
  (argUniqs0, innerLam) <- getProdMatchLams p
  let lastArg = last argUniqs0
      argUniqs = init argUniqs0

  let itemNames = map (\i -> pairCar i s) [0..length argUniqs0-1]

  -- TODO: Should the enivronment be saved and restored?
  cg_modifyNames (zip argUniqs itemNames)
  buildAndCall innerLam (pairCar (length argUniqs0-1) s) resultName


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
getProdMatchLams :: GPUExp (ProdMatch a r) -> CodeGen ([Int], SomeLambda)
getProdMatchLams (OneProdMatch (Lam (Name n) _)) = do
  lam <- lookupLambda n
  return ([n], lam)

getProdMatchLams (ProdMatchExp (Lam (Name n) x)) = do
  (restNs, lam) <- getProdMatchLams x
  return (n:restNs, lam)

getProdMatchLams (NullaryMatch _) = error "getProdMatchLams"

lambdaCName_byInt :: Int -> CName
lambdaCName_byInt i = "lam_" <> show i

lambdaCName :: SomeLambda -> CName
lambdaCName (SomeLambda cl) = lambdaCName_byInt (getNameIdent (lambda_name cl))

genLambda :: SomeLambda -> CodeGen CCode
genLambda sc@(SomeLambda c) = do
  rName <- freshCName

  currEnv <- fmap cg_le get

  let localEnv =
        le_modifyName
            (le_modifyNames
              currEnv
                (zip (map (\(SomeName n) -> getNameUniq n) (lambda_fvs c))
                   fvIxes))

            (getNameUniq (lambda_name c))
            rName

  body <- withLocalEnv localEnv (genExp (lambda_body c) rName)

  let body'
        | lambda_isTailRec c =
            unlines
              [ rName <> ".tag = EXPR_STEP;"
              , rName <> ".value = malloc(sizeof(var_t));"
              , "*(var_t*)(" <> rName <> ".value) = arg;"
              , "while (" <> rName <> ".tag != EXPR_DONE) {"
              , body
              , "}"
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
    Name n = lambda_name c

    fvIxes =
      map (\n -> "self->fv_env[" <> show n <> "]") [0..length (lambda_fvs c)-1]

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

cTest5 :: GPUExp Bool
cTest5 = Lit 6 &
  TailRec (Lam (Name 0 :: Name Int)
    (IfThenElse (Equal (Var (Name 0 :: Name Int)) (Lit 0))
      (DoneExp TrueExp)
      (IfThenElse (Equal (Var (Name 0 :: Name Int)) (Lit 1))
        (DoneExp FalseExp)
        (StepExp (Sub (Var (Name 0 :: Name Int)) (Lit 2))))))

