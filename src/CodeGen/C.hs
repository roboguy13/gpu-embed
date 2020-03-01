{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}

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

type CCode = String
type CName = String

data SomeName = forall a. Typeable a => SomeName (Name a)

newtype LocalEnv = LocalEnv (Map Int CName)

-- Takes a unique from a 'Name a' and gives back the current CName that
-- references it.
le_lookup :: Int -> LocalEnv -> CName
le_lookup uniq (LocalEnv env) =
  case Map.lookup uniq env of
    Nothing -> error "le_lookup"
    Just x  -> x

le_modifyName :: LocalEnv -> Int -> CName -> LocalEnv
le_modifyName (LocalEnv env) uniq cname = LocalEnv $ Map.insert uniq cname env

le_modifyNames :: LocalEnv -> [(Int, CName)] -> LocalEnv
le_modifyNames le [] = le
le_modifyNames (LocalEnv env) ((uniq, cname):changes) = le_modifyNames (LocalEnv (Map.insert uniq cname env)) changes

le_fromList :: [(Int, CName)] -> LocalEnv
le_fromList = LocalEnv . Map.fromList

le_initial :: Int -> LocalEnv
le_initial varCount = LocalEnv $ Map.fromList $ map (\n -> (n, "var[" <> show n <> "]")) [0..varCount]


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

cg_lookup :: Int -> CodeGen CName
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
    }

data SomeLambda = forall a b. Typeable a => SomeLambda (Lambda a b)

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


prelude :: Int -> CCode
prelude varCount =
  unlines
    [ "#include <stdio.h>"
    , ""
    , "typedef enum var_type_tag {"
    , "  EXPR_INT"
    , ", EXPR_FLOAT"
    , ", EXPR_DOUBLE"
    , ", EXPR_CHAR"
    , ", EXPR_LAMBDA"
    , ", EXPR_EITHER_LEFT"
    , ", EXPR_EITHER_RIGHT"
    , ", EXPR_PAIR"
    , ", EXPR_UNIT"
    , "} var_type_tag;"
    , ""
    , "typedef struct var_t {"
    , "  var_type_tag tag;"
    , "  void* value;"
    , "} var_t;"
    , ""
    , "typedef struct closure_t {"
    , "  var_t* fv_env;"
    , "  var_t (*fn)(struct closure_t*);"
    , "} closure_t;"
    , ""
    , "var_t vars[" <> show varCount <> "];"
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

genExp :: GPUExp a -> CName -> CodeGen CCode
genExp (Var (Name n)) resultName = do
  nCName <- cg_lookup n

  return $
    resultName <> " = " <> nCName

genExp (CaseExp s body) resultName = do
  sResultName <- freshCName

  computeS <- genExp s sResultName

  genCaseExp sResultName body resultName


-- genExp (ProdMatchExp (Lam (Name n) x)) resultName = _

genCaseExp :: CName -> GPUExp (SumMatch a r) -> CName -> CodeGen CCode
genCaseExp s (OneSumMatch p) resultName = genProdMatch s p resultName
genCaseExp s (SumMatchExp x y) resultName = do
  s' <- freshCName

  thenPart <- genProdMatch s' x resultName
  elsePart <- genCaseExp s' y resultName

  return $ unlines
    [ "ASSERT(" <> s <> ".tag == EXPR_EITHER_LEFT || " <> s <> ".tag == EXPR_EITHER_RIGHT);"
    , "var_t " <> s' <> " = *(var_t*)(" <> s <> ".value)"

    , "if (" <> s <> ".tag == EXPR_EITHER_LEFT) {"
    , thenPart
    , "} else if (" <> s <> ".tag == EXPR_EITHER_RIGHT) {"
    , elsePart
    , "}"
    ]

genProdMatch :: CName -> GPUExp (ProdMatch a r) -> CName -> CodeGen CCode
genProdMatch s p resultName = do
  (argUniqs0, innerLam) <- getProdMatchLams p
  let lastArg = last argUniqs0
      argUniqs = init argUniqs0

  let itemNames = map (\i -> pairCar i s) [0..length argUniqs-2]

  -- TODO: Should the enivronment be saved and restored?
  cg_modifyNames (zip argUniqs itemNames)
  buildAndCall innerLam (pairCar (length argUniqs-1) s) resultName

{-
genProdMatch s (OneProdMatch (Lam (Name n) _)) resultName = do
  le <- fmap cg_le get
  lam <- lookupLambda n

  buildAndCall lam s resultName

genProdMatch s (ProdMatchExp (Lam (Name n) restMatch)) resultName = do
  le <- fmap cg_le get
  lam <- lookupLambda n

  let s' = "(var_t*)" <> s <> "[0]"

  buildAndCall lam s' resultName
-}

pairCar :: Int -> CName -> CCode
pairCar 0 p = "((var_t*)" <> p <> "[0])"
pairCar depth p =
  "((var_t*)(" <> (pairCdr (depth-1) p) <> ")[0])"

pairCdr :: Int -> CName -> CCode
pairCdr 0 p = "((var_t*)" <> p <> "[1])"
pairCdr depth p =
  "((var_t*)" <> (pairCdr (depth-1) p) <> "[1])"

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

  let localEnv =
        le_fromList
          ((getNameUniq (lambda_name c), "arg")
            :zip (map (\(SomeName n) -> getNameUniq n) (lambda_fvs c))
               fvIxes)

  body <- withLocalEnv localEnv (genExp (lambda_body c) rName)

  return $
    unlines
      [ "var_t " <> lambdaCName sc <> "(var_t arg, struct closure_t* self) {"
      , "  var_t " <> rName <> ";"
      , body
      , "  return " <> rName <> ";"
      , "}"
      ]
  where
    Name n = lambda_name c

    fvIxes =
      map (\n -> "self->fv_env[" <> show n <> "]") [0..length (lambda_fvs c)-1]

collectLambdas :: GPUExp a -> [SomeLambda]
collectLambdas = undefined

genLambdas :: GPUExp a -> CodeGen ([(Int, SomeLambda)], CCode)
genLambdas e = do
  let lambdas = collectLambdas e

  lambdaCode <- mapM genLambda lambdas

  return
    ( map (\sc@(SomeLambda c) -> (getNameIdent (lambda_name c), sc))
          lambdas
    , unlines lambdaCode
    )
buildAndCall :: SomeLambda -> CName -> CName -> CodeGen CCode
buildAndCall sLam argName resultName = do
  closureVarName <- freshCName

  closureCode <- buildClosure sLam closureVarName
  callCode <- callClosure sLam closureVarName argName resultName

  return $ unlines [ closureCode, callCode ]

buildClosure :: SomeLambda -> CName -> CodeGen CCode
buildClosure sc@(SomeLambda c) closureVarName = do
  currEnv <- fmap cg_le get
  return $
    unlines
      [ lambdaCName sc <> ".fv_env = malloc(sizeof(var_t)*" <> show fvCount <> ";"
      , closureVarName <> ".fn = &" <> lambdaCName sc <> ";"
      , unlines
          (map (\n ->
                  closureVarName <> ".fv_env[" <> show n <> "]"
                      <> " = " <> le_lookup n currEnv <> ";"
               )
            [0..fvCount-1]
          )
      ]
  where
    fvCount = length (lambda_fvs c)

callClosure :: SomeLambda -> CName -> CName -> CName -> CodeGen CCode
callClosure (SomeLambda (Lambda { lambda_name })) closureName argName resultName =

  return $
    resultName <> " = " <> closureName <> ".fn(" <> argName <> ", &" <> closureName <> ");"

