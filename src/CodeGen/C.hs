{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module CodeGen.C
  where

import           Deep.Expr

import           Data.Typeable

import           Data.Semigroup
import           Control.Monad.Writer
import           Data.List

type CCode = String
type CName = String

data SomeName = forall a. Typeable a => SomeName (Name a)

data Closure a b
  = Closure
    { closure_fvs :: [SomeName] -- | Free variables
    , closure_name :: Name a
    , closure_body :: GPUExp b
    }

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
    , "};"
    , ""
    , "typedef struct var_t {"
    , "  var_type_tag tag;"
    , "  void* value;"
    , "};"
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

varNamed :: Name a -> CCode
varNamed (Name n) = "vars[" <> show n <> "]"

genExp :: GPUExp a -> [(SomeName, CName)] -> CName -> CCode
genExp e nameDict resultName = undefined

genLambda :: Closure a b -> (Int, Int, CCode)
genLambda c =
    (n, length (closure_fvs c), body)
  where
    Name n = closure_name c

    argsC =
      intercalate ", " $ map (\x -> "var_t " <> x) args

    args = argsGo 0 (closure_fvs c)

    argsGo i [] = []
    argsGo i (x:xs) = ("fv" ++ show i) : argsGo (i+1) xs

    body =
      unlines
        [ "var_t lam_" <> show n <> "(" <> argsC <> ") {"
        , genExp (closure_body c) (zip (closure_fvs c) args) "r"
        , "return r;"
        , "}"
        ]

