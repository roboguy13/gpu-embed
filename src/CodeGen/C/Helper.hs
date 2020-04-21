module CodeGen.C.Helper
  where

import           CodeGen.C.Types

import           Data.List

stmt :: CCode -> CCode
stmt = (<> ";")

cCall :: CName -> [CCode] -> CCode
cCall fnName args =
  fnName <> "(" <> intercalate ", " args <> ")"

derefPtr :: CCode -> CCode
derefPtr x = "*(" <> x <> ")"

cCast :: CCode -> CCode -> CCode
cCast toType x = "((" <> toType <> ")" <> x <> ")"

cIndex :: CCode -> Int -> CCode
cIndex x i = "(" <> x <> ")[" <> show i <> "]"

(!) :: CCode -> Int -> CCode
(!) = cIndex

(=:) :: CCode -> CCode -> CCode
x =: y = stmt (x <> " = " <> y)

cDecl :: CName -> CName -> CCode
cDecl cType v = stmt (cType <> " " <> v)

(#) :: CCode -> CName -> CCode
x # fieldName = x <> "." <> fieldName

macroDef :: CName -> [CName] -> [CCode] -> CCode
macroDef name args theLines =
  unlines
    [ "#define " <> name <> "(" <> intercalate ", " args <> ")\\"
    , "  do {\\"
    , unlines . map ("    "++) . map (++"\\") $ theLines
    , "  } while (0);"
    ]

