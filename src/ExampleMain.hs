-- This separation exists due to the GHC stage restriction of TH

{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -ddump-splices #-}

import Example
import Case
import qualified Case

main :: IO ()
main = print $(thExample6)

