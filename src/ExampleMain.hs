-- This separation exists due to the GHC stage restriction of TH

{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -ddump-splices #-}

import Example

main :: IO ()
main = do
  print $(thExample1)
  print $(thExample2)
  print $(thExample3)
  print $(thExample4)
  print $(thExample5)
  print (thExample6 8)
  -- print thExample6
  -- print ($(thExample6) 3)

