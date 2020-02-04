-- This separation exists due to the GHC stage restriction of TH

{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -ddump-splices #-}

import Example

import Data.Complex
import Control.Monad

main :: IO ()
main = do
  print $(thExample1)
  print ($(thExample2) :: Int)
  print $(thExample3)
  print ($(thExample4) :: Int)
  print $(thExample5)
  print (thExample6 8)
  print (thExample6 7)
  print $(thExample7)
  print (thExample9 (IntPair 4 1))

  putStrLn "mandelbrot:"

  print (mandelbrot_nextZ (1 :+ 1, 0))

  print (mandelbrot_point ((-1) :+ 0))
  print (mandelbrot_point (1 :+ 0))
  print (mandelbrot_point (0 :+ 0))

  putStrLn mandelbrotTestAscii


  -- print thExample6
  -- print ($(thExample6) 3)


mandelbrotTestAscii :: String
mandelbrotTestAscii =
  unlines
    (map go [0..mandelbrot_height-1])
  where
    go y = map (go2 y) [0..mandelbrot_width-1]

    go2 y x =
      case mandelbrot_point (mandelbrot_toCoord x y) of
        Just _ -> ' '
        Nothing -> '*'
    

mandelbrot_toCoord :: Int -> Int -> Complex Double
mandelbrot_toCoord x0 y0 =
    (mandelbrot_xMin + x * mandelbrot_xIncr) :+ (mandelbrot_yMin + y * mandelbrot_yIncr)
  where
    x, y :: Double
    x = fromIntegral x0
    y = fromIntegral y0

mandelbrot_xIncr :: Double
mandelbrot_xIncr = (mandelbrot_xMax - mandelbrot_xMin) / (fromIntegral mandelbrot_width - 1)

mandelbrot_yIncr :: Double
mandelbrot_yIncr = (mandelbrot_yMax - mandelbrot_yMin) / (fromIntegral mandelbrot_height - 1)

mandelbrot_xMin :: Double
mandelbrot_xMin = -2.5

mandelbrot_xMax :: Double
mandelbrot_xMax = 1

mandelbrot_yMin :: Double
mandelbrot_yMin = -1.5

mandelbrot_yMax :: Double
mandelbrot_yMax = 1

mandelbrot_width :: Int
mandelbrot_width = 200

mandelbrot_height :: Int
mandelbrot_height = 40

