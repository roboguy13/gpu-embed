Current examples (all work with Core plugin transformation before the attempt to add
lambdas). Note that the "underscore functions" (like `example2_`) exist to
prevent GHC from inlining and partially evaluating before the plugin is
executed.

Note that

    internalize :: GPURep a => GPUExp a -> a
    internalize = gpuAbs
    {-# NOINLINE internalize #-}

    externalize :: GPURep a => a -> GPUExp a
    externalize = Construct
    {-# NOINLINE externalize #-}

The examples:

1.

    example1 :: Int
    example1 =
      internalize (externalize
        (case eitherExample 1 of
          Left x -> x * 2
          Right y -> fromEnum y))

2.

    data Example' = N' Int | B' Bool deriving (Show, Generic)
    instance GPURep Example'

    example2_ :: Int -> Example'
    example2_ x = B' False

    example2 :: Example'
    example2 =
      internalize (externalize
        (case example2_ 0 of
          N' n -> N' (n+2)
          B' b -> B' (not b)))

3. 

    example3 :: (Bool, Int) -> Int
    example3 p =
      internalize (externalize
        (case p of
          (x, y) -> fromEnum x + y))

4.

    data Example4 = E1 Int | E2 Float | E3 Bool deriving (Show, Generic)
    instance GPURep Example4

    example4_ :: Int -> Example4
    example4_ x = E2 23.0

    example4 :: Int
    example4 =
      internalize (externalize
        (case example4_ 0 of
          E1 x -> 2
          E2 y -> 4
          E3 z -> 6))

5.


    data Example5 = A1 Float Float | A2 Int deriving (Show, Generic)
    instance GPURep Example5

    example5_ :: Int -> Example5
    example5_ x = A1 2.3 7.5

    example5 :: Float
    example5 =
      internalize (externalize
        (case example5_ 0 of
          A2 x -> fromIntegral x
          A1 x y -> x + y))

6.
isEven:


    example6 :: Int -> Bool
    example6 x =
      (internalize (externalize
        (case x == 0 of
          True -> True
          False ->
            case x == 1 of
              True -> False
              False -> example6 (x - 2))))

7. 

    data IntPair = IntPair Int Int deriving (Show, Generic)
    instance GPURep IntPair

    example7_ :: Int -> IntPair
    example7_ x = IntPair 1 2

    example7 :: Int
    example7 =
      internalize (externalize
        (case example7_ 0 of
          IntPair x y ->
            if x == 0
              then y
              else x))

8.



    example8 :: IntPair -> Int
    example8 p =
      internalize (externalize
        (case p of
          IntPair x y -> y))

9.
factorial:


    example9 :: IntPair -> Int
    example9 p =
      internalize (externalize
        (case p of
          IntPair x y ->
            if x == 0
              then example8 p
              else example9 (IntPair (x-1) (x*y))))

10.
Mandelbrot:


    mandelbrot_nextZ :: (Complex Double, Complex Double) -> Complex Double
    mandelbrot_nextZ t =
      internalize (externalize
        (case t of
          (c, z) -> (z*z) + c))

    mandelbrot_helper :: (Int, Complex Double, Complex Double) -> Maybe Int
    mandelbrot_helper t =
      internalize (externalize
        (case t of
          (iters, c, z) ->
            if iters == 50
              then Nothing
              else
                case z of
                  real :+ imag ->
                    if (real*real) + (imag*imag) > 4
                      then Just iters
                      else mandelbrot_helper (iters+1, c, mandelbrot_nextZ (c, z))))

    mandelbrot_point :: Complex Double -> Maybe Int
    mandelbrot_point c =
      internalize (externalize
        (mandelbrot_helper (0, c, 0)))

