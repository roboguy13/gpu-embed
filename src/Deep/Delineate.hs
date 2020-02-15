module Deep.Delineate
  where

import           Deep.Expr

internalize :: GPURep a => GPUExp a -> a
internalize = gpuAbs
{-# NOINLINE internalize #-}

externalize :: GPURep a => a -> GPUExp a
externalize = Construct
{-# NOINLINE externalize #-}

