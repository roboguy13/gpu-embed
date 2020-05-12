module Deep.Delineate
  where

import           Deep.Expr

internalize :: GPURep a => GPUExp a -> a
internalize = gpuAbs
{-# NOINLINE internalize #-}

externalize :: GPURep a => a -> GPUExp a
externalize = Construct
{-# NOINLINE externalize #-}

unrep :: GPUExp a -> a
unrep = error "unrep called"
{-# NOINLINE unrep #-}

-- Equal :: E a -> E a -> E Bool
--
-- unrep (Equal x y) :: Bool
--
-- rep (unrep (Equal x y)) :: E Bool

-- {-# RULES "rep/unrep" forall x. rep (unrep x) = x #-}

