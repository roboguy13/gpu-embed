{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}

module Run where

import           Control.Monad.Reader
import           Control.Monad.Writer

type Tid = (Int, Int, Int)

runKernel :: KernelM m => (Tid -> m ()) -> m (IO ())
runKernel = undefined

class KernelM (m :: * -> *)

instance KernelM (Reader r)
instance Monoid w => KernelM (Writer w)

pattern Phantom x = x

{-# NOINLINE Phantom #-}

-- test :: Maybe a -> Bool
-- test Nothing = False
-- test (Just _) = True

test' :: Maybe a -> Bool
test' (Phantom Nothing) = False
test' (Phantom (Just _)) = True

{-# RULES "elim-Phantom"
      forall x. Phantom x = x
  #-}

