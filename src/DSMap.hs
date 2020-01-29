{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveGeneric #-}

{-# OPTIONS_GHC -fplugin=Type.Compare.Plugin #-}

module DSMap where

import           Data.Dependent.Map

import           Data.Singletons
import           Data.Singletons.TypeLits

import           Data.Constraint
import           Type.Set

import           Data.Functor.Const

import           Data.Typeable

import           GHC.Generics
import Data.Void

data Test = D | B | C | A deriving (Generic)

-- Constructor names and with their "types"
type family ConstrDict t :: [(Symbol, *)] where
  ConstrDict (M1 C ('MetaCons name y z) r p) = '[ '(name, r p) ]
  ConstrDict (M1 x m r p) = ConstrDict (r p)


  -- ConstrDict ((x :+: y) p) = 


data SetSing f s where
  SetSingInsert :: Typeable x => Sing x -> f x -> SetSing f s -> SetSing f (Insert x s)
  SetSingEmpty :: SetSing f 'Empty

pattern SetSingOne s fx = SetSingInsert s fx SetSingEmpty

setSingLookup :: forall x s f. (Typeable x) => SetSing f s -> Sing x -> Maybe (f x)
setSingLookup SetSingEmpty _ = Nothing
setSingLookup (SetSingInsert (s :: Sing t) fx rest) s' =
  case eqT :: Maybe (x :~: t) of
    Nothing -> setSingLookup rest s'
    Just Refl -> Just fx


type family SetSingMerge a b where
  SetSingMerge (SetSing f a) (SetSing f b) = SetSing f (Merge a b)

type family IsSetSing a :: Constraint where
  IsSetSing (SetSing f a) = ()

-- type family IsSetSingInsert a :: Constraint where
--   IsSetSingInsert (SetSing f (Insert x s)) = ()

-- test :: SetSing (Insert "a" (Insert "b" 'Empty))
-- test = SetSing (sing :: Sing "b")

-- test :: DMap (SetSing (Insert "a" (Insert "b" 'Empty))) (Const Int)
-- test = undefined



-- -- type family Elem x xs :: Constraint where
-- --   Elem x (x:xs) = ()
-- --   Elem y (x:xs) = Elem y xs

-- data Elem x xs where
--   Here :: Elem x (x:xs)
--   There :: Elem x xs -> Elem x (y:xs)

-- -- data Append xs where
-- --   -- AppendNil :: Append '[] ys
-- --   AppendCons :: Proxy (x:xs) -> Proxy ys -> Append xs

-- data NotNull list where
--   NotNull :: NotNull (x:xs)

-- elemNotNull :: Elem x xs -> NotNull xs
-- elemNotNull Here = NotNull
-- elemNotNull (There _) = NotNull

-- -- appendNotNullL :: Proxy ys -> NotNull xs -> NotNull (Append xs ys)
-- -- appendNotNullL Proxy NotNull = NotNull

-- -- appendNotNullR :: Proxy xs -> NotNull ys -> NotNull (Append xs ys)
-- -- appendNotNullR Proxy NotNull = NotNull

-- -- appendNotNull :: Proxy y -> Proxy xs -> Proxy ys -> NotNull (Append xs (y:ys))
-- -- appendNotNull Proxy Proxy Proxy = NotNull

-- -- Order may not be preserved
-- type family Append0 (xs :: [k]) (ys :: [k]) (acc :: [k]) :: [k] where
--   Append0 (x:xs) ys acc = Append0 xs ys (x:acc)
--   Append0 xs (y:ys) acc = Append0 '[] ys (y:acc)
--   Append0 '[] '[] acc = acc

-- type Append xs ys = Append0 xs ys '[]


-- test :: Elem 2 [1,2,3]
-- test = There Here

-- -- type family Append (xs :: [k]) (ys :: [k]) :: [k] where
-- --   Append (x:xs) ys = x : Append xs ys
-- --   Append (x:xs) (y:ys) = x : Append xs (y:ys)
-- --   Append '[] ys    = ys
-- --   Append xs '[]    = xs

-- -- union :: Proxy xs -> Proxy ys -> Proxy (Append xs ys)
-- -- union Proxy Proxy = Proxy

-- -- cons :: Proxy x -> Proxy xs -> Proxy (x:xs)
-- -- cons Proxy Proxy = Proxy

-- -- flipAppend :: Proxy x -> Proxy xs -> Proxy ys -> Elem x (Append xs ys) -> Elem x (Append ys xs)
-- -- flipAppend p1@Proxy p2@Proxy p3@Proxy Here = flipAppend 

-- -- unionElem :: Proxy ys -> Elem x xs -> Elem x (Append xs ys)
-- -- unionElem Proxy Here = Here
-- -- unionElem p (There x) = There (unionElem p x)



-- -- unionElem2 :: Proxy xs -> Elem y ys -> Elem y (Append xs ys)
-- -- unionElem2 p@Proxy Here = Here

-- -- unionElem (There x) Here = There (unionElem x Here)
-- -- unionElem (There x) y = _ $ unionElem x y

-- -- data FinSet a where
-- --   FinCons :: Sing n -> Proxy ns -> FinSet (Elem n ns)

