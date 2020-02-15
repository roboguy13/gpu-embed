-- Boehm-Berrarduci encoding (which doesn't seem to be an encoding that
-- works for our use-case).

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}

module BB where

import           GHC.Generics
import           Data.Data

import           Data.Generics.Uniplate
import           Data.Generics.Uniplate.Data

-- data End f = forall a. End (f a)

-- type BBBool0 r = (() -> r) -> (() -> r) -> r
-- type BBNat0 r = (() -> r) -> (r -> r) -> r
-- type BBExample0 r = (BBNat -> r) -> (BBBool -> r) -> r


data Nat = Z | S Nat deriving (Generic, Show, Data)

data Example = N Nat | B Bool deriving (Generic, Show, Data)

data BBBool    = BBBool (forall r. (() -> r) -> (() -> r) -> r)
data BBNat     = BBNat (forall r. (() -> r) -> (r -> r) -> r)
data BBExample = BBExample (forall r. (BBNat -> r) -> (BBBool -> r) -> r)

bbnatZ :: BBNat
bbnatZ = BBNat $ \f _g -> f ()

bbnatS :: BBNat -> BBNat
bbnatS (BBNat nat) = BBNat $ \f g -> nat (g . f) g

bbfalse :: BBBool
bbfalse = BBBool $ \f _g -> f ()

bbtrue :: BBBool
bbtrue = BBBool $ \_f g -> g ()

bbnot :: BBBool -> BBBool
bbnot bool = elim_bbbool bool (\() -> bbtrue) (\() -> bbfalse)

boolBB :: Bool -> BBBool
boolBB False = bbfalse
boolBB True  = bbtrue

bbboolToBool :: BBBool -> Bool
bbboolToBool (BBBool bool) = bool (const False) (const True)

bbnatToNat :: BBNat -> Nat
bbnatToNat (BBNat nat) = nat (const Z) S

natBB :: Nat -> BBNat
natBB Z     = bbnatZ
natBB (S n) = bbnatS (natBB n)

exampleNat :: BBNat -> BBExample
exampleNat nat = BBExample $ \f _g -> f nat

exampleBool :: BBBool -> BBExample
exampleBool bool = BBExample $ \_f g -> g bool

bbexampleToExample :: BBExample -> Example
bbexampleToExample (BBExample ex) =
  ex (\nat -> N $ bbnatToNat nat) (\bool -> B $ bbboolToBool bool)

exampleBB :: Example -> BBExample
exampleBB (N n) = exampleNat (natBB n)
exampleBB (B b) = exampleBool (boolBB b)

elim_bbbool :: BBBool -> (() -> r) -> (() -> r) -> r
elim_bbbool (BBBool bool) = bool

elim_bbnat :: BBNat -> (() -> r) -> (r -> r) -> r
elim_bbnat (BBNat nat) = nat

elim_bbexample :: BBExample -> (BBNat -> r) -> (BBBool -> r) -> r
elim_bbexample (BBExample ex) = ex





exampleFn :: Example -> Example
exampleFn (N Z)     = B False
exampleFn (N (S n)) = N n
exampleFn (B b)     = B (not b)

exampleFn_bb :: BBExample -> BBExample
exampleFn_bb ex =
  elim_bbexample ex natPart boolPart
  where
    natPart :: BBNat -> BBExample
    natPart nat =
      elim_bbnat nat (\() -> exampleBool bbfalse)
                     (\n  -> n) -- XXX: ???

    -- This is unsimplified because this is an attempt at a relatively
    -- direct translation of the 'case' from 'exampleFn'.
    boolPart :: BBBool -> BBExample
    boolPart bool =
      elim_bbbool bool (\() -> exampleBool $ bbnot bbfalse) (\() -> exampleBool $ bbnot bbtrue)

overBBEx :: (BBExample -> BBExample) -> Example -> Example
overBBEx f ex = bbexampleToExample (f (exampleBB ex))

retranslated_exampleFn :: Example -> Example
retranslated_exampleFn = overBBEx exampleFn_bb

translated_exampleFn :: BBExample -> BBExample
translated_exampleFn ex = exampleBB (exampleFn (bbexampleToExample ex))

-- Unfolding the previous function by hand:
translated_exampleFn1 :: BBExample -> BBExample
translated_exampleFn1 ex0 = -- Inline 'bbexampleToExample'
  exampleBB (exampleFn
    (case ex0 of
      BBExample ex ->
        ex (\nat -> N $ bbnatToNat nat) (\bool -> B $ bbboolToBool bool)))

translated_exampleFn2 :: BBExample -> BBExample
translated_exampleFn2 ex0 = -- Inline 'exampleFn'
  exampleBB (
    case (case ex0 of
            BBExample ex ->
              ex (\nat -> N $ bbnatToNat nat) (\bool -> B $ bbboolToBool bool)) of
      N Z -> B False
      N (S n) -> N n
      B b -> B (not b))

translated_exampleFn3 :: BBExample -> BBExample
translated_exampleFn3 ex0 = -- Float case
  case ex0 of
    BBExample ex ->
      exampleBB (
        case ex (\nat -> N $ bbnatToNat nat) (\bool -> B $ bbboolToBool bool) of
          N Z -> B False
          N (S n) -> N n
          B b -> B (not b))

translated_exampleFn4 :: BBExample -> BBExample
translated_exampleFn4 ex0 = -- Inline 'exampleBB'
  case ex0 of
    BBExample ex ->
      case (case ex (\nat -> N $ bbnatToNat nat) (\bool -> B $ bbboolToBool bool) of
              N Z -> B False
              N (S n) -> N n
              B b -> B (not b)) of
        N n -> exampleNat (natBB n)
        B b -> exampleBool (boolBB b)

translated_exampleFn5 :: BBExample -> BBExample
translated_exampleFn5 ex0 = -- "Combining case expressions" with some additional simplification
  case ex0 of
    BBExample ex ->
      case ex (\nat -> N $ bbnatToNat nat) (\bool -> B $ bbboolToBool bool) of
        N Z     -> exampleBool (boolBB False)
        N (S n) -> exampleNat (natBB n)
        B b     -> exampleBool (boolBB (not b))

translated_exampleFn6 :: BBExample -> BBExample
translated_exampleFn6 ex0 =
  case ex0 of
    BBExample ex ->
      exampleBB (ex (\nat -> N $ bbnatToNat nat) (\bool -> B $ bbboolToBool bool))

