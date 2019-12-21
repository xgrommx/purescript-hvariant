module HFunctor.Variant where

import Prelude

import Control.Alternative (class Alternative, empty)
import Data.Symbol (class IsSymbol, SProxy, reflectSymbol)
import Higher (class HFunctor, hmap)
import Prim.Row as R
import Prim.RowList as RL
import Record.Unsafe (unsafeGet, unsafeHas)
import Type.Equality (class TypeEquals)
import Unsafe.Coerce (unsafeCoerce)
import Partial.Unsafe (unsafeCrashWith)

data HProxy (h ∷ (Type -> Type) -> Type -> Type) = HProxy

class HVariantFMatchCases (rl :: RL.RowList) (vo :: # Type) (a :: Type -> Type) b | rl -> vo a b

instance hvariantFMatchCons :: (HVariantFMatchCases rl vo' a b, R.Cons sym (HProxy h) vo' vo, TypeEquals k (h a b -> c)) => HVariantFMatchCases (RL.Cons sym k rl) vo a b

instance hvariantFMatchNil :: HVariantFMatchCases RL.Nil () a b

newtype HVariantFRep h t a = HVariantFRep
  { type :: String
  , value :: h t a
  , hmap :: forall f g. (f ~> g) -> (h f ~> h g)
  }

data HVariantF (r :: # Type) (f :: Type -> Type) a

instance hfunctorHVariantF ∷ HFunctor (HVariantF r) where
  hmap g a = case coerceY a of
    HVariantFRep v -> coerceV $ HVariantFRep
      { type : v.type
      , value: v.hmap g v.value
      , hmap: v.hmap
      }
    where
      coerceY ∷ forall h f. HVariantF r f ~> HVariantFRep h f
      coerceY = unsafeCoerce
      coerceV ∷ forall h f. HVariantFRep h f ~> HVariantF r f
      coerceV = unsafeCoerce

inj
  ∷ forall sym h f r1 r2
  . R.Cons sym (HProxy h) r1 r2
  => IsSymbol sym
  => HFunctor h
  => SProxy sym
  -> h f
  ~> HVariantF r2 f
inj p value = coerceV $ HVariantFRep { type: reflectSymbol p, value, hmap }
  where
  coerceV ∷ HVariantFRep h f ~> HVariantF r2 f
  coerceV = unsafeCoerce

prj
  ∷ forall sym h f g a r1 r2
  . R.Cons sym (HProxy h) r1 r2
  => Alternative g
  => IsSymbol sym
  => SProxy sym
  -> HVariantF r2 f a
  -> g (h f a)
prj p = on p pure (const empty)

on
  ∷ forall sym h f c a r1 r2
  . R.Cons sym (HProxy h) r1 r2
  => IsSymbol sym
  => SProxy sym
  -> (h f a -> c)
  -> (HVariantF r1 f a -> c)
  -> HVariantF r2 f a
  -> c
on p f g r =
  case coerceY r of
    HVariantFRep v | v.type == reflectSymbol p -> f v.value
    _ -> g (coerceR r)
  where
  coerceY ∷ HVariantF r2 f a -> HVariantFRep h f a
  coerceY = unsafeCoerce

  coerceR ∷ HVariantF r2 f a -> HVariantF r1 f a
  coerceR = unsafeCoerce

onMatch
  ∷ forall rl r r1 r2 r3 a b c
  . RL.RowToList r rl
  => HVariantFMatchCases rl r1 a b
  => R.Union r1 r2 r3
  => Record r
  -> (HVariantF r2 a b -> c)
  -> HVariantF r3 a b
  -> c
onMatch r k v =
  case coerceV v of
    HVariantFRep v' | unsafeHas v'.type r -> unsafeGet v'.type r v'.value
    _ → k (coerceR v)

  where
  coerceV ∷ forall h. HVariantF r3 a b -> HVariantFRep h a b
  coerceV = unsafeCoerce

  coerceR ∷ HVariantF r3 a b -> HVariantF r2 a b
  coerceR = unsafeCoerce

case_ ∷ forall a b c. HVariantF () a b -> c
case_ r = unsafeCrashWith case unsafeCoerce r of
  HVariantFRep v -> "HFunctor.Variant: pattern match failure [" <> v.type <> "]"

match
  ∷ forall rl r r1 r2 a b c
  . RL.RowToList r rl
  => HVariantFMatchCases rl r1 a b
  => R.Union r1 () r2
  => Record r
  -> HVariantF r2 a b
  -> c
match r = case_ # onMatch r

default :: forall a b c r. a -> HVariantF r b c -> a
default a _ = a

expand :: forall lt mix gt a b. R.Union lt mix gt => HVariantF lt a b -> HVariantF gt a b
expand = unsafeCoerce