module HFunctor.Variant where

import Prelude

import Control.Alternative (class Alternative, empty)
import Data.Symbol (class IsSymbol, SProxy(..), reflectSymbol)
import Higher (class HFoldable, class HFunctor, class HTraversable, type (~>.), NatM, hfoldMap, hfoldl, hfoldr, hmap, htraverse)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as R
import Prim.RowList as RL
import Record.Unsafe (unsafeGet, unsafeHas)
import Type.Data.RowList (RLProxy(..))
import Type.Equality (class TypeEquals)
import Unsafe.Coerce (unsafeCoerce)

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

class HFoldableHVFRL (rl :: RL.RowList) (row :: # Type) | rl -> row where
  hfoldrHVFRL :: forall a b. RLProxy rl -> (a ~>. (b -> b)) -> b -> HVariantF row a ~>. b
  hfoldlHVFRL :: forall a b. RLProxy rl -> (b -> (a ~>. b)) -> b -> HVariantF row a ~>. b
  hfoldMapHVFRL :: forall m a. Monoid m => RLProxy rl -> (a ~>. m) -> HVariantF row a ~>. m

instance hfoldableNil :: HFoldableHVFRL RL.Nil () where
  hfoldrHVFRL _ _ _ = case_
  hfoldlHVFRL _ _ _ = case_
  hfoldMapHVFRL _ _ = case_

instance hfoldableCons ::
  ( IsSymbol k
  , HFoldable f
  , HFoldableHVFRL rl r
  , R.Cons k (HProxy f) r r'
  ) => HFoldableHVFRL (RL.Cons k (HProxy f) rl) r' where
  hfoldrHVFRL _ f b = on k (hfoldr f b) (hfoldrHVFRL (RLProxy :: RLProxy rl) f b)
    where k = SProxy :: _ k
  hfoldlHVFRL _ f b = on k (hfoldl f b) (hfoldlHVFRL (RLProxy :: RLProxy rl) f b)
    where k = SProxy :: _ k
  hfoldMapHVFRL _ f = on k (hfoldMap f) (hfoldMapHVFRL (RLProxy :: RLProxy rl) f)
    where k = SProxy :: _ k

instance hfoldableHVariantF :: (RL.RowToList row rl, HFoldableHVFRL rl row) => HFoldable (HVariantF row) where
  hfoldr = hfoldrHVFRL (RLProxy :: RLProxy rl)
  hfoldl = hfoldlHVFRL (RLProxy :: RLProxy rl)
  hfoldMap = hfoldMapHVFRL (RLProxy :: RLProxy rl)

class HFoldableHVFRL rl row <= HTraversableHVFRL (rl :: RL.RowList) (row :: # Type) | rl -> row where
  htraverseHVFRL :: forall a b c. Applicative c => RLProxy rl -> NatM c a b -> NatM c (HVariantF row a) (HVariantF row b)

instance htraversableNil :: HTraversableHVFRL RL.Nil () where
  htraverseHVFRL _ f = case_

instance htraversableCons ::
  ( IsSymbol k
  , HTraversable f
  , HTraversableHVFRL rl r
  , R.Cons k (HProxy f) r r'
  , R.Union r rx r'
  ) => HTraversableHVFRL (RL.Cons k (HProxy f) rl) r' where
  htraverseHVFRL _ f = on k (htraverse f >>> map (inj k)) (htraverseHVFRL (RLProxy :: RLProxy rl) f >>> map expand)
    where k = SProxy :: SProxy k

instance htraversableVariantF :: (RL.RowToList row rl, HTraversableHVFRL rl row) => HTraversable (HVariantF row) where
  htraverse = htraverseHVFRL (RLProxy :: RLProxy rl)

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