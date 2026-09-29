{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --polarity #-}

open import Common.Common

module Experiments.InductivePredomain where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

import Cubical.Data.List as List
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Relation.Binary.Base

open import Semantics.Concrete.Predomain.Base


private
  variable
    ℓ ℓ' ℓ≤ ℓ≈ ℓ≤' ℓ≈' : Level
    ℓA ℓA' ℓB ℓB' : Level
    ℓR ℓR₁ ℓR₂ : Level

open BinaryRelation

open IsOrderingRelation
open IsBisim
open PredomainStr hiding (_≈_)

-- module _ (F : @++ Predomain ℓ ℓ≤ ℓ≈ → Predomain ℓ ℓ≤ ℓ≈) where
module _ (F : @++ Predomain ℓ ℓ ℓ → Predomain ℓ ℓ ℓ) where

  data |Mu| : Type ℓ

  {-# TERMINATING #-}
  Mu : Predomain ℓ ℓ ℓ

  {-# NO_POSITIVITY_CHECK #-}
  data |Mu| where
    fold : F Mu .fst → |Mu|

  isSetMu : isSet |Mu|
  isSetMu (fold x) (fold y) p q i j = {!!}

  data _⊑_ : |Mu| → |Mu| → Type ℓ where
    ord-fold : ∀ {x y : F Mu .fst}
      → F Mu .snd .PredomainStr._≤_ x y
      → fold x ⊑ fold y


  ord-prop : isPropValued _⊑_
  ord-prop (fold x) (fold y) (ord-fold p) (ord-fold q) =
    cong ord-fold (F Mu .snd .isOrderingRelation .is-prop-valued x y p q)

  ord-refl : isRefl _⊑_
  ord-refl (fold x) =
    ord-fold (F Mu .snd .isOrderingRelation .is-refl x)

  ord-trans : isTrans _⊑_
  ord-trans (fold x) (fold y) (fold z) (ord-fold x≤y) (ord-fold y≤z) =
    ord-fold (F Mu .snd .isOrderingRelation .is-trans x y z x≤y y≤z)

  ord-antisym : isAntisym _⊑_
  ord-antisym (fold x) (fold y) (ord-fold x≤y) (ord-fold y≤x) =
    cong fold (F Mu .snd .isOrderingRelation .is-antisym x y x≤y y≤x)

  isOrd⊑ : IsOrderingRelation _⊑_
  isOrd⊑ .is-prop-valued = ord-prop
  isOrd⊑ .is-refl = ord-refl
  isOrd⊑ .is-trans = ord-trans
  isOrd⊑ .is-antisym = ord-antisym


  data _≈_ : |Mu| → |Mu| → Type ℓ where
   bisim-fold : ∀ {x y : F Mu .fst}
      → F Mu .snd .PredomainStr._≈_ x y
      → fold x ≈ fold y

  bisim-prop : isPropValued _≈_
  bisim-prop (fold x) (fold y) (bisim-fold p) (bisim-fold q) =
    cong bisim-fold (F Mu .snd .isBisim .is-prop-valued x y p q)

  bisim-sym : isSym _≈_
  bisim-sym (fold x) (fold y) (bisim-fold x≈y) =
    bisim-fold (F Mu .snd .isBisim .is-sym x y x≈y)

  bisim-refl : isRefl _≈_
  bisim-refl (fold x) =
    bisim-fold (F Mu .snd .isBisim .is-refl x)

  isBisim≈ : IsBisim _≈_
  isBisim≈ .is-refl = bisim-refl
  isBisim≈ .is-sym = bisim-sym
  isBisim≈ .is-prop-valued = bisim-prop

  
  Mu .fst = |Mu|
  Mu .snd .is-set = isSetMu
  Mu .snd ._≤_ = _⊑_
  Mu .snd .isOrderingRelation = isOrd⊑
  Mu .snd .PredomainStr._≈_ = _≈_
  Mu .snd .isBisim = isBisim≈

-- predomainstr {!!} _⊑_ isOrd _≈_ {!!}
