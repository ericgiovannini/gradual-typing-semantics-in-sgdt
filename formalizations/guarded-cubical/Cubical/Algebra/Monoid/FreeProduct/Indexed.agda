{-# OPTIONS --safe #-}
module Cubical.Algebra.Monoid.FreeProduct.Indexed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid.Displayed

open import Cubical.Algebra.Monoid.FreeMonoid as Free hiding (elim)
open import Cubical.Data.Empty as Empty hiding (elim)

private variable
  ℓ ℓ' ℓ'' ℓ''' ℓᴰ : Level

module _ (X : Type ℓ) (M : X → Monoid ℓ') where
  ⊕ : Monoid ℓ
  ⊕ = FM X ⊥ ⊥

  module _ {Mᴰ : Monoidᴰ ⊕ ℓᴰ} where
    private
      module Mᴰ = Monoidᴰ Mᴰ
    module _ (iX : ∀ x → Mᴰ.eltᴰ ⟦ x ⟧) where
      elim : Section Mᴰ
      elim = Free.elim _ _ _ Mᴰ iX Empty.elim Empty.elim
