{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}


module Cubical.Algebra.Monoid.Displayed.Instances.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Reindex

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ (N : Monoid ℓ) where
  private
    module N = MonoidStr (N .snd)
    open Monoidᴰ

  MonPath : Monoidᴰ (N ×M N) ℓ
  MonPath = submonoid→Monoidᴰ sub
    where
      open Submonoid
      sub : Submonoid (N ×M N) ℓ
      sub .eltᴰ (x , y) = x ≡ y
      sub .εᴰ = refl
      sub ._·ᴰ_ p q = cong₂ N._·_ p q
      sub .isPropEltᴰ = N.is-set _ _


module _ {M : Monoid ℓ} {N : Monoid ℓ'}
  (f g : MonoidHom M N) where

  private
    module N = MonoidStr (N .snd)
    module f = IsMonoidHom (f .snd)
    module g = IsMonoidHom (g .snd)
    open Monoidᴰ

  Eq : Monoidᴰ M ℓ'
  Eq = Reindex (×M-intro f g) (MonPath N)

  module _ {P : Monoid ℓ''} {ϕ : MonoidHom P M}
    (eq : (f ∘hom ϕ) ≡ (g ∘hom ϕ))
    where

    private
      module P = MonoidStr (P .snd)

      ls : LocalSection ((×M-intro f g) ∘hom ϕ) (MonPath N)
      ls .fst x = funExt⁻ (cong fst eq) x
      ls .snd .fst = isProp→PathP (λ i → N.is-set _ _) _ _
      ls .snd .snd _ _ = isProp→PathP (λ i → N.is-set _ _) _ _

    corecEq : LocalSection ϕ Eq
    corecEq = ls-reind ls

