{-# OPTIONS --safe #-}
module Cubical.Algebra.Monoid.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

record Monoidᴰ (M : Monoid ℓ) ℓ' : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  open MonoidStr (M .snd)
  field
    eltᴰ : ⟨ M ⟩ → Type ℓ'
    εᴰ : eltᴰ ε
    _·ᴰ_ : ∀ {x y} → eltᴰ x → eltᴰ y → eltᴰ (x · y)
  _≡[_]_ : ∀ {x y} → eltᴰ x → x ≡ y → eltᴰ y → Type _
  xᴰ ≡[ p ] yᴰ = PathP (λ i → eltᴰ (p i)) xᴰ yᴰ
  field
    ·IdRᴰ : ∀ {x}(xᴰ : eltᴰ x) → (xᴰ ·ᴰ εᴰ) ≡[ ·IdR x ] xᴰ
    ·IdLᴰ : ∀ {x}(xᴰ : eltᴰ x) → (εᴰ ·ᴰ xᴰ) ≡[ ·IdL x ] xᴰ
    ·Assocᴰ  : ∀ {x y z}(xᴰ : eltᴰ x)(yᴰ : eltᴰ y)(zᴰ : eltᴰ z)
      → (xᴰ ·ᴰ (yᴰ ·ᴰ zᴰ)) ≡[ ·Assoc x y z ] ((xᴰ ·ᴰ yᴰ) ·ᴰ zᴰ)
    isSetEltᴰ : ∀ {x} → isSet (eltᴰ x)
Section : {M : Monoid ℓ} (Mᴰ : Monoidᴰ M ℓ') → Type (ℓ-max ℓ ℓ')
Section {M = M} Mᴰ =
  Σ[ f ∈ (∀ (x : ⟨ M ⟩) → eltᴰ x) ]
  (f ε ≡ εᴰ) ×
  (∀ x y → f (x · y) ≡ (f x ·ᴰ f y))
  where
  open MonoidStr (M .snd)
  open Monoidᴰ Mᴰ

MonoidHomᴰ : {M : Monoid ℓ}{N : Monoid ℓ'}
  (ϕ : MonoidHom M N)
  → Monoidᴰ M ℓᴰ
  → Monoidᴰ N ℓᴰ' → Type (ℓ-max (ℓ-max ℓ ℓᴰ) ℓᴰ')
MonoidHomᴰ {M = M}{N} ϕ Mᴰ Nᴰ =
  Σ[ ϕᴰ ∈ (∀ {x}(xᴰ : Mᴰ.eltᴰ x) → Nᴰ.eltᴰ (ϕ .fst x) )]
  (ϕᴰ Mᴰ.εᴰ Nᴰ.≡[ presε ] Nᴰ.εᴰ) ×
  (∀ {x y}(xᴰ : Mᴰ.eltᴰ x)(yᴰ : Mᴰ.eltᴰ y) →
  ϕᴰ (xᴰ Mᴰ.·ᴰ yᴰ) Nᴰ.≡[ pres· x y ] (ϕᴰ xᴰ Nᴰ.·ᴰ ϕᴰ yᴰ))
  where
    module Mᴰ = Monoidᴰ Mᴰ
    module Nᴰ = Monoidᴰ Nᴰ
    open IsMonoidHom (ϕ .snd)

open MonoidStr
wkn : (M : Monoid ℓ) (N : Monoid ℓ') → Monoidᴰ M ℓ'
wkn M N .Monoidᴰ.eltᴰ x = ⟨ N ⟩
wkn M N .Monoidᴰ.εᴰ = N .snd .ε
wkn M N .Monoidᴰ._·ᴰ_ = N .snd ._·_
wkn M N .Monoidᴰ.·IdRᴰ = N .snd .·IdR
wkn M N .Monoidᴰ.·IdLᴰ = N .snd .·IdL
wkn M N .Monoidᴰ.·Assocᴰ = N .snd .·Assoc
wkn M N .Monoidᴰ.isSetEltᴰ = is-set (N .snd)

open Monoidᴰ
_^opᴰ : ∀ {M : Monoid ℓ} → Monoidᴰ M ℓᴰ → Monoidᴰ (M ^op) ℓᴰ
(Mᴰ ^opᴰ) .Monoidᴰ.eltᴰ = Mᴰ .eltᴰ
(Mᴰ ^opᴰ) .Monoidᴰ.εᴰ = Mᴰ .εᴰ
(Mᴰ ^opᴰ) .Monoidᴰ._·ᴰ_ xᴰ yᴰ = Mᴰ ._·ᴰ_ yᴰ xᴰ
(Mᴰ ^opᴰ) .Monoidᴰ.·IdRᴰ = Mᴰ .·IdLᴰ
(Mᴰ ^opᴰ) .Monoidᴰ.·IdLᴰ = Mᴰ .·IdRᴰ
(Mᴰ ^opᴰ) .·Assocᴰ xᴰ yᴰ zᴰ = symP (Mᴰ .·Assocᴰ _ _ _)
(Mᴰ ^opᴰ) .Monoidᴰ.isSetEltᴰ = Mᴰ .isSetEltᴰ
