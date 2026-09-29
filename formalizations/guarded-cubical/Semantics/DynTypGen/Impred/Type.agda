{-# OPTIONS --allow-unsolved-metas #-}


module Semantics.DynTypGen.Impred.Type where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Categories.Category

private
  variable
    ℓ ℓ' : Level

{-

  This module postulates an impredicative universe of types.
  Specifically, there is a connective ∀ᵢ for impredicative universal
  quantification and a connective ∃ᵢ for impredicative existential
  quantification.

-}



postulate
  IType : Type

  ⟨_⟩s : IType → Type ℓ-zero   -- inclusion into Type ℓ-zero


postulate

  -- Closure under dependent products and sums
  Πᵢ : (A : IType) → (B : ⟨ A ⟩s → IType) → IType

  Σᵢ : (A : IType) → (B : ⟨ A ⟩s → IType) → IType

-- Non-dependent function types
_→ᵢ_ : IType → IType → IType
A →ᵢ B = Πᵢ A (λ _ → B)

postulate

  -- Identity and composition for →ᵢ
  idᵢ : (A : IType) → ⟨ A →ᵢ A ⟩s

  compᵢ : {A B C : IType}
    → ⟨ B →ᵢ C ⟩s
    → ⟨ A →ᵢ B ⟩s
    → ⟨ A →ᵢ C ⟩s

  compᵢ-idL : {A B : IType}
    → (f : ⟨ A →ᵢ B ⟩s)
    → compᵢ (idᵢ B) f ≡ f

  compᵢ-idR : {A B : IType}
    → (f : ⟨ A →ᵢ B ⟩s)
    → compᵢ f (idᵢ A) ≡ f

  compᵢ-assoc : {A B C D : IType}
    → (f : ⟨ A →ᵢ B ⟩s)
    → (g : ⟨ B →ᵢ C ⟩s)
    → (h : ⟨ C →ᵢ D ⟩s)
    → compᵢ h (compᵢ g f) ≡ compᵢ (compᵢ h g) f



postulate

  -- Closure under universal quantification over arbitrary types
  ∀ᵢ : {A : Type ℓ} (B : A → IType) → IType

  ∀ᵢ-intro : {A : Type ℓ} {B : A → IType}
    → (∀ (x : A) → ⟨ B x ⟩s)
    → ⟨ ∀ᵢ B ⟩s

  ∀ᵢ-elim : {A : Type ℓ} {B : A → IType}
    → ⟨ ∀ᵢ B ⟩s
    → (∀ (x : A) → ⟨ B x ⟩s)






