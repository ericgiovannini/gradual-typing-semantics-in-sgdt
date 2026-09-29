{-# OPTIONS --allow-unsolved-metas #-}


module Semantics.DynTypGen.Impred.Set where

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

  This module postulates an impredicative universe of h-sets.
  Specifically, there is a connective ∀ᵢ for impredicative universal
  quantification and a connective ∃ᵢ for impredicative existential
  quantification.

-}



postulate
  ISet : Type

  ⟨_⟩s : ISet → hSet ℓ-zero   -- inclusion into hSet ℓ-zero

⟨_⟩hs : ISet → Type ℓ-zero
⟨_⟩hs = ⟨_⟩ ∘ ⟨_⟩s


postulate

  -- Closure under dependent products and sums
  Πᵢ : (A : ISet) → (B : ⟨ A ⟩hs → ISet) → ISet

  Σᵢ : (A : ISet) → (B : ⟨ A ⟩hs → ISet) → ISet

-- Non-dependent function types
_→ᵢ_ : ISet → ISet → ISet
A →ᵢ B = Πᵢ A (λ _ → B)

postulate

  -- Identity and composition for →ᵢ
  idᵢ : (A : ISet) → ⟨ A →ᵢ A ⟩hs

  compᵢ : {A B C : ISet}
    → ⟨ B →ᵢ C ⟩hs
    → ⟨ A →ᵢ B ⟩hs
    → ⟨ A →ᵢ C ⟩hs

  compᵢ-idL : {A B : ISet}
    → (f : ⟨ A →ᵢ B ⟩hs)
    → compᵢ (idᵢ B) f ≡ f

  compᵢ-idR : {A B : ISet}
    → (f : ⟨ A →ᵢ B ⟩hs)
    → compᵢ f (idᵢ A) ≡ f

  compᵢ-assoc : {A B C D : ISet}
    → (f : ⟨ A →ᵢ B ⟩hs)
    → (g : ⟨ B →ᵢ C ⟩hs)
    → (h : ⟨ C →ᵢ D ⟩hs)
    → compᵢ h (compᵢ g f) ≡ compᵢ (compᵢ h g) f



postulate

  -- Closure under universal quantification over arbitrary types
  ∀ᵢ : {A : Type ℓ} (B : A → ISet) → ISet

  ∀ᵢ-intro : {A : Type ℓ} {B : A → ISet}
    → (∀ (x : A) → ⟨ B x ⟩hs)
    → ⟨ ∀ᵢ B ⟩hs

  ∀ᵢ-elim : {A : Type ℓ} {B : A → ISet}
    → ⟨ ∀ᵢ B ⟩hs
    → (∀ (x : A) → ⟨ B x ⟩hs)


----------------------------------
-- Category of impredicative sets
----------------------------------

open Category

ISET : Category ℓ-zero ℓ-zero
ISET .ob = ISet
ISET .Hom[_,_] A B = ⟨ A →ᵢ B ⟩hs
ISET .id = idᵢ _
ISET ._⋆_ f g = compᵢ g f
ISET .⋆IdL = compᵢ-idR
ISET .⋆IdR = compᵢ-idL
ISET .⋆Assoc = compᵢ-assoc
ISET .isSetHom {x} {y} = ⟨ x →ᵢ y ⟩s .snd











{-
postulate
  
  ∀ᵢ : {A : Type ℓ} (B : A → hSet ℓ-zero) → hSet ℓ-zero

  ∀ᵢ-intro : {A : Type ℓ} {B : A → hSet ℓ-zero}
    → (∀ (x : A) → ⟨ B x ⟩)
    → ⟨ ∀ᵢ B ⟩

  ∀ᵢ-elim : {A : Type ℓ} {B : A → hSet ℓ-zero}
    → ⟨ ∀ᵢ B ⟩
    → (∀ (x : A) → ⟨ B x ⟩)

-}



