{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.AbstractSyntax (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)
import Cubical.Data.Sigma as Data
open import Cubical.Foundations.Structure
open import Cubical.Data.List


open import Common.Common
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions
  using (LiftPredomain ; ℕ ; UnitP ; _×dp_ ; _⊎p_ ; π1 ; π2)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Combinators hiding (S ; U)
open import Semantics.Concrete.Predomain.SquareOpaque
open import Semantics.Concrete.Predomain.SquareCombinators

open import Semantics.Concrete.Predomain.SimpleErrorDomain k
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.ErrorDomain.Square k
open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k

open import Semantics.Concrete.Predomain.Error

open import Semantics.Concrete.Predomain.Ext k
open import Semantics.Concrete.Predomain.MonadRelationalResultsOpaque k
open import Semantics.Concrete.Predomain.FreeErrorDomainOpaque k
open import Semantics.Concrete.Predomain.MonadCombinatorsOpaque k

open ClockedCombinators k


private
  variable
    ℓ ℓ' : Level
    ℓa  ℓ≤A  ℓ≈A  : Level
    ℓA' ℓ≤A' ℓ≈A' : Level
    ℓB  ℓ≤B  ℓ≈B  : Level
    ℓB' ℓ≤B' ℓ≈B' : Level
    ℓΓ ℓ≤Γ ℓ≈Γ : Level

    ℓ≤ ℓ≈ : Level


private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

open F-ob
open F-mor
open LiftPredomain
open PMor


-- A syntax for building morphisms and squares in the predomain model

data VTy : Type
data CTy : Type

data CTy where
  F : VTy → CTy
  _⟶_ : VTy → CTy → CTy

data VTy where
  nat : VTy
  _×_ : VTy → VTy → VTy
  _⊎_ : VTy → VTy → VTy
  _⇒_ : VTy → VTy → VTy
  U : CTy → VTy
  -- eq : ∀ (A : VTy) (B : CTy) → U (A ⟶ B) ≡ (A ⇒ (U B))



Ctx : Type
Ctx = List VTy

-- reduce : Ctx → Predomain ℓ-zero ℓ-zero ℓ-zero
-- reduce Γ = {!!}

-- syntax reduce Γ = ⟦ Γ × ⟧

data _∈_ : VTy → Ctx → Type where
  Z : ∀ A Γ → A ∈ (A ∷ Γ)
  S : ∀ A B Γ → A ∈ Γ → A ∈ (B ∷ Γ)


-- _⇒_ : VTy → VTy → VTy
-- Aᵢ ⇒ Aₒ = {!Aᵢ ⟶ U !}

{-
Value types denote:
  1. Predomains
  2. Predomain relations

Computation types denote:
  1. Error domains
  2. Error doamin relations

Value morphisms denote:
  1. Predomain morphisms
  2. Predomain squares

Computation morphisms denote:
  1. Error domain morphisms
  2. Error domain squares
-}

module TypeSem (ℓ : Level) where

  ⟦_⟧v : VTy → Predomain ℓ ℓ ℓ
  ⟦_⟧c : CTy → ErrorDomain ℓ ℓ ℓ

  ⟦ nat ⟧v = LiftPredomain ℕ _ _ _
  ⟦ A₁ × A₂ ⟧v = ⟦ A₁ ⟧v ×dp ⟦ A₂ ⟧v
  ⟦ A₁ ⊎ A₂ ⟧v = ⟦ A₁ ⟧v ⊎p ⟦ A₂ ⟧v
  ⟦ Aᵢ ⇒ Aₒ ⟧v = ⟦ Aᵢ ⟧v ==> ⟦ Aₒ ⟧v
  ⟦ U B ⟧v = U-ob ⟦ B ⟧c
  -- ⟦ eq A B i ⟧v = U-ob (⟦ A ⟧v ⟶ob ⟦ B ⟧c)

  ⟦ F A ⟧c = F-ob ⟦ A ⟧v
  ⟦ A ⟶ B ⟧c = ⟦ A ⟧v ⟶ob ⟦ B ⟧c


  ⟦_⟧ctx : Ctx → Predomain ℓ ℓ ℓ
  ⟦ [] ⟧ctx = LiftPredomain UnitP ℓ ℓ ℓ
  ⟦ A ∷ Γ ⟧ctx = ⟦ A ⟧v ×dp ⟦ Γ ⟧ctx

  ⟦_⟧vr : VTy → Σ[ A ∈ Predomain ℓ ℓ ℓ ] Σ[ A' ∈ Predomain ℓ ℓ ℓ ] (PRel A A' ℓ)
  ⟦ nat ⟧vr = ⟦ nat ⟧v , ⟦ nat ⟧v , idPRel _
  ⟦ A₁ × A₂ ⟧vr =
    let A₁-l = ⟦ A₁ ⟧vr .fst      in
    let A₁-r = ⟦ A₁ ⟧vr .snd .fst in
    let c₁   = ⟦ A₁ ⟧vr .snd .snd in
    let A₂-l = ⟦ A₂ ⟧vr .fst      in
    let A₂-r = ⟦ A₂ ⟧vr .snd .fst in
    let c₂   = ⟦ A₂ ⟧vr .snd .snd in
    (A₁-l ×dp A₂-l) , (A₁-r ×dp A₂-r) , (c₁ ×pbmonrel c₂)
  ⟦ A₁ ⊎ A₂ ⟧vr = {!!}
  ⟦ Aᵢ ⇒ Aₒ ⟧vr = {!!}
  ⟦ U B ⟧vr = {!!}
  -- ⟦ eq A B i ⟧vr = {!!}
  





-- ⟦_⟧v' : VTy → (ℓ ℓ≤ ℓ≈ : Level)
--   → Σ[ ℓ' ∈ Level ] Σ[ ℓ≤' ∈ Level ] Σ[ ℓ≈' ∈ Level ] (Predomain ℓ' ℓ≤' ℓ≈')



data VTm (Γ : Ctx) : VTy → Type where
  π₁ : ∀ {A₁ A₂} → VTm Γ (A₁ × A₂) → VTm Γ A₁
  π₂ : ∀ {A₁ A₂} → VTm Γ (A₁ × A₂) → VTm Γ A₂
  i₁ : ∀ {A₁ A₂} → VTm Γ A₁ → VTm Γ (A₁ ⊎ A₂)
  i₂ : ∀ {A₁ A₂} → VTm Γ A₂ → VTm Γ (A₁ ⊎ A₂)



data CTm (Γ : Ctx) : CTy → Type where

module _ (ℓ : Level) where

  open TypeSem ℓ
  
  ⟦_⟧vtm : ∀ {Γ A} → VTm Γ A → PMor ⟦ Γ ⟧ctx ⟦ A ⟧v
  ⟦ π₁ M ⟧vtm = π1 ∘p ⟦ M ⟧vtm
  ⟦ π₂ M ⟧vtm = π2 ∘p ⟦ M ⟧vtm
  ⟦ i₁ M ⟧vtm = {!!}
  ⟦ i₂ M ⟧vtm = {!!}
  









