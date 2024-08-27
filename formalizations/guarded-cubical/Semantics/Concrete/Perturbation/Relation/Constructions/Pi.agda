{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
module Semantics.Concrete.Perturbation.Relation.Constructions.Pi (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_)
open import Cubical.Relation.Nullary.Base


open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.FreeProduct.Indexed as Indexed

open import Cubical.Relation.Nullary

open import Common.Common
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions hiding (π1; π2)
open import Semantics.Concrete.DoublePoset.DPMorRelation as PRel hiding (ΣR ; ΠR)
open import Semantics.Concrete.DoublePoset.PBSquare

open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Types k as Types hiding (U; F; _⟶_)
open import Semantics.Concrete.Perturbation.Relation.Alt k

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓ≤' ℓ≈' ℓM' : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂ : Level
    ℓc ℓc' ℓd ℓd' : Level
    ℓX : Level


ΠR : (X : DiscreteTy ℓX) →
  (A₁ : ⟨ X ⟩ → ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁) →
  (A₂ : ⟨ X ⟩ → ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂) →
  (rs : (x : ⟨ X ⟩) → VRelPP (A₁ x) (A₂ x) ℓc) →
  VRelPP (ΠV X A₁) (ΠV X A₂) (ℓ-max ℓX ℓc)

-- Predomain relation
ΠR (X , dec) A₁ A₂ rs .fst =
  PRel.ΠR X (ValType→Predomain ∘ A₁) (ValType→Predomain ∘ A₂) (VRelPP→PredomainRel ∘ rs)

-- Push
ΠR X A₁ A₂ rs .snd .fst = Indexed.elim _ _ _ aux
  where
    aux : _
    aux x .fst p = {!!} -- rs x .snd .fst
    aux x .snd = {!!}

-- Pull
ΠR X A₁ A₂ rs .snd .snd = {!!}
