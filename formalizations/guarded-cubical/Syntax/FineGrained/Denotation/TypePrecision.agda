{-

  Denotational semantics of type precision as quasi-representable
  predomain relations with a push-pull structure.
  
-}
{-# OPTIONS --rewriting --lossy-unification --allow-unsolved-metas #-}
open import Common.Later
module Syntax.FineGrained.Denotation.TypePrecision (k : Clock) where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Foundations.Structure
open import Cubical.Data.List

open import Syntax.Types
open import Syntax.FineGrained.Denotation.Types k
open import Semantics.Concrete.Relations k

⟦_⟧ty⊑ : ∀ {S T} → S ⊑ T → ValRel ⟦ S ⟧ty ⟦ T ⟧ty ℓ-zero
⟦ refl-⊑ ⟧ty⊑ = IdV _
⟦ trans-⊑ c c₁ ⟧ty⊑ = {!!}
⟦ c ⇀ d ⟧ty⊑ = {!!}
⟦ inj-nat ⟧ty⊑ = {!!}
⟦ inj-arr ⟧ty⊑ = {!!}

⟦_⟧ctx⊑ : ∀ {Γ Δ} → Γ ⊑ctx Δ → ValRel ⟦ Γ ⟧ctx ⟦ Δ ⟧ctx ℓ-zero
⟦ [] ⟧ctx⊑ = IdV _
⟦ c ∷ C ⟧ctx⊑ = {!!}

⟦_⟧ty⊑-≈ : ∀ {S T} {c d : S ⊑ T} → c ≈ d → ValRel≈ ⟦ c ⟧ty⊑ ⟦ d ⟧ty⊑
⟦_⟧ty⊑-≈ = {!!}
