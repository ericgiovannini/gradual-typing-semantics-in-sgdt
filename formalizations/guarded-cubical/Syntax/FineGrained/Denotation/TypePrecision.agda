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

open import Semantics.Concrete.ConcreteIntensionalModel k
open import Semantics.Concrete.ValType.Constructions k
open import Semantics.Concrete.CompType.Constructions k

⟦_⟧ty⊑ : ∀ {S T} → S ⊑ T → ValTypeRel ⟦ S ⟧ty ⟦ T ⟧ty ℓ-zero
⟦_⟧ty⊑ = {!!}

⟦_⟧ty⊑-≈ : ∀ {S T} {c d : S ⊑ T} → c ≈ d → ValTypeRel≈ ⟦ c ⟧ty⊑ ⟦ d ⟧ty⊑
⟦_⟧ty⊑-≈ = {!!}
