{-
  Denotational semantics of gradual types as error predomains
-}
{-# OPTIONS --rewriting --lossy-unification --allow-unsolved-metas #-}
open import Common.Later
module Syntax.FineGrained.Denotation.Types (k : Clock) where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Foundations.Structure
open import Cubical.Data.List
open import Syntax.Types
open import Semantics.Concrete.Types k as SemTypes
open import Semantics.Concrete.Dyn.DynInstantiated k

⟦_⟧ty : Ty → ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
⟦ nat ⟧ty = ℕ
⟦ dyn ⟧ty = DynV
⟦ A ⇀ B ⟧ty = U (⟦ A ⟧ty ⟶ F ⟦ B ⟧ty)

⟦_⟧ctx : Ctx → ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
⟦_⟧ctx = foldr (λ A ⟦Γ⟧ → ⟦Γ⟧ × ⟦ A ⟧ty) Unit
