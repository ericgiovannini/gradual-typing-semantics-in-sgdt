{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.Predomain.GuardedTheory.Shift where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.FinData

open import Semantics.Concrete.Predomain.GuardedTheory.Arity
open import Semantics.Concrete.Predomain.GuardedTheory.Signature
open import Semantics.Concrete.Predomain.GuardedTheory.Term
open import Semantics.Concrete.Predomain.GuardedTheory.Substitution



-- Shifting a Term (corresponds to the action of ▹ on objects)
shiftTerm : {Σ : Signature} {Γ : Arity} {d : ℕ}
  → Term Σ Γ d → Term Σ (shift Γ) (suc d)

shiftVar : {Γ : Arity} {d : ℕ} → Var Γ d → Var (shift Γ) (suc d)
shiftVar x = {!x!}

shiftArgs : {Σ : Signature} {Γ Δ : Arity} {p : ℕ}
  → Args Σ Γ p Δ → Args Σ (shift Γ) (suc p) Δ

shiftTerm t = {!!}
shiftArgs = {!!}


-- Shifting a substitution (corresponds to the action of ▹ on morphisms)
shiftSub : {Σ : Signature} {Γ Δ : Arity}
  → Subst Σ Γ Δ → Subst Σ (shift Γ) (shift Δ)
shiftSub = {!!}


-- substitution corresponding to `next`
-- TODO: should probably move to its own file
nextSubst : {Σ : Signature} {Γ : Arity} → Subst Σ Γ (shift Γ)
nextSubst = {!!}
