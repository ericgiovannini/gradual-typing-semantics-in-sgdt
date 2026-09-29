{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.Predomain.GuardedTheory.Substitution where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.FinData

open import Semantics.Concrete.Predomain.GuardedTheory.Arity
open import Semantics.Concrete.Predomain.GuardedTheory.Signature
open import Semantics.Concrete.Predomain.GuardedTheory.Term

open Signature


-- Substitutions:

Subst : Signature → Arity → Arity → Type
Subst Σ Γ Δ = (d : ℕ) → Var Δ d → Term Σ Γ d
-- Each variable of Δ at depth d is mapped to a term at depth d in context Γ


-- Identity substitution:

idSubst : ∀ {Σ : Signature} {Γ : Arity} → Subst Σ Γ Γ
idSubst {Σ} d x = var x


-- Action of a substitution on a term 

module _ {Σ : Signature} where

  sub     : {Γ Δ : Arity}   {d : ℕ} → Subst Σ Γ Δ → Term Σ Δ d   → Term Σ Γ d
  subArgs : {Γ Δ Ψ : Arity} {p : ℕ} → Subst Σ Γ Δ → Args Σ Δ p Ψ → Args Σ Γ p Ψ

  sub σ (var x) = σ _ x
  sub σ (next t) = next (sub σ t)
  sub {Γ} {Δ} σ (app f p x) = app f p (subArgs {Γ = Γ} {Δ = Δ} {Ψ = ar Σ f} σ x)
  --  subArgs σ x : Args Σ Γ p (ar Σ f)

  subArgs σ args i j = sub σ (args i j)


-- Composition of substitutions:

module _ {Σ : Signature} {Γ Δ Ψ} where

  _∘Sub_ : Subst Σ Δ Ψ → Subst Σ Γ Δ → Subst Σ Γ Ψ
  (σ ∘Sub τ) d x = sub τ (σ d x)


-- TODO: unit and associativity laws for substitution
