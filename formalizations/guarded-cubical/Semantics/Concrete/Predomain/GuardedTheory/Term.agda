{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.Predomain.GuardedTheory.Term where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Sum

open import Semantics.Concrete.Predomain.GuardedTheory.Arity
open import Semantics.Concrete.Predomain.GuardedTheory.Signature

open Signature


-- If there are `n_d` variables at depth d, then Var Γ d = Fin n_d
Var : Arity → ℕ → Type
Var Γ d = Fin (lookup Γ d)


-- Terms are defined in Signature Σ and arity context Γ, at output depth d
data Term (Σ : Signature) (Γ : Arity) : ℕ → Type

-- They are defined mutually with the type of recursive Args that can
-- be shifted by any natural number index
Args : Signature → Arity → ℕ → Arity → Type


data Term Σ Γ where

  var : ∀ {d : ℕ} → Var Γ d → Term Σ Γ d

  next : ∀ {d : ℕ} → Term Σ Γ d → Term Σ Γ (suc d)

  -- builds in the shift by p:
  app : ∀ (o : Op Σ) (p : ℕ) → Args Σ Γ p (ar Σ o) → Term Σ Γ p


Args Σ Γ p Δ = (i : ℕ) (j : Var Δ i) → Term Σ Γ (p + i)
-- Could we simplify this to remove the (i : ℕ) parameter?

-- Subst Σ Γ Δ = (d : ℕ) → Var Δ d → Term Σ Γ d


module _
  {Σ₁ Σ₂ : Signature}
  where

  inl-tm : {Γ : Arity} {d : ℕ}
    → (t : Term Σ₁ Γ d)
    → Term (Σ₁ +Sig Σ₂) Γ d

  inl-args : {Γ : Arity} {p : ℕ} {Δ : Arity}
    → (a : Args Σ₁ Γ p Δ)
    → Args (Σ₁ +Sig Σ₂) Γ p Δ
  

  inl-tm (var x) = var x
  inl-tm (next t) = next (inl-tm t)
  inl-tm (app o p args) = app (inl o) p (inl-args {Δ = ar Σ₁ o} args)

  inl-args a i j = inl-tm (a i j)

  --------------------------------------------------------------------
  inr-tm : {Γ : Arity} {d : ℕ}
    → (t : Term Σ₂ Γ d)
    → Term (Σ₁ +Sig Σ₂) Γ d

  inr-args : {Γ : Arity} {p : ℕ} {Δ : Arity}
    → (a : Args Σ₂ Γ p Δ)
    → Args (Σ₁ +Sig Σ₂) Γ p Δ

  inr-tm (var x) = var x
  inr-tm (next t) = next (inr-tm t)
  inr-tm (app o p args) = app (inr o) p (inr-args {Δ = ar Σ₂ o} args)

  inr-args a i j = inr-tm (a i j)
