{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.Predomain.GuardedTheory.Theory.Tensor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum
open import Cubical.Data.Nat

open import Semantics.Concrete.Predomain.GuardedTheory.Arity
open import Semantics.Concrete.Predomain.GuardedTheory.Signature
open import Semantics.Concrete.Predomain.GuardedTheory.Term
open import Semantics.Concrete.Predomain.GuardedTheory.Substitution
open import Semantics.Concrete.Predomain.GuardedTheory.Shift

open import Semantics.Concrete.Predomain.GuardedTheory.Theory.Base

module _
  (T₁ : GuardedTheory)
  (T₂ : GuardedTheory) where

  open Equation
  open GuardedTheory

  private
    module T₁ = GuardedTheory T₁
    module T₂ = GuardedTheory T₂

  data Eqn' : Type where
    left     : T₁.E → Eqn'
    right    : T₂.E → Eqn'
    commutes : (o : T₁.Op) (o' : T₂.Op) → Eqn'


  -- Example for o₁ of arity 3 and o₂ of arity 2:
  --
  --   o₁ (o₂ (x₁₁ , x₁₂) , o₂ (x₂₁ , x₂₂) , o₂ (x₃₁ , x₃₂)) =
  --   o₂ (o₁ (x₁₁ , x₂₁ , x₃₁) , o₁ (x₁₂ , x₂₂ , x₃₂))

  -- o₁ ∈ Σ₁ of arity Γ commutes with o₂ ∈ Σ₂ of arity Δ
  mkCommEqn : (o₁ : T₁.Op) (o₂ : T₂.Op)
    → Equation (T₁.sig +Sig T₂.sig)
  mkCommEqn o₁ o₂ .ctx = {!!}
  mkCommEqn o₁ o₂ .depth = zero
  mkCommEqn o₁ o₂ .lhs = app (inl o₁) zero (λ i j → app (inr o₂) {!!} (λ i' j' → var {!!}))
  mkCommEqn o₁ o₂ .rhs = {!!}

  eqn' : Eqn' → Equation (T₁.sig +Sig T₂.sig)
  eqn' (left e)        = inl-eq (T₁.eqn e)
  eqn' (right e')      = inr-eq (T₂.eqn e')
  eqn' (commutes o o') = mkCommEqn o o'

  _⊗Thy_ : GuardedTheory

  -- The operations are those of T₁ and T₂.
  _⊗Thy_ .sig = T₁.sig +Sig T₂.sig

  -- The equations are those of T₁ and T₂, plus commutativity
  -- equations: each operation of T₁ commutes with each operation of
  -- T₂.
  _⊗Thy_ .E = Eqn'
  _⊗Thy_ .eqn = eqn'
  -- _⊗Thy_ .eqn (inl e)  = inl-eq (T₁.eqn e)
  -- _⊗Thy_ .eqn (inr e') = inr-eq (T₂.eqn e')
