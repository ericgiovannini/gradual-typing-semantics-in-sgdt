{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.Predomain.GuardedTheory.Theory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.FinData

open import Semantics.Concrete.Predomain.GuardedTheory.Arity
open import Semantics.Concrete.Predomain.GuardedTheory.Signature
open import Semantics.Concrete.Predomain.GuardedTheory.Term
open import Semantics.Concrete.Predomain.GuardedTheory.Substitution
open import Semantics.Concrete.Predomain.GuardedTheory.Shift


record Equation (Σ : Signature) : Type where
  field
    ctx : Arity
    depth : ℕ
    lhs : Term Σ ctx depth
    rhs : Term Σ ctx depth


record GuardedTheory : Type₁ where
  field
    sig : Signature        -- The operations of the theory
    E   : Type             -- The indexing type of equations
    eqn : E → Equation sig -- The equations themselves

  open Signature sig public
  module Eqn (e : E) where
    open Equation (eqn e) public


module _ {Σ₁ Σ₂ : Signature} where
  open Equation

  module _ (eq : Equation Σ₁) where

    private module eq = Equation eq

    inl-eq : Equation (Σ₁ +Sig Σ₂)
    inl-eq .ctx = eq.ctx
    inl-eq .depth = eq.depth
    inl-eq .lhs = inl-tm eq.lhs
    inl-eq .rhs = inl-tm eq.rhs

  module _ (eq : Equation Σ₂) where

    private module eq = Equation eq

    inr-eq : Equation (Σ₁ +Sig Σ₂)
    inr-eq .ctx = eq.ctx
    inr-eq .depth = eq.depth
    inr-eq .lhs = inr-tm eq.lhs
    inr-eq .rhs = inr-tm eq.rhs
