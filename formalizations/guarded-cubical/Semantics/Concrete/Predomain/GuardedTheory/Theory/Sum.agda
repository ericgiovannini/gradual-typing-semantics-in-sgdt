{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.Predomain.GuardedTheory.Theory.Sum where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum

open import Semantics.Concrete.Predomain.GuardedTheory.Arity
open import Semantics.Concrete.Predomain.GuardedTheory.Signature
open import Semantics.Concrete.Predomain.GuardedTheory.Term
open import Semantics.Concrete.Predomain.GuardedTheory.Substitution
open import Semantics.Concrete.Predomain.GuardedTheory.Shift

open import Semantics.Concrete.Predomain.GuardedTheory.Theory.Base

module _
  (T₁ : GuardedTheory)
  (T₂ : GuardedTheory) where

  open GuardedTheory

  private
    module T₁ = GuardedTheory T₁
    module T₂ = GuardedTheory T₂
  
  _+Thy_ : GuardedTheory

  -- The operations are those of T₁ and T₂.
  _+Thy_ .sig = T₁.sig +Sig T₂.sig

  -- The equations are those of T₁ and T₂, with no additional equations.
  _+Thy_ .E = T₁.E ⊎ T₂.E
  _+Thy_ .eqn (inl e)  = inl-eq (T₁.eqn e)
  _+Thy_ .eqn (inr e') = inr-eq (T₂.eqn e')
