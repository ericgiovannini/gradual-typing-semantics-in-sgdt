{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --polarity #-}

module Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Theory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Binary

open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Signature
open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Term
open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Equations.Positive as PosEq
open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Equations.Negative as NegEq


private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓY ℓar ℓX' ℓar' : Level


EqnsSP : {ℓX ℓar : Level} → (σ : Sig ℓX ℓar) (ℓE ℓq : Level) → Typeω
EqnsSP σ ℓE ℓq =
  ∀ {ℓY : Level} {@++ Y : Type ℓY} → PosEq.Eqns σ Y ℓE ℓq

NEqnsSP : {ℓX ℓar : Level} → (σ : Sig ℓX ℓar) (ℓR : Level) → Typeω
NEqnsSP σ ℓR =
  ∀ {ℓY : Level} {@++ Y : Type ℓY} → NegEq.Equations σ Y ℓR
  

record AlgTheory (ℓX ℓar ℓE ℓq : Level) : Typeω where
  field
    σ : Sig ℓX ℓar
    eqns : ∀ {ℓY : Level} {Y : Type ℓY} → Eqns σ Y ℓE ℓq



record AlgTheory' (ℓX ℓar ℓE ℓq ℓY : Level)
  : Type (ℓ-max (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓar)) (ℓ-max (ℓ-max (ℓ-suc ℓE) (ℓ-suc ℓq)) (ℓ-suc ℓY))) where
  field
    σ : Sig ℓX ℓar   
    eqns : ∀ {Y : Type ℓY} → Eqns σ Y ℓE ℓq

  module σ = Sig σ



