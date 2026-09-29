{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --polarity #-}

module Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Equations.Positive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Data.Sigma

open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Signature
open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Term


private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓY ℓar ℓX' ℓar' : Level


module _ (σ : Sig ℓX ℓar)  where

  open Sig σ


  -- We specify a collection of equations over terms with variables in
  -- Y via (1) an indexing type E, (2) for each e : E, an arity `q e`,
  -- and (3) for each e : E and function (Γ : q e → Term Y), a pair
  -- Term Y × Term Y.
  record Eqns {ℓ : Level} (Y : Type ℓ) (ℓE ℓq : Level)
    : Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max (ℓ-max (ℓ-suc ℓE) (ℓ-suc ℓq)) ℓ)) where
    field
      E : Type ℓE
      q : (e : E) → Type ℓq
      eqn : (e : E) → (q e → Term σ Y) → Term σ Y × Term σ Y

    lhs rhs : (e : E) → (q e → Term σ Y) → Term σ Y
    lhs e Γ = fst (eqn e Γ)
    rhs e Γ = snd (eqn e Γ)


  -- We specify a collection of equations via an indexing type E, and
  -- for each e : E, and arity `q e` along with a pair of terms over
  -- variables `q e`.
  record Eqns' (ℓE ℓq : Level)
    : Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max (ℓ-suc ℓE) (ℓ-suc ℓq))) where
    field
      E : Type ℓE
      q : (e : E) → Type ℓq
      eqn : (e : E) → Term σ (q e) × Term σ (q e)

    lhs rhs : (e : E) → Term σ (q e)
    lhs e = fst (eqn e)
    rhs e = snd (eqn e)


{-
  record Eqns'' {ℓ : Level} (Y : Type ℓ) (ℓE : Level)
    : Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max (ℓ-suc ℓE) ℓ)) where
    field
      E : Type ℓE
      eqn : (e : E) → Term σ Y × Term σ Y

    lhs rhs : (e : E) → Term σ Y
    lhs e = fst (eqn e)
    rhs e = snd (eqn e)
-}
