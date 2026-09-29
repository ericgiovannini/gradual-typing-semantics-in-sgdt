{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --polarity #-}

module Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Equations.Negative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥


open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Signature
open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Term


private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓY ℓar ℓX' ℓar' : Level
    ℓR : Level


module _ (σ : Sig ℓX ℓar)  where

  open Sig σ


  -- We specify a collection of equations over terms with variables in
  -- Y as a binary relation on Term Y.
  Equations : (Y : Type ℓY) (ℓR : Level)
    → Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓY) (ℓ-suc ℓR))
  Equations Y ℓR = Rel (Term σ Y) (Term σ Y) ℓR


-- The coproduct of two sets of equations over different signatures.
module _ {ℓX ℓX' ℓar ℓar' : Level}
  (Σ₁ : Sig ℓX ℓar) (Σ₂ : Sig ℓX' ℓar')
  {ℓq ℓq' : Level}
  (Y : Type ℓY)
  (eqns  : Equations Σ₁ Y ℓq)
  (eqns' : Equations Σ₂ Y ℓq')
  where


  Equations-⊎ : Equations (Σ₁ ⊎Sig Σ₂) Y {!!}
  Equations-⊎ lhs rhs =
    (Σ[ H ∈ usesOnlyΣ₁ Σ₁ Σ₂ lhs ] Σ[ H' ∈ usesOnlyΣ₁ Σ₁ Σ₂ rhs ]
      eqns (Term-proj-inl _ _ lhs H) (Term-proj-inl _ _ rhs H'))
    ⊎ {!!}



-- The empty set of equations
module _ {ℓX ℓar : Level} (σ : Sig ℓX ℓar) (Y : Type ℓY) {ℓq : Level} where

  NoEqns : Equations σ Y ℓq
  NoEqns lhs rhs = ⊥*


-- Lifting equations over a signature Σ to be over a
-- coproduct of signatures Σ + Σ'.
module _ {ℓX ℓX' ℓar ℓar' : Level}
  (Σ₁ : Sig ℓX ℓar) (Σ₂ : Sig ℓX' ℓar')
  {ℓY : Level} {Y : Type ℓY}
  where

  Eqns-inl : 
      Equations Σ₁ Y ℓR
    → Equations (Σ₁ ⊎Sig Σ₂) Y (ℓ-max ℓar ℓR)
  Eqns-inl e lhs rhs =
      Σ[ H ∈ usesOnlyΣ₁ _ _ lhs ] Σ[ H' ∈ usesOnlyΣ₁ _ _ rhs ]
        e (Term-proj-inl _ _ lhs H) (Term-proj-inl _ _ rhs H')


-- Lifting equations over variables in Y to equations over
-- variables in Lift Y.
module _ {ℓX ℓar : Level}
  (Σ : Sig ℓX ℓar)
  where
  Eqn-Lift : {Y : Type ℓY} {j : Level}
    → Equations Σ Y ℓR
    → Equations Σ (Lift {j = j} Y) ℓR
  Eqn-Lift eqns lhs rhs = eqns (Term-Lower _ lhs) (Term-Lower _ rhs)
