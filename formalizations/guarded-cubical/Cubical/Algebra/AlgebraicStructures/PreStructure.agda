{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --polarity #-}

module Cubical.Algebra.AlgebraicStructures.PreStructure where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Relation.Binary

open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Signature
open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Term
open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Equations.Positive as PosEqn
open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Equations.Negative as NegEqn
open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Theory


private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓar ℓE ℓq : Level
    ℓY : Level


module _
  (σ : Sig ℓX ℓar)
  where

  open Sig σ

  record PreStructureStr (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-max ℓX ℓar)) where
    field
      op : (x : X) → (ar x → A) → A
      is-set : isSet A

  PreStructure : ∀ ℓ → Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-suc ℓ))
  PreStructure ℓ = TypeWithStr ℓ PreStructureStr


  module _ {ℓY : Level} (Y : Type ℓY) where

    -- Interpreting a term AST (with variables in Y) into a
    -- PreStructure. For technical reasons (related to the positivity
    -- checker when defining the free structure), we separate the
    -- module parameters into a type A and a PreStructureStr on A.
    module _ {ℓ : Level} (A : Type ℓ) (s : PreStructureStr A) where
      private module s = PreStructureStr s
    
      interp : (Y → A) → Term σ Y → A
      interp f (var y) = f y
      interp f (oper x vars) = s.op x (λ z → interp f (vars z))

      -- or equivalently: interp f = recTerm σ Y f s.op


  -- Given a PreStructure on a set A, and a Term t with variables in
  -- A, we can interpret t as an element of A:
  module _ (A : Type ℓ) (s : PreStructureStr A) where

    alg* : Term σ A → A
    alg* = interp A A s (λ x → x)


  -- Given a PreStructure on a set A, and a collection of
  -- (negatively-described) equations on Term A, we can interpret
  -- those equations in A:
  module _
    {A : Type ℓ} (s : PreStructureStr A) where

    interp-neg-eqns : (ℓq : Level)
      → Equations σ A ℓq
      → Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓ) ℓq)
    interp-neg-eqns ℓq eqns = ∀ (lhs rhs : Term σ A)
      → eqns lhs rhs
      → interp A A s (λ x → x) lhs ≡ interp A A s (λ x → x) rhs


    -- Given a collection of positively-described equations on Term A,
    -- we can similarly interpret those equations in A:
    interp-eqns : {ℓE ℓq : Level}
      → Eqns σ A ℓE ℓq
      → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓ) ℓE) ℓq)
    interp-eqns eqns = (e : E)
      → (vars : q e → Term σ A)
      → alg* A s (lhs e vars) ≡ alg* A s (rhs e vars)
      where open Eqns eqns
  
