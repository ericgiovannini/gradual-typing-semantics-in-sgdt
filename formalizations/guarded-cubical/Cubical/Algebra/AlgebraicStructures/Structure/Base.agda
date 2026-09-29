{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --polarity #-}

module Cubical.Algebra.AlgebraicStructures.Structure.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Relation.Binary

open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Signature
open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Term
open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Equations.Positive as PosEqn
open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Equations.Negative as NegEqn
open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Theory
open import Cubical.Algebra.AlgebraicStructures.PreStructure

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓar ℓE ℓq : Level
    ℓY : Level
    ℓR : Level
    ℓA ℓB : Level


module _ (σ : Sig ℓX ℓar) (eqns : NEqnsSP σ ℓR) where

  open Sig σ

  record StructureStr (A : Type ℓ)
    : Type (ℓ-max ℓX (ℓ-max ℓar (ℓ-max ℓR ℓ))) where
    field
      s : PreStructureStr σ A
      eqns-hold : interp-neg-eqns σ s ℓR (eqns {Y = A})

    open PreStructureStr s public


  Structure : ∀ ℓ → Type (ℓ-max ℓX (ℓ-max ℓar (ℓ-max ℓR (ℓ-suc ℓ))))
  Structure ℓ = TypeWithStr ℓ StructureStr


  -- The free structure on a set A, i.e., the left adjoint to the
  -- forgetful functor from the category of structures to sets.
  module _ {ℓ : Level} (A : Type ℓ) where

    data |Free| : Type (ℓ-max ℓX (ℓ-max ℓar (ℓ-max ℓR ℓ)))
    Free-P : PreStructureStr σ |Free|
    Free : Structure (ℓ-max ℓX (ℓ-max ℓar (ℓ-max ℓR ℓ)))

    data |Free| where

      -- generator
      ⟦_⟧ : A → |Free|

      -- operations
      opFree : (x : X) → (ar x → |Free|) → |Free|

      -- equations
      eqFree :
        ∀ (lhs rhs : Term σ |Free|)
        → eqns {Y = |Free|} lhs rhs
        → alg* σ |Free| Free-P lhs ≡
          alg* σ |Free| Free-P rhs

      -- isSet
      trunc : isSet |Free|


    Free-P .PreStructureStr.op = opFree
    Free-P .PreStructureStr.is-set = trunc

    Free .fst = |Free|
    Free .snd .StructureStr.s = Free-P
    Free .snd .StructureStr.eqns-hold = eqFree



  module _ (A : Type ℓA) (B : ⟨ Free A ⟩ → Type ℓB)
    (⟦_⟧* : (a : A) → B ⟦ a ⟧)
    (op* : {x : X} → {vars : ar x → |Free| A}
      → ((z : ar x) → B (vars z))
      → B (opFree x vars))
    (interp* : {ℓY : Level} {Y : Type ℓY}
        → (f : (Y → ⟨ Free A ⟩))
        → (fᴰ : (y : Y) → B (f y))
        → (t : Term σ Y)
        → B (interp σ Y ⟨ Free A ⟩ (Free-P A) f t))
    (trunc* : ∀ y → isSet (B y))
    where

    elim : (y : ⟨ Free A ⟩) → B y
    elim ⟦ a ⟧ = ⟦ a ⟧*
    elim (opFree x vars) = op* (λ z → elim (vars z))
    elim (eqFree lhs rhs eqs-hold i) = {!!}
      -- let H = eq* (λ z → elim (gamma z)) in
      -- (sym (lem lhs) ◁ H ▷ lem rhs) i
      where
        -- lem : ∀ t →
        --   interp* {Y = ?} gamma (λ z → elim (gamma z)) t ≡
        --   elim (interp σ (eqns.q e) ⟨ Free A ⟩ (Free-P A) gamma t)
        
    elim (trunc x y p q i j) = {!!}


{-
-- The definition of the free structure below does not pass the
-- positivity checker!

module Bad (σ : Sig ℓX ℓar) (eqns : EqnsSP σ ℓE ℓq) where

  open Sig σ

  record StructureStr (A : Type ℓ)
    : Type (ℓ-max ℓX (ℓ-max ℓar (ℓ-max (ℓ-max ℓE ℓq) ℓ))) where
    field
      s : PreStructureStr σ A
      eqns-hold : interp-eqns σ s (eqns {Y = A})

    open PreStructureStr s public


  Structure : ∀ ℓ → Type (ℓ-max ℓX (ℓ-max ℓar (ℓ-max (ℓ-max ℓE ℓq) (ℓ-suc ℓ))))
  Structure ℓ = TypeWithStr ℓ StructureStr


  -- The free structure on a set A, i.e., the left adjoint to the
  -- forgetful functor from the category of structures to sets.
  module _ {ℓ : Level} (A : Type ℓ) where

    data |Free| : Type (ℓ-max ℓX (ℓ-max ℓar (ℓ-max ℓE (ℓ-max ℓq ℓ))))
    Free-P : PreStructureStr σ |Free|
    Free : Structure (ℓ-max ℓX (ℓ-max ℓar (ℓ-max ℓE (ℓ-max ℓq ℓ))))

    data |Free| where

      -- generator
      ⟦_⟧ : A → |Free|

      -- operations
      opFree : (x : X) → (ar x → |Free|) → |Free|

      -- equations
      eqFree : -- interp-eqn σ Free-P ℓq eqns
        (e : Eqns.E (eqns {Y = |Free|}))
        (vars : Eqns.q (eqns {Y = |Free|}) e → Term σ |Free|)
        → alg* σ |Free| Free-P (Eqns.lhs (eqns {Y = |Free|}) e vars) ≡
          alg* σ |Free| Free-P (Eqns.rhs (eqns {Y = |Free|}) e vars)

      -- isSet
      trunc : isSet |Free|


    Free-P .PreStructureStr.op = opFree
    Free-P .PreStructureStr.is-set = trunc

    Free .fst = |Free|
    Free .snd .StructureStr.s = Free-P
    Free .snd .StructureStr.eqns-hold = eqFree
-}
  

{-
-- The definition of the free structure below does not pass the
-- positivity checker!

module Bad2 (T : AlgTheory ℓX ℓar ℓE ℓq) where

  open AlgTheory T
  open Sig σ

  record StructureStr (A : Type ℓ)
    : Type (ℓ-max ℓX (ℓ-max ℓar (ℓ-max (ℓ-max ℓE ℓq) ℓ))) where
    field
      s : PreStructureStr σ A
      eqns-hold : interp-eqns σ s (eqns {Y = A})

    open PreStructureStr s public


  Structure : ∀ ℓ → Type (ℓ-max ℓX (ℓ-max ℓar (ℓ-max (ℓ-max ℓE ℓq) (ℓ-suc ℓ))))
  Structure ℓ = TypeWithStr ℓ StructureStr


  -- The free structure on a set A, i.e., the left adjoint to the
  -- forgetful functor from the category of structures to sets.
  module _ {ℓ : Level} (A : Type ℓ) where

    data |Free| : Type (ℓ-max ℓX (ℓ-max ℓar (ℓ-max ℓE (ℓ-max ℓq ℓ))))
    Free-P : PreStructureStr σ |Free|
    Free : Structure (ℓ-max ℓX (ℓ-max ℓar (ℓ-max ℓE (ℓ-max ℓq ℓ))))

    data |Free| where

      -- generator
      ⟦_⟧ : A → |Free|

      -- operations
      opFree : (x : X) → (ar x → |Free|) → |Free|

      -- equations
      eqFree : -- interp-eqn σ Free-P ℓq eqns
        (e : Eqns.E (eqns {Y = |Free|}))
        (vars : Eqns.q (eqns {Y = |Free|}) e → Term σ |Free|)
        → alg* σ |Free| Free-P (Eqns.lhs (eqns {Y = |Free|}) e vars) ≡
          alg* σ |Free| Free-P (Eqns.rhs (eqns {Y = |Free|}) e vars)

      -- isSet
      trunc : isSet |Free|


    Free-P .PreStructureStr.op = opFree
    Free-P .PreStructureStr.is-set = trunc

    Free .fst = |Free|
    Free .snd .StructureStr.s = Free-P
    Free .snd .StructureStr.eqns-hold = eqFree

-}
