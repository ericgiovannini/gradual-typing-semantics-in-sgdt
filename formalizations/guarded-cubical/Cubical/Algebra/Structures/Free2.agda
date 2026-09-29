{-# OPTIONS --polarity #-}

module Cubical.Algebra.Structures.Free2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Bool as Bool hiding (elim)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥ hiding (elim)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Structures.Base
open import Cubical.Algebra.Structures.Morphism
open import Cubical.Algebra.Structures.Displayed
open import Cubical.Algebra.Structures.AlgebraicTheory

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓᴰ ℓᴰ' : Level
    ℓM ℓN ℓP : Level
    ℓMᴰ ℓNᴰ ℓPᴰ : Level
    ℓA ℓB : Level


module _ {ℓX ℓar : Level} (σ : Sig ℓX ℓar) where

  open Signature

  module _ {ℓ : Level} (A : Type ℓ) where

    -- Terms form a PreStructure.
    Term-As-Prestructure : PreStructure σ (ℓ-max (ℓ-max ℓX ℓar) ℓ)
    Term-As-Prestructure .fst = Term σ A
    Term-As-Prestructure .snd .PreStructureStr.op = oper
    Term-As-Prestructure .snd .PreStructureStr.is-set = {!!}

    -- Universal property


module _ {ℓX ℓar ℓE ℓq : Level}
  (T : AlgTheory ℓX ℓar ℓE ℓq)
  where

  open AlgTheory T
  open Signature
  open Sig σ


  -- The free structure on a set A, i.e., the left adjoint to the
  -- forgetful functor from the category of structures to sets.
  module _ {ℓ : Level} (A : Type ℓ) where

    data |Free| : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) ℓ)
    Free-P : PreStructureStr σ |Free|
    Free : Structure σ eqns (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) ℓ)

    Term→Free : Term σ A → |Free|

    data |Free| where

      -- generator
      ⟦_⟧ : A → |Free|

      -- operations
      opFree : (x : X) → (ar x → |Free|) → |Free|

      -- equations
      -- eqFree : (e : eqns.E)
      --    → (gamma : eqns.q e → |Free|)
      --    → interp σ (eqns.q e) |Free| Free-P gamma (eqns.lhs e) ≡
      --      interp σ (eqns.q e) |Free| Free-P gamma (eqns.rhs e)
      eqFree : (e : eqns.E)
        → (gamma : eqns.q e → Term σ A)
        → Term→Free (interp σ (eqns.q e) (Term σ A) (Term-As-Prestructure σ A .snd) gamma (eqns.lhs e)) ≡
          Term→Free (interp σ (eqns.q e) (Term σ A) (Term-As-Prestructure σ A .snd) gamma (eqns.rhs e))

      -- isSet
      trunc : isSet |Free|


    Free-P .PreStructureStr.op = opFree
    Free-P .PreStructureStr.is-set = trunc

    Free .fst = |Free|
    Free .snd .StructureStr.s = Free-P
    Free .snd .StructureStr.eqns-hold = {!!} -- eqFree
      where
        lemma : (e : eqns.E) → interp-eqn σ Free-P (eqns.q e) (eqns.eqn e)
        lemma e gamma = {!!}

    
    Term→Free (var y) = ⟦ y ⟧
    Term→Free (oper x vars) = opFree x (λ z → Term→Free (vars z))

    lem : ∀ (t : Term σ A) (gamma : A → |Free|) →
      Σ[ gamma' ∈ (A → Term σ A) ]
        interp σ A |Free| Free-P gamma t ≡
        Term→Free (interp σ A (Term σ A) (Term-As-Prestructure σ A .snd) gamma' t)
    lem (var y) gamma with gamma y
    ... | ⟦ a ⟧ = (λ x → var a) , refl
    ... | opFree x vars = (λ _ → oper x {!!}) , {!!}
    ... | eqFree e gamma₁ i = {!!} , {!!}
    ... | trunc x y p q i j = {!!}
    lem (oper x vars) gamma = {!!} , {!!}
