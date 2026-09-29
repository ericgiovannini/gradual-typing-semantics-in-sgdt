{-# OPTIONS --polarity #-}


module Cubical.Algebra.Structures.Free where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP
-- open import Cubical.Foundations.Structure

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Fin


open import Cubical.Algebra.Structures.Base

private
  variable
    ℓ ℓ' ℓ'' : Level


module _
  {ℓX ℓar : Level}
  (X : Type ℓX)
  (ar : X → Type ℓar)
  where
    open Struct

    module _
      {ℓE ℓq : Level}
      (E : Type ℓE)
      (q : E → Type ℓq)
      (lhs : {ℓ : Level} → (@++ A : PreStructure X ar ℓ) → (e : E) → ((q e) → ⟨ A ⟩) → ⟨ A ⟩)
      (rhs : {ℓ : Level} → (@++ A : PreStructure X ar ℓ) → (e : E) → ((q e) → ⟨ A ⟩) → ⟨ A ⟩)
      where

      open Eqns X ar E q lhs rhs

      module _ {ℓ : Level} (A : Type ℓ) where

        data |Free| : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) ℓ)
        Free-P : PreStructureStr X ar |Free|
        Free : Structure (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) ℓ)

        data |Free| where
          -- generator
          ⟦_⟧ : A → |Free|

          -- operations
          opFree : (x : X) → (ar x → |Free|) → |Free|

          -- equations
          eqFree : (e : E) → (vars : (q e) → |Free|)
            → lhs (|Free| , Free-P) e vars ≡ rhs (|Free| , Free-P) e vars

          -- isSet
          trunc : isSet |Free|


        Free-P .PreStructureStr.op = opFree
        Free-P .PreStructureStr.isStructure .IsPreStructure.is-set = trunc

        Free .fst = |Free|
        Free .snd .StructureStr.s = Free-P
        Free .snd .StructureStr.eqn = eqFree
