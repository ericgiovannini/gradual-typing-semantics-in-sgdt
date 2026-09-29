{-# OPTIONS --polarity #-}

{-

Formalization of algebraic structures as an hSet A equipped with a
type-indexed collection of operations and equations.

-}


module Cubical.Algebra.Structures.Experiments.Term where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Function
-- open import Cubical.Foundations.Structure

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet

open import Agda.Primitive

private
  variable
    ℓ ℓ' ℓ'' : Level

  variable
    S : Type ℓ → Type ℓ'


module Term {ℓX ℓar : Level}
  (X : Type ℓX) (ar : X → Type ℓar)
  where

  record PreStructureStr (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-max ℓX ℓar)) where
    field
      op : (x : X) → (ar x → A) → A
      is-set : isSet A

  PreStructure : ∀ ℓ → Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-suc ℓ))
  PreStructure ℓ = TypeWithStr ℓ PreStructureStr


  module _ {ℓY : Level} (Y : Type ℓY) where

    data Term : Type (ℓ-max ℓY (ℓ-max ℓX ℓar)) where
      var : Y → Term
      oper : (x : X) (vars : ar x → Term) → Term


    record Eqns (ℓE : Level)
      : Type (ℓ-max (ℓ-max (ℓ-suc ℓE) ℓY) (ℓ-max ℓX ℓar)) where
      field
        E : Type ℓE
        eqn : (e : E) → Term × Term

      lhs rhs : (e : E) → Term
      lhs e = fst (eqn e)
      rhs e = snd (eqn e)


    module _ {ℓ : Level} (A : Type ℓ) (s : PreStructureStr A) where
      private module s = PreStructureStr s
    
      interp : (Y → A) → Term → A
      interp f (var x) = f x
      interp f (oper x vars) = s.op x (λ z → interp f (vars z))
        

  module _ (ℓE : Level) (eqns : Eqns ⊥ ℓE) where
    private module eqns = Eqns eqns
    
    record StructureStr (A : Type ℓ) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-max ℓX ℓar) ℓE)) where
      field
        s : PreStructureStr A
        eqn : ∀ (e : eqns.E) →
          interp ⊥ A s ⊥.rec (eqns.lhs e) ≡ interp ⊥ A s ⊥.rec (eqns.rhs e)

      open PreStructureStr s public


    Structure : ∀ ℓ → Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) (ℓ-suc ℓ))
    Structure ℓ = TypeWithStr ℓ StructureStr


{-
  module _ {ℓ ℓY : Level} (s : PreStructure ℓ) where
    private module s = PreStructureStr (s .snd)
    
    interp' : Term ⊥ → ⟨ s ⟩
    interp' (oper x vars) = s.op x (λ z → interp' (vars z))
-}


    module _ (A : Structure ℓ) (A' : Structure ℓ') where

      private
        module A  = StructureStr (A  .snd)
        module A' = StructureStr (A' .snd)

      record StructureMorphism : Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓ ℓ')) where
        field
          f : ⟨ A ⟩ → ⟨ A' ⟩
          is-hom : ∀ x (vars : (ar x) → ⟨ A ⟩)
            → f (A.op x vars) ≡ A'.op x (f ∘ vars)

    
    -- The free structure on a set A, i.e., the left adjoint to the
    -- forgetful functor from the category of structures to sets.
    module Free {ℓ : Level} (A : Type ℓ) where

      data |Free| : Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓ)
      Free-P : PreStructureStr |Free|
      Free : Structure (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓ)

      data |Free| where
      
        -- generator
        ⟦_⟧ : A → |Free|

        -- operations
        opFree : (x : X) → (ar x → |Free|) → |Free|

        -- equations
        eqFree : (e : eqns.E) →
          interp ⊥ |Free| Free-P ⊥.rec (eqns.lhs e) ≡
          interp ⊥ |Free| Free-P ⊥.rec (eqns.rhs e) 

        -- isSet
        trunc : isSet |Free|


      Free-P .PreStructureStr.op = opFree
      Free-P .PreStructureStr.is-set = trunc

      Free .fst = |Free|
      Free .snd .StructureStr.s = Free-P
      Free .snd .StructureStr.eqn = eqFree


