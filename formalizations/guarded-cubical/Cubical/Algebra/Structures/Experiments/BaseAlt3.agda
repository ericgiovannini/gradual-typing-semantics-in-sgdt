{-# OPTIONS --polarity #-}

{-

Formalization of algebraic structures as an hSet A equipped with a
type-indexed collection of operations and equations.

-}


module Cubical.Algebra.Structures.Experiments.BaseAlt3 where

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




module Struct {ℓX ℓar : Level}
  (X : Type ℓX) (ar : X → Type ℓar)
  where

  -- For x : X, the operation corresponding to x has arity ar x.
  -- E.g., for a semigroup, X = Unit, and ar tt = Bool.
  -- Then the operation has type (A × A) → A, i.e., (Bool → A) → A.

  record PreStructureStr (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-max ℓX ℓar)) where
    field
      op : (x : X) → (ar x → A) → A
      is-set : isSet A

  PreStructure : ∀ ℓ → Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-suc ℓ))
  PreStructure ℓ = TypeWithStr ℓ PreStructureStr

  OpData : {ℓ : Level} → (A : Type ℓ) → Type (ℓ-max (ℓ-max ℓX ℓar) ℓ)
  OpData A = (x : X) → (ar x → A) → A

  Expr : {ℓE ℓq : Level}
    → (E : Type ℓE)
    → (q : E → Type ℓq)
    → Typeω
  Expr E q = {ℓ : Level}
      → (@++ A : Type ℓ)
      → OpData A
      → (e : E)
      → ((q e) → A)
      → A

  record EqnData : Typeω where
    field
      ℓE ℓq : Level
      E : Type ℓE
      q : E → Type ℓq
      lhs rhs : Expr E q
      

  module Eqns {ℓE ℓq : Level}
    (E : Type ℓE)
    (q : E → Type ℓq)
    (lhs rhs : Expr E q)
    where

    record StructureStr' : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓE ℓq))) where
      field
        s : PreStructure ℓ
        eqn : (e : E) → (vars : (q e) → ⟨ s ⟩) →
          lhs (s .fst) (s .snd .PreStructureStr.op) e vars ≡ rhs (s .fst) (s .snd .PreStructureStr.op) e vars


    record StructureStr (A : Type ℓ) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓE ℓq))) where
      field
        s : PreStructureStr A
        eqn : (e : E) → (vars : (q e) → A)
          → lhs A (s .PreStructureStr.op) e vars ≡ rhs A (s .PreStructureStr.op) e vars

      open PreStructureStr s public

    Structure : ∀ ℓ → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) (ℓ-suc ℓ))
    Structure ℓ = TypeWithStr ℓ StructureStr


    module _ (A : Structure ℓ) (A' : Structure ℓ') where

      private
        module A  = StructureStr (A  .snd)
        module A' = StructureStr (A' .snd)

      record StructureMorphism : Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓ ℓ')) where
        field
          f : ⟨ A ⟩ → ⟨ A' ⟩
          is-hom : ∀ x (vars : (ar x) → ⟨ A ⟩)
            → f (A.op x vars) ≡ A'.op x (f ∘ vars)

    
    -- The free structure on a set A, i.e., the left adjoint to the forgetful functor
    -- from the category of structures to sets
    module Free {ℓ : Level} (A : Type ℓ) where

      data |Free| : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) ℓ)
      Free-P : PreStructureStr |Free|
      Free : Structure (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) ℓ)

      data |Free| where
      
        -- generator
        ⟦_⟧ : A → |Free|

        -- operations
        opFree : (x : X) → (ar x → |Free|) → |Free|

        -- equations
        eqFree : (e : E) → (vars : (q e) → |Free|)
          → lhs |Free| opFree e vars ≡ rhs |Free| opFree e vars

        -- isSet
        trunc : isSet |Free|


      Free-P .PreStructureStr.op = opFree
      Free-P .PreStructureStr.is-set = trunc

      Free .fst = |Free|
      Free .snd .StructureStr.s = Free-P
      Free .snd .StructureStr.eqn = eqFree



-- Example: Semigroups

module Semigroup where

  -- A semigroup has one kind of operation
  X : Type
  X = Unit

  -- The operation takes 2 arguments
  ar : X → Type
  ar tt = Bool

  open Struct X ar

  module Notation (@++ A : Type ℓ) (op : (x : X) → (ar x → A) → A)  where

    _·_ : A → A → A
    x · y = op tt aux
      where
        aux : Bool → A
        aux true = x
        aux false = y
        -- aux b = if b then x else y
        -- aux = (Bool.elim {A = λ _ → A} x y)


  -- There is one equation (associativity)
  E : Type
  E = Unit

  data Three : Type where
    one two three : Three

  q : E → Type
  q tt = Three

  lhs : (@++ A : Type ℓ) → ((x : X) → (ar x → A) → A) → (e : E) → (q e → A) → A
  lhs A op tt f = f one · (f two · f three)
    where open Notation A op

  rhs : (@++ A : Type ℓ) → ((x : X) → (ar x → A) → A) → (e : E) → (q e → A) → A
  rhs A op tt f = (f one · f two) · f three
    where open Notation A op

  open Eqns E q lhs rhs

  Semigroup : ∀ ℓ → Type (ℓ-suc ℓ)
  Semigroup = Structure


