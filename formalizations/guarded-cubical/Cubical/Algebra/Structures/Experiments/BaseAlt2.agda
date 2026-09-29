{-# OPTIONS --polarity #-}

{-

Formalization of algebraic structures as an hSet A equipped with a
type-indexed collection of operations and equations.

-}


module Cubical.Algebra.Structures.Experiments.BaseAlt2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Fin


private
  variable
    ℓ ℓ' ℓ'' : Level



module Struct {ℓX ℓar : Level}
  (X : Type ℓX)
  (ar : X → Type ℓar)
  where

  -- For x : X, the operation corresponding to x has arity ar x.
  -- E.g., for a semigroup, X = Unit, and ar tt = Bool.
  -- Then the operation has type (A × A) → A, i.e., (Bool → A) → A.

  record IsPreStructure {A : Type ℓ} (op : (x : X) → ((ar x) → A) → A)
    : Type (ℓ-max ℓ (ℓ-max ℓX ℓar)) where
    
    field
      is-set : isSet A

  record PreStructureStr (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-max ℓX ℓar)) where
    field
      op : (x : X) → (ar x → A) → A
      isStructure : IsPreStructure op

  PreStructure : ∀ ℓ → Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-suc ℓ))
  PreStructure ℓ = TypeWithStr ℓ PreStructureStr

  module Eqns {ℓ ℓE ℓq : Level} (A : Type ℓ)
    (s : PreStructureStr A)
    (E : Type ℓE)
    (q : E → Type ℓq)
    (lhs : (e : E) → ((q e) → A) → A)
    (rhs : (e : E) → ((q e) → A) → A)
    where

    record EqnStr : Type (ℓ-max ℓ (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓE ℓq))) where
      field
        eqn : (e : E) → (vars : (q e) → A) → lhs e vars ≡ rhs e vars

  module _ {ℓ ℓE ℓq : Level} (A : Type ℓ)
    (E : Type ℓE)
    (q : E → Type ℓq)
    (lhs : (e : E) → ((q e) → A) → A)
    (rhs : (e : E) → ((q e) → A) → A)
    where
    
    record StructureStr : Type ((ℓ-max ℓ (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓE ℓq)))) where
      field
        s : PreStructureStr A
        eq : Eqns.EqnStr A s E q lhs rhs

    Structure : ∀ ℓ → Type {!!}
    Structure ℓ = TypeWithStr ℓ {!!}
    


module Semigroup where

  -- A semigroup has one kind of operation
  X : Type
  X = Unit

  -- The operation takes 2 arguments
  ar : X → Type
  ar tt = Bool

  open Struct X ar
  
  PreSemigroup : ∀ ℓ → Type (ℓ-suc ℓ)
  PreSemigroup ℓ = PreStructure ℓ

  module _ (M : PreSemigroup ℓ) where

    _·_ : ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
    x · y = M .snd .PreStructureStr.op tt (Bool.elim x y)


    -- There is one equation (associativity)
    E : Type
    E = Unit

    data Three : Type where
      one two three : Three

    q : E → Type
    q tt = Three

    lhs : (e : E) → (q e → ⟨ M ⟩) → ⟨ M ⟩
    lhs tt f = f one · (f two · f three)

    rhs : (e : E) → (q e → ⟨ M ⟩) → ⟨ M ⟩
    rhs tt f = (f one · f two) · f three

    open Eqns ⟨ M ⟩ (M .snd) E q lhs rhs

