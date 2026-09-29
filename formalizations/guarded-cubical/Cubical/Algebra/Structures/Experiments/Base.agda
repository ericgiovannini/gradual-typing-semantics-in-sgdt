{-# OPTIONS --polarity #-}

{-

Formalization of algebraic structures as an hSet A equipped with a
type-indexed collection of operations and equations.

-}


module Cubical.Algebra.Structures.Experiments.Base where

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
open import Cubical.Data.Sigma

open import Agda.Primitive

private
  variable
    ℓ ℓ' ℓ'' : Level


  variable
    S : Type ℓ → Type ℓ'


record Σ' {a b} (@++ A : Set a) (@++ B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst' : A
    snd' : B fst'

open Σ' public

infixr 4 _,_

-- Σ-types
infix 2 Σ'-syntax

Σ'-syntax : ∀ {ℓ ℓ'} (@++ A : Type ℓ) (@++ B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Σ'-syntax = Σ'

syntax Σ'-syntax A (λ x → B) = Σ'[ x ∈ A ] B


TypeWithStr' : (ℓ : Level) (S : Type ℓ → Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
TypeWithStr' ℓ S = Σ'[ X ∈ Type ℓ ] S X

typ' : TypeWithStr' ℓ S → Type ℓ
typ' = fst'

str' : (A : TypeWithStr' ℓ S) → S (typ' A)
str' = snd'

-- Alternative notation for typ
⟨_⟩' : TypeWithStr ℓ S → Type ℓ
⟨_⟩' = typ

{-
module _
  (A : Type ℓ) where

  record Structure {ℓX ℓar ℓE : Level} :
    Type (ℓ-max (ℓ-max ℓ (ℓ-suc ℓE)) (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓar))) where
    field
      is-set : isSet A
      X : Type ℓX
      ar : X → Type ℓar
      op : (x : X) → ar x → A

      E : Type ℓE
      lhs : E → A
      rhs : E → A
      eqn : (e : E) → lhs e ≡ rhs e
-}




{-
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

  module Eqns {ℓE ℓq : Level}
    (E : Type ℓE)
    (q : E → Type ℓq)
    (lhs : {ℓ : Level} → (A : PreStructure ℓ) → (e : E) → ((q e) → ⟨ A ⟩) → ⟨ A ⟩)
    (rhs : {ℓ : Level} → (A : PreStructure ℓ) → (e : E) → ((q e) → ⟨ A ⟩) → ⟨ A ⟩)
    where

    record StructureStr' : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓE ℓq))) where
      field
        s : PreStructure ℓ
        eqn : (e : E) → (vars : (q e) → ⟨ s ⟩) → lhs s e vars ≡ rhs s e vars


    record StructureStr (A : Type ℓ) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓE ℓq))) where
      field
        s : PreStructureStr A
        eqn : (e : E) → (vars : (q e) → A) → lhs (A , s) e vars ≡ rhs (A , s) e vars

    Structure : ∀ ℓ → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) (ℓ-suc ℓ))
    Structure ℓ = TypeWithStr ℓ StructureStr


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
          → lhs (|Free| , Free-P) e vars ≡ rhs (|Free| , Free-P) e vars

        -- isSet
        trunc : isSet |Free|


      Free-P .PreStructureStr.op = opFree
      Free-P .PreStructureStr.isStructure .IsPreStructure.is-set = trunc
      

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
  
  PreSemigroup : ∀ ℓ → Type (ℓ-suc ℓ)
  PreSemigroup ℓ = PreStructure ℓ

  module Notation (M : PreSemigroup ℓ) where

    _·_ : ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
    x · y = M .snd .PreStructureStr.op tt (Bool.elim x y)


  -- There is one equation (associativity)
  E : Type
  E = Unit

  data Three : Type where
    one two three : Three

  q : E → Type
  q tt = Three

  lhs : (s : PreSemigroup ℓ) → (e : E) → (q e → ⟨ s ⟩) → ⟨ s ⟩
  lhs s tt f = f one · (f two · f three)
    where open Notation s

  rhs : (s : PreSemigroup ℓ) → (e : E) → (q e → ⟨ s ⟩) → ⟨ s ⟩
  rhs s tt f = (f one · f two) · f three
    where open Notation s

  open Eqns E q lhs rhs

  Semigroup : ∀ ℓ → Type (ℓ-suc ℓ)
  Semigroup = Structure


-}


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

  module Eqns {ℓE ℓq : Level}
    (E : Type ℓE)
    (q : E → Type ℓq)
    (lhs : {ℓ : Level} → (@++ A : Type ℓ)
      → ((x : X) → (ar x → A) → A)
      → (e : E)
      → ((q e) → A)
      → A)
    (rhs : {ℓ : Level} → (@++ A : Type ℓ)
      → ((x : X) → (ar x → A) → A)
      → (e : E)
      → ((q e) → A)
      → A)
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

    Structure : ∀ ℓ → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) (ℓ-suc ℓ))
    Structure ℓ = TypeWithStr ℓ StructureStr


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
      Free-P .PreStructureStr.isStructure .IsPreStructure.is-set = trunc
      

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



