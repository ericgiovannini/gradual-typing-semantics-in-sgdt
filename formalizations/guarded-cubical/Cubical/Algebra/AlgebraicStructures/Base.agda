{-# OPTIONS --polarity #-}

{-

Formalization of algebraic structures as an hSet A equipped with a
type-indexed collection of operations and equations.

-}


module Cubical.Algebra.AlgebraicStructures.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.Sum as Sum

open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory


private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓar ℓE ℓq : Level
    ℓY : Level
    ℓA ℓB : Level



module _ {ℓX ℓar : Level}
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


  -- Interpreting an equation in a PreStructure.
  module _
    {A : Type ℓ} (s : PreStructureStr A) where

    interp-eqn : (ℓq : Level)
      → Equations σ A ℓq
      → Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓ) ℓq)
    interp-eqn ℓq eqns = ∀ (lhs rhs : Term σ A)
      → eqns lhs rhs
      → interp A A s (λ x → x) lhs ≡ interp A A s (λ x → x) rhs 



-- Now, for a given collection of equations as defined above, we
-- define a Structure as a PreStructure `s` in which the equations
-- hold.
module _ (T : AlgTheory' ℓX ℓar ℓE ℓq) where

  open AlgTheory' T

  record StructureStr' (A : Type ℓE)
    : Type (ℓ-max ℓX (ℓ-max ℓar (ℓ-max (ℓ-suc ℓE) ℓq))) where
    field
      s : PreStructureStr σ A
      eqns-hold : interp-eqn σ s ℓq (eqns {Y = A})

       -- eqns-hold : ∀ (e : eqns.E)
       --  → (gamma : eqns.q e → A)
       --  → interp (eqns.q e) A s gamma (eqns.lhs e) ≡ interp (eqns.q e) A s gamma (eqns.rhs e)

    open PreStructureStr s public


  Structure' : Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) (ℓ-suc ℓE)) ℓq)
  Structure' = TypeWithStr ℓE StructureStr'


module _ (T : AlgTheory ℓX ℓar ℓq) where

  private
    σ = AlgTheory→Sig T
    eqns = AlgTheory→Eqns T

  open Sig σ

  record StructureStr (A : Type ℓ)
    : Type (ℓ-max ℓX (ℓ-max ℓar (ℓ-max ℓq ℓ))) where
    field
      s : PreStructureStr σ A
      eqns-hold : interp-eqn σ s ℓq (eqns {Y = A})

    open PreStructureStr s public


  Structure : ∀ ℓ → Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓq) (ℓ-suc ℓ))
  Structure ℓ = TypeWithStr ℓ StructureStr



  -- The free structure on a set A, i.e., the left adjoint to the
  -- forgetful functor from the category of structures to sets.
  module _ {ℓ : Level} (A : Type ℓ) where

    data |Free| : Type (ℓ-max ℓX (ℓ-max ℓar (ℓ-max ℓq ℓ)))
    Free-P : PreStructureStr σ |Free|
    Free : Structure (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓq) ℓ)

    data |Free| where

      -- generator
      ⟦_⟧ : A → |Free|

      -- operations
      opFree : (x : X) → (ar x → |Free|) → |Free|

      -- equations
      eqFree : -- interp-eqn σ Free-P ℓq eqns
        ∀ (lhs rhs : Term σ |Free|)
        → eqns {Y = |Free|} lhs rhs
        → interp σ |Free| |Free| Free-P (λ x → x) lhs ≡ interp σ |Free| |Free| Free-P (λ x → x) rhs

      -- isSet
      trunc : isSet |Free|
      


    Free-P .PreStructureStr.op = opFree
    Free-P .PreStructureStr.is-set = trunc

    Free .fst = |Free|
    Free .snd .StructureStr.s = Free-P
    Free .snd .StructureStr.eqns-hold = eqFree










Structure→PreStructure : {ℓX ℓar ℓE ℓq : Level} {T : AlgTheory' ℓX ℓar ℓE ℓq}
  → Structure' T → PreStructure (AlgTheory'.σ T) ℓE
Structure→PreStructure M = ⟨ M ⟩ , M .snd .StructureStr'.s
    
    


-- Example: Semigroups
module Semigroup where

  -- A semigroup has one kind of operation
  X : Type
  X = Unit

  -- The operation takes 2 arguments
  ar : X → Type
  ar tt = Bool

  σ : Sig _ _
  σ .Sig.X = X
  σ .Sig.isDiscreteX x y = yes refl
  σ .Sig.ar = ar

  module Notation (@++ Y : Type ℓY) where

    _·_ : Term σ Y → Term σ Y → Term σ Y
    x · y = oper tt aux
      where
        aux : Bool → Term σ Y
        aux true = x
        aux false = y
        

  module _ (@++ Y : Type ℓY) where
    open Notation Y

    data SemigroupEqns : Term σ Y → Term σ Y → Type ℓY where
      assoc : ∀ (x y z : Y)
        → SemigroupEqns ((var x · var y) · var z) (var x · (var y · var z))

{-
    -- This throws an error: Variable Y is bound with strictly
    positive polarity, so it cannot be used here at a mixed position
    when checking the constructor assoc in the declaration of
    SemigroupEqns'
    
    data SemigroupEqns' : Term σ Y → Term σ Y → Type ℓY where
      assoc : ∀ (x y z : Term σ Y)
        → SemigroupEqns' ((x · y) · z) (x · (y · z))
-}

  eqns : ∀ {Y : Type ℓY} → Equations σ Y ℓY
  eqns {Y = Y} lhs rhs = SemigroupEqns Y lhs rhs

  T : AlgTheory' ℓ-zero ℓ-zero ℓ-zero ℓ-zero
  T .AlgTheory'.σ = σ
  T .AlgTheory'.eqns {Y = Y} = eqns {Y = Y}
 

  Semigroup : Type (ℓ-suc ℓ-zero)
  Semigroup = Structure' T


