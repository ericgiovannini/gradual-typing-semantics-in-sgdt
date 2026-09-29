-- {-# OPTIONS --polarity #-}

{-

Formalization of algebraic structures as an hSet A equipped with a
type-indexed collection of operations and equations.

-}


module Cubical.Algebra.Structures.Base where

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


private
  variable
    ℓ ℓ' ℓ'' : Level

  variable
    S : Type ℓ → Type ℓ'


record Sig (ℓX ℓar : Level) : Type (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓar)) where
  constructor signature
  field
    X : Type ℓX
    isDiscreteX : Discrete X
    ar : X → Type ℓar


module _ {ℓX ℓX' ℓar ℓar' : Level}
  (Σ₁ : Sig ℓX ℓar)
  (Σ₂ : Sig ℓX' ℓar')
  where

  private
    module Σ₁ = Sig Σ₁
    module Σ₂ = Sig Σ₂
    
  _⊎Sig_ : Sig (ℓ-max ℓX ℓX') (ℓ-max ℓar ℓar')
  (_⊎Sig_) .Sig.X = (Σ₁.X ⊎ Σ₂.X)
  (_⊎Sig_) .Sig.isDiscreteX = discrete⊎ Σ₁.isDiscreteX Σ₂.isDiscreteX
  (_⊎Sig_) .Sig.ar = Sum.rec (Lift {j = ℓar'} ∘ Σ₁.ar) (Lift {j = ℓar} ∘ Σ₂.ar)



module Signature {ℓX ℓar : Level}
  (Σ : Sig ℓX ℓar)
  where

  open Sig Σ

  record PreStructureStr (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-max ℓX ℓar)) where
    field
      op : (x : X) → (ar x → A) → A
      is-set : isSet A

  PreStructure : ∀ ℓ → Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-suc ℓ))
  PreStructure ℓ = TypeWithStr ℓ PreStructureStr


  module _ {ℓY : Level} (Y : Type ℓY) where

    -- The type of ASTs of terms with variables in Y. Such a tree is either:
    --   1. A leaf labeled by a variable in y
    --   2. A node labeled by the operation x : X, with a child tree/term
    --      for each z ∈ ar x.
    data Term : Type (ℓ-max ℓY (ℓ-max ℓX ℓar)) where
      var : Y → Term
      oper : (x : X) (vars : ar x → Term) → Term

    -- Interpreting a term AST (with variables in Y) into a
    -- PreStructure. For technical reasons (related to the positivity
    -- checker when defining the free structure), we separate the
    -- module parameters into a type A and a PreStructureStr on A.
    module _ {ℓ : Level} (A : Type ℓ) (s : PreStructureStr A) where
      private module s = PreStructureStr s
    
      interp : (Y → A) → Term → A
      interp f (var y) = f y
      interp f (oper x vars) = s.op x (λ z → interp f (vars z))


  -- We specify a collection of equations via an indexing type E, and
  -- for each e : E, and arity `q e` along with a pair of terms over
  -- variables `q e`. Note that this specification is purely
  -- syntactic, i.e., we do not require a PreStructure to specify
  -- equations.
  Equation : {ℓY : Level} (Y : Type ℓY) → Type (ℓ-max (ℓ-max ℓX ℓar) ℓY)
  Equation Y = Term Y × Term Y

  -- Interpreting an equation in a PreStructure.
  module _
    {A : Type ℓ} (s : PreStructureStr A) where

    interp-eqn : {ℓY : Level} (Y : Type ℓY)
      → Equation Y
      → Type (ℓ-max ℓ ℓY)
    interp-eqn Y eqn = (gamma : Y → A)
      → interp Y A s gamma (eqn .fst) ≡ interp Y A s gamma (eqn .snd)


  record Eqns (ℓE ℓq : Level)
    : Type (ℓ-max (ℓ-max (ℓ-suc ℓE) (ℓ-suc ℓq)) (ℓ-max ℓX ℓar)) where
    field
      E : Type ℓE
      q : (e : E) → Type ℓq
      eqn : (e : E) → Equation (q e)

    lhs rhs : (e : E) → Term (q e)
    lhs e = fst (eqn e)
    rhs e = snd (eqn e)


  -- Now, for a given collection of equations as defined above, we
  -- define a Structure as a PreStructure `s` in which the equations
  -- hold.  That is, when we interpret the LHS and RHS of each
  -- equation `e` as an element of `s`, those elements are equal.
  --
  -- To deal with the free variables in each equation, we universally
  -- quantify over all interpretations `gamma` of those variables as
  -- elements of s.
  module _ {ℓE ℓq : Level} (eqns : Eqns ℓE ℓq) where
    private module eqns = Eqns eqns
    
    record StructureStr (A : Type ℓ)
      : Type (ℓ-max (ℓ) (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓE ℓq))) where
      field
        s : PreStructureStr A
        eqns-hold : ∀ (e : eqns.E)
          → interp-eqn s (eqns.q e) (eqns.eqn e)

         -- eqns-hold : ∀ (e : eqns.E)
         --  → (gamma : eqns.q e → A)
         --  → interp (eqns.q e) A s gamma (eqns.lhs e) ≡ interp (eqns.q e) A s gamma (eqns.rhs e)

      open PreStructureStr s public


    Structure : ∀ ℓ → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) (ℓ-suc ℓ))
    Structure ℓ = TypeWithStr ℓ StructureStr

    
       


{-
  module _ {ℓ ℓY : Level} (s : PreStructure ℓ) where
    private module s = PreStructureStr (s .snd)
    
    interp' : Term ⊥ → ⟨ s ⟩
    interp' (oper x vars) = s.op x (λ z → interp' (vars z))
-}


{-
    -- The free structure on a set A, i.e., the left adjoint to the
    -- forgetful functor from the category of structures to sets.
    module _ {ℓ : Level} (A : Type ℓ) where

      data |Free| : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) ℓ)
      Free-P : PreStructureStr |Free|
      Free : Structure (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) ℓ)

      data |Free| where
      
        -- generator
        ⟦_⟧ : A → |Free|

        -- operations
        opFree : (x : X) → (ar x → |Free|) → |Free|

        -- equations
        eqFree : (e : eqns.E)
           → (gamma : eqns.q e → |Free|)
           → interp (eqns.q e) |Free| Free-P gamma (eqns.lhs e) ≡
             interp (eqns.q e) |Free| Free-P gamma (eqns.rhs e) 

        -- isSet
        trunc : isSet |Free|


      Free-P .PreStructureStr.op = opFree
      Free-P .PreStructureStr.is-set = trunc

      Free .fst = |Free|
      Free .snd .StructureStr.s = Free-P
      Free .snd .StructureStr.eqns-hold = eqFree
-}



open Signature

Structure→PreStructure : {ℓX ℓar ℓE ℓq : Level} {σ : Sig ℓX ℓar} {eqns : Eqns σ ℓE ℓq}
  → Structure σ eqns ℓ → PreStructure σ ℓ
Structure→PreStructure M = ⟨ M ⟩ , M .snd .StructureStr.s
    
    


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

  open Signature

  module Notation (Y : Type)  where

    _·_ : Term σ Y → Term σ Y  → Term σ Y
    x · y = oper tt aux
      where
        aux : Bool → Term σ Y
        aux true = x
        aux false = y
        

  data Three : Type where
    one two three : Three

  open Notation Three

  open Eqns

  eqns : Eqns σ ℓ-zero ℓ-zero
  eqns .E = Unit     -- one equation
  eqns .q tt = Three -- each side mentions three variables
  eqns .eqn tt .fst = (var one · var two) · var three
  eqns .eqn tt .snd = var one · (var two · var three)

  Semigroup : ∀ ℓ → Type (ℓ-suc ℓ)
  Semigroup ℓ = Structure σ eqns ℓ
