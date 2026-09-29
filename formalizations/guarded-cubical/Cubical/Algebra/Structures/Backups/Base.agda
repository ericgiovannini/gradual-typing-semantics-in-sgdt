{-# OPTIONS --polarity #-}

{-

Formalization of algebraic structures as an hSet A equipped with a
type-indexed collection of operations and equations.

-}


module Cubical.Algebra.Structures.Backups.Base where

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


module _ {ℓX ℓar : Level}
  (X : Type ℓX) (ar : X → Type ℓar)
  where

  record PreStructureStr (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-max ℓX ℓar)) where
    field
      op : (x : X) → (ar x → A) → A
      is-set : isSet A

  PreStructure : ∀ ℓ → Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-suc ℓ))
  PreStructure ℓ = TypeWithStr ℓ PreStructureStr


  module _ {ℓY : Level} (Y : Type ℓY) where

    -- The type of ASTs of terms with variables in Y. Such a tree is either:
    --   1. A leaf labeled by a variable in y
    --   2. A node labeled by the operation x : X, with a child tree/term for each z ∈ ar x.
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



  record PreStructureᴰ (M : PreStructure ℓ) ℓᴰ
    : Type (ℓ-max (ℓ-max ℓ (ℓ-suc ℓᴰ)) (ℓ-max ℓX ℓar)) where
    
      open PreStructureStr (M .snd)
      
      field
        eltᴰ : ⟨ M ⟩ → Type ℓᴰ

        -- Given x : X, an `ar x`-indexed collection `vars` of elements of M, and
        -- a family for each z ∈ ar x displayed over the element `vars z` ∈ M,
        -- we get a single element displayed over `op x vars`.
        opᴰ : ∀ {x : X} {vars : ar x → ⟨ M ⟩}
          → (varsᴰ : (z : ar x) → eltᴰ (vars z))
          → eltᴰ (op x vars)

        isSetEltᴰ : ∀ {x} → isSet (eltᴰ x)

      _≡[_]_ : ∀ {x y} → eltᴰ x → x ≡ y → eltᴰ y → Type _
      xᴰ ≡[ p ] yᴰ = PathP (λ i → eltᴰ (p i)) xᴰ yᴰ


  module _ {ℓY : Level} (Y : Type ℓY) where

    -- Interpreting a term AST (with variables in Y) into a displayed PreStructure.
    module _ {ℓ ℓᴰ : Level} (s : PreStructure ℓ) (sᴰ : PreStructureᴰ s ℓᴰ) where
      private module sᴰ = PreStructureᴰ sᴰ
    
      interpᴰ : (f : (Y → ⟨ s ⟩)) (fᴰ : (y : Y) → sᴰ.eltᴰ (f y))
        → (t : Term Y)
        → sᴰ.eltᴰ (interp Y ⟨ s ⟩ (s .snd) f t)
      interpᴰ f fᴰ (var y) = fᴰ y
      interpᴰ f fᴰ (oper x vars) = sᴰ.opᴰ (λ z → interpᴰ f fᴰ (vars z))



  -- We specify a collection of equations via an indexing type E, and
  -- for each e : E, and arity `q e` along with a pair of terms over
  -- variables `q e`. Note that this specification is purely
  -- syntactic, i.e., we do not require a PreStructure to specify
  -- equations.
  record Eqns (ℓE ℓq : Level)
    : Type (ℓ-max (ℓ-max (ℓ-suc ℓE) (ℓ-suc ℓq)) (ℓ-max ℓX ℓar)) where
    field
      E : Type ℓE
      q : (e : E) → Type ℓq
      eqn : (e : E) → Term (q e) × Term (q e)

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
  module _ (ℓE ℓq : Level) (eqns : Eqns ℓE ℓq) where
    private module eqns = Eqns eqns
    
    record StructureStr (A : Type ℓ)
      : Type (ℓ-max (ℓ) (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓE ℓq))) where
      field
        s : PreStructureStr A
        eqn : ∀ (e : eqns.E)
          → (gamma : eqns.q e → A)
          → interp (eqns.q e) A s gamma (eqns.lhs e) ≡ interp (eqns.q e) A s gamma (eqns.rhs e)

      open PreStructureStr s public


    Structure : ∀ ℓ → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) (ℓ-suc ℓ))
    Structure ℓ = TypeWithStr ℓ StructureStr


{-
  module _ {ℓ ℓY : Level} (s : PreStructure ℓ) where
    private module s = PreStructureStr (s .snd)
    
    interp' : Term ⊥ → ⟨ s ⟩
    interp' (oper x vars) = s.op x (λ z → interp' (vars z))
-}


    -- Homomorphisms of structures
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
      Free .snd .StructureStr.eqn = eqFree


    -- Displayed structures
    record Structureᴰ (M : Structure ℓ) ℓᴰ
      : Type (ℓ-max (ℓ-max ℓ (ℓ-suc ℓᴰ)) (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓE ℓq))) where
      
      private module M = StructureStr (M .snd)
      |M| : PreStructure ℓ
      |M| = ⟨ M ⟩ , M.s

      field
        -- A family indexed by elements of M
        sᴰ : PreStructureᴰ |M| ℓᴰ

      open PreStructureᴰ sᴰ public
      
      field

        -- For each "syntactic" equation e of the structure M, we have a
        -- semantic equation displayed over the interpretation of e in M.
        eqnᴰ : (e : eqns.E) {gamma : eqns.q e → ⟨ M ⟩}
          → (gammaᴰ : (z : eqns.q e) → eltᴰ (gamma z))
          → interpᴰ (eqns.q e) |M| sᴰ gamma gammaᴰ (eqns.lhs e)
              ≡[ M.eqn e gamma ]
            interpᴰ (eqns.q e) |M| sᴰ gamma gammaᴰ (eqns.rhs e)
    


-- Example: Semigroups
module Semigroup where

  -- A semigroup has one kind of operation
  X : Type
  X = Unit

  -- The operation takes 2 arguments
  ar : X → Type
  ar tt = Bool

  module Notation (Y : Type)  where

    _·_ : Term X ar Y → Term X ar Y  → Term X ar Y
    x · y = oper tt aux
      where
        aux : Bool → Term X ar Y
        aux true = x
        aux false = y
        

  data Three : Type where
    one two three : Three

  open Notation Three

  open Eqns

  eqns : Eqns X ar ℓ-zero ℓ-zero
  eqns .E = Unit     -- one equation
  eqns .q tt = Three -- each side mentions three variables
  eqns .eqn tt .fst = (var one · var two) · var three
  eqns .eqn tt .snd = var one · (var two · var three)

  Semigroup : ∀ ℓ → Type (ℓ-suc ℓ)
  Semigroup ℓ = Structure X ar ℓ-zero ℓ-zero eqns ℓ
