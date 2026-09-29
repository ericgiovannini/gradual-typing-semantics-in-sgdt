{-# OPTIONS --polarity #-}

module Cubical.Algebra.Structures.AlgebraicTheory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary

open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Algebra.Structures.Base
-- open import Cubical.Algebra.Structures.Morphism
-- open import Cubical.Algebra.Structures.Displayed

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓᴰ ℓᴰ' : Level
    ℓM ℓN ℓP : Level
    ℓMᴰ ℓNᴰ ℓPᴰ : Level


open Signature
open Eqns


module _ {ℓX ℓar : Level} where

  NullaryOp : Sig ℓX ℓar
  NullaryOp .Sig.X = ⊤*
  NullaryOp .Sig.isDiscreteX x y = yes refl
  NullaryOp .Sig.ar tt* = ⊥*

  UnaryOp : Sig ℓX ℓar
  UnaryOp .Sig.X = ⊤*
  UnaryOp .Sig.isDiscreteX x y = yes refl
  UnaryOp .Sig.ar tt* = ⊤*

  BinaryOp : Sig ℓX ℓar
  BinaryOp .Sig.X = ⊤*
  BinaryOp .Sig.isDiscreteX x y = yes refl
  BinaryOp .Sig.ar tt* = Lift ℓar Bool




-- Lifting terms and equations over a signature Σ to be over a
-- coproduct of signatures Σ + Σ'.
module _ {ℓX ℓX' ℓar ℓar' : Level}
  (Σ₁ : Sig ℓX ℓar) (Σ₂ : Sig ℓX' ℓar')
  {ℓY : Level} {Y : Type ℓY}
  where
  
  Term-inl : 
      Term Σ₁ Y
    → Term (Σ₁ ⊎Sig Σ₂) Y
  Term-inl (var y) = var y
  Term-inl (oper x vars) = oper (inl x) (λ z → Term-inl (vars (lower z)))

  Eqn-inl : 
      Equation Σ₁ Y
    → Equation (Σ₁ ⊎Sig Σ₂) Y
  Eqn-inl (lhs , rhs) = (Term-inl lhs , Term-inl rhs)


  Term-inr : 
      Term Σ₂ Y
    → Term (Σ₁ ⊎Sig Σ₂) Y
  Term-inr (var y) = var y
  Term-inr (oper x vars) = oper (inr x) λ z → Term-inr (vars (lower z))

  Eqn-inr : 
      Equation Σ₂ Y
    → Equation (Σ₁ ⊎Sig Σ₂) Y
  Eqn-inr (lhs , rhs) = (Term-inr lhs , Term-inr rhs)


-- Lifting terms and equations over variables in Y to equations over
-- variables in Lift Y.
module _ {ℓX ℓar : Level}
  (Σ : Sig ℓX ℓar)
  where

  Term-Lift : {ℓY : Level} {Y : Type ℓY} {j : Level}
    → Term Σ Y
    → Term Σ (Lift j Y)
  Term-Lift (var y) = var (lift y)
  Term-Lift (oper x vars) = oper x (λ z → Term-Lift (vars z))

  Eqn-Lift : {ℓY : Level} {Y : Type ℓY} {j : Level}
    → Equation Σ Y
    → Equation Σ (Lift j Y)
  Eqn-Lift (lhs , rhs) = (Term-Lift lhs , Term-Lift rhs)


-- The coproduct of two sets of equations over different signatures.
module _ {ℓX ℓX' ℓar ℓar' : Level}
  (Σ₁ : Sig ℓX ℓar) (Σ₂ : Sig ℓX' ℓar')
  {ℓE ℓE' ℓq ℓq' : Level}
  (eqns  : Eqns Σ₁ ℓE  ℓq)
  (eqns' : Eqns Σ₂ ℓE' ℓq')
  where

  private
    module eqns  = Eqns eqns
    module eqns' = Eqns eqns'

  Eqns-⊎ : Eqns (Σ₁ ⊎Sig Σ₂) (ℓ-max ℓE ℓE') (ℓ-max ℓq ℓq')
  Eqns-⊎ .E = eqns.E ⊎ eqns'.E
  Eqns-⊎ .q = Sum.rec (Lift ℓq' ∘ eqns.q) (Lift ℓq ∘ eqns'.q)
  Eqns-⊎ .eqn = Sum.elim
    (λ e → Eqn-Lift (Σ₁ ⊎Sig Σ₂) (Eqn-inl Σ₁ Σ₂ (eqns.eqn e)))
    (λ e → Eqn-Lift (Σ₁ ⊎Sig Σ₂) (Eqn-inr Σ₁ Σ₂ (eqns'.eqn e)))


-- The empty set of equations
module _ {ℓX ℓar : Level} (σ : Sig ℓX ℓar) {ℓE ℓq : Level} where

  NoEqns : Eqns σ ℓE ℓq
  NoEqns .E = ⊥*
  NoEqns .q = ⊥.rec*
  NoEqns .eqn = ⊥.elim*



-- An AlgTheory contains the data specifying an algebraic
-- theory, namely:
-- 
--   1. The collection of operation names and arities (`X` and `ar`,
--   respectively).
-- 
--   2. The equations associated with this structure (`eqns`). The
--   Eqns structure represents a collection of equations, and stores
--   their names and arities (`E` and `q`), where the arity of an
--   equation is simply a type large enough to hold all of the
--   distinct variables mentioned in the equation. The Eqns structure
--   additionally contains the data of the equations themselves, i.e.,
--   the LHS and RHS terms.
record AlgTheory (ℓX ℓar ℓE ℓq : Level)
  : Type (ℓ-max (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓar)) (ℓ-max (ℓ-suc ℓE) (ℓ-suc ℓq))) where
  field
    -- ℓX ℓar ℓE ℓq : Level
    σ : Sig ℓX ℓar
    -- X : Type ℓX
    -- ar : X → Type ℓar
    eqns : Eqns σ ℓE ℓq

  -- open Sig σ public
  -- open Eqns eqns public
  module σ = Sig σ
  module eqns = Eqns eqns
 

open AlgTheory


-- The algebraic theory of a single nullary operation.
module _ {ℓX ℓar ℓE ℓq : Level} where

  𝟙 : AlgTheory ℓX ℓar ℓE ℓq
  𝟙 .σ = NullaryOp
  𝟙 .eqns = NoEqns NullaryOp


-- The coproduct of two algebraic theories.
module _
  {ℓX  ℓar  ℓE  ℓq : Level}
  {ℓX' ℓar' ℓE' ℓq' : Level}
  (T₁ : AlgTheory ℓX ℓar ℓE ℓq)
  (T₂ : AlgTheory ℓX' ℓar' ℓE' ℓq')
  where

  private
    module T₁ = AlgTheory T₁
    module T₂ = AlgTheory T₂

  AlgTheory-⊎ : AlgTheory (ℓ-max ℓX ℓX') (ℓ-max ℓar ℓar') (ℓ-max ℓE ℓE') (ℓ-max ℓq ℓq')
  AlgTheory-⊎ .σ = T₁.σ ⊎Sig T₂.σ
  AlgTheory-⊎ .eqns = Eqns-⊎ T₁.σ T₂.σ T₁.eqns T₂.eqns


module _ {ℓX ℓar ℓE ℓq : Level} (T : AlgTheory ℓX ℓar ℓE ℓq) where
  private module T = AlgTheory T
  
  mkPointed : AlgTheory ℓX ℓar ℓE ℓq
  mkPointed = AlgTheory-⊎ T (𝟙 {ℓX} {ℓar} {ℓE} {ℓq})
  
