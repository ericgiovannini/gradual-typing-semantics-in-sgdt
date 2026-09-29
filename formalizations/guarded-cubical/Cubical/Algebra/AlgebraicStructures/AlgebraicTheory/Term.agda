{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --polarity #-}

module Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Term where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool

open import Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Signature

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓar : Level
    ℓY : Level


module _ (σ : Sig ℓX ℓar)  where

  open Sig σ

  module _ (Y : Type ℓY) where
    -- The type of ASTs of terms with variables in Y. Such a tree is either:
    --   1. A leaf labeled by a variable in y
    --   2. A node labeled by the operation x : X, with a child tree/term
    --      for each z ∈ ar x.
    data Term : Type (ℓ-max ℓY (ℓ-max ℓX ℓar)) where
      var : (y : Y) → Term
      oper : (x : X) (vars : ar x → Term) → Term



    -- Elim principle for Terms
    module _
      {B : Term → Type ℓ}
      (var* : (y : Y) → B (var y))
      (oper* : (x : X) (vars : ar x → Term)
        → (recursive : (z : ar x) → B (vars z))
        → B (oper x vars))
      where
      
      elimTerm : (t : Term) → B t
      elimTerm (var y) = var* y
      elimTerm (oper x vars) = oper* x vars (λ z → elimTerm (vars z))

    -- Recursion principle
    module _
      {B : Type ℓ}
      (var* : Y → B)
      (oper* : (x : X) → (ar x → B) → B)
      where

      recTerm : Term → B
      recTerm t = elimTerm {B = λ _ → B} var* (λ x _ → oper* x) t
      


  -- Functorial action
  mapTerm : {A : Type ℓ} {B : Type ℓ'}
    → (f : A → B)
    → Term A → Term B
  mapTerm {A = A} {B = B} f = elimTerm A {B = λ _ → Term B}
    (λ y → var (f y))
    (λ x vars recursive → oper x recursive)



-- Lifting terms over a signature Σ to be over a coproduct of
-- signatures Σ + Σ'.
module _ {ℓX ℓX' ℓar ℓar' : Level}
  (Σ₁ : Sig ℓX ℓar) (Σ₂ : Sig ℓX' ℓar')
  {ℓY : Level} {Y : Type ℓY}
  where

  private
    module Σ₁ = Sig Σ₁
    module Σ₂ = Sig Σ₂
    
  Term-inl : 
      Term Σ₁ Y
    → Term (Σ₁ ⊎Sig Σ₂) Y
  Term-inl (var y) = var y
  Term-inl (oper x vars) = oper (inl x) (λ z → Term-inl (vars (lower z)))

  usesOnlyΣ₁ :
    Term (Σ₁ ⊎Sig Σ₂) Y → Type ℓar
  usesOnlyΣ₁ (var y) = ⊤*
  usesOnlyΣ₁ (oper (inl x) vars) = (z : Σ₁.ar x) → usesOnlyΣ₁ (vars (lift z)) 
  usesOnlyΣ₁ (oper (inr x) vars) = ⊥*

  usesOnlyΣ₁-Term-inl : ∀ t → usesOnlyΣ₁ (Term-inl t)
  usesOnlyΣ₁-Term-inl (var y) = tt*
  usesOnlyΣ₁-Term-inl (oper x vars) = (λ z → usesOnlyΣ₁-Term-inl (vars z))

  Term-proj-inl :
      (t : Term (Σ₁ ⊎Sig Σ₂) Y)
    → usesOnlyΣ₁ t
    → Term Σ₁ Y
  Term-proj-inl (var y) H = var y
  Term-proj-inl (oper (inl x) vars) H =
    oper x (λ z → Term-proj-inl (vars (lift z)) (H z))


  Term-inr : 
      Term Σ₂ Y
    → Term (Σ₁ ⊎Sig Σ₂) Y
  Term-inr (var y) = var y
  Term-inr (oper x vars) = oper (inr x) λ z → Term-inr (vars (lower z))


module _ {ℓX ℓX' ℓar ℓar' : Level}
  (Σ₁ : Sig ℓX ℓar) (Σ₂ : Sig ℓX' ℓar')
  {ℓY : Level} {Y : Type ℓY}
  where

  swap : Term (Σ₁ ⊎Sig Σ₂) Y → Term (Σ₂ ⊎Sig Σ₁) Y
  swap (var y) = var y
  swap (oper (inl x) vars) = oper (inr x) (λ z → swap (vars z))
  swap (oper (inr x) vars) = oper (inl x) (λ z → swap (vars z))



-- Lifting and lowering the variables in a term.
module _ {ℓX ℓar : Level}
  (Σ : Sig ℓX ℓar)
  where

  Term-Lift : {Y : Type ℓY} {j : Level}
    → Term Σ Y
    → Term Σ (Lift {j = j} Y)
  Term-Lift (var y) = var (lift y)
  Term-Lift (oper x vars) = oper x (λ z → Term-Lift (vars z))

  Term-Lower : {Y : Type ℓY} {j : Level}
    → Term Σ (Lift {j = j} Y)
    → Term Σ Y
  Term-Lower (var y) = var (lower y)
  Term-Lower (oper x vars) = oper x λ z → Term-Lower (vars z)
