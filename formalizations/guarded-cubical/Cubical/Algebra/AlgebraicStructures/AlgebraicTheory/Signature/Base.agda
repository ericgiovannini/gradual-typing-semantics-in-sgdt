{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --polarity #-}

module Cubical.Algebra.AlgebraicStructures.AlgebraicTheory.Signature.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool


open import Cubical.Relation.Nullary


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
  BinaryOp .Sig.ar tt* = Lift {j = ℓar} Bool
