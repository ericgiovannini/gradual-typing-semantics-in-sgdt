{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.Predomain.GuardedTheory.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum

open import Semantics.Concrete.Predomain.GuardedTheory.Arity

record Signature : Type₁ where
  field
    Op : Type
    ar : Op → Arity


module _
  (S₁ : Signature)
  (S₂ : Signature) where

  open Signature

  private
    module S₁ = Signature S₁
    module S₂ = Signature S₂

  _+Sig_ : Signature
  _+Sig_ .Op = S₁.Op ⊎ S₂.Op
  _+Sig_ .ar (inl o)  = S₁.ar o
  _+Sig_ .ar (inr o') = S₂.ar o'

