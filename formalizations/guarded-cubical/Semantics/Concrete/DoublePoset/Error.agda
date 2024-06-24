{-# OPTIONS --rewriting --guarded #-}

open import Common.Later


module Semantics.Concrete.DoublePoset.Error (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.Relation.Binary

open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.DoublePoset.Base


private
  variable
    ℓ ℓ' ℓR : Level


open BinaryRelation

-- Defining bisimilarity on Error X given bisimilarity on X


≈ErrorX : {X : Type ℓ} (R : X → X → Type ℓR) → Error X → Error X → Type ℓR
≈ErrorX R (ok x) (ok y) = R x y
≈ErrorX R error error = Unit*
≈ErrorX R _ _ = ⊥*

IsBisimErrorX : {X : Type ℓ} (R : X → X → Type ℓR) →
  IsBisim R → IsBisim (≈ErrorX R)
IsBisimErrorX R isBisimR =
  isbisim reflexive symmetric prop
    where
      reflexive : isRefl (≈ErrorX R)
      reflexive (ok x) = isBisimR .IsBisim.is-refl x
      reflexive error = tt*

      symmetric : isSym (≈ErrorX R)
      symmetric (ok x) (ok y) Rxy = isBisimR .IsBisim.is-sym x y Rxy
      symmetric error error tt* = tt*

      prop : isPropValued (≈ErrorX R)
      prop (ok x) (ok y) p q = isBisimR .IsBisim.is-prop-valued x y p q
      prop error error p q = refl
