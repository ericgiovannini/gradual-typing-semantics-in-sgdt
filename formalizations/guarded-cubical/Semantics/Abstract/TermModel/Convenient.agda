{-# OPTIONS --cubical #-}
module Semantics.Abstract.TermModel.Convenient where

-- A convenient model of the term language is
-- 1. A cartesian closed category
-- 2. Equipped with a strong monad
-- 3. An object modeling the numbers with models of the con/dtors
-- 4. An object modeling the dynamic type with models of the up/dn casts that are independent of the derivation

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Exponentials

open import Semantics.Abstract.TermModel.Strength

private
  variable
    ℓ ℓ' : Level

record Model {ℓ}{ℓ'} : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    -- A cartesian closed category
    cat : Category ℓ ℓ'
    term : Terminal cat
    binProd : BinProducts cat
    exponentials : Exponentials cat binProd

    -- with a strong monad
    monad : Monad cat
    strength : Strength cat term binProd monad

    -- a model of the natural numbers

    -- a model of dyn/casts
