{-# OPTIONS --cubical #-}
module Semantics.Abstract.TermModel.Convenient where

-- A convenient model of the term language is
-- 1. A cartesian closed category
-- 2. Equipped with a strong monad
-- 3. An object modeling the numbers with models of the con/dtors
-- 4. An object modeling the dynamic type with models of the up/dn casts that are independent of the derivation

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Exponentials

open import Cubical.Categories.Presheaf.Representable
open import Semantics.Abstract.TermModel.Strength

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open BinCoproduct
open BinProduct

record Model ℓ ℓ' ℓ'' : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓ''))) where
  field
    -- A cartesian closed category
    cat : Category ℓ ℓ'
    term : Terminal cat
    binProd : BinProducts cat
    exponentials : Exponentials cat binProd
    binCoprod : BinCoproducts cat

  𝟙 = term .fst

  _×_ : (a b : cat .ob) → cat .ob
  a × b = binProd a b .binProdOb

  _+_ : (a b : cat .ob) → cat .ob
  a + b = binCoprod a b .binCoprodOb

  _⇒_ : (a b : cat .ob) → cat .ob
  a ⇒ b = ExponentialF cat binProd exponentials ⟅ a , b ⟆

  field
    -- with a strong monad
    monad : Monad cat
    strength : Strength cat term binProd monad
  T = monad .fst


  _⇀_ : (a b : cat .ob) → cat .ob
  a ⇀ b = a ⇒ T ⟅ b ⟆

  field
    -- a weak model of the natural numbers, but good enough for our syntax
    nat : cat .ob
    nat-fp : CatIso cat (𝟙 + nat) nat

    -- now the dyn stuff
    -- a model of dyn/casts
    dyn : cat .ob
    -- type precision
    _⊑_ : (cat .ob) → (cat .ob) → Type ℓ''
    isReflexive⊑  : ∀ {a} → a ⊑ a
    isTransitive⊑ : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c
    isProp⊑ : ∀ {a b} → isProp (a ⊑ b)

    -- monotonicity of type constructors
    prod-is-monotone : ∀ {a a' b b'} → a ⊑ a' → b ⊑ b' → (a × b) ⊑ (a' × b')
    parfun-is-monotone : ∀ {a a' b b'} → a ⊑ a' → b ⊑ b' → (a ⇀ b) ⊑ (a' ⇀ b')
    inj-nat : nat ⊑ dyn
    inj-arr : (dyn ⇀ dyn) ⊑ dyn

    up : ∀ {a b} → a ⊑ b → cat [ a , b ]
    dn : ∀ {a b} → a ⊑ b → cat [ b , T ⟅ a ⟆ ]
