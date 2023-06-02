{-# OPTIONS --cubical #-}
module Semantics.Abstract.TermModel.Convenient where

-- A convenient model of the term language is
-- 1. A bicartesian closed category
-- 2. Equipped with a strong monad
-- 3. An object modeling the numbers with models of the con/dtors
-- 4. An object modeling the dynamic type with models of the inj casts

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation as NT hiding (NatTrans)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Monad.ExtensionSystem
open import Cubical.Categories.Comonad.Instances.Environment
open import Cubical.Categories.Monad.Strength.Cartesian.ExtensionSystem

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open BinCoproduct
open BinProduct

record Model ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    -- a bicartesian closed category
    cat : Category ℓ ℓ'
    term : Terminal cat
    binProd : BinProducts cat
    exponentials : Exponentials cat binProd
    binCoprod : BinCoproducts cat
    -- with a strong monad
    monad : StrongExtensionSystem binProd


  -- TODO: rename Notation and make similar modules for terminal, coprod
  open Notation cat binProd public
  open ExpNotation cat binProd exponentials public
  open TerminalNotation cat term public
  open StrongMonadNotation binProd monad public
  open EnvNotation binProd public

  _+_ : (a b : cat .ob) → cat .ob
  a + b = binCoprod a b .binCoprodOb

  σ1 : {a b : cat .ob} → cat [ a , a + b ]
  σ1 = binCoprod _ _ .binCoprodInj₁
  σ2 : {a b : cat .ob} → cat [ b , a + b ]
  σ2 = binCoprod _ _ .binCoprodInj₂
  _||_ : {a b c : cat .ob} → cat [ a , c ] → cat [ b , c ] → cat [ a + b , c ]
  f1 || f2 = binCoprod _ _ .univProp f1 f2 .fst .fst

  _⇀_ : (a b : cat .ob) → cat .ob
  a ⇀ b = a ⇒ T b

  -- TODO: should this go into notation?
  Linear = PKleisli
  ClLinear = Kleisli cat (StrongMonad→Monad binProd term monad)

  field
    -- a weak model of the natural numbers, but good enough for our syntax
    nat : cat .ob
    nat-fp : CatIso cat (𝟙 + nat) nat

    -- now the dyn stuff
    -- a model of dyn/casts
    dyn : cat .ob

    -- at this point we will model injection and projection as
    -- arbitrary morphisms
    inj : cat      [ nat + (dyn ⇀ dyn) , dyn ]
    prj : ClLinear [ dyn , nat + (dyn ⇀ dyn) ]

    -- and the error of course!
    -- err : 1 ⇀ A
    -- naturality says err ≡ T f ∘ err
    -- not sure if that's exactly right...
    err : ∀ {a} → cat [ 𝟙 , a ]
  ℧ : ∀ {Γ a} → cat [ Γ , T a ]
  ℧ = err ∘⟨ cat ⟩ !t

  field
    ℧-homo : ∀ {Γ a b} → (f : Linear Γ [ a , b ])
           -- define this explicitly as a profunctor?
           → bind f ∘⟨ cat ⟩ ((cat .id ,p ℧)) ≡ ℧

