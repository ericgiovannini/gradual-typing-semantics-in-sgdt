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
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Exponentials

open import Semantics.Abstract.TermModel.Strength

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open BinCoproduct
open BinProduct

record Model ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    -- A cartesian closed category
    cat : Category ℓ ℓ'
    term : Terminal cat
    binProd : BinProducts cat
    exponentials : Exponentials cat binProd
    binCoprod : BinCoproducts cat
    monad : Monad cat
    strength : Strength cat term binProd monad


  -- TODO: rename Notation and make similar modules for terminal, coprod
  open Notation cat binProd public
  open ExpNotation cat binProd exponentials public
  open StrengthNotation cat term binProd monad strength public

  𝟙 = term .fst

  !t : ∀ {a} → cat [ a , 𝟙 ]
  !t = terminalArrow cat term _

  𝟙η : ∀ {a} → (f : cat [ a , 𝟙 ]) → f ≡ !t
  𝟙η f = sym (terminalArrowUnique cat {T = term} f)

  _+_ : (a b : cat .ob) → cat .ob
  a + b = binCoprod a b .binCoprodOb

  σ1 : {a b : cat .ob} → cat [ a , a + b ]
  σ1 = binCoprod _ _ .binCoprodInj₁
  σ2 : {a b : cat .ob} → cat [ b , a + b ]
  σ2 = binCoprod _ _ .binCoprodInj₂
  _||_ : {a b c : cat .ob} → cat [ a , c ] → cat [ b , c ] → cat [ a + b , c ]
  f1 || f2 = binCoprod _ _ .univProp f1 f2 .fst .fst

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

    -- at this point we will model injection and projection as
    -- arbitrary morphisms
    inj : cat [ nat + (dyn ⇀ dyn) , dyn ]
    prj : cat [ dyn , T ⟅ nat + (dyn ⇀ dyn) ⟆ ]

    -- and the error of course!
    -- err : 1 ⇀ A
    -- naturality says err ≡ T f ∘ err
    -- not sure if that's exactly right...
    err : NT.NatTrans (Constant _ _ 𝟙) T

  ℧ : ∀ {Γ d} → cat [ Γ , T ⟅ d ⟆ ]
  ℧ {Γ} = NT.NatTrans.N-ob err _ ∘⟨ cat ⟩ terminalArrow cat term Γ

