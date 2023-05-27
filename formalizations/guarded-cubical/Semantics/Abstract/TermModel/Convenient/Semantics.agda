{-# OPTIONS --cubical #-}
module Semantics.Abstract.TermModel.Convenient.Semantics where

-- A convenient model of the term language is
-- 1. A bicartesian closed category
-- 2. Equipped with a strong monad
-- 3. An object modeling the numbers with models of the con/dtors
-- 4. An object modeling the dynamic type with models of the inj casts

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Exponentials

open import Semantics.Abstract.TermModel.Strength
open import Syntax.Types
open import Syntax.Terms
open import Semantics.Abstract.TermModel.Convenient

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open BinCoproduct
open BinProduct

private
 variable
   R R' S S' : Ty

module _ (M : Model ℓ ℓ') where
  module M = Model M
  module T = IsMonad (M.monad .snd)
  ⇒F = ExponentialF M.cat M.binProd M.exponentials
  ⟦_⟧ty : Ty → M.cat .ob
  ⟦ nat ⟧ty = M.nat
  ⟦ dyn ⟧ty = M.dyn
  ⟦ S ⇀ T ⟧ty = ⟦ S ⟧ty M.⇀ ⟦ T ⟧ty

  ⟦_⟧e : S ⊑ R → M.cat [ ⟦ S ⟧ty , ⟦ R ⟧ty ]
  ⟦_⟧p : S ⊑ R → M.cat [ ⟦ R ⟧ty , M.T ⟅ ⟦ S ⟧ty ⟆ ]
  ⟦_⟧p' : S ⊑ R → M.cat [ M.T ⟅ ⟦ R ⟧ty ⟆ , M.T ⟅ ⟦ S ⟧ty ⟆ ]


  ⟦ nat ⟧e = M.cat .id
  ⟦ dyn ⟧e = M.cat .id
  -- The most annoying one because it's not from bifunctoriality, more like separate functoriality
  -- λ f . λ x . x'  <- p x;
  --             y'  <- app(f,x');
  --             η (e y')
  ⟦ c ⇀ d ⟧e     = M.lda ((T.η .N-ob _ ∘⟨ M.cat ⟩ ⟦ d ⟧e) M.∘k
                         (M.app' (M.π₁ ∘⟨ M.cat ⟩ M.π₁) M.π₂ M.∘sk
                         (⟦ c ⟧p ∘⟨ M.cat ⟩ M.π₂)))
  ⟦ inj-nat ⟧e   = M.inj ∘⟨ M.cat ⟩ M.σ1
  ⟦ inj-arr c ⟧e = M.inj ∘⟨ M.cat ⟩ M.σ2 ∘⟨ M.cat ⟩ ⟦ c ⟧e

  ⟦ nat ⟧p = T.η .N-ob M.nat
  ⟦ dyn ⟧p = T.η .N-ob M.dyn
  -- = η ∘ (⟦ c ⟧e ⇒ ⟦ d ⟧p')
  ⟦ c ⇀ d ⟧p     = T.η .N-ob _ ∘⟨ M.cat ⟩ ⇒F ⟪ ⟦ c ⟧e , ⟦ d ⟧p' ⟫
  ⟦ inj-nat ⟧p   = (T.η .N-ob _ M.|| M.℧) M.∘k M.prj
  ⟦ inj-arr c ⟧p = (M.℧ M.|| ⟦ c ⟧p) M.∘k M.prj

  ⟦ c ⟧p' = T.bind .N-ob _ ⟦ c ⟧p
