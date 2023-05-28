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
open import Cubical.Data.List hiding ([_])

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
   Γ Γ' Δ Δ' : Ctx
   γ γ' : Subst Δ Γ
   V V' : Val Γ S
   E E' F F' : EvCtx Γ R S
   M M' N N' : Comp Γ S

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

  ⟦_⟧ctx : Ctx → M.cat .ob
  ⟦ [] ⟧ctx = M.𝟙
  ⟦ A ∷ Γ ⟧ctx = ⟦ Γ ⟧ctx M.× ⟦ A ⟧ty

  -- The term syntax
  -- substitutions, values, ev ctxts, terms

  ⟦_⟧S : Subst Δ Γ → M.cat [ ⟦ Δ ⟧ctx , ⟦ Γ ⟧ctx ]
  ⟦_⟧V : Val Γ S → M.cat [ ⟦ Γ ⟧ctx , ⟦ S ⟧ty ]
  ⟦_⟧E : EvCtx Γ R S → M.cat [ ⟦ Γ ⟧ctx M.× ⟦ R ⟧ty , M.T ⟅ ⟦ S ⟧ty ⟆ ]
  ⟦_⟧C : Comp Γ S → M.cat [ ⟦ Γ ⟧ctx , M.T ⟅ ⟦ S ⟧ty ⟆ ]

  ⟦ ids ⟧S = M.cat .id
  ⟦ γ ∘s δ ⟧S = ⟦ γ ⟧S ∘⟨ M.cat ⟩ ⟦ δ ⟧S
  ⟦ ∘IdL {γ = γ} i ⟧S = M.cat .⋆IdR ⟦ γ ⟧S i
  ⟦ ∘IdR {γ = γ} i ⟧S = M.cat .⋆IdL ⟦ γ ⟧S i
  ⟦ ∘Assoc {γ = γ}{δ = δ}{θ = θ} i ⟧S = M.cat .⋆Assoc ⟦ θ ⟧S ⟦ δ ⟧S ⟦ γ ⟧S i
  ⟦ !s ⟧S = M.!t
  ⟦ []η {γ = γ} i ⟧S = M.𝟙η ⟦ γ ⟧S i
  ⟦ γ ,s V ⟧S = ⟦ γ ⟧S M.,p ⟦ V ⟧V
  ⟦ wk ⟧S = M.π₁
  ⟦ wkβ {δ = γ}{V = V} i ⟧S = M.×β₁ {f = ⟦ γ ⟧S}{g = ⟦ V ⟧V} i
  ⟦ ,sη {δ = γ} i ⟧S = M.×η {f = ⟦ γ ⟧S} i
  ⟦ isSetSubst γ γ' p q i j ⟧S = M.cat .isSetHom ⟦ γ ⟧S ⟦ γ' ⟧S (cong ⟦_⟧S p) (cong ⟦_⟧S q) i j

  ⟦ V [ γ ]v ⟧V = ⟦ V ⟧V ∘⟨ M.cat ⟩ ⟦ γ ⟧S
  ⟦ substId {V = V} i ⟧V = M.cat .⋆IdL ⟦ V ⟧V i
  ⟦ substAssoc {V = V}{δ = δ}{γ = γ} i ⟧V = M.cat .⋆Assoc ⟦ γ ⟧S ⟦ δ ⟧S ⟦ V ⟧V i
  ⟦ var ⟧V = M.π₂
  ⟦ varβ {δ = γ}{V = V} i ⟧V = M.×β₂ {f = ⟦ γ ⟧S}{g = ⟦ V ⟧V} i
  ⟦ zro ⟧V = {!!}
  ⟦ suc ⟧V = {!!}
  ⟦ lda x ⟧V = {!!}
  ⟦ fun-η i ⟧V = {!!}
  ⟦ up S⊑T ⟧V = {!!}
  ⟦ isSetVal V V' p q i j ⟧V = M.cat .isSetHom ⟦ V ⟧V ⟦ V' ⟧V (cong ⟦_⟧V p) (cong ⟦_⟧V q) i j

  ⟦_⟧E = {!!}
  ⟦_⟧C = {!!}
