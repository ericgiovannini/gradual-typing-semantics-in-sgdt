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
open import Cubical.Categories.Comonad.Instances.Environment
open import Cubical.Categories.Exponentials
open import Cubical.Data.List hiding ([_])

open import Syntax.Types
open import Syntax.Terms
open import Semantics.Abstract.TermModel.Convenient
open import Semantics.Abstract.TermModel.Convenient.Computations

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open BinCoproduct
open BinProduct
open TyPrec

private
 variable
   R R' S S' : Ty
   Γ Γ' Δ Δ' : Ctx
   γ γ' : Subst Δ Γ
   V V' : Val Γ S
   E E' F F' : EvCtx Γ R S
   M M' N N' : Comp Γ S

module _ (𝓜 : Model ℓ ℓ') where
  module 𝓜 = Model 𝓜
  ⇒F = ExponentialF 𝓜.cat 𝓜.binProd 𝓜.exponentials

  ⟦_⟧ty : Ty → 𝓜.cat .ob
  ⟦ nat ⟧ty = 𝓜.nat
  ⟦ dyn ⟧ty = 𝓜.dyn
  ⟦ S ⇀ T ⟧ty = ⟦ S ⟧ty 𝓜.⇀ ⟦ T ⟧ty

  ⟦_⟧e : S ⊑ R → 𝓜.cat [ ⟦ S ⟧ty , ⟦ R ⟧ty ]
  ⟦_⟧p : S ⊑ R → 𝓜.ClLinear [ ⟦ R ⟧ty , ⟦ S ⟧ty ]
  ⟦_⟧p' : S ⊑ R → 𝓜.cat [ 𝓜.T ⟦ R ⟧ty , 𝓜.T ⟦ S ⟧ty ]

  ⟦ nat ⟧e = 𝓜.cat .id
  ⟦ dyn ⟧e = 𝓜.cat .id
  -- The most annoying one because it's not from bifunctoriality, more like separate functoriality
  -- λ f . λ x . x'  <- p x;
  --             y'  <- app(f,x');
  --             η (e y')
  ⟦ c ⇀ d ⟧e     = 𝓜.lda ((𝓜.ClLinear .id ∘⟨ 𝓜.cat ⟩ ⟦ d ⟧e) ∘⟨ 𝓜.ClLinear ⟩
                         𝓜.app ∘⟨ 𝓜.Linear _ ⟩
                         ⟦ c ⟧p ∘⟨ 𝓜.cat ⟩ 𝓜.π₂)
  ⟦ inj-nat ⟧e   = 𝓜.inj ∘⟨ 𝓜.cat ⟩ 𝓜.σ1
  ⟦ inj-arr c ⟧e = 𝓜.inj ∘⟨ 𝓜.cat ⟩ 𝓜.σ2 ∘⟨ 𝓜.cat ⟩ ⟦ c ⟧e

  ⟦ nat ⟧p = 𝓜.ClLinear .id
  ⟦ dyn ⟧p = 𝓜.ClLinear .id
  -- = η ∘ (⟦ c ⟧e ⇒ ⟦ d ⟧p')
  ⟦ c ⇀ d ⟧p     = 𝓜.ClLinear .id ∘⟨ 𝓜.cat ⟩ ⇒F ⟪ ⟦ c ⟧e , ⟦ d ⟧p' ⟫
  ⟦ inj-nat ⟧p   = (𝓜.ClLinear .id 𝓜.|| 𝓜.℧) ∘⟨ 𝓜.ClLinear ⟩ 𝓜.prj
  ⟦ inj-arr c ⟧p = (𝓜.℧ 𝓜.|| ⟦ c ⟧p) ∘⟨ 𝓜.ClLinear ⟩ 𝓜.prj

  ⟦ c ⟧p' = 𝓜.clBind ⟦ c ⟧p

  ⟦_⟧ctx : Ctx → 𝓜.cat .ob
  ⟦ [] ⟧ctx = 𝓜.𝟙
  ⟦ A ∷ Γ ⟧ctx = ⟦ Γ ⟧ctx 𝓜.× ⟦ A ⟧ty

  -- The term syntax
  -- substitutions, values, ev ctxts, terms

  ⟦_⟧S : Subst Δ Γ   → 𝓜.cat [ ⟦ Δ ⟧ctx , ⟦ Γ ⟧ctx ]
  ⟦_⟧V : Val Γ S     → 𝓜.cat [ ⟦ Γ ⟧ctx , ⟦ S ⟧ty ]
  ⟦_⟧E : EvCtx Γ R S → 𝓜.Linear ⟦ Γ ⟧ctx [ ⟦ R ⟧ty  , ⟦ S ⟧ty ]
  ⟦_⟧C : Comp Γ S    → 𝓜.ClLinear        [ ⟦ Γ ⟧ctx , ⟦ S ⟧ty ]

  ⟦ ids ⟧S = 𝓜.cat .id
  ⟦ γ ∘s δ ⟧S = ⟦ γ ⟧S ∘⟨ 𝓜.cat ⟩ ⟦ δ ⟧S
  ⟦ ∘IdL {γ = γ} i ⟧S = 𝓜.cat .⋆IdR ⟦ γ ⟧S i
  ⟦ ∘IdR {γ = γ} i ⟧S = 𝓜.cat .⋆IdL ⟦ γ ⟧S i
  ⟦ ∘Assoc {γ = γ}{δ = δ}{θ = θ} i ⟧S = 𝓜.cat .⋆Assoc ⟦ θ ⟧S ⟦ δ ⟧S ⟦ γ ⟧S i
  ⟦ !s ⟧S = 𝓜.!t
  ⟦ []η {γ = γ} i ⟧S = 𝓜.𝟙η ⟦ γ ⟧S i
  ⟦ γ ,s V ⟧S = ⟦ γ ⟧S 𝓜.,p ⟦ V ⟧V
  ⟦ wk ⟧S = 𝓜.π₁
  ⟦ wkβ {δ = γ}{V = V} i ⟧S = 𝓜.×β₁ {f = ⟦ γ ⟧S}{g = ⟦ V ⟧V} i
  ⟦ ,sη {δ = γ} i ⟧S = 𝓜.×η {f = ⟦ γ ⟧S} i
  ⟦ isSetSubst γ γ' p q i j ⟧S = 𝓜.cat .isSetHom ⟦ γ ⟧S ⟦ γ' ⟧S (cong ⟦_⟧S p) (cong ⟦_⟧S q) i j

  ⟦ V [ γ ]v ⟧V = ⟦ V ⟧V ∘⟨ 𝓜.cat ⟩ ⟦ γ ⟧S
  ⟦ substId {V = V} i ⟧V = 𝓜.cat .⋆IdL ⟦ V ⟧V i
  ⟦ substAssoc {V = V}{δ = δ}{γ = γ} i ⟧V = 𝓜.cat .⋆Assoc ⟦ γ ⟧S ⟦ δ ⟧S ⟦ V ⟧V i
  ⟦ var ⟧V = 𝓜.π₂
  ⟦ varβ {δ = γ}{V = V} i ⟧V = 𝓜.×β₂ {f = ⟦ γ ⟧S}{g = ⟦ V ⟧V} i
  ⟦ zro ⟧V = 𝓜.nat-fp .fst ∘⟨ 𝓜.cat ⟩ 𝓜.σ1 ∘⟨ 𝓜.cat ⟩ 𝓜.!t
  ⟦ suc ⟧V = 𝓜.nat-fp .fst ∘⟨ 𝓜.cat ⟩ 𝓜.σ2 ∘⟨ 𝓜.cat ⟩ 𝓜.π₂
  ⟦ lda M ⟧V = 𝓜.lda ⟦ M ⟧C
  ⟦ fun-η i ⟧V = {!!}
  ⟦ up S⊑T ⟧V = ⟦ S⊑T .ty-prec  ⟧e ∘⟨ 𝓜.cat ⟩ 𝓜.π₂
  ⟦ isSetVal V V' p q i j ⟧V = 𝓜.cat .isSetHom ⟦ V ⟧V ⟦ V' ⟧V (cong ⟦_⟧V p) (cong ⟦_⟧V q) i j

  ⟦ ∙E ⟧E = 𝓜.Linear _ .id
  ⟦ E ∘E F ⟧E = ⟦ E ⟧E ∘⟨ 𝓜.Linear _ ⟩ ⟦ F ⟧E
  ⟦ ∘IdL {E = E} i ⟧E = 𝓜.Linear _ .⋆IdR ⟦ E ⟧E i
  ⟦ ∘IdR {E = E} i ⟧E = 𝓜.Linear _ .⋆IdL ⟦ E ⟧E i
  ⟦ ∘Assoc {E = E}{F = F}{F' = F'} i ⟧E = 𝓜.Linear _ .⋆Assoc ⟦ F' ⟧E ⟦ F ⟧E ⟦ E ⟧E i
  ⟦ E [ γ ]e ⟧E = (𝓜.pull ⟦ γ ⟧S) ⟪ ⟦ E ⟧E ⟫
  ⟦ substId {E = E} i ⟧E = 𝓜.id^* i ⟪ ⟦ E ⟧E ⟫
  ⟦ substAssoc {E = E}{γ = γ}{δ = δ} i ⟧E = 𝓜.comp^* ⟦ γ ⟧S ⟦ δ ⟧S i ⟪ ⟦ E ⟧E ⟫
  ⟦ ∙substDist {γ = γ} i ⟧E = (𝓜.pull ⟦ γ ⟧S) .F-id i
    
  ⟦ ∘substDist {E = E}{F = F}{γ = γ} i ⟧E = 𝓜.pull ⟦ γ ⟧S .F-seq ⟦ F ⟧E ⟦ E ⟧E i
  ⟦ bind M ⟧E = ⟦ M ⟧C
  ⟦ ret-η i ⟧E = {!!}
  ⟦ dn S⊑T ⟧E = ⟦ S⊑T .ty-prec ⟧p ∘⟨ 𝓜.cat ⟩ 𝓜.π₂
  ⟦ isSetEvCtx E F p q i j ⟧E = 𝓜.cat .isSetHom ⟦ E ⟧E ⟦ F ⟧E (cong ⟦_⟧E p) (cong ⟦_⟧E q) i j

  ⟦ E [ M ]∙ ⟧C = (COMP _ 𝓜 ⟪ ⟦ E ⟧E ⟫) ⟦ M ⟧C
  ⟦ plugId {M = M} i ⟧C = (COMP _ 𝓜 .F-id i) ⟦ M ⟧C
  ⟦ plugAssoc {F = F}{E = E}{M = M} i ⟧C = (COMP _ 𝓜 .F-seq ⟦ E ⟧E ⟦ F ⟧E i) ⟦ M ⟧C

  ⟦ M [ γ ]c ⟧C = ⟦ M ⟧C ∘⟨ 𝓜.cat ⟩ ⟦ γ ⟧S
  ⟦ substId {M = M} i ⟧C = 𝓜.cat .⋆IdL ⟦ M ⟧C i
  ⟦ substAssoc {M = M}{δ = δ}{γ = γ} i ⟧C = 𝓜.cat .⋆Assoc ⟦ γ ⟧S ⟦ δ ⟧S ⟦ M ⟧C i
  ⟦ substPlugDist {E = E}{M = M}{γ = γ} i ⟧C = COMP-Enriched 𝓜 ⟦ γ ⟧S ⟦ M ⟧C ⟦ E ⟧E i
  ⟦ err ⟧C = 𝓜.℧
  ⟦ strictness {E = E} i ⟧C = 𝓜.℧-homo ⟦ E ⟧E {!i!}

  ⟦ ret ⟧C = 𝓜.Linear _ .id
  ⟦ ret-β i ⟧C = {!!}

  ⟦ app ⟧C = {!!}
  ⟦ fun-β i ⟧C = {!!}

  ⟦ matchNat Mz Ms ⟧C = {!!}
  ⟦ matchNatβz Mz Ms i ⟧C = {!!}
  ⟦ matchNatβs Mz Ms V i ⟧C = {!!}
  ⟦ matchNatη i ⟧C = {!!}

  ⟦ isSetComp M N p q i j ⟧C = 𝓜.cat .isSetHom ⟦ M ⟧C ⟦ N ⟧C (cong ⟦_⟧C p) (cong ⟦_⟧C q) i j
