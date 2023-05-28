{-# OPTIONS --cubical --lossy-unification #-}
module Semantics.Abstract.TermModel.Strength.KleisliSlice where

{- Given a strong monad on a cartesian category and a fixed object Γ,
we get a paramaterized version of the Kleisli category -}

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Monad.Base

open import Cubical.Categories.Limits.BinProduct.More
open import Semantics.Abstract.TermModel.Strength

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open BinProduct
open IsMonad

--
module _ (C : Category ℓ ℓ') (term : Terminal C) (bp : BinProducts C) (T : Monad C) (s : Strength C term bp T) where
  module C = Category C
  open Notation C bp
  open StrengthNotation C term bp T s
  module _ (Γ : C .ob) where
    KleisliSlice : Category ℓ ℓ'
    KleisliSlice .ob = C .ob
    KleisliSlice .Hom[_,_] a b = C [ Γ × a , T .fst ⟅ b ⟆ ]
    KleisliSlice .id = T .snd .η .N-ob _ C.∘ π₂
    -- Γ , x → T y    |-> 
    -- Γ , y → T z
    --------------
    -- Γ , x → T z
    KleisliSlice ._⋆_ f g = bind (T .snd) .N-ob _ g C.∘ σ .N-ob _ C.∘ (π₁ ,p f)
    -- bind (T .snd) .N-ob _ g C.∘ σ .N-ob _ C.∘ (π₁ ,p T .snd .η .N-ob _ C.∘ π₂)
    --
    -- μ ∘ T g ∘ σ ∘ (π1 , η ∘ π₂)
    -- μ ∘ T g ∘ σ ∘ (id × η)
    -- μ ∘ T g ∘ η
    -- μ ∘ η ∘ g
    -- ≡ g
    KleisliSlice .⋆IdL g =
      cong₂ C._∘_ refl (cong₂ C._∘_ refl (cong₂ _,p_ (sym (C.⋆IdR _)) refl) ∙ (λ i → strength-η (~ i) _ _))
      ∙ sym (C.⋆Assoc _ _ _)
      ∙ cong₂ C._∘_ refl (sym (T .snd .η .N-hom _))
      ∙ C.⋆Assoc _ _ _
      ∙ cong (C._∘ g) (λ i → T .snd .idl-μ i .N-ob _)
      ∙ C.⋆IdR g
    -- μ ∘ T (T η ∘ π₂) ∘ σ ∘ (π₁ , f)
    -- μ ∘ T^2 η ∘ T π₂ ∘ σ ∘ (π₁ , f)
    -- T η ∘ μ ∘ T π₂ ∘ σ ∘ (π₁ , f)
    -- T π₂ ∘ σ ∘ (π₁ , f)
    -- ≡ f
    KleisliSlice .⋆IdR f = {!!}
    KleisliSlice .⋆Assoc = {!!}
    KleisliSlice .isSetHom = C.isSetHom

  module _ {Δ : C .ob} {Γ : C .ob} where
    _^* : (γ : C [ Δ , Γ ]) → Functor (KleisliSlice Γ) (KleisliSlice Δ)
    (γ ^*) .F-ob a = a
    (γ ^*) .F-hom f = f C.∘ (γ ×p C.id)
    (γ ^*) .F-id = sym (C.⋆Assoc _ _ _) ∙ cong₂ C._⋆_ (×β₂ ∙ C .⋆IdR π₂) refl
    (γ ^*) .F-seq f g = {!!}
