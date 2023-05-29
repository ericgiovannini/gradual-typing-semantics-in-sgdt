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
module _ (C : Category ℓ ℓ') (term : Terminal C) (bp : BinProducts C) (T : Monad C) (s : Strength C bp T) where
  module C = Category C
  open Notation C bp
  open StrengthNotation C bp T s
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
    KleisliSlice .⋆IdR f =
    -- μ ∘ T (η ∘ π₂) ∘ σ ∘ (π₁ , f)
      cong₂ C._∘_ (cong₂ C._∘_ refl (T .fst .F-seq _ _)) refl
    -- μ ∘ T η ∘ T π₂ ∘ σ ∘ (π₁ , f)
      ∙ cong₂ C._∘_ (C .⋆Assoc _ _ _) refl
      ∙ cong₂ C._∘_ (cong₂ C._∘_ (λ i → T .snd .idr-μ i .N-ob _) refl) refl
      ∙ cong₂ C._∘_ (C .⋆IdR _) refl
    -- T π₂ ∘ σ ∘ (π₁ , f)
      ∙ C .⋆Assoc _ _ _
      ∙ cong₂ C._∘_ (λ i → strength-𝟙 (~ i) _ _) refl
    -- π₂ ∘ (π₁ , f)
      ∙ ×β₂
    -- ≡ f

    -- μ ∘ T h ∘ σ ∘ (π₁ , μ ∘ T g ∘ σ ∘ (π1 , f))
    -- μ ∘ T h ∘ σ ∘ (π₁ ∘ (π₁ , T g ∘ σ ∘ (π1 , f)) , μ ∘ π₂ ∘ (π₁ , T g ∘ σ ∘ (π1 , f)))
    -- μ ∘ T h ∘ σ ∘ (id ∘ π1 , μ ∘ π2) ∘ (π₁ , T g ∘ σ ∘ (π1 , f))
    -- μ ∘ T h ∘ σ ∘ (id × μ) ∘ (π₁ , T g ∘ σ ∘ (π1 , f))
    -- μ ∘ T h ∘ μ ∘ T σ ∘ σ ∘ (π₁ , T g ∘ σ ∘ (π1 , f))

    -- μ ∘ T h ∘ μ ∘ T σ ∘ σ ∘ T (π₁ , g) ∘ σ ∘ (π1 , f)
    -- μ ∘ T h ∘ μ ∘ T σ ∘ T (π₁ , g) ∘ σ ∘ (π1 , f)
    -- μ ∘ μ ∘ T^2 h ∘ T σ ∘ T (π₁ , g) ∘ σ ∘ (π1 , f)
    -- μ ∘ T μ ∘ T^2 h ∘ T σ ∘ T (π₁ , g) ∘ σ ∘ (π1 , f)
    -- μ ∘ T (μ ∘ T h ∘ σ ∘ (π₁ , g)) ∘ σ ∘ (π1 , f)
    KleisliSlice .⋆Assoc f g h = {!!}
    KleisliSlice .isSetHom = C.isSetHom

  module _ {Δ : C .ob} {Γ : C .ob} where
    _^* : (γ : C [ Δ , Γ ]) → Functor (KleisliSlice Γ) (KleisliSlice Δ)
    (γ ^*) .F-ob a = a
    (γ ^*) .F-hom f = f C.∘ (γ ×p C.id)
    (γ ^*) .F-id = sym (C.⋆Assoc _ _ _) ∙ cong₂ C._⋆_ (×β₂ ∙ C .⋆IdR π₂) refl
    -- T (γ × V) ∘ σ ≡ σ ∘ (γ × T V)

    (γ ^*) .F-seq f g =
    -- μ ∘ T g ∘ σ ∘ (π₁ , f) ∘ (γ ∘ π₁ , id ∘ π₂)
      sym (C .⋆Assoc _ _ _)
      ∙ cong₂ C._∘_ refl (sym (C .⋆Assoc _ _ _))
      ∙ cong₂ C._∘_ refl (cong₂ C._∘_ refl (,p-natural
                                           ∙ cong₂ _,p_ ×β₁ (sym (C .⋆IdR _) ∙ cong₂ C._∘_ (sym (T .fst .F-id)) refl)))
    -- ≡ μ ∘ T g ∘ σ ∘ (π₁ ∘ (γ ∘ π₁ , id ∘ π₂) , f ∘ (γ ∘ π₁ , id ∘ π₂))
    -- ≡ μ ∘ T g ∘ σ ∘ (γ ∘ π₁ , T id ∘ f ∘ (γ ∘ π₁ , id ∘ π₂))
      ∙ {!!}
    -- ≡ μ ∘ T g ∘ σ ∘ (γ ∘ π₁ , T id ∘ π₂) ∘ (π₁ , f ∘ (γ ∘ π₁ , id ∘ π₂))
    -- ≡ μ ∘ T g ∘ σ ∘ (γ × T id) ∘ (π₁ , f ∘ (γ ∘ π₁ , id ∘ π₂))
    --
    -- Problem: naturality of σ isn't behaving correctly because of some stuff we did...
      ∙ cong₂ C._∘_ refl (cong₂ C._∘_ refl (cong₂ C._∘_ ({!σ .N-hom ?!}) refl ∙ sym (C .⋆Assoc _ _ _))
                         ∙ C .⋆Assoc _ _ _)
      ∙ C .⋆Assoc _ _ _
    -- ≡ μ ∘ T g ∘ T (γ × id) ∘ σ ∘ (π₁ , f ∘ (γ ∘ π₁ , id ∘ π₂))
      ∙ cong₂ C._∘_ (cong₂ C._∘_ refl (sym (T .fst .F-seq _ _))) refl
    -- ≡ μ ∘ T (g ∘ (γ ∘ π₁ , id ∘ π₂)) ∘ σ ∘ (π₁ , f ∘ (γ ∘ π₁ , id ∘ π₂))
