{-# OPTIONS --cubical #-}
module Semantics.Abstract.TermModel.Strength where

{- Strength of a monad an a *cartesian* category -}
{- TODO: generalize to monoidal -}

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Monad.Base

open import Cubical.Categories.Limits.BinProduct.More

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open BinProduct

module _ (C : Category ℓ ℓ') (term : Terminal C) (bp : BinProducts C) (T : Monad C) where
  -- A is a kind of "lax equivariance"
  -- A × T B → T (A × B)
  StrengthTrans = NatTrans {C = C ×C C} {D = C} (BinProductF C bp ∘F (Id {C = C} ×F T .fst )) (T .fst ∘F BinProductF C bp)

  module _ (σ : StrengthTrans) where
    open Notation _ bp

    -- This says the strength interacts well with the unitor
    StrengthUnitor : Type _
    StrengthUnitor = (λ (a : C .ob) → π₂ {term .fst} {T .fst ⟅ a ⟆}) ≡ λ a → σ .N-ob ((term .fst) , a) ⋆⟨ C ⟩ T .fst ⟪ π₂ ⟫

    -- This says the strength interacts well with the associator
    StrengthAssoc : Type _
    StrengthAssoc = -- This one is nicer to express as a square along two isos
              (λ (a b c : C .ob) → C .id {a} ×p σ .N-ob (b , c) ⋆⟨ C ⟩ σ .N-ob (a , (b × c)))
              ≡ λ a b c → ((π₁ ,p (π₁ ∘⟨ C ⟩ π₂)) ,p (π₂ ∘⟨ C ⟩ π₂)) ⋆⟨ C ⟩ σ .N-ob ((a × b) , c) ⋆⟨ C ⟩ T .fst ⟪ (π₁ ∘⟨ C ⟩ π₁) ,p ((π₂ ∘⟨ C ⟩ π₁) ,p π₂) ⟫

    open IsMonad
    -- This says the strength interacts well with the unit
    StrengthUnit : Type _
    StrengthUnit = (λ (a b : C .ob) → T .snd .η .N-ob (a × b)) ≡ λ a b → (C .id ×p T .snd .η .N-ob b) ⋆⟨ C ⟩ σ .N-ob _

    StrengthMult : Type _
    StrengthMult =
      (λ (a b : C .ob) → σ .N-ob (a , (T .fst ⟅ b ⟆)) ⋆⟨ C ⟩ T .fst ⟪ σ .N-ob (a , b) ⟫ ⋆⟨ C ⟩ T .snd .μ .N-ob _)
      ≡ λ a b → C .id ×p T .snd .μ .N-ob _ ⋆⟨ C ⟩ σ .N-ob (a , b)

  open import Cubical.Data.Sigma
  Strength : Type _
  Strength = Σ[ σ ∈ StrengthTrans ] (StrengthUnitor σ × (StrengthAssoc σ × (StrengthUnit σ × StrengthMult σ)))

  -- The reason strength is useful is because we get "strong bind"
  -- C [ Γ × a , T b ] → C [ Γ , T a ] → C [ Γ , T b ]
  module StrengthNotation (str : Strength) where
    open Notation _ bp renaming (_×_ to _×c_)
    σ = str .fst


    strength-η : StrengthUnit σ
    strength-η = str .snd .snd .snd .fst

    strength-μ : StrengthMult σ
    strength-μ = str .snd .snd .snd .snd

    -- TODO: move this upstream in Monad.Notation
    _∘k_ : ∀ {a b c} → C [ b , T .fst ⟅ c ⟆ ] → C [ a , T .fst ⟅ b ⟆ ] → C [ a , T .fst ⟅ c ⟆ ]
    f ∘k g = (IsMonad.bind (T .snd)) .N-ob _ f ∘⟨ C ⟩ g

    strong-bind : ∀ {Γ a b} → C [ Γ ×c a , T .fst ⟅ b ⟆ ] → C [ Γ , T .fst ⟅ a ⟆ ] → C [ Γ , T .fst ⟅ b ⟆ ]
    strong-bind f m = f ∘k σ .N-ob _ ∘⟨ C ⟩ (C .id ,p m)

    _∘sk_ = strong-bind
    -- TODO: lemma for how strength interacts with bind
