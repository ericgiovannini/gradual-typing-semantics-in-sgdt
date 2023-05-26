{-# OPTIONS --cubical #-}
module Semantics.Abstract.TermModel.Strength where

{- Strength of a functor between *cartesian* categories -}

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
