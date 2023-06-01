module Semantics.Abstract.TermModel.Convenient.Linear.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monad.Strength.Cartesian
open import Cubical.Categories.Monad.Kleisli
open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.BiKleisli.Base
open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.BiKleisli.Morphism
open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.BiKleisli.Morphism.Properties
open import Cubical.Categories.Comonad.Instances.Environment

open import Semantics.Abstract.TermModel.Convenient
open import Semantics.Abstract.TermModel.Convenient.Linear
private
  variable
    ℓ ℓ' : Level

module StrengthLemmas (𝓜 : Model ℓ ℓ') where
  open Model 𝓜
  open Category cat
  open Functor
  open StrengthNotation 𝓜

  private
    variable
      Γ Δ a b c : ob
      γ δ : Hom[ Δ , Γ ]
      E : Linear Γ [ a , b ]
  id^* : (id ^*) ⟪ E ⟫ ≡ E
  id^* {E = E} = cong₂ _∘_ refl (×pF .F-id) ∙ ⋆IdL _

  comp^* : ((γ ∘ δ) ^*) ⟪ E ⟫ ≡ ((δ ^*) ⟪ ((γ ^*) ⟪ E ⟫) ⟫)
  comp^* {E = E} =
    cong₂ _∘_ refl (cong₂ _,p_ (sym (⋆Assoc _ _ _) ∙ cong₂ _∘_ refl (sym ×β₁) ∙ ⋆Assoc _ _ _)
                               (sym ×β₂ ∙ cong₂ _∘_ (sym (⋆IdR _)) refl)
                   ∙ sym ,p-natural)
    ∙ (⋆Assoc _ _ _)
