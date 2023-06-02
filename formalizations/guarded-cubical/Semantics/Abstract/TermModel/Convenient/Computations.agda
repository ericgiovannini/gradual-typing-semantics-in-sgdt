{-# OPTIONS --cubical #-}
module Semantics.Abstract.TermModel.Convenient.Computations where

-- Computations form a covariant presheaf on evaluation contexts

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Monad.ExtensionSystem
open import Cubical.Categories.Monad.Strength.Cartesian.ExtensionSystem
open import Cubical.Categories.Comonad.Instances.Environment

open import Semantics.Abstract.TermModel.Convenient

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open BinCoproduct
open BinProduct

module _ (𝓜 : Model ℓ ℓ') where
  open Model 𝓜
  open StrongExtensionSystem
  COMP : ∀ Γ → Functor (Linear Γ) (SET ℓ')
  COMP Γ .F-ob a = (ClLinear [ Γ , a ]) , cat .isSetHom
  COMP Γ .F-hom E M = bind E ∘⟨ cat ⟩ (cat .id ,p M)
  COMP Γ .F-id = funExt λ M → cong₂ (comp' cat) (ExtensionSystemFor.bind-r (monad .systems Γ)) refl ∙ ×β₂
  COMP Γ .F-seq f g = funExt (λ M → cong₂ (cat ._⋆_) refl (sym (ExtensionSystemFor.bind-comp (monad .systems Γ)))
    ∙ sym (cat .⋆Assoc _ _ _) ∙ cong₂ (comp' cat) refl (,p-natural ∙ cong₂ _,p_ ×β₁ refl) )

  COMP-Enriched : ∀ {Δ Γ a b} (γ : cat [ Δ , Γ ]) (M : ⟨ COMP Γ ⟅ a ⟆ ⟩) (E : Linear Γ [ a , b ])
                → (COMP Γ ⟪ E ⟫) M ∘⟨ cat ⟩ γ ≡ (COMP Δ ⟪ (γ ^*) ⟪ E ⟫ ⟫) (M ∘⟨ cat ⟩ γ)
  COMP-Enriched γ M E =
    sym (⋆Assoc cat _ _ _)
    ∙ cong₂ (comp' cat) refl ((,p-natural ∙ cong₂ _,p_ (cat .⋆IdR _ ∙ (sym (cat .⋆IdL _) ∙ cong₂ (comp' cat) refl (sym ×β₁)) ∙ cat .⋆Assoc _ _ _) (sym ×β₂)) ∙ sym ,p-natural)
    ∙ ⋆Assoc cat _ _ _
    ∙ cong₂ (seq' cat) refl (bind-natural monad)
