{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.GuardedResults.LaterAndExists where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation renaming (rec to PTrec)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Common.ClockProperties

private
  variable
    ℓ ℓ'  : Level


not-∀k-later-⊥ : ¬ (∀ (k : Clock) → ▹ k , ⊥)
not-∀k-later-⊥ H = let ∀k⊥ = force' H in ∀k⊥ k0

∀k-not-not-later-⊥ : ∀ (k : Clock) → ¬ (¬ (▹ k , ⊥))
∀k-not-not-later-⊥ k H = fix (λ ⊥~ → H ⊥~)


module _ (k : Clock) where

  private
    ▹_ : Type ℓ → Type ℓ
    ▹ A = ▹_,_ k A

  module _ (X : Type ℓ) (Y : X → Type ℓ') where
    later-exists→exists-later : Type (ℓ-max ℓ ℓ')
    later-exists→exists-later = (▹ (∃[ x ∈ X ] (Y x))) → ∃[ x~ ∈ ▹ X ] (▸ (λ t → Y (x~ t)))


  later-exists-unit : later-exists→exists-later ⊤ (λ _ → ⊤)
  later-exists-unit x = ∣ next tt , next tt ∣₁

  later-exists-lemma : ¬ (∀ (X : Type ℓ) (Y : X → Type ℓ') → later-exists→exists-later X Y)
  later-exists-lemma H = {!H ⊥* (λ _ → ⊥*)!}




  
