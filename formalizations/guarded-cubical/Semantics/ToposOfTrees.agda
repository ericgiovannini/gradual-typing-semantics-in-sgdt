{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Common
open import Common.Later

module Semantics.ToposOfTrees (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty hiding (rec; elim)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum hiding (elim)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat hiding (_^_; elim)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

open import Common.Common
open import Common.LaterProperties

open import Semantics.Lift k

private
  variable
    ℓ ℓ' : Level
    X A B C : Type ℓ
private
  ▹_ : Set ℓ → Set ℓ
  ▹_ A = ▹_,_ k A


postulate
  n→▹^n⊥ : ∃[ n ∈ ℕ ] (▹_ ^ n) ⊥


foo : {X : Type ℓ} → ∀ (l : L℧ X) →
  l ≡ fix θ → ∃[ n ∈ ℕ ] ∃[ x ∈ X ] l ≡ (δ ^ n) (η x)

foo l l≡fixθ = elim (λ _ → isPropPropTrunc) (λ n → {!!}) {!!}





