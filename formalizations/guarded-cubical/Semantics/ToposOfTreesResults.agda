{-# OPTIONS --cubical --rewriting --guarded #-}

open import Common.Later

module Semantics.ToposOfTreesResults (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty hiding (rec; elim)
open import Cubical.Data.Nat hiding (_^_; elim)
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary

import Cubical.HITs.PropositionalTruncation as PT
open PT using (∣_∣₁)


private
  variable
    ℓ ℓ' ℓR : Level
private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


-- Iterated function application.
_^_ : {ℓ : Level} -> {A : Type ℓ} -> (A -> A) -> ℕ -> A -> A
f ^ zero = λ x → x
f ^ suc n = f ∘ (f ^ n)


-- This axiom forces our model to be the topos of trees.
postulate
  ∃n▹^n⊥ : ∃[ n ∈ ℕ ] (▹_ ^ n) ⊥


-----------------------------------------------------
-------------------- Definitions --------------------
-----------------------------------------------------

-- The guarded Lift monad.
data L (X : Type ℓ) : Type ℓ where
  η : X -> L X
  θ : ▹ (L X) -> L X

-- The delay function on Lift.
δL : {X : Type ℓ} -> L X -> L X
δL = θ ∘ next


-- Prop-valued weak bisimilarity on Lift X.
module WeakBisim (X : Type ℓ) (R : X → X → Type ℓR) where

  data _≈I_ : L X → L X → Type (ℓ-max ℓ ℓR) where
    ≈ηη : ∀ {x y : X} →
      R x y →
      (η x) ≈I (η y)
      
    ≈ηθ : ∀ {x y : X} {n : ℕ} →
      R x y →
      (η x) ≈I ((δL ^ suc n) (η y))
      
    ≈θη : ∀ {x y : X} {n : ℕ} →
      R x y →
      ((δL ^ suc n) (η x)) ≈I (η y)
      
    ≈θθ : ∀ {lx~ ly~ : ▹ L X} →
      ▸ (λ t → (lx~ t) ≈I (ly~ t)) →
      (θ lx~) ≈I (θ ly~)

    is-prop : ∀ lx ly → isProp (lx ≈I ly)


-------------------------------------------------
-------------------- Results --------------------
-------------------------------------------------

-- For all n, if ▹^n ⊥ holds, then fix θ = (δL ^ n)(η x) for any x : X.
later-n-⊥→fixθ-term : {X : Type ℓ} →
  ∀ n → (▹_ ^ n) ⊥ → ∀ (x : X) → fix θ ≡ (δL ^ n) (η x)
later-n-⊥→fixθ-term (suc n) contra x =
  fix-eq θ ∙ congS θ (▹≡→next≡ _ _ (λ t → later-n-⊥→fixθ-term n (contra t) x))


-- The property of terminating with a value is trivial in that (fix θ)
-- terminates with x for any x : X.
term-trivial : {X : Type ℓ} → (x : X) →
  ∃[ n ∈ ℕ ] fix θ ≡ (δL ^ n) (η x)
term-trivial x =
  PT.rec PT.isPropPropTrunc (λ (n , ⊥n) → ∣ n , later-n-⊥→fixθ-term n ⊥n x ∣₁) ∃n▹^n⊥


-- If weak bisimilarity on Lift X is prop-valued, then we can show
-- that it is trivial in that (fix θ) ≈ (η x) for any x : X.
module _ (X : Type ℓ) (R : X → X → Type ℓR)
         (isReflR : BinaryRelation.isRefl R) where

  open WeakBisim X R

  bisim-trivial : (x : X) → (fix θ) ≈I (η x)
  bisim-trivial x = PT.rec (is-prop (fix θ) (η x)) (λ (n , ⊥n) → lem n ⊥n) ∃n▹^n⊥
    where
      lem : (m : ℕ) → (⊥m : (▹_ ^ m) ⊥) → fix θ ≈I η x
      lem (suc m) ⊥m = transport (λ i → sym eq i ≈I η x) (≈θη {n = m} (isReflR x))
        where
           eq : fix θ ≡ (δL ^ (suc m)) (η x)
           eq = later-n-⊥→fixθ-term (suc m) ⊥m x

