{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Common
open import Common.Later

module Semantics.LiftNegativeResults (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma

open import Common.Common
open import Common.LaterProperties

open import Semantics.Lift k



private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ
private
  ▹_ : Set ℓ → Set ℓ
  ▹_ A = ▹_,_ k A




module _ (X : Type ℓ) (lx0 ly0 : L X) (lx0≠ly0 : ¬ (lx0 ≡ ly0)) where

  -- We can show that δ : L X → L X is *not* injective provided that there
  -- are at least two distinct elements of L X.
  ¬inj-helper :
    ¬ (∀ (lx ly : L X) → δL lx ≡ δL ly → lx ≡ ly)
  ¬inj-helper contra = lx0≠ly0 (fix aux)
    where
      aux : ▹ (lx0 ≡ ly0) → (lx0 ≡ ly0)
      aux H = contra lx0 ly0 (cong L.θ (▹≡→next≡ lx0 ly0 H))



module _ (X : Type ℓ) (x0 : X) where

  -- δ : L X → L X is *not* injective, provided there is at least one element x0 of X.
  -- This follows from the above result because we have η x0 ≠ δ (η x0), giving us
  -- two distinct elements of L X.
  ¬inj-δ :
    ¬ (∀ (lx ly : L X) → δL lx ≡ δL ly → lx ≡ ly)
  ¬inj-δ contra = ¬inj-helper X (η x0) (δL (η x0)) Lη≠Lθ contra



-- It suffices to establish that δ is injective *on η* to derive a contradiction.
¬inj-δL' : {X : Type ℓ} →
  (x y : X) → ¬ (x ≡ y) →
  ¬ (∀ (x' y' : X) → δL (η x') ≡ δL (η y') → (L.η x') ≡ (L.η y'))
¬inj-δL' {X = X} x y x≠y contra = x≠y (fix aux)
  where
    aux : ▹ (x ≡ y) → (x ≡ y)
    aux H = inj-ηL x y (contra x y (cong L.θ (▹≡→next≡ (η x) (η y) later-ηx≡ηy)))
      where
        later-ηx≡ηy : ▹ (η x ≡ η y)
        later-ηx≡ηy = (λ t → cong η (H t))


-- The "termination predicate" on L X where we use Σ types for the quantification
-- is provably *not* a Prop.
¬isProp-terminates : {X : Type ℓ} →
  (x y : X) → ¬ (x ≡ y) →
  ¬ (∀ l → (isProp (Σ[ n ∈ ℕ ] Σ[ z ∈ X ] l ≡ (δL {X = X} ^ n) (L.η z))))
¬isProp-terminates {X = X} x y x≠y H = ¬inj-δL' x y x≠y aux
  where
    -- We show that δ is injective on η by appealing to the assumption that the Sigma
    -- type is a prop. But we know that δ is not injective on η by the above
    -- lemma, so we can use this to prove false.
    aux : (x' y' : X) → δL (η x') ≡ δL (η y') → η x' ≡ η y'
    aux x' y' eq =
      let eqSigma = H (δL (η x')) (1 , x' , refl) (1 , y' , eq) in
      cong L.η (cong (fst ∘ snd) eqSigma)








-----------------------------------------------------------------------------

-- Older code:

-- We can prove that the delay function δ : L X → L X is *not*
-- injective, provided there are at least two distinct elements of X.
¬inj-δL : {X : Type ℓ} → (x y : X) → ¬ (x ≡ y) →
  ¬ (∀ (lx ly : L X) → δL lx ≡ δL ly → lx ≡ ly)
¬inj-δL x y x≠y contra = x≠y (fix aux)
  where
    aux : ▹ (x ≡ y) → (x ≡ y)
    aux H = inj-ηL x y (contra _ _ (cong L.θ (▹≡→next≡ _ _ later-ηx≡ηy)))
      where
        later-ηx≡ηy : ▹ (η x ≡ η y)
        later-ηx≡ηy = (λ t → cong η (H t))


-- Idea:
-- Let lx and ly be such that lx ≠ ly
-- (e.g. let x and y s.t. x ≠ y and let lx = η x and ly = η y).
--
-- ▹ (lx ≡ ly)               [assumption]
-- next lx ≡ next ly         [by later extensionality]
-- θ (next lx) ≡ θ (next ly) [congruence]
-- lx ≡ ly                   [assumption]
-- Contradiction!

