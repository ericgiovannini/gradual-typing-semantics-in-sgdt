{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

module Semantics.AdequacyLiftNat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport -- pathToIso
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Relation.Binary
open import Cubical.Data.Nat hiding (_^_ ; _+_)
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)

open import Common.Later
open import Common.ClockProperties
open import Semantics.GlobalLift
open import Semantics.Concrete.DoublePoset.Error

open import Semantics.Concrete.GuardedLift using (mapL ; unfold-mapL)
open import Semantics.Concrete.GuardedLiftError hiding (mapL)
open import Semantics.Concrete.LockStepErrorOrdering
open import Semantics.Concrete.WeakBisimilarity

open import Semantics.CombinedAdequacy


private
  variable
    ℓ ℓ' ℓR : Level
    ℓ≈X ℓ≈Y ℓ⊑ : Level


-- Definition of global Lift + Error.
L℧^gl : (X : Type ℓ) -> Type ℓ
L℧^gl X = ∀ (k : Clock) -> L℧ k X

-- Adequacy result specialized to natural numbers:

open Result

  -- Underlying sets
  ℕ isSetℕ nat-clock-irrel ℕ isSetℕ nat-clock-irrel

  -- Bisim relations + properties
  (_≡_) isSetℕ (λ n m → path-clock-irrel nat-clock-irrel)
  (_≡_) isSetℕ (λ n m → path-clock-irrel nat-clock-irrel)

  -- Ordering relation
  _≡_ (λ n m → path-clock-irrel nat-clock-irrel)


-- The globalized definitions of weak bisimilarity and lock-step error
-- ordering for ℕ:

_≈L℧ℕ^gl_ : L℧^gl ℕ → L℧^gl ℕ → Type
_≈L℧ℕ^gl_ ln ln' = ∀ (k : Clock) →
  LiftBisim._≈_ k (Error ℕ) (≈ErrorX _≡_) (ln k) (ln' k)

_⊑L℧ℕ^gl_ : L℧^gl ℕ → L℧^gl ℕ → Type
_⊑L℧ℕ^gl_ ln lm = ∀ (k : Clock) →
  LiftOrdHomogenous._⊑_ k ℕ _≡_ (ln k) (lm k)


module _
  (ln ln' lm' lm : L℧^gl ℕ)
  (ln≈ln'  : ln  ≈L℧ℕ^gl ln')
  (ln'⊑lm' : ln' ⊑L℧ℕ^gl lm')
  (lm'≈lm  : lm' ≈L℧ℕ^gl lm)
  where

  -- Convert from L℧ ℕ to L (ℕ ⊎ ⊤):
  convert : L^gl (Error ℕ) → L^gl (ℕ ⊎ ⊤)
  convert lx k = mapL k ErrorX→X⊎⊤ (lx k)
  
  l1 : L^gl (ℕ ⊎ ⊤)
  l1 = convert ln

  l1' : L^gl (ℕ ⊎ ⊤)
  l1' = convert ln'

  l2' : L^gl (ℕ ⊎ ⊤)
  l2' = convert lm'

  l2 : L^gl (ℕ ⊎ ⊤)
  l2 = convert lm


  -- Lastly, when applying the adequacy theorem, we convert from the
  -- globalization of the original definitions of the relations to the
  -- globalization of the versions as sum types.
  
  nat-adequate : LS.⟦ l1 ⟧x ≾ LS.⟦ l2 ⟧y
  nat-adequate = final-adequacy-theorem l1 l1' l2' l2
  
    (λ k → ≈→≈Sum k (ℕ ⊎ ⊤) (Sum≈ ℕ _≡_) (l1 k) (l1' k)
      (L-map-preserves-bisim k (Error ℕ) (≈ErrorX _≡_) (ℕ ⊎ ⊤)
        (Sum≈ ℕ _≡_) (Sum≈-sym ℕ _≡_ (λ _ _ eq → sym eq)) (Sum≈-prop-valued ℕ _≡_ isSetℕ)
        ErrorX→X⊎⊤ (≈Error→≈⊎ _≡_) (ln k) (ln' k) (ln≈ln' k)))
        
    (λ k → ⊑→⊑S k ℕ ℕ _≡_ k (ln' k) (lm' k) (ln'⊑lm' k))
    
    (λ k → ≈→≈Sum k (ℕ ⊎ ⊤) (Sum≈ ℕ _≡_) (l2' k) (l2 k)
      ((L-map-preserves-bisim k (Error ℕ) (≈ErrorX _≡_) (ℕ ⊎ ⊤)
        (Sum≈ ℕ _≡_) (Sum≈-sym ℕ _≡_ (λ _ _ eq → sym eq)) (Sum≈-prop-valued ℕ _≡_ isSetℕ)
        ErrorX→X⊎⊤ (≈Error→≈⊎ _≡_) (lm' k) (lm k) (lm'≈lm k))))


-- (Bisim.≈ k (ℕ ⊎ ⊤)) (Sum≈ ℕ _≡_) (l1 k) (l1' k)
-- LR.⊑ ℕ k ℕ _≡_ k (ln' k) (lm' k)
