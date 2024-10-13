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
open import Cubical.Data.Sigma

open import Common.Later
open import Common.ClockProperties
open import Semantics.GlobalLift
open import Semantics.Concrete.Predomain.Error

open import Semantics.Concrete.GuardedLift using (mapL ; unfold-mapL)
open import Semantics.Concrete.GuardedLiftError hiding (mapL)
open import Semantics.Concrete.LockStepErrorOrdering
open import Semantics.Concrete.WeakBisimilarity

open import Semantics.Partial
open import Semantics.BigStepFunction
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
  public

-- The globalized definitions of weak bisimilarity and lock-step error
-- ordering for ℕ:

_≈L℧ℕ^gl_ : L℧^gl ℕ → L℧^gl ℕ → Type
_≈L℧ℕ^gl_ ln ln' = ∀ (k : Clock) →
  LiftBisim._≈_ k (Error ℕ) (≈ErrorX _≡_) (ln k) (ln' k)

_⊑L℧ℕ^gl_ : L℧^gl ℕ → L℧^gl ℕ → Type
_⊑L℧ℕ^gl_ ln lm = ∀ (k : Clock) →
  LiftOrdHomogenous._⊑_ k ℕ _≡_ (ln k) (lm k)


-- The big-step term semantics for L^gl (ℕ ⊎ ⊤)
open BigStep (ℕ ⊎ ⊤) (⊎-clock-irrel nat-clock-irrel Unit-clock-irrel) public

-- The ordering relation on partial elements of type ℕ ⊎ ⊤
open ErrorOrdPartial _X≈⊑≈Y_ public

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


  nat-adequate : ⟦ l1 ⟧partial ≤part ⟦ l2 ⟧partial --⟦ l1 ⟧ ≾ ⟦ l2 ⟧
  nat-adequate = extensional-adequacy l1 l1' l2' l2
  
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


  -- A simpler definition of relation on partial elements of type (ℕ ⊎ ⊤).
  -- Here, the relation on values is simply equality rather than the
  -- bisimilarity closure which is equivalent to the original definition
  -- because bisimilarity for ℕ is just equality.
  _≤partNat_ : Part (ℕ ⊎ ⊤) ℓ-zero → Part (ℕ ⊎ ⊤) ℓ-zero → Type ℓ-zero
  px ≤partNat py = ErrorOrdPartial._≤part_ _≡_ px py

  private
    Rel→ResultRel-lem : ∀ {X : Type ℓ} {Y : Type ℓ'} (R S : X → Y → Type ℓR) →
      (∀ x y → R x y → S x y) →
      (∀ x? y? → Rel→ResultRel R x? y? → Rel→ResultRel S x? y?)
    Rel→ResultRel-lem R S R→S (inl x) (inl y) H = R→S x y H
    Rel→ResultRel-lem R S R→S (inr tt) y? H = tt*

    ≡-closure→≡ : ∀ n m → n X≈⊑≈Y m → n ≡ m
    ≡-closure→≡ n m (n' , m' , n≡n' , n'≡m' , m'≡m) = n≡n' ∙ n'≡m' ∙ m'≡m

  ≤part→≤partNat : (px py : Part (ℕ ⊎ ⊤) ℓ-zero) →
    px ≤part py → px ≤partNat py
  ≤part→≤partNat px py (fact1 , fact2) .fst a with (result px a) | (fact1 a)
  ... | inl n | (b , H-related) = b ,
    (Rel→ResultRel-lem _ _ ≡-closure→≡ _ _ H-related)
      
  ... | inr tt | s = tt*
  
  ≤part→≤partNat px py (fact1 , fact2) .snd b with (fact2 b)
  ... | (a , H-related) = a , (Rel→ResultRel-lem _ _ ≡-closure→≡ _ _ H-related)
