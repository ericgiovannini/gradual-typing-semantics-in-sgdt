{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}



open import Common.Later

module Semantics.Concrete.DynPerturb (k : Clock) where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Nat hiding (_·_)

open import Semantics.Concrete.Dyn k


private variable
  ℓ : Level
  A : Type ℓ

private
  ▹_ : {ℓ : Level} → Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

-------------------------
-- Perturbations for Dyn
-------------------------

-- The monoid of perturbations for Dyn is defined as a
-- higher-inductive type.

-- Recall that Dyn ≅ ℕ + (Dyn × Dyn) + (Dyn ==> UF Dyn)
--                 ≅ ℕ + (Dyn × Dyn) + U (Dyn ⟶ F Dyn)
--                 
-- We define PtbD to be the least solution in the category of
-- monoids to the equation
--
-- PtbD ≅ (PtbD ⊕ PtbD) ⊕ (ℕ ⊕ PtbD ⊕ ℕ ⊕ PtbD)
--
data PtbD : Type where
  ε : PtbD
  _·_ : PtbD → PtbD → PtbD
 
  ⟦_⟧×-left    : PtbD → PtbD
  ⟦_⟧×-right   : PtbD → PtbD
  ⟦_⟧arr-left  : PtbD → PtbD
  ⟦_⟧arr-right : PtbD → PtbD
  ⟦_⟧arr-n₁    : ℕ → PtbD
  ⟦_⟧arr-n₂    : ℕ → PtbD

  id-×-left    : ⟦ ε ⟧×-left ≡ ε
  id-×-right   : ⟦ ε ⟧×-right ≡ ε
  id-arr-left  : ⟦ ε ⟧arr-left ≡ ε
  id-arr-right : ⟦ ε ⟧arr-right ≡ ε
  id-arr-n₁    : ⟦ 0 ⟧arr-n₁ ≡ ε
  id-arr-n₂    : ⟦ 0 ⟧arr-n₂ ≡ ε

  comp-×-left    : ∀ p p' → ⟦ p · p' ⟧×-left    ≡ (⟦ p ⟧×-left · ⟦ p' ⟧×-left)
  comp-×-right   : ∀ p p' → ⟦ p · p' ⟧×-right   ≡ (⟦ p ⟧×-right · ⟦ p' ⟧×-right)
  comp-arr-left  : ∀ p p' → ⟦ p · p' ⟧arr-left  ≡ (⟦ p ⟧arr-left · ⟦ p' ⟧arr-left)
  comp-arr-right : ∀ p p' → ⟦ p · p' ⟧arr-right ≡ (⟦ p ⟧arr-right · ⟦ p' ⟧arr-right)
  comp-arr-n₁    : ∀ n m → ⟦ n + m ⟧arr-n₁ ≡ (⟦ n ⟧arr-n₁ · ⟦ m ⟧arr-n₁)
  comp-arr-n₂    : ∀ n m → ⟦ n + m ⟧arr-n₂ ≡ (⟦ n ⟧arr-n₂ · ⟦ m ⟧arr-n₂)

 -- _×d_ : PtbD → PtbD → PtbD
 -- _⟶d_ : PtbD
 -- _⟶ptb_ : PtbD → (PtbD × {!!}) → PtbD

  identityᵣ : ∀ x → x · ε ≡ x
  identityₗ  :  ∀ x → ε · x ≡ x
  assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
  trunc : isSet PtbD



-- Monoid homomorphism into the endomorphisms on Dyn




-- The push-pull property for the three relations inj-nat, inj-prod, and inj-arr



