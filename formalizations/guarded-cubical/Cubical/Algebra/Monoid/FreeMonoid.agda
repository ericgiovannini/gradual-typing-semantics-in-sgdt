{-# OPTIONS --safe #-}

module Cubical.Algebra.Monoid.FreeMonoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

private variable
  ℓ : Level
  A : Type ℓ

data FreeMonoid (A : Type ℓ) : Type ℓ where
  ⟦_⟧       : A → FreeMonoid A
  ε         : FreeMonoid A
  _·_       : FreeMonoid A → FreeMonoid A → FreeMonoid A
  identityᵣ : ∀ x     → x · ε ≡ x
  identityₗ : ∀ x     → ε · x ≡ x
  assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
  trunc     : isSet (FreeMonoid A)

module Elim {ℓ'} {B : FreeMonoid A → Type ℓ'}
  (⟦_⟧*       : (x : A) → B ⟦ x ⟧)
  (ε*         : B ε)
  (_·*_       : ∀ {x y}   → B x → B y → B (x · y))
  (identityᵣ* : ∀ {x}     → (xs : B x)
    → PathP (λ i → B (identityᵣ x i)) (xs ·* ε*) xs)
  (identityₗ* : ∀ {x}     → (xs : B x)
    → PathP (λ i → B (identityₗ x i)) (ε* ·* xs) xs)
  (assoc*     : ∀ {x y z} → (xs : B x) (ys : B y) (zs : B z)
    → PathP (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs)) ((xs ·* ys) ·* zs))
  (trunc*     : ∀ xs → isSet (B xs)) where

  f : (xs : FreeMonoid A) → B xs
  f ⟦ x ⟧ = ⟦ x ⟧*
  f ε = ε*
  f (xs · ys) = f xs ·* f ys
  f (identityᵣ xs i) = identityᵣ* (f xs) i
  f (identityₗ xs i) = identityₗ* (f xs) i
  f (assoc xs ys zs i) = assoc* (f xs) (f ys) (f zs) i
  f (trunc xs ys p q i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f xs) (f ys)
    (cong f p) (cong f q) (trunc xs ys p q) i j

module ElimProp {ℓ'} {B : FreeMonoid A → Type ℓ'}
  (BProp : {xs : FreeMonoid A} → isProp (B xs))
  (⟦_⟧*       : (x : A) → B ⟦ x ⟧)
  (ε*         : B ε)
  (_·*_       : ∀ {x y}   → B x → B y → B (x · y)) where

  f : (xs : FreeMonoid A) → B xs
  f = Elim.f ⟦_⟧* ε* _·*_
    (λ {x} xs → toPathP (BProp (transport (λ i → B (identityᵣ x i)) (xs ·* ε*)) xs))
    (λ {x} xs → toPathP (BProp (transport (λ i → B (identityₗ x i)) (ε* ·* xs)) xs))
    (λ {x y z} xs ys zs → toPathP (BProp (transport (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs))) ((xs ·* ys) ·* zs)))
    (λ _ → (isProp→isSet BProp))

module Rec {ℓ'} {B : Type ℓ'} (BType : isSet B)
  (⟦_⟧*       : (x : A) → B)
  (ε*         : B)
  (_·*_       : B → B → B)
  (identityᵣ* : (x : B) → x ·* ε* ≡ x)
  (identityₗ* : (x : B) → ε* ·* x ≡ x)
  (assoc*     : (x y z : B) → x ·* (y ·* z) ≡ (x ·* y) ·* z)
  where

  f : FreeMonoid A → B
  f = Elim.f ⟦_⟧* ε* _·*_ identityᵣ* identityₗ* assoc* (const BType)
