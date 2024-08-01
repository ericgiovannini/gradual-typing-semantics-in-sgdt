{-# OPTIONS --safe #-}

module Cubical.Algebra.Monoid.FreeMonoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid.Displayed

private variable
  ℓ ℓ' ℓ'' ℓ''' ℓᴰ : Level

module _  (A : Type ℓ) (B : Type ℓ') (C : Type ℓ'') where
  data FreeMonoid : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    ⟦_⟧       : A → FreeMonoid
    ⟦_⟧co     : B → FreeMonoid → FreeMonoid
    ⟦_⟧op     : C → FreeMonoid → FreeMonoid
    ε         : FreeMonoid
    _·_       : FreeMonoid → FreeMonoid → FreeMonoid
    identityᵣ : ∀ x     → x · ε ≡ x
    identityₗ : ∀ x     → ε · x ≡ x
    assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
    co-ε : ∀ b → ⟦ b ⟧co ε ≡ ε
    co-· : ∀ b x y → ⟦ b ⟧co (x · y) ≡ (⟦ b ⟧co x · ⟦ b ⟧co y)
    op-ε : ∀ b → ⟦ b ⟧op ε ≡ ε
    op-· : ∀ b x y → ⟦ b ⟧op (y · x) ≡ (⟦ b ⟧op x · ⟦ b ⟧op y)
    trunc     : isSet FreeMonoid

  FM : Monoid _
  FM = FreeMonoid , (monoidstr ε _·_ (ismonoid (issemigroup trunc assoc) identityᵣ identityₗ))

  coHom : B → MonoidHom FM FM
  coHom b .fst = ⟦ b ⟧co
  coHom b .snd .IsMonoidHom.presε = co-ε b
  coHom b .snd .IsMonoidHom.pres· = co-· b

  opHom : C → MonoidHom (FM ^op) FM
  opHom c .fst = ⟦ c ⟧op
  opHom c .snd .IsMonoidHom.presε = op-ε c
  opHom c .snd .IsMonoidHom.pres· = op-· c

  module _ (Mᴰ : Monoidᴰ FM ℓᴰ) where
    private
      module Mᴰ = Monoidᴰ Mᴰ
    module _
      (iA : ∀ a → Mᴰ.eltᴰ ⟦ a ⟧)
      (iB : ∀ b → MonoidHomᴰ (coHom b) Mᴰ Mᴰ)
      (iC : ∀ c → MonoidHomᴰ (opHom c) (Mᴰ ^opᴰ) Mᴰ)
      
      where
      elim : Section Mᴰ
      elim .fst = f where
        f : ∀ x → Mᴰ.eltᴰ x
        f ⟦ a ⟧ = iA a
        f (⟦ b ⟧co x) = iB b .fst (f x)
        f (co-ε b i) = iB b .snd .fst i
        f (co-· b x y i) = iB b .snd .snd (f x) (f y) i
        f (⟦ c ⟧op x) = iC c .fst (f x)
        f (op-ε c i) = iC c .snd .fst i
        f (op-· c x y i) = iC c .snd .snd (f x) (f y) i
        f ε = Mᴰ.εᴰ
        f (x · y) = f x Mᴰ.·ᴰ f y
        f (identityᵣ x i) = Mᴰ.·IdRᴰ (f x) i
        f (identityₗ x i) = Mᴰ.·IdLᴰ (f x) i
        f (assoc x y z i) = Mᴰ.·Assocᴰ (f x) (f y) (f z) i
        f (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2 (λ x → Mᴰ.isSetEltᴰ)
          (f x) (f y)
          (cong f p) (cong f q)
          (trunc x y p q)
          i j
      elim .snd .fst = refl
      elim .snd .snd x y = refl

  -- -- general principle...
  -- rec : ∀ (N : Monoid ℓ''') → (A → N .fst) → MonoidHom FM N
  -- rec N iA .fst = elim (wkn FM N) iA .fst
  -- rec N iA .snd .IsMonoidHom.presε = elim (wkn FM N) iA .snd .fst
  -- rec N iA .snd .IsMonoidHom.pres· = elim (wkn FM N) iA .snd .snd

  -- elim : ∀ 
-- module Elim {ℓ'} {B : FreeMonoid A → Type ℓ'}
--   (⟦_⟧*       : (x : A) → B ⟦ x ⟧)
--   (ε*         : B ε)
--   (_·*_       : ∀ {x y}   → B x → B y → B (x · y))
--   (identityᵣ* : ∀ {x}     → (xs : B x)
--     → PathP (λ i → B (identityᵣ x i)) (xs ·* ε*) xs)
--   (identityₗ* : ∀ {x}     → (xs : B x)
--     → PathP (λ i → B (identityₗ x i)) (ε* ·* xs) xs)
--   (assoc*     : ∀ {x y z} → (xs : B x) (ys : B y) (zs : B z)
--     → PathP (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs)) ((xs ·* ys) ·* zs))
--   (trunc*     : ∀ xs → isSet (B xs)) where

--   f : (xs : FreeMonoid A) → B xs
--   f ⟦ x ⟧ = ⟦ x ⟧*
--   f ε = ε*
--   f (xs · ys) = f xs ·* f ys
--   f (identityᵣ xs i) = identityᵣ* (f xs) i
--   f (identityₗ xs i) = identityₗ* (f xs) i
--   f (assoc xs ys zs i) = assoc* (f xs) (f ys) (f zs) i
--   f (trunc xs ys p q i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f xs) (f ys)
--     (cong f p) (cong f q) (trunc xs ys p q) i j

-- module ElimProp {ℓ'} {B : FreeMonoid A → Type ℓ'}
--   (BProp : {xs : FreeMonoid A} → isProp (B xs))
--   (⟦_⟧*       : (x : A) → B ⟦ x ⟧)
--   (ε*         : B ε)
--   (_·*_       : ∀ {x y}   → B x → B y → B (x · y)) where

--   f : (xs : FreeMonoid A) → B xs
--   f = Elim.f ⟦_⟧* ε* _·*_
--     (λ {x} xs → toPathP (BProp (transport (λ i → B (identityᵣ x i)) (xs ·* ε*)) xs))
--     (λ {x} xs → toPathP (BProp (transport (λ i → B (identityₗ x i)) (ε* ·* xs)) xs))
--     (λ {x y z} xs ys zs → toPathP (BProp (transport (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs))) ((xs ·* ys) ·* zs)))
--     (λ _ → (isProp→isSet BProp))

-- module Rec {ℓ'} {B : Type ℓ'} (BType : isSet B)
--   (⟦_⟧*       : (x : A) → B)
--   (ε*         : B)
--   (_·*_       : B → B → B)
--   (identityᵣ* : (x : B) → x ·* ε* ≡ x)
--   (identityₗ* : (x : B) → ε* ·* x ≡ x)
--   (assoc*     : (x y z : B) → x ·* (y ·* z) ≡ (x ·* y) ·* z)
--   where

--   f : FreeMonoid A → B
--   f = Elim.f ⟦_⟧* ε* _·*_ identityᵣ* identityₗ* assoc* (const BType)
