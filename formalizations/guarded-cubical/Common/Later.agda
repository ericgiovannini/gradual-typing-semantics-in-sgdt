{-# OPTIONS --cubical --rewriting --guarded #-}
module Common.Later where

-- | This file is adapted from the supplementary material for the
-- | paper https://doi.org/10.1145/3372885.3373814, originally written
-- | by Niccolò Veltri and Andrea Vezzosi see the LICENSE.txt for
-- | their license.

open import Agda.Builtin.Equality renaming (_≡_ to _≣_) hiding (refl)
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

open import Cubical.Data.Nat

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Clock : Set
  Tick : Clock → LockU

private
  variable
    l : Level
    A B : Set l
    k : Clock

▹_,_ : Clock → Set l → Set l
▹ k , A = (@tick t : Tick k) → A

▸_ : ▹ k , Set l → Set l
▸ A = (@tick t : Tick _) → A t

next : A → ▹ k , A
next x _ = x

_⊛_ : ▹ k , (A → B) → ▹ k , A → ▹ k , B
_⊛_ f x a = f a (x a)

map▹ : (f : A → B) → ▹ k , A → ▹ k , B
map▹ f x α = f (x α)
_<$>_ = map▹

-- The behaviour of fix is encoded with rewrite rules, following the
-- definitional equalities of Clocked CTT.
postulate
  dfix : ∀ {k}{l} {A : Set l} → (f : ▹ k , A → A) → I → ▹ k , A
  dfix-beta : ∀ {l} {A : Set l} → (f : ▹ k , A → A) → dfix f i1 ≣ next (f (dfix f i0))

{-# REWRITE dfix-beta #-}

pfix : ∀ {l} {A : Set l} → (f : ▹ k , A → A) → dfix f i0 ≡ next (f (dfix f i0))
pfix f i = dfix f i

abstract
  fix : ∀ {l} {A : Set l} → (f : ▹ k , A → A) → A
  fix f = f (pfix f i0)

  fix-eq : ∀ {l} {A : Set l} → (f : ▹ k , A → A) → fix f ≡ f (next (fix f))
  fix-eq f = cong f (pfix f)

later-ext : ∀ {A : ▹ k , Set} → {f g : ▸ A} → (▸ \ a → f a ≡ g a) → f ≡ g
later-ext eq i a = eq a i

transpLater : ∀ (A : I → ▹ k , Set) → ▸ (A i0) → ▸ (A i1)
transpLater A u0 a = transp (\ i → A i a) i0 (u0 a)

hcompLater : ∀ (A : ▹ k , Set) φ (u : I → Partial φ (▸ A)) → (u0 : ▸ A [ φ ↦ u i0 ]) → ▸ A
hcompLater A φ u u0 a = hcomp (\ { i (φ = i1) → u i 1=1 a }) (outS u0 a)

postulate
  force : (∀ k → (▹ k , A)) → (∀ (k : Clock) → A)

postulate
  force-beta : ∀ {A : Set l} (x : A) → force (λ k _ → x) ≣ λ k → x





-- ########################################################## --
--
-- Added by Eric (not part of original file from Niccolò Veltri
-- and Andrea Vezzosi)


-- Tick irrelevance axiom. This is needed in the development.
-- There is likely a better way to do this, see
-- https://arxiv.org/pdf/2102.01969.pdf (in particular Section 3.2).
postulate
  tick-irrelevance : {A : Type} -> (M : ▹ k , A) (t t' : Tick k) ->
    M t ≡ M t'

  tr' : {A : Type} -> (M : ▹ k , A) ->
    ▸ λ t -> ▸ λ t' -> M t ≡ M t'

{-
tr→tr' : {M : ▹ k , A} -> tick-irrelevance M -> tr' M
-}

-- The tick constant.
postulate
  -- _◇ : (k : Clock) -> Tick k
  ◇ : {k : Clock} -> Tick k

-- From Section V.C of Bahr et. al
-- (See https://bahr.io/pubs/files/bahr17lics-paper.pdf).
postulate
  tick-irrelevance-◇-refl : {A : Type} -> (M : ▹ k , A) ->
    (tick-irrelevance M (◇) (◇)) ≡ Cubical.Foundations.Everything.refl
      -- Should this use _≣_.refl instead?


-- This relies on tick irrelevance.
next-Mt≡M : {A : Type} -> (M : ▹ k , A) ->
  ▸ λ t -> (next (M t) ≡ M)
next-Mt≡M M t = later-ext (λ t' → tick-irrelevance M t t')


next-Mt≡M' : {A : Type} -> (M : ▹ k , A) -> (t : Tick k) ->
  next (M t) ≡ M
next-Mt≡M' M t = next-Mt≡M M t





-- Clock-related postulates.

clock-ext : {ℓ : Level} {A : (k : Clock) -> Type ℓ} -> {M N : (k : Clock) -> A k} →
  (∀ k → M k ≡ N k) → M ≡ N
clock-ext eq i k = eq k i


-- "Dependent" forcing (where the type can mention the clock).
-- This seems to be the correct type of the force function.

postulate
  force' : {A : Clock -> Type} -> (∀ k → (▹ k , A k)) → (∀ (k : Clock) → A k)
  -- original (non-dependent) version:
  -- force'-beta : ∀ {A : Type} (x : A) → force' (λ k -> next x) ≡ λ k → x

  -- "Reduction" rules:

  -- Builds in clock extensionality
  force'-beta : ∀ {A : Clock -> Type} (f : ∀ k -> A k) →
    force' (λ k -> next (f k)) ≡ f

  -- Builds in clock extensionality
  next-force' :     ∀ {A : Clock -> Type} (f : ∀ k -> ▹ k , A k) ->
    (λ k -> next (force' f k)) ≡ f

  --next-force' :     ∀ {A : Clock -> Type} (f : ∀ k -> ▹ k , A k) ->
  --  (k : Clock) -> next (force' f k) ≡ f k


force-iso : {A : Clock -> Type} -> Iso (∀ k -> (▹ k , A k)) (∀ k -> A k)
force-iso = iso force' (λ f k → next (f k))
  force'-beta
  next-force'
  -- (λ f → clock-ext (λ k → next-force' f k))



postulate
  k0 : Clock

{-
postulate
  nat-clock-irrel : (∀ (k : Clock) -> ℕ) ≡ ℕ
-}

-- Definition of clock irrelevance, parameterized by a specific type
clock-irrel : {ℓ : Level} -> Type ℓ -> Type ℓ
clock-irrel A =
  (M : ∀ (k : Clock) -> A) ->
  (k k' : Clock) ->
  M k ≡ M k'


∀kA->A : (A : Type) ->
  (∀ (k : Clock) -> A) -> A
∀kA->A A f = f k0

-- If A is clock irrelevant, then the above map is inverse
-- to the map A -> ∀ k . A.
Iso-∀kA-A : {A : Type} -> clock-irrel A -> Iso (∀ (k : Clock) -> A) A
Iso-∀kA-A {A} H-irrel-A = iso
  (∀kA->A A)
  (λ a k -> a)
  (λ a → refl)
  (λ f → clock-ext (λ k → H-irrel-A f k0 k))


postulate
  nat-clock-irrel : clock-irrel ℕ
  type-clock-irrel : clock-irrel Type







