{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --termination-depth=5 #-}

open import Common.Later
open import Common.Common

module Experiments.InductiveGuarded (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function

open import Cubical.Data.List as List
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)

private
  variable
    ℓ ℓ' ℓB : Level



private
  ▹_ : Type ℓ -> Type ℓ
  ▹ A = ▹_,_ k A


-- A mixed inductive + guarded-recursive type.

data Foo (A : Type ℓ) : Type ℓ where
  foo : (A → Foo A) → Foo A
  theta : (▹ Foo A) → Foo A
  -- The occurrence of Foo in theta is inductive, so we can get away without actually using guarded recursion.


-- Attempting to define the recursor.
-- The termination checker does not accept this definition.

module _ {A : Type ℓ} where

  recFoo : ∀ {B : Type ℓ'}
    → ((A → B) → B)
    → (▹ B → B)
    → (Foo A → B)
  recFoo {B = B} foo* theta* = fix recFoo'
    where
      recFoo' : ▹ (Foo A → B) → (Foo A → B)
      recFoo' _   (foo f) = foo* (λ x → recFoo foo* theta* (f x))
      recFoo' rec (theta x~) = theta* (λ t → rec t (x~ t))

  -- But this is accepted:
  -- recFoo foo* theta* (foo f) = foo* (λ x → recFoo foo* theta* (f x))


----------------------------------------------------------------------------

-- A different approach to defining the above type.

data Tree (A : Type ℓ) (X : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  foo : (A → Tree A X) → Tree A X
  bar : X → Tree A X

module _ {A : Type ℓ} {X : Type ℓ'} where

  -- recTree : ∀ {B : Type ℓ'}
  --     → ((A → B) → B)
  --     → B
  --     → (Foo A → B)
  -- recTree foo* bar* (foo f) = foo* (recTree foo* bar* ∘ f)
  -- recTree foo* bar* (theta x) = bar*

  recTree : ∀ {B : Type ℓB}
    → ((A → B) → B)
    → B
    → (Tree A X → B)
  recTree foo* bar* (foo f) = foo* (recTree foo* bar* ∘ f)
  recTree foo* bar* (bar x) = bar*


Foo' : (A : Type ℓ) → Type ℓ
Foo' A = fix {k} (λ T~ → Tree A (▸ T~))

unfold-Foo' : ∀ {A : Type ℓ} → Foo' A ≡ Tree A (▹ (Foo' A))
unfold-Foo' = fix-eq _



module _ (A : Type ℓ) where

  recFoo' : ∀ {B : Type ℓ'}
    → ((A → B) → B)
    → (▹ B → B)
    → (Foo' A → B)
  recFoo' {B = B} foo* theta* x = fix aux (transport unfold-Foo' x)
    where
      Tr : Type ℓ
      Tr = Tree A (▹ Foo' A)

      aux : ▹ (Tr → B) → (Tr → B)
      aux rec x = recTree foo* (theta* (λ t → rec t x)) x
