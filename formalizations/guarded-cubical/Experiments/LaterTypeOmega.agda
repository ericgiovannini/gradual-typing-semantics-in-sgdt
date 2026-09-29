{-# OPTIONS --cubical --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Experiments.LaterTypeOmega (k : Clock) where

open import Agda.Builtin.Equality renaming (_≡_ to _≣_) hiding (refl)
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat as Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation


private
  variable
    ℓ : Level

  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A
  

ℓn : ℕ → Level
ℓn zero = ℓ-suc ℓ-zero
ℓn (suc n) = ℓ-suc (ℓn n)

A : (n : ℕ) → Type (ℓn n)
A zero = Type
A (suc n) = Type (ℓn n)

f : (n : ℕ) → A n
f zero = Unit
f (suc zero) = {!!}
f (suc (suc n)) = {!!}


-- bar : ▹ (A n) → (A n)

record Foo {ℓx : Level} (X : Type ℓx) (lf : X → Level) (f : (x : X) → Type (lf x))
  : Typeω where
  field
    x : X
    y : f x


foo : Foo ℕ ℓn A
foo .Foo.x = fix (λ n~ → {!!})
foo .Foo.y = {!!}

n : Tick k → ℕ
n = fix (λ f~ t → {!f~ t!}) 


record Liftω {ℓ : Level} (X : Type ℓ) : Typeω where
  field
    liftω : X






