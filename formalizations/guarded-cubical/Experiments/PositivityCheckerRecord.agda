{-# OPTIONS --polarity #-}

module Experiments.PositivityCheckerRecord where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat


Pred : {ℓ : Level} (X : Type ℓ) → Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
Pred X = X → Type


module Attempt1 where

  record Foo : Typeω where
    field
      foo : (ℓ : Level) (X : Type ℓ) → Pred X

  module _ (z : Foo) where
    open Foo z

    data Test : Type ℓ-zero where
      test : (x : Test) → foo ℓ-zero Test x → Test


module Attempt2 where

  record Foo (ℓ : Level) : Type (ℓ-suc ℓ) where
    field
      foo : (X : Type ℓ) → Pred X

  module _ (ℓ : Level) (z : Foo ℓ) where
    open Foo z

    data Test : Type ℓ where
      test : (x : Test) → foo Test x → Test


module Attempt3 where

  module _ (ℓ : Level) (p : (X : Type ℓ) → Pred X) where

    data Test : Type ℓ where
      test : (x : Test) → p Test x → Test


module Attempt4 where

  module _ (ℓ : Level) (p : (@++ X : Type ℓ) → Pred X) where

    data Test : Type ℓ where
      test : (x : Test) → p Test x → Test


module Attempt5 where

  Bar : (ℓ : Level) → Type (ℓ-suc ℓ)
  Bar ℓ = (@++ X : Type ℓ) → (X → Type) 

  record Foo (ℓ : Level) : Type (ℓ-suc ℓ) where
    field
      foo : Bar ℓ

  module _ (ℓ : Level) (z : Foo ℓ) where
    open Foo z

    data Test : Type ℓ where
      test : (x : Test) → foo Test x → Test


module Attempt6 where

  Bar : (ℓ : Level) → Type (ℓ-suc ℓ)
  Bar ℓ = (@++ X : Type ℓ) → (X → Type)

  module _ (ℓ : Level) (z : Bar ℓ) where

    data Test : Type ℓ where
      test : (x : Test) → z Test x → Test

module Attempt7 where

  Foo : (ℓ : Level) → Type (ℓ-suc ℓ)
  Foo ℓ = Σ[ n ∈ ℕ ] ((@++ X : Type ℓ) → (X → Type))

  module _ (ℓ : Level) (z : Foo ℓ) where

    data Test : Type ℓ where
      test : (x : Test) → snd z Test x → Test
