{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


module Common.Common where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat hiding (_^_) renaming (ℕ to Nat)


id : {ℓ : Level} -> {A : Type ℓ} -> A -> A
id x = x

_^_ : {ℓ : Level} -> {A : Type ℓ} -> (A -> A) -> Nat -> A -> A
f ^ zero = id
f ^ suc n = f ∘ (f ^ n)
