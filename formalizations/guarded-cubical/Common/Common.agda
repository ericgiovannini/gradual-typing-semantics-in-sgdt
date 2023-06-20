{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


module Common.Common where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat hiding (_^_) renaming (ℕ to Nat)
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming (Unit to ⊤)


id : {ℓ : Level} -> {A : Type ℓ} -> A -> A
id x = x

_^_ : {ℓ : Level} -> {A : Type ℓ} -> (A -> A) -> Nat -> A -> A
f ^ zero = id
f ^ suc n = f ∘ (f ^ n)

⊥*→⊥ : {ℓ : Level} -> ⊥* {ℓ} -> ⊥
⊥*→⊥ ()


inl≠inr : ∀ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} ->
  (a : A) (b : B) -> inl a ≡ inr b -> ⊥
inl≠inr {_} {_} {A} {B} a b eq = transport (cong (diagonal ⊤ ⊥) eq) tt
  where
    diagonal : (Left Right : Type) -> (A ⊎ B) -> Type
    diagonal Left Right (inl a) = Left
    diagonal Left Right (inr b) = Right
