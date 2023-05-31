{-# OPTIONS --lossy-unification #-}
module Semantics.Abstract.TermModel.Convenient.Linear where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monad.Strength.Cartesian
open import Cubical.Categories.Monad.Kleisli
open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.BiKleisli.Base
open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.BiKleisli.Morphism
open import Cubical.Categories.Comonad.Instances.Environment

open import Semantics.Abstract.TermModel.Convenient

private
  variable
    ℓ ℓ' : Level

module StrengthNotation (𝓜 : Model ℓ ℓ') where
  open Model 𝓜
  open Category cat
  Linear : ∀ (Γ : ob) → Category _ _
  Linear Γ = BiKleisli (Env Γ (binProd Γ)) monad (strength-law binProd monad strength Γ)

  ClosedLinear : Category _ _
  ClosedLinear = Kleisli monad

  wkClosed : ∀ Γ → Functor ClosedLinear (Linear Γ)
  wkClosed = wkF binProd monad strength

  _^* : ∀ {Δ Γ}(γ : Hom[ Δ , Γ ]) → Functor (Linear Γ) (Linear Δ)
  γ ^* = change-of-comonad (change-of-base _ _ strength γ)
