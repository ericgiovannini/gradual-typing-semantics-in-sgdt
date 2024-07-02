{- The trivial monoid having one element -}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Monoid.Instances.Trivial where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

open MonoidStr

TrivialMonoid : Monoid ℓ-zero
TrivialMonoid .fst = Unit
TrivialMonoid .snd .ε = tt
TrivialMonoid .snd ._·_ = λ _ _ → tt
TrivialMonoid .snd .isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set = isSetUnit
TrivialMonoid .snd .isMonoid .IsMonoid.isSemigroup .IsSemigroup.·Assoc = λ x y z i → tt
TrivialMonoid .snd .isMonoid .IsMonoid.·IdR = λ x i → tt
TrivialMonoid .snd .isMonoid .IsMonoid.·IdL = λ x i → tt

rec : ∀ {ℓ}{M : Monoid ℓ} → MonoidHom TrivialMonoid M
rec {M = M} .fst x = M .snd .ε
rec {M = M} .snd .IsMonoidHom.presε = refl
rec {M = M} .snd .IsMonoidHom.pres· x y = sym (M .snd .isMonoid .IsMonoid.·IdR _)

corec : ∀ {ℓ}{M : Monoid ℓ} → MonoidHom M TrivialMonoid
corec .fst x = tt
corec .snd .IsMonoidHom.presε = refl
corec .snd .IsMonoidHom.pres· x y = refl
