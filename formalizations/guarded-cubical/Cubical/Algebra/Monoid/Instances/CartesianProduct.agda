{-# OPTIONS --safe #-}

module Cubical.Algebra.Monoid.Instances.CartesianProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid.Displayed

open import Cubical.Data.Sigma as Sigma hiding (_×_)

private variable
  ℓ ℓ' ℓ'' ℓ''' ℓᴰ : Level

open MonoidStr
open IsMonoid
open IsSemigroup
module _ (M : Monoid ℓ) (N : Monoid ℓ') where
  _×_ : Monoid _
  _×_ .fst = ⟨ M ⟩ Sigma.× ⟨ N ⟩
  _×_ .snd .ε = (M .snd .ε) , (N .snd .ε)
  _×_ .snd ._·_ (m , n) (m' , n') = (M .snd ._·_ m m') , (N .snd ._·_ n n')
  _×_ .snd .isMonoid = ismonoid
    (issemigroup (isSet× (M .snd .isMonoid .isSemigroup .is-set)
                         (N .snd .isMonoid .isSemigroup .is-set))
      λ _ _ _ → ΣPathP ( M .snd .isMonoid .isSemigroup .·Assoc _ _ _
                       , N .snd .isMonoid .isSemigroup .·Assoc _ _ _))
    (λ _ → ΣPathP (M .snd .isMonoid .·IdR _ , N .snd .isMonoid .·IdR _))
    (λ _ → ΣPathP (M .snd .isMonoid .·IdL _ , N .snd .isMonoid .·IdL _))

module _ {M : Monoid ℓ} {N : Monoid ℓ'} where
  open IsMonoidHom
  corec : {P : Monoid ℓ''}
    → MonoidHom P M
    → MonoidHom P N
    → MonoidHom P (M × N)
  corec ϕ ψ .fst x = (ϕ .fst x) , (ψ .fst x)
  corec ϕ ψ .snd .presε = ΣPathP (ϕ .snd .presε , ψ .snd .presε)
  corec ϕ ψ .snd .pres· x y = ΣPathP ((ϕ .snd .pres· x y) , (ψ .snd .pres· x y))
