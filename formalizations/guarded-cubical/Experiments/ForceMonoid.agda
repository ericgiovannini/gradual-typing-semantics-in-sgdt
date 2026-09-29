{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Common.Later

module Semantics.Concrete.ForceMonoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_·_)

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.Instances.Pi

open import Common.LaterProperties

open import Semantics.Concrete.LaterMonoid

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓM : Level

module _ (M : Monoid ℓ) where

  forceMonoid : MonoidHom (Πₘ Clock (λ k → Monoid▹ k M)) (Πₘ Clock (λ _ → M))
  forceMonoid .fst = force'
  forceMonoid .snd .IsMonoidHom.presε = force'-beta _
  forceMonoid .snd .IsMonoidHom.pres· x~ y~ = {!!}
