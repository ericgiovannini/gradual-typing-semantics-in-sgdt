{-# OPTIONS --cubical --rewriting --guarded #-}

open import Later

module Results (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_)
open import Cubical.Foundations.Structure

open import StrongBisimulation k
open import Semantics k
open import SyntacticTermPrecision k
open import GradualSTLC

private
  variable
    l : Level
    A B : Set l
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A


gradual_guarantee : (M : Tm · nat) (N : Tm · nat) ->
                    · |- M ⊑tm N # nat ->
                    ⟦ M ⟧ ≲ ⟦ N ⟧
