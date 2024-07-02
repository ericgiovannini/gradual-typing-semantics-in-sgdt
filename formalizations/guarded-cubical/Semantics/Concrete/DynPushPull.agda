{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}



open import Common.Later

module Semantics.Concrete.DynPushPull (k : Clock) where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.Instances.Trivial as Trivial
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Data.Nat hiding (_·_ ; ℕ)

import Semantics.Concrete.DoublePoset.Constructions as PB
open import Semantics.Concrete.DoublePoset.Morphism
import Semantics.Concrete.DoublePoset.DblPosetCombinators as DPC
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k

open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Predomains.Perturbations k
open import Semantics.Concrete.Dyn k
import Semantics.Concrete.DynPerturb k as DP

open import Semantics.Concrete.Types k as Types
-- open import Semantics.Concrete.Types.Constructions k
open import Semantics.Concrete.Perturbation.Relation.Base k

open PB using (_×dp_)
open ValTypeStr

private variable
  ℓ : Level
  A : Type ℓ

private
  ▹_ : {ℓ : Level} → Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A



open DynDef {ℓ-zero}
open LiftPredomain
open Guarded (next Dyn)
module Rel = Relations

open F-ob
open F-rel

-- The push-pull property for the three relations inj-nat, inj-prod,
-- and inj-arr:


inj-nat : VRelPP ℕ dyn' ℓ-zero
inj-nat .fst = Rel.inj-nat

-- Push
inj-nat .snd .fst = Trivial.rec , refl

-- Pull
inj-nat .snd .snd = {!!}


--------------------------------------------

inj-times : VRelPP (dyn' × dyn') dyn' ℓ-zero
inj-times .fst = Rel.inj-times

-- Push
inj-times .snd .fst = corecPushV _ _ _ DP.inj-times {!!}
-- elimSection _
--   (corecFact1 (dyn' × dyn') dyn' (fst inj-times) {!!} {!!})
--   {!!}

-- Pull
inj-times .snd .snd = corecPullV _ _ _
  (DP.cases (idMon _) ε-hom)
  λ {p (d₁ , d₂) (prod d₁' d₂') (⊑-prod d₁⊑d₁' d₂⊑d₂') → {!!}}


--------------------------------------------


inj-arr : VRelPP (U (dyn ⟶ F dyn)) dyn' ℓ-zero
inj-arr .fst = Rel.inj-arr

-- Push
inj-arr .snd .fst = {!!}

-- Pull 
inj-arr .snd .snd = {!!}





-- Π-inj-nat : PushPullV PB.ℕ 𝟙M (𝟙M→ (Endo PB.ℕ)) Dyn' PtbD ι-dyn Rel.inj-nat
-- Π-inj-nat = {!!}

-- Π-inj-prod : PushPullV (Dyn' ×dp Dyn') {!!} {!!} Dyn' PtbD ι-dyn Rel.inj-times
-- Π-inj-prod = {!!}

-- Π-inj-arr : PushPullV (Dyn ==> 𝕃 Dyn) {!!} {!!} Dyn' PtbD ι-dyn Rel.inj-arr
-- Π-inj-arr = {!!}
