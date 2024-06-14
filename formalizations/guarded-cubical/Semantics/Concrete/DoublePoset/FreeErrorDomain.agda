{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.DoublePoset.FreeErrorDomain (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Relation.Binary.Base
open import Cubical.Foundations.Structure


open import Common.Common
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.DblPosetCombinators

open import Semantics.Concrete.DoublePoset.ErrorDomain k

open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k

private
  variable
    ℓ ℓ' : Level
    ℓA ℓ≤A ℓ≈A : Level
    ℓB ℓ≤B ℓ≈B : Level
    

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A



-- Give an error domain sturcture on L℧ X

open ErrorDomainStr hiding (℧ ; θ)
open PosetBisimStr



module LiftPredomain (A : PosetBisim ℓA ℓ≤A ℓ≈A) where

  module A = PosetBisimStr (A .snd)
  module LockStep = LiftOrdHomogenous ⟨ A ⟩ (A._≤_)
  _≤LA_ = LockStep._⊑_

  𝕃 : PosetBisim ℓA (ℓ-max ℓA ℓ≤A) {!!}
  𝕃 .fst = L℧ ⟨ A ⟩
  𝕃 .snd = posetbisimstr (isSetL℧ _ A.is-set) _≤LA_ {!!} {!!} {!!}


module Free (A : PosetBisim ℓA ℓ≤A ℓ≈A) where

  module A = PosetBisimStr (A .snd)
  module LockStepA = LiftOrdHomogenous ⟨ A ⟩ (A._≤_)

  F-ob :  ErrorDomain ℓA {!!} {!!}
  F-ob .fst = L℧ ⟨ A ⟩
  F-ob .snd .is-predomain = {!!}
  F-ob .snd .ErrorDomainStr.℧ = ℧
  F-ob .snd .ErrorDomainStr.θ =
    record { f = θ ; isMon = {!!} ; pres≈ = {!!} }


-- Defining the "call-by-push-value ext" of type (A → U B) → (F A -* B).
-- This is not the same as the "Kleisli extension" (A → U F A') → (F A -* F A'), because there B has the form F A'
module CBPVMonad (A : PosetBisim ℓA ℓ≤A ℓ≈A) (B : ErrorDomain ℓB ℓ≤B ℓ≈B) where

  module A = PosetBisimStr (A .snd)
  module B = ErrorDomainStr (B .snd)

  module LockStep = LiftOrdHomogenous ⟨ A ⟩ (A._≤_)

  _≤LA_ : _
  _≤LA_ = LockStep._⊑_

  open LiftPredomain

  module _ (f : ⟨ A ⟩ → ⟨ B ⟩) where

    ext' : ▹ (L℧ ⟨ A ⟩ → ⟨ B ⟩) → L℧ ⟨ A ⟩ → ⟨ B ⟩
    ext' rec (η x) = f x
    ext' rec ℧ = B.℧
    ext' rec (θ lx~) = B.θ $ (λ t → rec t (lx~ t))

    ext : _
    ext = fix ext'

    ext-mon : monotone {X = 𝕃 A} {Y = ErrorDomain→Predomain B} ext
    ext-mon = λ x₁ → {!!}


-- Action of F on vertical morphisms

-- Given: f : Aᵢ → Aₒ morphism
-- Define : F f: F Aᵢ -o F Aₒ
-- Given by applying the map function on L℧
-- NTS: map is a morphism of error domains (monotone pres≈, pres℧, presθ)
-- Recall that map is defined using ext (hard to show that ext pres ≈)


-- Action of F on horizontal morphisms




-- Action of F on squares
