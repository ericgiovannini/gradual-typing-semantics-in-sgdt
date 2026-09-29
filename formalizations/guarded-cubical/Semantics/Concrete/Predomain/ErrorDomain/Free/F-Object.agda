{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.Predomain.ErrorDomain.Free.F-Object (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Relation.Binary.Base
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.HITs.PropositionalTruncation hiding (map) renaming (rec to PTrec)
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Empty
open import Cubical.Foundations.HLevels

open import Common.Common
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions hiding (𝔽)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Combinators
open import Semantics.Concrete.Predomain.Square

open import Semantics.Concrete.Predomain.SimpleErrorDomain k
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k

open import Semantics.Concrete.Predomain.Error
open import Semantics.Concrete.Predomain.Ext k

open ClockedCombinators k


private
  variable
    ℓ ℓ' : Level
    ℓA  ℓ≤A  ℓ≈A  : Level
    ℓA' ℓ≤A' ℓ≈A' : Level
    ℓB  ℓ≤B  ℓ≈B  : Level
    ℓB' ℓ≤B' ℓ≈B' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ : Level
    ℓA₂ ℓ≤A₂ ℓ≈A₂ : Level
    ℓA₃ ℓ≤A₃ ℓ≈A₃ : Level
    ℓΓ ℓ≤Γ ℓ≈Γ : Level
    ℓC : Level
    ℓc ℓc' ℓd ℓR : Level
    ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  : Level
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' : Level
    ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  : Level
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' : Level
    ℓcᵢ ℓcₒ : Level
   

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


open BinaryRelation
open ErrorDomainStr hiding (℧ ; θ ; δ)
open PredomainStr
open Clocked k -- brings in definition of later on predomains


-- The purpose of this module is to define the functor F : Predomain →
-- ErrorDomain left adjoint to the forgetful functor U.

-- We define:
--
-- - The action on objects
-- - The action on vertical morphisms (i.e. fmap)
-- - The action on horizontal morpisms
-- - The action on squares

-- In the below, "UF X" will be sometimes be written in place of the monad L℧ X.

--------------------------------------------------------------------------------


--------------------------
-- Defining the functor F
--------------------------

-- Towards constructing the free error domain FA on a predomain A, we
-- first define the underlying predomain UFA.
-- 
--   * The underlying set is L℧ A.
--   * The ordering is the lock-step error ordering.
--   * The bisimilarity relation is weak bisimilarity on L℧ A = L (Error A).
--
module LiftPredomain (A : Predomain ℓA ℓ≤A ℓ≈A) where

  private module A = PredomainStr (A .snd)
  module LockStepA = LiftOrdHomogenous ⟨ A ⟩ (A._≤_)
  _≤LA_ = LockStepA._⊑_
  module BisimLift = LiftBisim (Error ⟨ A ⟩) (≈ErrorX A._≈_)

  bisimErrorA : IsBisim (≈ErrorX A._≈_)
  bisimErrorA = IsBisimErrorX A._≈_ A.isBisim
  module BisimErrorA = IsBisim (bisimErrorA)

  opaque
    𝕃 : Predomain ℓA (ℓ-max ℓA ℓ≤A) (ℓ-max ℓA ℓ≈A)
    𝕃 .fst = L℧ ⟨ A ⟩
    𝕃 .snd = predomainstr (isSetL℧ _ A.is-set) _≤LA_ ordering BisimLift._≈_ bisim
      where
        ordering : IsOrderingRelation _≤LA_
        ordering = isorderingrelation
          LockStepA.Properties.isProp⊑
          (LockStepA.Properties.⊑-refl A.is-refl)
          (LockStepA.Properties.⊑-transitive A.is-trans)
          (LockStepA.Properties.⊑-antisym A.is-antisym)

        bisim : IsBisim BisimLift._≈_
        bisim = isbisim
                (BisimLift.Properties.reflexive BisimErrorA.is-refl)
                (BisimLift.Properties.symmetric BisimErrorA.is-sym)
                (BisimLift.Properties.is-prop BisimErrorA.is-prop-valued)


module _ {A : Predomain ℓA ℓ≤A ℓ≈A} where

  open LiftPredomain A

  -- η as a morphism of predomain from A to 𝕃A
  opaque
    unfolding 𝕃
    
    η-mor : PMor A 𝕃
    η-mor .PMor.f = η
    η-mor .PMor.isMon = LockStepA.Properties.η-monotone
    η-mor .PMor.pres≈ = BisimLift.Properties.η-pres≈

    -- ℧ as a morphism of predomains from any A' to 𝕃A
    ℧-mor : {A' : Predomain ℓA' ℓ≤A' ℓ≈A'} → PMor A' 𝕃
    ℧-mor = K _ ℧ 

    -- θ as a morphism of *predomains* from ▹𝕃A to 𝕃A
    θ-mor : PMor (P▹ 𝕃) 𝕃
    θ-mor .PMor.f = θ
    θ-mor .PMor.isMon = LockStepA.Properties.θ-monotone
    θ-mor .PMor.pres≈ = BisimLift.Properties.θ-pres≈

    -- δ as a morphism of *predomains* from 𝕃A to 𝕃A.
    δ-mor : PMor 𝕃 𝕃
    δ-mor .PMor.f = δ
    δ-mor .PMor.isMon = LockStepA.Properties.δ-monotone
    δ-mor .PMor.pres≈ = BisimLift.Properties.δ-pres≈

  -- δ ≈ id
  -- δ≈id : δ-mor ≈mon Id
  -- δ≈id = ≈mon-sym Id δ-mor BisimLift.Properties.δ-closed-r




-------------------------
-- 1. Action on objects.
-------------------------

-- We extend the predomain structure on L℧ X defined above to an error
-- domain structure. This defines the action of the functor F on
-- objects.

module F-ob (A : Predomain ℓA ℓ≤A ℓ≈A) where

  open LiftPredomain -- brings 𝕃 and modules into scope
  
  -- module A = PredomainStr (A .snd)
  -- module LockStepA = LiftOrdHomogenous ⟨ A ⟩ (A._≤_)
  -- module WeakBisimErrorA

  opaque
    unfolding 𝕃 δ-mor
    
    F-ob : ErrorDomain ℓA (ℓ-max ℓA ℓ≤A) (ℓ-max ℓA ℓ≈A)
    F-ob = mkErrorDomain
      (𝕃 A) ℧ (LockStepA.Properties.℧⊥ A) (θ-mor)
      (≈mon-sym Id (δ-mor)
        (BisimLift.Properties.δ-closed-r A (BisimErrorA.is-prop-valued A)))

open F-ob

module _ {A : Predomain ℓA ℓ≤A ℓ≈A} where
  open F-ob
  opaque
    unfolding LiftPredomain.𝕃 F-ob
    
    ηM : PMor A (U-ob (F-ob A))
    ηM = η-mor

    -- ℧ as a morphism of predomains from any A' to UFA
    ℧M : {A' : Predomain ℓA' ℓ≤A' ℓ≈A'} → PMor A' (U-ob (F-ob A))
    ℧M = ℧-mor

    -- θ as a morphism of *predomains* from ▹UFA to UFA
    θM : PMor (P▹ (U-ob (F-ob A))) (U-ob (F-ob A))
    θM = θ-mor
  
    -- δ as a morphism of *predomains* from UFA to UFA.
    δM : PMor (U-ob (F-ob A)) (U-ob (F-ob A))
    δM = δ-mor
