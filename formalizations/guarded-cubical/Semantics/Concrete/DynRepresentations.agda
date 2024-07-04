{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.DynRepresentations (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.LockStepErrorOrdering k

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Constructions renaming (ℕ to NatP)
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.MonadRelationalResults k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.MonadCombinators k

open import Semantics.Concrete.Dyn k


private
  variable
    ℓ ℓ' : Level
    ℓA ℓ≤A ℓ≈A : Level
    ℓ≤ ℓ≈ : Level

  ▹_ : {ℓ : Level} → Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


module _ {ℓ : Level} where

  open ClockedCombinators k
  open LiftPredomain
  open F-ob
  open F-mor
  open F-rel

  open DynDef {ℓ = ℓ}
  
  open Guarded (next Dyn) -- Dyn', ordering, and bisimilarity
  open Embeddings
  open Projections
  open Relations


  module NatP = PosetBisimStr (NatP .snd)


  -----------------------------------------------------------------
  -- Quasi-left representations for inj-nat, inj-prod, and inj-arr
  -----------------------------------------------------------------

  -- inj-nat
  ----------

  UpR-inj-nat : PBSq (idPRel NatP) inj-nat Id emb-nat'
  UpR-inj-nat n m n≡m = ⊑-nat n≡m

  UpL-inj-nat : PBSq inj-nat (idPRel Dyn') emb-nat' Id
  UpL-inj-nat = SqV-functionalRel emb-nat' Id (idPRel Dyn')
  
  -- UpL-inj-nat n .(DynTy.nat m) (⊑-nat {n = n} {m = m} n≡m) = ⊑-nat n≡m


  -- inj-times
  ------------

  UpR-inj-prod : PBSq (idPRel (Dyn' ×dp Dyn')) inj-times Id emb-times'
  UpR-inj-prod (d₁ , d₂) (d₁' , d₂') (d₁≤d₁' , d₂≤d₂') = ⊑-prod d₁≤d₁' d₂≤d₂'

  UpL-inj-prod : PBSq inj-times (idPRel Dyn') emb-times' Id
  UpL-inj-prod = SqV-functionalRel emb-times' Id (idPRel Dyn')

  -- UpL-inj-prod (d₁ , d₂) .(DynTy.prod _ _)
  --   (⊑-prod {d₁ = d₁} {d₂ = d₂} {d₁' = d₁'} {d₂' = d₂'} d₁≤d₁' d₂≤d₂') = ⊑-prod d₁≤d₁' d₂≤d₂'

  -- inj-arr
  ---------- 

  UpR-inj-arr : PBSq (idPRel (Dyn ==> 𝕃 Dyn)) inj-arr Id emb-arr'
  UpR-inj-arr f g f≤g = ⊑-fun (next f≤g)

  UpL-inj-arr : PBSq inj-arr (idPRel Dyn') emb-arr' Id
  UpL-inj-arr = SqV-functionalRel emb-arr' Id (idPRel Dyn')


  -----------------------------------------------------------------------
  -- Quasi-right representations for F inj-nat, F inj-prod, and F inj-arr
  -----------------------------------------------------------------------

  open LiftOrd
  open ExtAsEDMorphism
  open ExtMonotone

  -- inj-nat
  ----------

  DnL-inj-nat : ErrorDomSq (F-rel (idPRel Dyn')) (F-rel inj-nat) (Ext proj-nat) (Ext η-mor)
  DnL-inj-nat = Ext-sq (idPRel Dyn') (F-rel inj-nat) proj-nat η-mor α
    where
      α : PBSq (idPRel Dyn') (U-rel (F-rel inj-nat)) proj-nat η-mor
      α .(nat _) .(nat _) (⊑-nat eq) = ⊑ηη _ _ (⊑-nat eq)
      α .(prod _ _) .(prod _ _) (⊑-prod d₁⊑d₁' d₂⊑d₂') = ⊑℧⊥ _
      α .(fun _) .(fun _) (⊑-fun f~≤g~) = ⊑℧⊥ _
    

  DnR-inj-nat : ErrorDomSq (F-rel inj-nat) (F-rel (idPRel NatP)) (Ext η-mor) (Ext proj-nat)
  DnR-inj-nat = Ext-sq inj-nat (F-rel (idPRel NatP)) η-mor proj-nat α
    where
      α : PBSq inj-nat (U-rel (F-rel (idPRel NatP))) η-mor proj-nat
      α n .(nat _) (⊑-nat eq) = ⊑ηη n _ eq


  -- inj-times
  ------------

  DnL-inj-times : ErrorDomSq (F-rel (idPRel Dyn')) (F-rel inj-times) (Ext proj-times) (Ext η-mor)
  DnL-inj-times = Ext-sq (idPRel Dyn') (F-rel inj-times) proj-times η-mor α
    where
      α : PBSq (idPRel Dyn') (U-rel (F-rel inj-times)) proj-times η-mor
      α .(nat _) .(nat _) (⊑-nat x) = ⊑℧⊥ _
      α .(prod _ _) .(prod _ _) (⊑-prod p q) = ⊑ηη _ _ (⊑-prod p q)
      α .(fun _) .(fun _) (⊑-fun x) = ⊑℧⊥ _

  DnR-inj-times : ErrorDomSq (F-rel inj-times) (F-rel (idPRel (Dyn' ×dp Dyn'))) (Ext η-mor) (Ext proj-times)
  DnR-inj-times = Ext-sq inj-times (F-rel (idPRel (Dyn' ×dp Dyn'))) η-mor proj-times α
    where
      α : PBSq inj-times (U-rel (F-rel (idPRel (Dyn' ×dp Dyn')))) η-mor proj-times
      α (d₁ , d₂) .(prod _ _) (⊑-prod p q) = ⊑ηη (d₁ , d₂) (_ , _) (p , q)


  
  -- inj-arr
  ---------- 

  -- The below squares invole the morphism δ* defined as ext (δ ∘ η), where δ = θ ∘ next.
  
  DnL-inj-arr : ErrorDomSq (F-rel (idPRel Dyn')) (F-rel inj-arr) (Ext proj-arr) δ*
  DnL-inj-arr = Ext-sq (idPRel Dyn') (F-rel inj-arr) proj-arr (δ-mor ∘p η-mor) α
    where

      Fn = (Dyn ==> 𝕃 Dyn)
      module Fn = PosetBisimStr (Fn .snd)

      α : PBSq (idPRel Dyn') (U-rel (F-rel inj-arr)) proj-arr (δ-mor ∘p η-mor)
      α .(nat _) .(nat _) (⊑-nat eq) = ⊑℧⊥ _
      α .(prod _ _) .(prod _ _)
         (⊑-prod {d₁ = d₁} {d₂ = d₂} {d₁' = d₁'} {d₂' = d₂'} d₁≤d₁' d₂≤d₂') = ⊑℧⊥ _
      α .(fun _) .(fun _) (⊑-fun {f~ = f~} {g~ = g~} f~≤g~) =
        ⊑θθ _ _ (λ t → ⊑ηη _ _ (⊑-fun
          (λ t' →
            -- Need to use tick-irrelevance to show that (f~ t) ≡ (f~ t')
            let tirr = tick-irrelevance f~ t t' in 
            transport (λ i → Fn._≤_ (tirr (~ i)) (g~ t')) (f~≤g~ t'))))
            

  DnR-inj-arr : ErrorDomSq (F-rel inj-arr) (F-rel (idPRel (Dyn ==> 𝕃 Dyn))) δ* (Ext proj-arr)
  DnR-inj-arr = Ext-sq inj-arr (F-rel (idPRel (Dyn ==> 𝕃 Dyn))) (δ-mor ∘p η-mor) proj-arr α
    where
      -- delay : PBMor (Dyn ==> 𝕃 Dyn) (𝕃 (Dyn ==> 𝕃 Dyn))
      -- delay = δ-mor ∘p η-mor 

      α : PBSq inj-arr (U-rel (F-rel (idPRel (Dyn ==> 𝕃 Dyn)))) (δ-mor ∘p η-mor) proj-arr
      α f .(DynTy.fun _) (⊑-fun {f~ = f~} {g~ = g~} H~) =
        ⊑θθ _ _ λ t → ⊑ηη f (g~ t) (H~ t)

  
