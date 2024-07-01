{- Extension of pertubrations from types to relations, and push-pull -}
{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
module Semantics.Concrete.Perturbation.Relation.Constructions (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_)


open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct as FP

open import Common.Common
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions hiding (π1; π2)
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.KleisliFunctors k

open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Types k as Types
open import Semantics.Concrete.Perturbation.Relation.Base k

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓ≤' ℓ≈' ℓM' : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓc ℓc' ℓd ℓd' : Level
  
    ℓA₁   ℓ≤A₁   ℓ≈A₁   : Level
    ℓA₁'  ℓ≤A₁'  ℓ≈A₁'  : Level
    ℓA₂   ℓ≤A₂   ℓ≈A₂   : Level
    ℓA₂'  ℓ≤A₂'  ℓ≈A₂'  : Level
    ℓA₃   ℓ≤A₃   ℓ≈A₃   : Level
    ℓA₃'  ℓ≤A₃'  ℓ≈A₃'  : Level

    ℓB₁   ℓ≤B₁   ℓ≈B₁   : Level
    ℓB₁'  ℓ≤B₁'  ℓ≈B₁'  : Level
    ℓB₂   ℓ≤B₂   ℓ≈B₂   : Level
    ℓB₂'  ℓ≤B₂'  ℓ≈B₂'  : Level
    ℓB₃   ℓ≤B₃   ℓ≈B₃   : Level
    ℓB₃'  ℓ≤B₃'  ℓ≈B₃'  : Level

    ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ : Level
    ℓAₒ ℓ≤Aₒ ℓ≈Aₒ : Level
    ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ : Level
    ℓBₒ ℓ≤Bₒ ℓ≈Bₒ : Level
   
    ℓc₁ ℓc₂ ℓc₃  : Level

    ℓMA₁ ℓMA₂ ℓMA₃ : Level
    ℓMA₁' ℓMA₂' ℓMA₃' : Level
    ℓMB₁ ℓMB₂ ℓMB₃ : Level
    ℓMAᵢ ℓMAₒ ℓMBᵢ ℓMBₒ : Level

open ValTypeStr
open MonoidStr
open IsMonoidHom
open IsSemigroup
open IsMonoid

module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} where
  private
    iA = A .snd .interpV
  IdRelV : VRelPP A A _
  IdRelV .fst = idPRel _
  IdRelV .snd .fst = corecPushV _ _ _ (idMon _) λ pA → Predom-IdSqH (iA .fst pA .fst)
  IdRelV .snd .snd = corecPullV _ _ _ (idMon _)λ pA → Predom-IdSqH (iA .fst pA .fst)

module _  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁}{A₁' : ValType ℓA₁' ℓ≤A₁' ℓ≈A₁' ℓMA₁'}
          {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂}{A₂' : ValType ℓA₂' ℓ≤A₂' ℓ≈A₂' ℓMA₂'}
  where
  _×PP_ : (c₁ : VRelPP A₁ A₁' ℓc₁) (c₂ : VRelPP A₂ A₂' ℓc₂)
        → VRelPP (A₁ Types.× A₂) (A₁' Types.× A₂') _
  (c₁ ×PP c₂) .fst = c₁ .fst ×pbmonrel c₂ .fst
  (c₁ ×PP c₂) .snd .fst = elimSection _
    (corecFact1 _ _ _ (i₁ ∘hom pushV c₁) λ pA₁ (a₁ , a₂) (a₁' , a₂') ×-rel →
      pushVSq c₁ pA₁ _ _ (×-rel .fst) , ×-rel .snd)
    (corecFact1 _ _ _ (i₂ ∘hom pushV c₂) (λ pA₂ (a₁ , a₂) (a₁' , a₂') ×-rel →
      (×-rel .fst) , pushVSq c₂ pA₂ _ _ (×-rel .snd)))
  (c₁ ×PP c₂) .snd .snd = elimSection _
    (corecFact2 _ _ _ (i₁ ∘hom pullV c₁) (λ pA₁' _ _ ×-rel →
      pullVSq c₁ pA₁' _ _ (×-rel .fst) , ×-rel .snd))
    (corecFact2 _ _ _ (i₂ ∘hom pullV c₂) (λ pA₂' _ _ ×-rel →
      ×-rel .fst , pullVSq c₂ pA₂' _ _ (×-rel .snd)))
