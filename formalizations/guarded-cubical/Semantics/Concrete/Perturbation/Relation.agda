{- Extension of pertubrations from types to relations, and push-pull -}
{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
module Semantics.Concrete.Perturbation.Relation (k : Clock) where

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
open import Semantics.Concrete.Types.Base k

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
module _ (A : ValType ℓ ℓ≤ ℓ≈ ℓM) (A' : ValType ℓ' ℓ≤' ℓ≈' ℓM')
         (c : PBRel (ValType→Predomain A) (ValType→Predomain A') ℓc)
  where
  private
    MA = A .snd .PtbV
    iA = A .snd .interpV
    MA' = A' .snd .PtbV
    iA' = A' .snd .interpV

  |VRelPtb| : Type _
  |VRelPtb| =
    Σ[ pA ∈ ⟨ A .snd .PtbV ⟩ ]
    Σ[ pA' ∈ ⟨ A' .snd .PtbV ⟩ ]
    PBSq c c (A .snd .interpV .fst pA .fst) (A' .snd .interpV .fst pA' .fst)

  VRelPtb : Monoid _
  VRelPtb .fst = |VRelPtb|
  VRelPtb .snd .ε .fst      = MA .snd .ε
  VRelPtb .snd .ε .snd .fst = MA' .snd .ε
  VRelPtb .snd .ε .snd .snd = subst2
    (PBSq c c)
    (cong fst (sym (A .snd .interpV .snd .presε))) 
    (cong fst (sym (A' .snd .interpV .snd .presε))) 
    (Predom-IdSqV c)
  VRelPtb .snd ._·_ (pA , pA' , pSq) (qA , qA' , qSq) .fst      =
    MA .snd ._·_ pA qA
  VRelPtb .snd ._·_ (pA , pA' , pSq) (qA , qA' , qSq) .snd .fst =
    MA' .snd ._·_ pA' qA'
  VRelPtb .snd ._·_ (pA , pA' , pSq) (qA , qA' , qSq) .snd .snd =
    subst2
      (PBSq c c)
      (cong fst (sym (A .snd .interpV .snd .pres· pA qA)))
      (cong fst (sym (A' .snd .interpV .snd .pres· pA' qA')))
      (CompSqV {c₁ = c}{c₂ = c}{c₃ = c}
        {f₁ = iA .fst qA .fst}{g₁ = iA' .fst qA' .fst}
        {f₂ = iA .fst pA .fst}{g₂ = iA' .fst pA' .fst}
        qSq pSq)
  VRelPtb .snd .isMonoid .·IdL (pA , pA' , pSq) =
    ΣPathP ((MA .snd .isMonoid .·IdL pA) , ΣPathPProp (λ pA' → isPropPBSq c c (iA .fst pA .fst) (iA' .fst pA' .fst) ) (MA' .snd .isMonoid .·IdL pA'))
  VRelPtb .snd .isMonoid .·IdR (pA , pA' , pSq) =
    ΣPathP ((MA .snd .isMonoid .·IdR pA) , ΣPathPProp (λ pA' → isPropPBSq c c (iA .fst pA .fst) (iA' .fst pA' .fst) ) (MA' .snd .isMonoid .·IdR pA'))
  VRelPtb .snd .isMonoid .isSemigroup .·Assoc (pA , pA' , pSq) (qA , qA' , qSq) (rA , rA' , rSq) =
    ΣPathP ((MA .snd .isMonoid .isSemigroup .·Assoc pA qA rA)
      , (ΣPathPProp (λ pA' → isPropPBSq c c ((iA .fst (MA .snd ._·_ (MA .snd ._·_ pA qA) rA) .fst)) ((iA' .fst pA' .fst) ))
      ((MA' .snd .isMonoid .isSemigroup .·Assoc pA' qA' rA'))))
  VRelPtb .snd .isMonoid .isSemigroup .is-set =
    isSetΣ (MA .snd .isSemigroup .is-set) λ _ →
    isSetΣ (MA' .snd .isSemigroup .is-set) λ _ →
    isProp→isSet (isPropPBSq _ _ _ _)

  π1 : MonoidHom VRelPtb MA
  π1 .fst sq = sq .fst
  π1 .snd .presε = refl
  π1 .snd .pres· x y = refl

  π2 : MonoidHom VRelPtb MA'
  π2 .fst sq = sq .snd .fst
  π2 .snd .presε = refl
  π2 .snd .pres· x y = refl

  PushV = sectionHom π1
  PullV = sectionHom π2

module _ (A : ValType ℓ ℓ≤ ℓ≈ ℓM) (A' : ValType ℓ' ℓ≤' ℓ≈' ℓM') where
  VrelPP : ∀ (ℓc : Level) → Type _
  VrelPP ℓc = Σ[ c ∈ PBRel (ValType→Predomain A) (ValType→Predomain A') ℓc ]
    PushV A A' c
    × PullV A A' c
  
