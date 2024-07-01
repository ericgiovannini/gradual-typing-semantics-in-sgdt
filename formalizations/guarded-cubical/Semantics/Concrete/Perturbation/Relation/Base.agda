{- Extension of pertubrations from types to relations, and push-pull -}
{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
module Semantics.Concrete.Perturbation.Relation.Base (k : Clock) where

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

  VRelPtbSq : ⟨ MA ⟩ → ⟨ MA' ⟩ → Type _
  VRelPtbSq pA pA' = PBSq c c (iA .fst pA .fst) (iA' .fst pA' .fst)

  isPropVRelPtbSq : ∀ pA pA' → isProp (VRelPtbSq pA pA')
  isPropVRelPtbSq pA pA' = isPropPBSq c c (iA .fst pA .fst) (iA' .fst pA' .fst)

  |VRelPtb| : Type _
  |VRelPtb| = Σ[ pA ∈ ⟨ MA ⟩ ] Σ[ pA' ∈ ⟨ MA' ⟩ ] VRelPtbSq pA pA'

  opaque 
    VRelPtb≡ : {sq1 sq2 : |VRelPtb|} → (sq1 .fst ≡ sq2 .fst) → (sq1 .snd .fst ≡ sq2 .snd .fst) → sq1 ≡ sq2
    VRelPtb≡ {sq1} {sq2} pfst psnd = ΣPathP (pfst , (ΣPathPProp (λ pA' →
      isPropPBSq c c (iA .fst (sq2 .fst) .fst) (iA' .fst pA' .fst)) psnd))

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
    VRelPtb≡ (MA .snd .isMonoid .·IdL pA) (MA' .snd .isMonoid .·IdL pA')
  VRelPtb .snd .isMonoid .·IdR (pA , pA' , pSq) =
    VRelPtb≡ (MA .snd .isMonoid .·IdR pA) (MA' .snd .isMonoid .·IdR pA')
  VRelPtb .snd .isMonoid .isSemigroup .·Assoc (pA , pA' , pSq) (qA , qA' , qSq) (rA , rA' , rSq) =
    VRelPtb≡ (MA .snd .isMonoid .isSemigroup .·Assoc pA qA rA) (MA' .snd .isMonoid .isSemigroup .·Assoc pA' qA' rA')
  VRelPtb .snd .isMonoid .isSemigroup .is-set =
    isSetΣ (MA .snd .isSemigroup .is-set) λ pA →
    isSetΣ (MA' .snd .isSemigroup .is-set) λ pA' →
    isProp→isSet (isPropVRelPtbSq pA pA')

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

  module _ {M : Monoid ℓ''} where
    corec : ∀ (ϕ : MonoidHom M MA) (ϕ' : MonoidHom M MA')
          → (∀ m → PBSq c c (iA .fst (ϕ .fst m) .fst) (iA' .fst (ϕ' .fst m) .fst))
          → MonoidHom M VRelPtb
    corec ϕ ϕ' ϕSq .fst m = (ϕ .fst m) , (ϕ' .fst m , ϕSq m)
    corec ϕ ϕ' ϕSq .snd .presε = VRelPtb≡ (ϕ .snd .presε) (ϕ' .snd .presε)
    corec ϕ ϕ' ϕSq .snd .pres· p q = VRelPtb≡ (ϕ .snd .pres· p q) (ϕ' .snd .pres· p q)

    corecFact1 : {ϕ : MonoidHom M MA} (ϕ' : MonoidHom M MA')
        → (∀ m → PBSq c c (iA .fst (ϕ .fst m) .fst) (iA' .fst (ϕ' .fst m) .fst))
        → factorization π1 ϕ
    corecFact1 {ϕ} ϕ' ϕSq = (corec ϕ ϕ' ϕSq) , eqMonoidHom _ _ refl

    corecFact2 : (ϕ : MonoidHom M MA) {ϕ' : MonoidHom M MA'}
        → (∀ m → PBSq c c (iA .fst (ϕ .fst m) .fst) (iA' .fst (ϕ' .fst m) .fst))
        → factorization π2 ϕ'
    corecFact2 ϕ {ϕ'} ϕSq = (corec ϕ ϕ' ϕSq) , eqMonoidHom _ _ refl

  corecPushV : (ϕ' : MonoidHom MA MA')
        → (∀ m → PBSq c c (iA .fst m .fst) (iA' .fst (ϕ' .fst m) .fst))
        → sectionHom π1
  corecPushV ϕ' ϕSq = corecFact1 ϕ' ϕSq

  corecPullV : (ϕ : MonoidHom MA' MA)
        → (∀ m' → PBSq c c (iA .fst (ϕ .fst m') .fst) (iA' .fst m' .fst))
        → sectionHom π2
  corecPullV ϕ ϕSq = corecFact2 ϕ ϕSq

module _ (A : ValType ℓ ℓ≤ ℓ≈ ℓM) (A' : ValType ℓ' ℓ≤' ℓ≈' ℓM') where
  VRelPP : ∀ (ℓc : Level) → Type _
  VRelPP ℓc = Σ[ c ∈ PBRel (ValType→Predomain A) (ValType→Predomain A') ℓc ]
    PushV A A' c
    × PullV A A' c
module _ {A : ValType ℓ ℓ≤ ℓ≈ ℓM} {A' : ValType ℓ' ℓ≤' ℓ≈' ℓM'} {ℓc}
         (c : VRelPP A A' ℓc)
  where
  pushV : MonoidHom (A .snd .PtbV) (A' .snd .PtbV)
  pushV = π2 _ _ _ ∘hom c .snd .fst .fst

  pushVSq : ∀ pA → VRelPtbSq A A' (c .fst) pA (pushV .fst pA)
  pushVSq pA = subst (λ pA' → VRelPtbSq A A' (c .fst) pA' (pushV .fst pA))
    (funExt⁻ (cong fst (c .snd .fst .snd)) pA)
    (c .snd .fst .fst .fst pA .snd .snd)

  pullV : MonoidHom (A' .snd .PtbV) (A .snd .PtbV)
  pullV = π1 _ _ _ ∘hom c .snd .snd .fst

  pullVSq : ∀ pA' → VRelPtbSq A A' (c .fst) (pullV .fst pA') pA'
  pullVSq pA' = subst (λ pA → VRelPtbSq A A' (c .fst) (pullV .fst pA') pA)
    (funExt⁻ (cong fst (c .snd .snd .snd)) pA')
    (c .snd .snd .fst .fst pA' .snd .snd)
