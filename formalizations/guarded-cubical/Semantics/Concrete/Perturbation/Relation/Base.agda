{-
   Extension of pertubrations from types to relations, and push-pull

   In principle this construction could be abstracted to work on any
   double category with perturbations but for now at least we copy the
   construction for value relations and computation relations
-}

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
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions hiding (π1; π2)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.Combinators
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Predomain.Kleisli k

open import Semantics.Concrete.Perturbation.Semantic k
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

-- open ValTypeStr
open MonoidStr
open IsMonoidHom
open IsSemigroup
open IsMonoid



module _ (A : ValType ℓ ℓ≤ ℓ≈ ℓM) (A' : ValType ℓ' ℓ≤' ℓ≈' ℓM')
         (c : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc)
  where
  private
    MA = PtbV A
    iA = interpV A
    MA' = PtbV A'
    iA' = interpV A'

  VRelPtbSq : ⟨ MA ⟩ → ⟨ MA' ⟩ → Type _
  VRelPtbSq pA pA' = PSq c c (iA .fst pA .fst) (iA' .fst pA' .fst)

  isPropVRelPtbSq : ∀ pA pA' → isProp (VRelPtbSq pA pA')
  isPropVRelPtbSq pA pA' = isPropPSq c c (iA .fst pA .fst) (iA' .fst pA' .fst)

  |VRelPtb| : Type _
  |VRelPtb| = Σ[ pA ∈ ⟨ MA ⟩ ] Σ[ pA' ∈ ⟨ MA' ⟩ ] VRelPtbSq pA pA'

  opaque
    VRelPtb≡ : {sq1 sq2 : |VRelPtb|} → (sq1 .fst ≡ sq2 .fst) → (sq1 .snd .fst ≡ sq2 .snd .fst) → sq1 ≡ sq2
    VRelPtb≡ {sq1} {sq2} pfst psnd = ΣPathP (pfst , (ΣPathPProp (isPropVRelPtbSq (sq2 .fst)) psnd))

  VRelPtb : Monoid _
  VRelPtb .fst = |VRelPtb|
  VRelPtb .snd .ε .fst      = MA .snd .ε
  VRelPtb .snd .ε .snd .fst = MA' .snd .ε
  VRelPtb .snd .ε .snd .snd = subst2
    (PSq c c)
    (cong fst (sym (iA .snd .presε)))
    (cong fst (sym (iA' .snd .presε)))
    (Predom-IdSqV c)
  VRelPtb .snd ._·_ (pA , pA' , pSq) (qA , qA' , qSq) .fst      =
    MA .snd ._·_ pA qA
  VRelPtb .snd ._·_ (pA , pA' , pSq) (qA , qA' , qSq) .snd .fst =
    MA' .snd ._·_ pA' qA'
  VRelPtb .snd ._·_ (pA , pA' , pSq) (qA , qA' , qSq) .snd .snd =
    subst2
      (PSq c c)
      (cong fst (sym (iA .snd .pres· pA qA)))
      (cong fst (sym (iA' .snd .pres· pA' qA')))
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

  π1V : MonoidHom VRelPtb MA
  π1V .fst sq = sq .fst
  π1V .snd .presε = refl
  π1V .snd .pres· x y = refl

  π2V : MonoidHom VRelPtb MA'
  π2V .fst sq = sq .snd .fst
  π2V .snd .presε = refl
  π2V .snd .pres· x y = refl

  PushV = sectionHom π1V
  PullV = sectionHom π2V

  module _ {M : Monoid ℓ''} where
    corecV : ∀ (ϕ : MonoidHom M MA) (ϕ' : MonoidHom M MA')
          → (∀ m → PSq c c (iA .fst (ϕ .fst m) .fst) (iA' .fst (ϕ' .fst m) .fst))
          → MonoidHom M VRelPtb
    corecV ϕ ϕ' ϕSq .fst m = (ϕ .fst m) , (ϕ' .fst m , ϕSq m)
    corecV ϕ ϕ' ϕSq .snd .presε = VRelPtb≡ (ϕ .snd .presε) (ϕ' .snd .presε)
    corecV ϕ ϕ' ϕSq .snd .pres· p q = VRelPtb≡ (ϕ .snd .pres· p q) (ϕ' .snd .pres· p q)

    corecVFact1 : {ϕ : MonoidHom M MA} (ϕ' : MonoidHom M MA')
        → (∀ m → PSq c c (iA .fst (ϕ .fst m) .fst) (iA' .fst (ϕ' .fst m) .fst))
        → factorization π1V ϕ
    corecVFact1 {ϕ} ϕ' ϕSq = (corecV ϕ ϕ' ϕSq) , eqMonoidHom _ _ refl

    corecVFact2 : (ϕ : MonoidHom M MA) {ϕ' : MonoidHom M MA'}
        → (∀ m → PSq c c (iA .fst (ϕ .fst m) .fst) (iA' .fst (ϕ' .fst m) .fst))
        → factorization π2V ϕ'
    corecVFact2 ϕ {ϕ'} ϕSq = (corecV ϕ ϕ' ϕSq) , eqMonoidHom _ _ refl

  corecPushV : (ϕ' : MonoidHom MA MA')
        → (∀ m → PSq c c (iA .fst m .fst) (iA' .fst (ϕ' .fst m) .fst))
        → sectionHom π1V
  corecPushV ϕ' ϕSq = corecVFact1 ϕ' ϕSq

  corecPullV : (ϕ : MonoidHom MA' MA)
        → (∀ m' → PSq c c (iA .fst (ϕ .fst m') .fst) (iA' .fst m' .fst))
        → sectionHom π2V
  corecPullV ϕ ϕSq = corecVFact2 ϕ ϕSq

module _ (A : ValType ℓ ℓ≤ ℓ≈ ℓM) (A' : ValType ℓ' ℓ≤' ℓ≈' ℓM') where
  VRelPP : ∀ (ℓc : Level) → Type _
  VRelPP ℓc = Σ[ c ∈ PRel (ValType→Predomain A) (ValType→Predomain A') ℓc ]
    PushV A A' c
    × PullV A A' c

module _ {A : ValType ℓ ℓ≤ ℓ≈ ℓM} {A' : ValType ℓ' ℓ≤' ℓ≈' ℓM'} {ℓc}
         (c : VRelPP A A' ℓc)
  where

  private
    MA = PtbV A
    iA = interpV A
    MA' = PtbV A'
    iA' = interpV A'

  pushV : MonoidHom MA MA'
  pushV = π2V _ _ _ ∘hom c .snd .fst .fst

  pushVSq : ∀ pA → VRelPtbSq A A' (c .fst) pA (pushV .fst pA)
  pushVSq pA = subst (λ pA' → VRelPtbSq A A' (c .fst) pA' (pushV .fst pA))
    (funExt⁻ (cong fst (c .snd .fst .snd)) pA)
    (c .snd .fst .fst .fst pA .snd .snd)

  pullV : MonoidHom MA' MA
  pullV = π1V _ _ _ ∘hom c .snd .snd .fst

  pullVSq : ∀ pA' → VRelPtbSq A A' (c .fst) (pullV .fst pA') pA'
  pullVSq pA' = subst (λ pA → VRelPtbSq A A' (c .fst) (pullV .fst pA') pA)
    (funExt⁻ (cong fst (c .snd .snd .snd)) pA')
    (c .snd .snd .fst .fst pA' .snd .snd)

module _ (B : CompType ℓ ℓ≤ ℓ≈ ℓM) (B' : CompType ℓ' ℓ≤' ℓ≈' ℓM') {ℓd}
         (d : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd)
  where
  private
    MB = B .snd .snd .fst
    module MB = MonoidStr (MB .snd)
    iB = B .snd .snd .snd
    MB' = B' .snd .snd .fst
    module MB' = MonoidStr (MB' .snd)
    iB' = B' .snd .snd .snd

  CRelPtbSq : ⟨ MB ⟩ → ⟨ MB' ⟩ → Type _
  CRelPtbSq pB pB' = ErrorDomSq d d (iB .fst pB .fst) (iB' .fst pB' .fst)

  isPropCRelPtbSq : ∀ pB pB' → isProp (CRelPtbSq pB pB')
  isPropCRelPtbSq pB pB' = isPropErrorDomSq d d (iB .fst pB .fst) (iB' .fst pB' .fst)

  |CRelPtb| : Type _
  |CRelPtb| = Σ[ pB ∈ ⟨ MB ⟩ ] Σ[ pB' ∈ ⟨ MB' ⟩ ] CRelPtbSq pB pB'

  opaque
    CRelPtb≡ : {sq1 sq2 : |CRelPtb|} → (sq1 .fst ≡ sq2 .fst) → (sq1 .snd .fst ≡ sq2 .snd .fst) → sq1 ≡ sq2
    CRelPtb≡ {sq1} {sq2} pfst psnd = ΣPathP (pfst , (ΣPathPProp (isPropCRelPtbSq (sq2 .fst)) psnd))

  CRelPtb : Monoid _
  CRelPtb .fst = |CRelPtb|
  CRelPtb .snd .ε .fst      = MB .snd .ε
  CRelPtb .snd .ε .snd .fst = MB' .snd .ε
  CRelPtb .snd .ε .snd .snd = subst2 (ErrorDomSq d d)
    (cong fst (sym (iB .snd .presε)))
    (cong fst (sym (iB' .snd .presε)))
    (ED-IdSqV d)
  CRelPtb .snd ._·_ (pB , pB' , pSq) (qB , qB' , qSq) .fst      = pB MB.· qB
  CRelPtb .snd ._·_ (pB , pB' , pSq) (qB , qB' , qSq) .snd .fst = pB' MB'.· qB'
  CRelPtb .snd ._·_ (pB , pB' , pSq) (qB , qB' , qSq) .snd .snd =
    subst2 (ErrorDomSq d d)
      (cong fst (sym (iB .snd .pres· pB qB)))
      (cong fst (sym (iB' .snd .pres· pB' qB')))
      (ED-CompSqV {d₁ = d}{d₂ = d}{d₃ = d}
        {ϕ₁ = iB .fst qB .fst}{ϕ₁' = iB' .fst qB' .fst}
        {ϕ₂ = iB .fst pB .fst}{ϕ₂' = iB' .fst pB' .fst}
        qSq pSq)
  CRelPtb .snd .isMonoid .·IdR (pB , pB' , pSq) = CRelPtb≡ (MB .snd .isMonoid .·IdR pB) (MB' .snd .isMonoid .·IdR pB')
  CRelPtb .snd .isMonoid .·IdL (pB , pB' , pSq) = CRelPtb≡ (MB .snd .isMonoid .·IdL pB) (MB' .snd .isMonoid .·IdL pB')
  CRelPtb .snd .isMonoid .isSemigroup .·Assoc (pB , pB' , pSq) (qB , qB' , qSq) (rB , rB' , rSq) =
    CRelPtb≡ (MB .snd .isMonoid .isSemigroup .·Assoc pB qB rB) (MB' .snd .isMonoid .isSemigroup .·Assoc pB' qB' rB')
  CRelPtb .snd .isMonoid .isSemigroup .is-set =
    isSetΣ (MB .snd .isSemigroup .is-set) λ pB →
    isSetΣ (MB' .snd .isSemigroup .is-set) λ pB' →
    isProp→isSet (isPropCRelPtbSq pB pB')

  π1C : MonoidHom CRelPtb MB
  π1C .fst sq = sq .fst
  π1C .snd .presε = refl
  π1C .snd .pres· x y = refl

  π2C : MonoidHom CRelPtb MB'
  π2C .fst sq = sq .snd .fst
  π2C .snd .presε = refl
  π2C .snd .pres· x y = refl

  PushC = sectionHom π1C
  PullC = sectionHom π2C

  module _ {M : Monoid ℓ''} where
    corecC : ∀ (ϕ : MonoidHom M MB) (ϕ' : MonoidHom M MB')
          → (∀ m → ErrorDomSq d d (iB .fst (ϕ .fst m) .fst) (iB' .fst (ϕ' .fst m) .fst))
          → MonoidHom M CRelPtb
    corecC ϕ ϕ' ϕSq .fst m = (ϕ .fst m) , (ϕ' .fst m , ϕSq m)
    corecC ϕ ϕ' ϕSq .snd .presε = CRelPtb≡ (ϕ .snd .presε) (ϕ' .snd .presε)
    corecC ϕ ϕ' ϕSq .snd .pres· p q = CRelPtb≡ (ϕ .snd .pres· p q) (ϕ' .snd .pres· p q)

    corecCFact1 : {ϕ : MonoidHom M MB} (ϕ' : MonoidHom M MB')
        → (∀ m → ErrorDomSq d d (iB .fst (ϕ .fst m) .fst) (iB' .fst (ϕ' .fst m) .fst))
        → factorization π1C ϕ
    corecCFact1 {ϕ} ϕ' ϕSq = (corecC ϕ ϕ' ϕSq) , eqMonoidHom _ _ refl

    corecCFact2 : (ϕ : MonoidHom M MB) {ϕ' : MonoidHom M MB'}
        → (∀ m → ErrorDomSq d d (iB .fst (ϕ .fst m) .fst) (iB' .fst (ϕ' .fst m) .fst))
        → factorization π2C ϕ'
    corecCFact2 ϕ {ϕ'} ϕSq = (corecC ϕ ϕ' ϕSq) , eqMonoidHom _ _ refl

  corecPushC : (ϕ' : MonoidHom MB MB')
        → (∀ m → ErrorDomSq d d (iB .fst m .fst) (iB' .fst (ϕ' .fst m) .fst))
        → sectionHom π1C
  corecPushC ϕ' ϕSq = corecCFact1 ϕ' ϕSq

  corecPullC : (ϕ : MonoidHom MB' MB)
        → (∀ m' → ErrorDomSq d d (iB .fst (ϕ .fst m') .fst) (iB' .fst m' .fst))
        → sectionHom π2C
  corecPullC ϕ ϕSq = corecCFact2 ϕ ϕSq

module _ (B : CompType ℓ ℓ≤ ℓ≈ ℓM) (B' : CompType ℓ' ℓ≤' ℓ≈' ℓM') where
  CRelPP : ∀ (ℓd : Level) → Type _
  CRelPP ℓd = Σ[ d ∈ ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd ]
    PushC B B' d
    × PullC B B' d

module _ {B : CompType ℓ ℓ≤ ℓ≈ ℓM} {B' : CompType ℓ' ℓ≤' ℓ≈' ℓM'} {ℓd}
         (d : CRelPP B B' ℓd)
  where
  private
    MB = B .snd .snd .fst
    module MB = MonoidStr (MB .snd)
    iB = B .snd .snd .snd
    MB' = B' .snd .snd .fst
    module MB' = MonoidStr (MB' .snd)
    iB' = B' .snd .snd .snd

  pushC : MonoidHom MB MB'
  pushC = π2C _ _ _ ∘hom d .snd .fst .fst

  pushCSq : ∀ pB → CRelPtbSq B B' (d .fst) pB (pushC .fst pB)
  pushCSq pB = subst (λ pB' → CRelPtbSq B B' (d .fst) pB' (pushC .fst pB))
    (funExt⁻ (cong fst (d .snd .fst .snd)) pB)
    (d .snd .fst .fst .fst pB .snd .snd)

  pullC : MonoidHom MB' MB
  pullC = π1C _ _ _ ∘hom d .snd .snd .fst

  pullCSq : ∀ pB → CRelPtbSq B B' (d .fst) (pullC .fst pB) pB
  pullCSq pB = subst (λ pB' → CRelPtbSq B B' (d .fst) (pullC .fst pB) pB')
    (funExt⁻ (cong fst (d .snd .snd .snd)) pB)
    (d .snd .snd .fst .fst pB .snd .snd)
