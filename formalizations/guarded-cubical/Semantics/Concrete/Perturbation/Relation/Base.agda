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
open import Cubical.Data.Sigma as Data
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_)


open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.Instances.CartesianProduct as Monoid
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Sigma

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


  opaque
    VRelPtb : Monoidᴰ (MA Monoid.× MA') (ℓ-max (ℓ-max ℓ ℓ') ℓc)
    VRelPtb = submonoid→Monoidᴰ (record
      { eltᴰ = λ (pA , pA') → VRelPtbSq pA pA'
      ; εᴰ = subst2
        (PSq c c)
        (cong fst (sym (iA .snd .presε)))
        (cong fst (sym (iA' .snd .presε)))
        (Predom-IdSqV c)
      ; _·ᴰ_ = λ {(pA , pA')}{(qA , qA')} pSq qSq →
        subst2
        (PSq c c)
        (cong fst (sym (iA .snd .pres· pA qA)))
        (cong fst (sym (iA' .snd .pres· pA' qA')))
        (CompSqV {c₁ = c}{c₂ = c}{c₃ = c}
          {f₁ = iA .fst qA .fst}{g₁ = iA' .fst qA' .fst}
          {f₂ = iA .fst pA .fst}{g₂ = iA' .fst pA' .fst}
          qSq pSq)
      ; isPropEltᴰ = isPropVRelPtbSq _ _
      })

    Sq→VRelPtb : ∀ {pA pA'} → VRelPtbSq pA pA' → VRelPtb .Monoidᴰ.eltᴰ (pA , pA')
    Sq→VRelPtb sq = sq

  PushV = Section (Σl VRelPtb)
  PullV = Section (Σr VRelPtb)

module _ {A : ValType ℓ ℓ≤ ℓ≈ ℓM} {A' : ValType ℓ' ℓ≤' ℓ≈' ℓM'}
         {c : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc} where

  opaque
    unfolding VRelPtb
    corecVRelPtb : ∀ {ℓm}{M : Monoid ℓm}{ϕ : MonoidHom M _}
      → (∀ x → VRelPtbSq A A' c (ϕ .fst x .fst) (ϕ .fst x .snd))
      → LocalSection ϕ (VRelPtb A A' c)
    corecVRelPtb = mkSectionSubmonoid (λ _ → isPropVRelPtbSq A A' c _ _)

module _ (A : ValType ℓ ℓ≤ ℓ≈ ℓM) (A' : ValType ℓ' ℓ≤' ℓ≈' ℓM') where
  VRelPP : ∀ (ℓc : Level) → Type _
  VRelPP ℓc = Σ[ c ∈ PRel (ValType→Predomain A) (ValType→Predomain A') ℓc ]
    PushV A A' c Data.× PullV A A' c

  mkVRelPP :
    (c : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc) →
    PushV A A' c →
    PullV A A' c →
    VRelPP ℓc
  mkVRelPP c push pull = c , push , pull

module _ {A : ValType ℓ ℓ≤ ℓ≈ ℓM} {A' : ValType ℓ' ℓ≤' ℓ≈' ℓM'} {ℓc}
         (c : VRelPP A A' ℓc)
  where

  private
    MA = PtbV A
    iA = interpV A
    MA' = PtbV A'
    iA' = interpV A'

  VRelPP→PredomainRel : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc
  VRelPP→PredomainRel = fst c

  pushV : MonoidHom MA MA'
  pushV = fstL' ∘hom corecΣ _ (c .snd .fst)

  opaque
    unfolding VRelPtb
    pushVSq : ∀ pA → VRelPtbSq A A' (c .fst) pA (pushV .fst pA)
    pushVSq pA = snd (c .snd .fst .fst pA)

  pullV : MonoidHom MA' MA
  pullV = fstR' ∘hom corecΣ _ (c .snd .snd)

  opaque
    unfolding VRelPtb
    pullVSq : ∀ pA' → VRelPtbSq A A' (c .fst) (pullV .fst pA') pA'
    pullVSq pA' = snd (c .snd .snd .fst pA')

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
  isPropCRelPtbSq pB pB' =
    isPropErrorDomSq d d (iB .fst pB .fst) (iB' .fst pB' .fst)

  opaque
    CRelPtb : Monoidᴰ (MB Monoid.× MB') (ℓ-max (ℓ-max ℓ ℓ') ℓd)
    CRelPtb = submonoid→Monoidᴰ (record
      { eltᴰ = λ (pB , pB') → CRelPtbSq pB pB'
      ; εᴰ = subst2 (ErrorDomSq d d)
        (cong fst (sym (iB .snd .presε)))
        (cong fst (sym (iB' .snd .presε)))
        (ED-IdSqV d)
      ; _·ᴰ_ = λ {(pB , pB')}{(qB , qB')} pSq qSq → subst2 (ErrorDomSq d d)
        (cong fst (sym (iB .snd .pres· pB qB)))
        (cong fst (sym (iB' .snd .pres· pB' qB')))
        (ED-CompSqV {d₁ = d}{d₂ = d}{d₃ = d}
          {ϕ₁ = iB .fst qB .fst}{ϕ₁' = iB' .fst qB' .fst}
          {ϕ₂ = iB .fst pB .fst}{ϕ₂' = iB' .fst pB' .fst}
          qSq pSq)
      ; isPropEltᴰ = isPropCRelPtbSq _ _
      })
      
    Sq→CRelPtb : ∀ {pB pB'} → CRelPtbSq pB pB' → CRelPtb .Monoidᴰ.eltᴰ (pB , pB')
    Sq→CRelPtb sq = sq

  PushC = Section (Σl CRelPtb)
  PullC = Section (Σr CRelPtb)

module _ {B : CompType ℓ ℓ≤ ℓ≈ ℓM} {B' : CompType ℓ' ℓ≤' ℓ≈' ℓM'}
         {d : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd} where

  opaque
    unfolding CRelPtb
    corecCRelPtb : ∀ {ℓm}{M : Monoid ℓm}{ϕ : MonoidHom M _}
      → (∀ x → CRelPtbSq B B' d (ϕ .fst x .fst) (ϕ .fst x .snd))
      → LocalSection ϕ (CRelPtb B B' d)
    corecCRelPtb = mkSectionSubmonoid (λ _ → isPropCRelPtbSq B B' d _ _)


module _ (B : CompType ℓ ℓ≤ ℓ≈ ℓM) (B' : CompType ℓ' ℓ≤' ℓ≈' ℓM') where
  CRelPP : ∀ (ℓd : Level) → Type _
  CRelPP ℓd = Σ[ d ∈ ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd ]
    PushC B B' d
    Data.× PullC B B' d

  mkCRelPP :
    (d : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd) →
    PushC B B' d →
    PullC B B' d →
    CRelPP ℓd
  mkCRelPP d push pull = d , push , pull

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

  CRelPP→ErrorDomRel : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd
  CRelPP→ErrorDomRel = fst d

  pushC : MonoidHom MB MB'
  pushC = fstL' ∘hom corecΣ _ (d .snd .fst)

  opaque
    unfolding CRelPtb
    pushCSq : ∀ pB → CRelPtbSq B B' (d .fst) pB (pushC .fst pB)
    pushCSq pB = snd (d .snd .fst .fst pB)

  pullC : MonoidHom MB' MB
  pullC = fstR' ∘hom corecΣ _ (d .snd .snd)

  opaque
    unfolding CRelPtb
    pullCSq : ∀ pB' → CRelPtbSq B B' (d .fst) (pullC .fst pB') pB'
    pullCSq pB' = snd (d .snd .snd .fst pB')
