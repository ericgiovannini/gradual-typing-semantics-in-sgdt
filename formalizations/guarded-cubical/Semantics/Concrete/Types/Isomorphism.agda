
{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Common.Later

module Semantics.Concrete.Types.Isomorphism (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Bool
import Cubical.Data.Sum as Sum
import Cubical.Data.Unit as Unit
open import Cubical.Relation.Nullary
open import Cubical.Functions.Embedding

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.Instances.Trivial as Trivial
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeMonoid as Free
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.FreeProduct.Indexed as IFP

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions
open import Semantics.Concrete.Predomain.Combinators
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Perturbation.Semantic k

open import Semantics.Concrete.Types.Base k as Types
open import Semantics.Concrete.Types.Constructions k

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓc ℓd : Level
    
    ℓA₁  ℓ≤A₁  ℓ≈A₁  ℓMA₁  : Level
    ℓA₁' ℓ≤A₁' ℓ≈A₁' ℓMA₁' : Level
    ℓA₂  ℓ≤A₂  ℓ≈A₂  ℓMA₂  : Level
    ℓA₂' ℓ≤A₂' ℓ≈A₂' ℓMA₂' : Level
    ℓA₃  ℓ≤A₃  ℓ≈A₃  ℓMA₃  : Level

    ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  ℓMAᵢ  : Level
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' ℓMAᵢ' : Level
    ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  ℓMAₒ  : Level
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' ℓMAₒ' : Level
    ℓcᵢ ℓcₒ                : Level

    ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ  ℓMBᵢ  : Level
    ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ' ℓMBᵢ' : Level
    ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ  ℓMBₒ  : Level
    ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ' ℓMBₒ' : Level
    ℓdᵢ ℓdₒ                : Level

    ℓX ℓY ℓR : Level
    ℓX₁ ℓX₂ : Level

open PMor



-- Strong isomorphisms of value types
--------------------------------------

-- We say that A is strongly isomorphic to A' if:

-- 1. The underlying predomains are isomorphic.
--
-- 2. There is an isomorphism of monoids h' : Ptb A → Ptb A'
--
-- 3. The above monoid isomorphism is coherent with respect to the interpretation
--    as semantic perturbations, i.e.,
--   
--        interp A' ∘ h ≡ SemPtbA→SemPtbA' ∘ interp A
--
--    where SemPtbA→SemPtbA' turns a semantic perturbation on A to one on A'
--    (see PredomIso→EndoHom in semantic perturbations file).
--
-- Note that (3) implies that 
--        interp A ∘ h⁻¹ ≡ SemPtbA'→SemPtbA ∘ interp A'
--
-- because h is an isomorphism, and because SemPtbA→SemPtbA'
-- and SemPtbA'→SemPtbA are inverses.


module _
  (A : ValType ℓA ℓ≤A ℓ≈A ℓMA) (A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA')
  where

  private
    |A| = ValType→Predomain A
    |A'| = ValType→Predomain A'
    MA = PtbV A
    MA' = PtbV A'
    iA = interpV A
    iA' = interpV A'

  StrongIsoV : Type (ℓ-max
      (ℓ-max (ℓ-max ℓA ℓA')   (ℓ-max ℓ≤A ℓ≤A'))
      (ℓ-max (ℓ-max ℓ≈A ℓ≈A') (ℓ-max ℓMA ℓMA')))
  StrongIsoV =
    Σ[ isom ∈ PredomIso |A| |A'| ]
    Σ[ monIso ∈ (MonoidIso MA MA') ]
      iA' ∘hom (monIso .MonoidIso.fun) ≡ PredomIso→EndoHom isom ∘hom iA


module _
  {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  where

  private
    |A| = ValType→Predomain A
    |A'| = ValType→Predomain A'
    MA = PtbV A
    MA' = PtbV A'
    iA = interpV A
    iA' = interpV A'

  mkStrongIsoV :
    (isom : PredomIso |A| |A'|) →
    (monIso : MonoidIso MA MA') →
    ((iA' ∘hom (monIso .MonoidIso.fun)) ≡ (PredomIso→EndoHom isom ∘hom iA)) →
    StrongIsoV A A'
  mkStrongIsoV isom monIso eq = isom , monIso , eq -- isomAA' , isomMonoid

  StrongIsoV→PredomIso : StrongIsoV A A' → PredomIso |A| |A'|
  StrongIsoV→PredomIso = fst

  StrongIsoV→MonoidIso : StrongIsoV A A' → MonoidIso MA MA'
  StrongIsoV→MonoidIso x = x .snd .fst

  StrongIsoV→coherence : (x : StrongIsoV A A') → _
  StrongIsoV→coherence x = x .snd .snd





module _
  {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} where

  idStrongIsoV : StrongIsoV A A
  idStrongIsoV = mkStrongIsoV idPredomIso idMonoidIso
    (eqMonoidHom _ _ (funExt (λ m → SemPtb≡ _ _ refl)))

module _
  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁}
  {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂}
  {A₃ : ValType ℓA₃ ℓ≤A₃ ℓ≈A₃ ℓMA₃}
  (iso  : StrongIsoV A₁ A₂)
  (iso' : StrongIsoV A₂ A₃)
  where

  private
    |A₁| = ValType→Predomain A₁
    |A₂| = ValType→Predomain A₂
    |A₃| = ValType→Predomain A₃

    isoP₁₂ = StrongIsoV→PredomIso iso
    isoP₂₃ = StrongIsoV→PredomIso iso'
    module isoP₁₂ = PredomIso isoP₁₂
    module isoP₂₃ = PredomIso isoP₂₃

    isoM₁₂ = StrongIsoV→MonoidIso iso
    isoM₂₃ = StrongIsoV→MonoidIso iso'
    module isoM₁₂ = MonoidIso isoM₁₂
    module isoM₂₃ = MonoidIso isoM₂₃

  compStrongIsoV : StrongIsoV A₁ A₃
  compStrongIsoV = mkStrongIsoV isoP isoM eq 
    where
      isoP = (compPredomIso isoP₁₂ isoP₂₃)
      isoM = (compMonoidIso isoM₁₂ isoM₂₃)
      
      eq : (interpV A₃ ∘hom isoM .MonoidIso.fun) ≡ (PredomIso→EndoHom isoP ∘hom interpV A₁)
      eq = sym (∘hom-Assoc (isoM₁₂ .MonoidIso.fun) (isoM₂₃ .MonoidIso.fun) _)
        ∙ cong₂ _∘hom_ (StrongIsoV→coherence iso') refl
        ∙ ∘hom-Assoc _ _ _
        ∙ cong₂ _∘hom_ refl (StrongIsoV→coherence iso)
        ∙ sym (∘hom-Assoc _ _ _)
        ∙ cong₂ _∘hom_ (sym (PredomIso→EndoHom-comp isoP₁₂ isoP₂₃)) refl

      -- Know:   iA₂ ∘hom M₁→M₂ ≡ PredomIso→EndoHom iso  ∘hom iA₁
      --         iA₃ ∘hom M₂→M₃ ≡ PredomIso→EndoHom iso' ∘hom iA₂
      -- NTS:    iA₃ ∘hom (M₂→M₃ ∘hom M₁→M₂) ≡ PredomIso→EndoHom (iso|A₁||A₂| ∘ iso|A₂||A₃|) ∘hom iA₁
     
   


module _
  {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  (isom : StrongIsoV A A')
  where

  StrongIsoV-Inv : StrongIsoV A' A
  StrongIsoV-Inv = mkStrongIsoV isoP-inv isoM-inv eq
    where
      iA = interpV A
      iA' = interpV A'
      
      isoP = StrongIsoV→PredomIso isom
      isoM = StrongIsoV→MonoidIso isom
      isoP-inv = (PredomIso-Inv isoP)
      isoM-inv = (MonoidIso-Inv isoM)

      symCoherence : (PredomIso→EndoHom isoP ∘hom iA) ≡ (iA' ∘hom isoM .MonoidIso.fun)
      symCoherence = sym (StrongIsoV→coherence isom)

      eq : iA ∘hom (isoM .MonoidIso.inv)
        ≡ (PredomIso→EndoHom isoP-inv) ∘hom iA'
      eq = sym (∘hom-IdL _)
        ∙ cong₂ _∘hom_ (sym (PredomIso→EndoHom-inv₂ isoP)) refl
        ∙ ∘hom-Assoc _ _ _
        ∙ cong₂ _∘hom_ refl (sym (∘hom-Assoc _ _ _))
        ∙ cong₂ _∘hom_ refl (cong₂ _∘hom_ symCoherence refl)
        ∙ cong₂ _∘hom_ refl (∘hom-Assoc _ _ _)
        ∙ cong₂ _∘hom_ refl (cong₂ _∘hom_ refl (MonoidIso→RightInv isoM))
        ∙ cong₂ _∘hom_ refl (∘hom-IdR _)

{-
    sym (∘hom-IdR _)
        ∙ cong₂ _∘hom_ refl (sym (MonoidIso→RightInv isoM))
        ∙ sym (∘hom-Assoc _ _ _)
        ∙ cong₂ _∘hom_ (∘hom-Assoc _ _ _ ∙ (cong₂ _∘hom_ refl (MonoidIso→LeftInv isoM)) ∙ (∘hom-IdR _)) refl
        ∙ {!!}
        ∙ {!!}
-}



---------------------------------------------------------------------

-- Constructions on isomorphisms

module _
  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁} {A₁' : ValType ℓA₁' ℓ≤A₁' ℓ≈A₁' ℓMA₁'}
  {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂} {A₂' : ValType ℓA₂' ℓ≤A₂' ℓ≈A₂' ℓMA₂'}
  (iso₁ : StrongIsoV A₁ A₁')
  (iso₂ : StrongIsoV A₂ A₂')
  where

  private
    isoM₁ : MonoidIso (PtbV A₁) (PtbV A₁')
    isoM₁ = StrongIsoV→MonoidIso iso₁

    isoM₂ : MonoidIso (PtbV A₂) (PtbV A₂')
    isoM₂ = StrongIsoV→MonoidIso iso₂

  ×-iso : StrongIsoV (A₁ × A₂) (A₁' × A₂')
  ×-iso = mkStrongIsoV
    (×-PredomIso (StrongIsoV→PredomIso iso₁) (StrongIsoV→PredomIso iso₂))
    isoM
    eq
    where
      isoM : MonoidIso (PtbV (A₁ × A₂)) (PtbV (A₁' × A₂'))
      isoM = mkMonoidIso
        (FP.rec (i₁ ∘hom isoM₁ .MonoidIso.fun) (i₂ ∘hom isoM₂ .MonoidIso.fun))
        
        (FP.rec (i₁ ∘hom isoM₁ .MonoidIso.inv) (i₂ ∘hom isoM₂ .MonoidIso.inv))
        
        (FP.ind
          (eqMonoidHom _ _ (funExt (λ pA₁' → cong (i₁ .fst) (isoM₁ .MonoidIso.rightInv pA₁'))))
          (eqMonoidHom _ _ (funExt (λ pA₂' → cong (i₂ .fst) (isoM₂ .MonoidIso.rightInv pA₂')))))
        (FP.ind
          (eqMonoidHom _ _ (funExt (λ pA₁ → cong (i₁ .fst) (isoM₁ .MonoidIso.leftInv pA₁))))
          (eqMonoidHom _ _ (funExt (λ pA₂ → cong (i₂ .fst) (isoM₂ .MonoidIso.leftInv pA₂)))))

      -- Know : iA₁' ∘hom MA₁→MA₁' ≡ PredomIso→EndoHom isoA₁A₁' ∘hom iA₁
      --        iA₂' ∘hom MA₂→MA₂' ≡ PredomIso→EndoHom isoA₂A₂' ∘hom iA₂

      eq : interpV (A₁' × A₂') ∘hom isoM .MonoidIso.fun ≡ (PredomIso→EndoHom _) ∘hom interpV (A₁ × A₂)
      eq = FP.ind
        (eqMonoidHom _ _ (funExt (λ pA₁ → SemPtb≡ _ _ (funExt (λ {(a₁' , a₂') →
          ≡-× (funExt⁻ (cong (PMor.f ∘ fst) (funExt⁻ (cong fst (StrongIsoV→coherence iso₁)) pA₁)) a₁')
              (sym (StrongIsoV→PredomIso iso₂ .PredomIso.invRight a₂'))})))))

        (eqMonoidHom _ _ (funExt (λ pA₂ → SemPtb≡ _ _ (funExt (λ {(a₁' , a₂') →
          ≡-× (sym (StrongIsoV→PredomIso iso₁ .PredomIso.invRight a₁'))
              (funExt⁻ (cong (PMor.f ∘ fst) (funExt⁻ (cong fst (StrongIsoV→coherence iso₂)) pA₂)) a₂')})))))

        -- (eqMonoidHom _ _ (funExt (λ pA₂ → ×-SemPtb-Ind _ _
        --   (eqPMor _ _ (funExt (λ x → sym (StrongIsoV→PredomIso iso₁ .PredomIso.invRight (x .fst)))))
        --   (eqPMor _ _ (funExt (λ x → funExt⁻ (cong (PMor.f ∘ fst) (funExt⁻ (cong fst (StrongIsoV→coherence iso₂)) pA₂)) (x .snd)))))))



  

module _
  (X : DiscreteTy ℓX)
  (A₁ : ⟨ X ⟩ → ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁)
  (A₂ : ⟨ X ⟩ → ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂)
  (isom : ((x : ⟨ X ⟩) → StrongIsoV (A₁ x) (A₂ x)))
  where

  private
    isoPx : (x : ⟨ X ⟩) → PredomIso (ValType→Predomain (A₁ x)) (ValType→Predomain (A₂ x))
    isoPx x = StrongIsoV→PredomIso (isom x)

    isoMx : (x : ⟨ X ⟩) → MonoidIso (PtbV (A₁ x)) (PtbV (A₂ x))
    isoMx x = StrongIsoV→MonoidIso (isom x)

    coherence-x : (x : ⟨ X ⟩) →
        ((interpV (A₂ x)) ∘hom (isoMx x .MonoidIso.fun))
      ≡ ((PredomIso→EndoHom (isoPx x)) ∘hom (interpV (A₁ x)))
    coherence-x x = StrongIsoV→coherence (isom x)

  ΣV-cong-iso-snd : StrongIsoV (ΣV X A₁) (ΣV X A₂)
  ΣV-cong-iso-snd = mkStrongIsoV isoP isoM eq
    where
      isoP : PredomIso _ _
      isoP = ΣP-cong-iso-snd (⟨ X ⟩ , Discrete→isSet (X .snd))
        (ValType→Predomain ∘ A₁) (ValType→Predomain ∘ A₂)
        (StrongIsoV→PredomIso ∘ isom)

      opaque
        unfolding IFP.elim IFP.rec
        isoM : MonoidIso (PtbV (ΣV X A₁)) (PtbV (ΣV X A₂))
        isoM = mkMonoidIso
          (IFP.rec _ _ _ (λ x → IFP.σ _ _ x ∘hom (StrongIsoV→MonoidIso (isom x) .MonoidIso.fun)))
          (IFP.rec _ _ _ (λ x → IFP.σ _ _ x ∘hom (StrongIsoV→MonoidIso (isom x) .MonoidIso.inv)))
          (IFP.ind _ _ (λ x → eqMonoidHom _ _ (funExt (λ p → cong ((IFP.σ _ _ x) .fst) (StrongIsoV→MonoidIso (isom x) .MonoidIso.rightInv p)))))
          (IFP.ind _ _ (λ x → eqMonoidHom _ _ (funExt (λ p → cong ((IFP.σ _ _ x) .fst) (StrongIsoV→MonoidIso (isom x) .MonoidIso.leftInv p)))))

        eq : (interpV (ΣV X A₂) ∘hom isoM .MonoidIso.fun) ≡ (PredomIso→EndoHom isoP ∘hom interpV (ΣV X A₁))
        eq = IFP.ind _ _ (λ x → eqMonoidHom _ _
          (funExt (λ p → SemPtb≡ _ _ (funExt (λ {(x' , a') → ΣPathP (refl , aux₁ x p x' a' (X .snd x x'))})))))
            where
              aux₁ : ∀ (x : ⟨ X ⟩) (p : ⟨ PtbV (A₁ x) ⟩) (x' : ⟨ X ⟩) (a' : ⟨ A₂ x' ⟩) (x≡x'? : Dec (x ≡ x'))
                → PMor.f {Y = ValType→Predomain (A₂ x')} (PtbIfEqual x (interpV (A₂ x) .fst
                  (StrongIsoV→MonoidIso (isom x) .MonoidIso.fun .fst p)) x' x≡x'? .fst) a'
                ≡ PredomIso.fun (StrongIsoV→PredomIso (isom x')) .PMor.f
                  (PMor.f {Y = ValType→Predomain (A₁ x')} (PtbIfEqual x (interpV (A₁ x) .fst p) x' x≡x'? .fst)
                    (StrongIsoV→PredomIso (isom x') .PredomIso.inv .PMor.f a'))
              aux₁ x p x' a' (yes x≡x') =
                let LHS  = PMor.f ((subst (λ z → ⟨ Endo (ValType→Predomain (A₂ z)) ⟩) x≡x' (interpV (A₂ x) .fst (isoMx x .MonoidIso.fun .fst p))) .fst) a' in
                let LHS' = PMor.f ((subst (λ z → ⟨ Endo (ValType→Predomain (A₂ z)) ⟩) x≡x' ((PredomIso→EndoHom (isoPx x) .fst (interpV (A₁ x) .fst p)))) .fst) a' in
                let RHS  = (isoPx x') .PredomIso.fun .PMor.f
                      (subst (λ x → ⟨ A₁ x ⟩) x≡x'
                        (interpV (A₁ x) .fst p .fst .PMor.f
                          (subst (λ x → ⟨ A₁ x ⟩) (sym x≡x') (isoPx x' .PredomIso.inv .PMor.f a')))) in
                let equals : LHS ≡ RHS
                    equals = fromPathP
                      ((funExt⁻ (cong (PMor.f ∘ fst) (funExt⁻ (cong fst (coherence-x x)) p)) _) -- apply the hypothesis relating A₁ x and A₂ x
                       ◁ congP₂ (λ _ → PMor.f ∘ PredomIso.fun ∘ isoPx)
                         x≡x'
                         (toPathP (cong
                           (subst (λ x → ⟨ A₁ x ⟩) x≡x') (cong (interpV (A₁ x) .fst p .fst .PMor.f)
                           (sym (fromPathP (congP₂ (λ _ → PMor.f ∘ PredomIso.inv ∘ isoPx) (sym x≡x') (toPathP refl)))))))) in
                equals
              aux₁ x p x' a' (no x≢x') =
                sym (StrongIsoV→PredomIso (isom x') .PredomIso.invRight a')


   


{-


PMor.f (fst (A₁ x .snd .snd .snd) p .fst)
(PMor.f (PredomIso.inv (fst (isom x)))
 (transp (λ j → fst (A₂ (x≡x' (~ j)))) i0 a'))

(subst (λ x → ⟨ A₁ x ⟩) x≡x'
    (interpV (A₁ x) .fst p .fst .PMor.f
    (subst (λ x → ⟨ A₁ x ⟩) (sym x≡x') (isoPx x' .PredomIso.inv .PMor.f a'))))

-}


-- For simplicity, we require that A₁ and A₂ have the same universe levels.
-- This could be improved by using a version of Lift for ValTypes.
module _
  (X₁ : DiscreteTy ℓX₁)
  (X₂ : DiscreteTy ℓX₂)
  (A₁ : ⟨ X₁ ⟩ → ValType ℓA ℓ≤A ℓ≈A ℓMA)
  (A₂ : ⟨ X₂ ⟩ → ValType ℓA ℓ≤A ℓ≈A ℓMA)
  where

  private
    X₁⊎X₂ : DiscreteTy (ℓ-max ℓX₁ ℓX₂)
    X₁⊎X₂ = (⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩ , Sum.discrete⊎ (X₁ .snd) (X₂ .snd))

    Sigma₁ = ΣV X₁ A₁
    Sigma₂ = ΣV X₂ A₂
   
    Sum = Sigma₁ ⊎ Sigma₂

    Sigma : ValType _ _ _ _
    Sigma = ΣV X₁⊎X₂ (Sum.rec A₁ A₂)

    X₁Set : hSet ℓX₁
    X₁Set = (⟨ X₁ ⟩ , Discrete→isSet (X₁ .snd))

    X₂Set : hSet ℓX₂
    X₂Set = (⟨ X₂ ⟩ , Discrete→isSet (X₂ .snd))

  isoΣ⊎Σ-Σ : StrongIsoV (Sigma₁ ⊎ Sigma₂) Sigma
  isoΣ⊎Σ-Σ = mkStrongIsoV isoP isoM eq
    where
      isoP : PredomIso (ValType→Predomain Sum) (ValType→Predomain Sigma)
      isoP .PredomIso.fun = ⊎p-rec
        (Σ-mor' X₁Set ((⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩) , Discrete→isSet (X₁⊎X₂ .snd)) Sum.inl _ _ (λ x₁ → Id))
        (Σ-mor' X₂Set ((⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩) , Discrete→isSet (X₁⊎X₂ .snd)) Sum.inr _ _ (λ x₂ → Id))
      isoP .PredomIso.inv = Σ-elim (Sum.elim (λ x₁ → σ1 ∘p Σ-intro x₁) (λ x₂ → σ2 ∘p Σ-intro x₂))
      isoP .PredomIso.invRight (Sum.inl _ , a) = refl
      isoP .PredomIso.invRight (Sum.inr _ , a) = refl
      isoP .PredomIso.invLeft (Sum.inl _) = refl
      isoP .PredomIso.invLeft (Sum.inr _) = refl

      to : MonoidHom (PtbV Sum) (PtbV Sigma)
      to = FP.rec
             (IFP.rec _ _ _ (λ x₁ → IFP.σ _ _ (Sum.inl x₁)))
             (IFP.rec _ _ _ (λ x₂ → IFP.σ _ _ (Sum.inr x₂)))

      from : MonoidHom (PtbV Sigma) (PtbV Sum)
      from = IFP.rec _ _ _
        (Sum.elim (λ x₁ → i₁ ∘hom IFP.σ _ _ x₁) (λ x₂ → i₂ ∘hom IFP.σ _ _ x₂))
        
      opaque
        unfolding IFP.elim IFP.rec
        isoM : MonoidIso (PtbV Sum) (PtbV Sigma)
        isoM = mkMonoidIso to from inv₁ inv₂
          where
            inv₁ : to ∘hom from ≡ idMon (PtbV Sigma)
            inv₁ = IFP.ind _ _ (Sum.elim (λ x₁ → eqMonoidHom _ _ refl) (λ x₂ → eqMonoidHom _ _ refl))

            inv₂ : from ∘hom to ≡ idMon (PtbV Sum)
            inv₂ = FP.ind
              (IFP.ind _ _ (λ x₁ → eqMonoidHom _ _ refl))
              (IFP.ind _ _ λ x₂ → eqMonoidHom _ _ refl)

        eq : interpV Sigma ∘hom isoM .MonoidIso.fun ≡
             PredomIso→EndoHom isoP ∘hom interpV Sum
        eq = FP.ind
              (IFP.ind _ _ (λ x₁ → eqMonoidHom _ _
                (funExt (λ pA₁ → SemPtb≡ _ _ (funExt (λ
                  { (Sum.inl x₁' , a) → ΣPathP (refl ,
                    --let foo = Σ-SemPtb-ind X₁Set (X₁ .snd) x₁ (((((interpV Sigma ∘hom isoM .MonoidIso.fun) ∘hom i₁) ∘hom IFP.σ (X₁ .fst) (λ x → PtbV (A₁ x)) x₁)) .fst pA₁) {!!} {!!} in
                    --let bar = funExt⁻ ((cong (PMor.f ∘ fst)) foo) (x₁ , ({!!} , {!!})) in
                    lem1 x₁ x₁' pA₁ a (X₁ .snd x₁ x₁'))
                  ; (Sum.inr x₂  , a) → refl}))))))
              (IFP.ind _ _ (λ x₂ → eqMonoidHom _ _
                (funExt (λ pA₂ → SemPtb≡ _ _ (funExt (λ
                  { (Sum.inl x₁  , a) → refl
                  ; (Sum.inr x₂' , a) → ΣPathP (refl , lem2 x₂ x₂' pA₂ a (X₂ .snd x₂ x₂'))}))))))
                  -- Σ-SemPtb-ind _ (X₁⊎X₂ .snd) (Sum.inr x₂) _ {!!} λ x' b' neq → {!!}))))

          where
            LHS2A LHS2B LHS2C LHS2D LHS2E LHS2F RHS2A RHS2B RHS2C RHS2D RHS2E :
              ∀ (x₂ x₂' : ⟨ X₂ ⟩) (pA₂ : ⟨ PtbV (A₂ x₂) ⟩) (a : ⟨ A₂ x₂' ⟩) → ⟨ A₂ x₂' ⟩
            LHS2A x₂ x₂' pA₂ a = snd (fst (((interpV Sigma ∘hom isoM .MonoidIso.fun) ∘hom i₂) ∘hom IFP.σ (X₂ .fst) (λ x → PtbV (A₂ x)) x₂) pA₂ .fst .PMor.f (Sum.inr x₂' , a))
            LHS2B x₂ x₂' pA₂ a = interpV Sigma .fst (isoM .MonoidIso.fun .fst (i₂ .fst (IFP.σ _ _ _ .fst pA₂))) .fst .PMor.f (Sum.inr x₂' , a) .snd
            LHS2C x₂ x₂' pA₂ a = interpV Sigma .fst (IFP.σ _ _ (Sum.inr x₂) .fst pA₂) .fst .PMor.f (Sum.inr x₂' , a) .snd
    
            -- IFP.rec _ _ _ (λ s → Σ-SemPtb {!!} (X₁⊎X₂ .snd) s ∘hom interpV (A₂ x₂)) .fst (IFP.σ _ _ (Sum.inr x₂) .fst pA₂) .fst .PMor.f (Sum.inr x₂' , a) .snd
            
            -- IFP.rec _ _ _ (λ s → Σ-SemPtb ((⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩) , Discrete→isSet (X₁⊎X₂ .snd)) (X₁⊎X₂ .snd) s ∘hom interpV (Sum.rec A₁ A₂ s))
            --  .fst (isoM .MonoidIso.fun .fst (i₂ .fst (IFP.σ _ _ _ .fst pA₂))) .fst .PMor.f (Sum.inr x₂' , a) .snd
            --
            -- IFP.rec _ _ _ (λ s → Σ-SemPtb ((⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩) , Discrete→isSet (X₁⊎X₂ .snd)) (X₁⊎X₂ .snd) s ∘hom interpV (Sum.rec A₁ A₂ s))
            -- .fst (IFP.σ _ _ (inr x₂) .fst pA₂)
            -- .fst .PMor.f (Sum.inr x₂' , a) .snd
            --
            --
            --  Σ-SemPtb ((⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩) , Discrete→isSet (X₁⊎X₂ .snd)) (X₁⊎X₂ .snd) (inr x₂) .fst (interpV (A₂ x₂) .fst pA₂)        
            -- .fst .PMor.f (Sum.inr x₂' , a) .snd
            
            LHS2D x₂ x₂' pA₂ a = (Σ-SemPtb ((⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩) , Discrete→isSet (X₁⊎X₂ .snd)) (X₁⊎X₂ .snd) {B = λ s → ValType→Predomain (Sum.rec A₁ A₂ s)} (Sum.inr x₂))
              .fst (interpV (A₂ x₂) .fst pA₂) .fst .PMor.f (Sum.inr x₂' , a) .snd

            LHS2E x₂ x₂' pA₂ a = liftΣ
              ((⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩) , Discrete→isSet (X₁⊎X₂ .snd)) (X₁⊎X₂ .snd)
              (λ y → PtbIfEqual {B = λ s → ValType→Predomain (Sum.rec A₁ A₂ s)} (Sum.inr x₂) (interpV (A₂ x₂) .fst pA₂) y (X₁⊎X₂ .snd (Sum.inr x₂) y))
              .fst .PMor.f (Sum.inr x₂' , a) .snd

            LHS2F x₂ x₂' pA₂ a = (PtbIfEqual {B = λ s → ValType→Predomain (Sum.rec A₁ A₂ s)}
              (Sum.inr x₂) (interpV (A₂ x₂) .fst pA₂) (Sum.inr x₂') (X₁⊎X₂ .snd (Sum.inr x₂) (Sum.inr x₂')))
              .fst .PMor.f a

            equal : ∀ (x₂ x₂' : ⟨ X₂ ⟩) (pA₂ : ⟨ PtbV (A₂ x₂) ⟩) (a : ⟨ A₂ x₂' ⟩) →
              LHS2A x₂ x₂' pA₂ a ≡ LHS2F x₂ x₂' pA₂ a
            equal x₂ x₂' pA₂ a = refl
            
            RHS2A x₂ x₂' pA₂ a = PredomIso→EndoHom isoP .fst (interpV Sum .fst (i₂ .fst (IFP.σ _ _ _ .fst pA₂))) .fst .PMor.f (Sum.inr x₂' , a) .snd
            RHS2B x₂ x₂' pA₂ a = PredomIso→EndoHom isoP .fst ((A⊎-SemPtb ∘hom interpV Sigma₂) .fst (IFP.σ _ _ _ .fst pA₂)) .fst .PMor.f (Sum.inr x₂' , a) .snd
            RHS2C x₂ x₂' pA₂ a = PredomIso→EndoHom isoP .fst
              (SemPtbId ⊎SemPtb
                (liftΣ (⟨ X₂ ⟩ , (Discrete→isSet (X₂ .snd))) (X₂ .snd)
                  (λ y → PtbIfEqual x₂ (interpV (A₂ x₂) .fst pA₂) y (X₂ .snd x₂ y))))
              .fst .PMor.f (Sum.inr x₂' , a) .snd
            RHS2D x₂ x₂' pA₂ a = isoP .PredomIso.fun .PMor.f (interpV Sum .fst (i₂ .fst (IFP.σ _ _ _ .fst pA₂)) .fst .PMor.f (isoP .PredomIso.inv .PMor.f (Sum.inr x₂' , a))) .snd
            RHS2E x₂ x₂' pA₂ a = isoP .PredomIso.fun .PMor.f (σ2 .PMor.f (x₂' , PtbIfEqual {B = ValType→Predomain ∘ A₂} x₂ (interpV (A₂ x₂) .fst pA₂) x₂' (X₂ .snd x₂ x₂') .fst .PMor.f a)) .snd          

            equal' : ∀ (x₂ x₂' : ⟨ X₂ ⟩) (pA₂ : ⟨ PtbV (A₂ x₂) ⟩) (a : ⟨ A₂ x₂' ⟩) →
              RHS2A x₂ x₂' pA₂ a ≡ RHS2E x₂ x₂' pA₂ a
            equal' x₂ x₂' pA₂ a = refl
           
            -- This is part of the defintion of Sum.discrete⊎, but we need to inline it
            -- here so we can generalize over the proof of equality of x₁ and x₁'.
            dec→dec-inl : ∀ (x₁ x₁' : ⟨ X₁ ⟩) → Dec (x₁ ≡ x₁') → Dec (Sum.inl {B = ⟨ X₂ ⟩} x₁ ≡ Sum.inl x₁')
            dec→dec-inl x₁ x₁' x₁≡x₁'? = mapDec (cong Sum.inl) (λ p q → p (isEmbedding→Inj Sum.isEmbedding-inl x₁ x₁' q)) x₁≡x₁'?
            
            dec→dec-inr : ∀ (x₂ x₂' : ⟨ X₂ ⟩) → Dec (x₂ ≡ x₂') → Dec (Sum.inr {A = ⟨ X₁ ⟩} x₂ ≡ Sum.inr x₂')
            dec→dec-inr x₂ x₂' x₂≡x₂'? = mapDec (cong Sum.inr) (λ p q → p (isEmbedding→Inj Sum.isEmbedding-inr x₂ x₂' q)) x₂≡x₂'?

            LHS₁' : ∀ (x₁ x₁' : ⟨ X₁ ⟩) (pA₁ : ⟨ PtbV (A₁ x₁) ⟩) (a : ⟨ A₁ x₁' ⟩) →
              (Dec (Sum.inl {B = ⟨ X₂ ⟩} x₁ ≡ Sum.inl x₁')) → ⟨ A₁ x₁' ⟩
            LHS₁' x₁ x₁' pA₁ a x₁≡x₁'? = (PtbIfEqual {B = λ s → ValType→Predomain (Sum.rec A₁ A₂ s)}
              (Sum.inl x₁) (interpV (A₁ x₁) .fst pA₁) (Sum.inl x₁') x₁≡x₁'?)
              .fst .PMor.f a

            RHS₁' : ∀ (x₁ x₁' : ⟨ X₁ ⟩) (pA₁ : ⟨ PtbV (A₁ x₁) ⟩) (a : ⟨ A₁ x₁' ⟩) →
              (Dec (x₁ ≡ x₁')) → ⟨ A₁ x₁' ⟩
            RHS₁' x₁ x₁' pA₁ a x₁≡x₁'? = isoP .PredomIso.fun .PMor.f
              (σ1 .PMor.f (x₁' , PtbIfEqual {B = ValType→Predomain ∘ A₁} x₁ (interpV (A₁ x₁) .fst pA₁) x₁' x₁≡x₁'? .fst .PMor.f a)) .snd

            LHS₂' : ∀ (x₂ x₂' : ⟨ X₂ ⟩) (pA₂ : ⟨ PtbV (A₂ x₂) ⟩) (a : ⟨ A₂ x₂' ⟩) →
              (Dec (Sum.inr {A = ⟨ X₁ ⟩} x₂ ≡ Sum.inr x₂')) → ⟨ A₂ x₂' ⟩
            LHS₂' x₂ x₂' pA₂ a x₂≡x₂'? = (PtbIfEqual {B = λ s → ValType→Predomain (Sum.rec A₁ A₂ s)}
              (Sum.inr x₂) (interpV (A₂ x₂) .fst pA₂) (Sum.inr x₂') x₂≡x₂'?)
              .fst .PMor.f a

            RHS₂' : ∀ (x₂ x₂' : ⟨ X₂ ⟩) (pA₂ : ⟨ PtbV (A₂ x₂) ⟩) (a : ⟨ A₂ x₂' ⟩) →
              (Dec (x₂ ≡ x₂')) → ⟨ A₂ x₂' ⟩
            RHS₂' x₂ x₂' pA₂ a x₂≡x₂'? = isoP .PredomIso.fun .PMor.f
              (σ2 .PMor.f (x₂' , PtbIfEqual {B = ValType→Predomain ∘ A₂} x₂ (interpV (A₂ x₂) .fst pA₂) x₂' x₂≡x₂'? .fst .PMor.f a)) .snd

            lem1 : ∀ x₁ x₁' (pA₁ : ⟨ PtbV (A₁ x₁) ⟩) (a : ⟨ A₁ x₁' ⟩)
                   (x₁≡x₁'? : Dec (x₁ ≡ x₁')) →
                    LHS₁' x₁ x₁' pA₁ a (dec→dec-inl _ _ x₁≡x₁'?) ≡ RHS₁' x₁ x₁' pA₁ a x₁≡x₁'?
            lem1 x₁ x₁' pA₁ a (yes x₁≡x₁') = refl
            lem1 x₁ x₁' pA₁ a (no x₁≢x₁') = refl

            lem2 : ∀ x₂ x₂' (pA₂ : ⟨ PtbV (A₂ x₂) ⟩) (a : ⟨ A₂ x₂' ⟩)
                   (x₂≡x₂'? : Dec (x₂ ≡ x₂')) →
                    LHS₂' x₂ x₂' pA₂ a (dec→dec-inr _ _ x₂≡x₂'?) ≡ RHS₂' x₂ x₂' pA₂ a x₂≡x₂'?
            lem2 x₂ x₂' pA₂ a (yes x₂≡x₂') = refl
            lem2 x₂ x₂' pA₂ a (no x₂≢x₂') = refl



{-
IFP.rec ⟨ X ⟩ (PtbV ∘ B) _ int
    where
      int : (x : ⟨ X ⟩) → MonoidHom (PtbV (B x)) (Endo P-Σ)
      int x = (Σ-SemPtb (⟨ X ⟩ , isSetX) (X .snd) x) ∘hom (interpV (B x))
-}          

module _ {ℓX₁ ℓX₂ : Level}
  (X₁ : DiscreteTy ℓX₁)
  (X₂ : DiscreteTy ℓX₂)
  (Y₁ : DiscreteTy ℓY)
  (Y₂ : DiscreteTy ℓY)
  (A : ValType ℓA ℓ≤A ℓ≈A ℓMA)
  where

  private
    X₁⊎X₂ : DiscreteTy (ℓ-max ℓX₁ ℓX₂)
    X₁⊎X₂ = (⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩ , Sum.discrete⊎ (X₁ .snd) (X₂ .snd))

    P : ⟨ X₁⊎X₂ ⟩ → DiscreteTy ℓY
    P = Sum.rec (λ _ → Y₁) (λ _ → Y₂)

    Sigma₁ : ValType _ _ _ _
    Sigma₁ = (ΣV X₁ (λ x₁ → ΠV Y₁ (λ _ → A)))

    Sigma₂ : ValType _ _ _ _
    Sigma₂ = (ΣV X₂ (λ x₂ → ΠV Y₂ (λ _ → A)))

    Sum : ValType _ _ _ _
    Sum = Sigma₁ ⊎ Sigma₂

    Sigma : ValType _ _ _ _
    Sigma = ΣV X₁⊎X₂ (λ s → ΠV (P s) (λ _ → A))

    X₁Set : hSet ℓX₁
    X₁Set = (⟨ X₁ ⟩ , Discrete→isSet (X₁ .snd))

    X₂Set : hSet ℓX₂
    X₂Set = (⟨ X₂ ⟩ , Discrete→isSet (X₂ .snd))
   
  isoΣΠ⊎ΣΠ-ΣΠ : StrongIsoV (Sigma₁ ⊎ Sigma₂) Sigma
  isoΣΠ⊎ΣΠ-ΣΠ = compStrongIsoV
    (isoΣ⊎Σ-Σ X₁ X₂ (λ _ → ΠV Y₁ (λ _ → A)) (λ _ → ΠV Y₂ (λ _ → A)))
    (ΣV-cong-iso-snd X₁⊎X₂
      (Sum.rec (λ _ → ΠV Y₁ (λ _ → A)) (λ _ → ΠV Y₂ (λ _ → A)))
      (λ s → ΠV (P s) (λ _ → A))
      (Sum.elim (λ _ → idStrongIsoV) λ _ → idStrongIsoV))


module _
  (A : ValType ℓA ℓ≤A ℓ≈A ℓMA)
  where

  private
    BoolDisc : DiscreteTy ℓ-zero
    BoolDisc = Bool , _≟_

    PiBoolA : ValType _ _ _ _
    PiBoolA = ΠV BoolDisc (λ _ → A)

  isoA×A-ΠBool : StrongIsoV (A × A) PiBoolA
  isoA×A-ΠBool = mkStrongIsoV isoP isoM eq
    where
      isoP : PredomIso _ _
      isoP .PredomIso.fun = Π-intro (λ b → if b then π1 else π2)
      isoP .PredomIso.inv = ×-intro (Π-elim true) (Π-elim false)
      isoP .PredomIso.invRight as = funExt (λ { false → refl ; true → refl})
      isoP .PredomIso.invLeft (x , y) = refl

      opaque
        unfolding IFP.elim IFP.rec
        isoM : MonoidIso (PtbV (A × A)) (PtbV (PiBoolA))
        isoM = mkMonoidIso
          (FP.rec (IFP.σ _ _ true) (IFP.σ _ _ false))
          (IFP.rec _ _ _ (λ b → if b then i₁ else i₂))
          (IFP.ind _ _ (λ { false → eqMonoidHom _ _ refl ; true → eqMonoidHom _ _ refl}))
          (FP.ind (eqMonoidHom _ _ refl) (eqMonoidHom _ _ refl))

        eq : interpV PiBoolA ∘hom isoM .MonoidIso.fun
           ≡ PredomIso→EndoHom isoP ∘hom interpV (A × A)
        eq = FP.ind
               (eqMonoidHom _ _ (funExt (λ pA → SemPtb≡ _ _ (funExt (λ as → funExt (λ { false → refl ; true → refl}))))))
               (eqMonoidHom _ _ (funExt (λ pA → SemPtb≡ _ _ (funExt (λ as → funExt (λ { false → refl ; true → refl}))))))

module _ (A : ValType ℓA ℓ≤A ℓ≈A ℓMA)
  where
  private
    UnitDisc : DiscreteTy ℓ-zero
    UnitDisc .fst = Unit.Unit
    UnitDisc .snd x y = yes refl

    SigmaA = (ΣV UnitDisc (λ _ → A))

  isoA-ΣUnitA : StrongIsoV A SigmaA
  isoA-ΣUnitA = mkStrongIsoV isoP isoM eq
    where
      isoP : PredomIso (ValType→Predomain A) (ValType→Predomain SigmaA)
      isoP .PredomIso.fun = Σ-intro Unit.tt
      isoP .PredomIso.inv = Σ-elim (λ tt → Id)
      isoP .PredomIso.invRight (_ , x) = refl
      isoP .PredomIso.invLeft a = refl

      opaque
        unfolding IFP.rec IFP.elim
        isoM : MonoidIso (PtbV A) (PtbV SigmaA)
        isoM = mkMonoidIso
                 (IFP.σ _ _ Unit.tt)
                 (IFP.rec _ _ _ (λ tt → idMon (PtbV A)))
                 (IFP.ind _ _ (λ tt → eqMonoidHom _ _ refl))
                 (eqMonoidHom _ _ refl)

        eq : interpV SigmaA ∘hom isoM .MonoidIso.fun
           ≡ PredomIso→EndoHom isoP ∘hom interpV A
        eq = eqMonoidHom _ _ (funExt (λ pA → SemPtb≡ _ _ refl))
 



{-
  mkStrongIsoV isoP isoM eq
    where

    isoP : PredomIso
        (ValType→Predomain Sum)
        (ValType→Predomain Sigma)
    isoP .PredomIso.fun = ⊎p-rec
      (Σ-mor' X₁Set ((⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩) , Discrete→isSet (X₁⊎X₂ .snd)) Sum.inl _ _ (λ x₁ → Id))
      (Σ-mor' X₂Set ((⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩) , Discrete→isSet (X₁⊎X₂ .snd)) Sum.inr _ _ (λ x₂ → Id))
    isoP .PredomIso.inv = Σ-elim (Sum.elim (λ x₁ → σ1 ∘p Σ-intro x₁) (λ x₂ → σ2 ∘p Σ-intro x₂))
    isoP .PredomIso.invRight = {!!}
    isoP .PredomIso.invLeft = {!!}

    to : MonoidHom (PtbV Sum) (PtbV Sigma)
    to = FP.rec
        (IFP.rec _ _ _ (λ x₁ → IFP.rec _ _ _
          (λ y₁ → IFP.σ _ _ (Sum.inl x₁) ∘hom IFP.σ _ _ y₁)))
        (IFP.rec _ _ _ (λ x₂ → IFP.rec _ _ _ (λ y₂ →
               (IFP.σ _ _ (Sum.inr x₂))
          ∘hom (IFP.σ _ _ y₂))))

    from : MonoidHom (PtbV Sigma) (PtbV Sum)
    from = IFP.rec _ _ _
        λ { (Sum.inl x₁) → IFP.rec _ _ _
            (λ y₁ → i₁
               ∘hom IFP.σ _ _ x₁
               ∘hom IFP.σ _ _ y₁)
          ; (Sum.inr x₂) → IFP.rec _ _ _
            (λ y₂ → i₂
              ∘hom (IFP.σ _ _ x₂)
              ∘hom (IFP.σ _ _ y₂))}

    opaque
      unfolding IFP.elim IFP.rec
      isoM : MonoidIso (PtbV Sum) (PtbV Sigma)
      isoM = mkMonoidIso to from inv₁ inv₂
        where
          inv₁ : to ∘hom from ≡ idMon (PtbV Sigma)
          inv₁ = IFP.ind _ _
            (λ { (Sum.inl x₁) → IFP.ind _ _ (λ y₁ → eqMonoidHom _ _ refl)
               ; (Sum.inr x₂) → IFP.ind _ _ (λ y₂ → eqMonoidHom _ _ refl)})
          inv₂ : from ∘hom to ≡ idMon (PtbV _)
          inv₂ = FP.ind
            (IFP.ind _ _ (λ x₁ → IFP.ind _ _ λ y₁ → eqMonoidHom _ _ refl))
            (IFP.ind _ _ (λ x₂ → IFP.ind _ _ λ y₂ → eqMonoidHom _ _ refl))

      eq : interpV Sigma ∘hom isoM .MonoidIso.fun ≡
           PredomIso→EndoHom isoP ∘hom interpV Sum
      eq = FP.ind
        (IFP.ind _ _ (λ x₁ → IFP.ind _ _ (λ y₁ →
          eqMonoidHom _ _ (funExt (λ pA → SemPtb≡ _ _
            (funExt (λ { (Sum.inl x₁' , as) → ΣPathP (refl , funExt (λ y₁' → {!!})) -- foo pA as x₁ x₁' y₁ y₁' (X₁ .snd x₁ x₁') (Y₁ .snd y₁ y₁')))
                       ; (Sum.inr _ , _) → refl})))))))

        (IFP.ind _ _ λ x₂ → IFP.ind _ _ (λ b →
          eqMonoidHom _ _ (funExt (λ pA → SemPtb≡ _ _
            (funExt (λ { (Sum.inl _ , _) → refl
                       ; (Sum.inr x₂' , as) → ΣPathP (refl , funExt λ y₂' → {!!})}))))))
        where
          -- foo : ∀ (pA : ⟨ PtbV A ⟩) (as : ⟨ Y₁ ⟩ → ⟨ A ⟩)  (x₁ x₁' : ⟨ X₁ ⟩) (y₁ y₁' : ⟨ Y₁ ⟩)
          --   → Dec (x₁ ≡ x₁') → Dec (y₁ ≡ y₁')
          --   → (fst ((((interpV Sigma ∘hom isoM .MonoidIso.fun) ∘hom i₁) ∘hom IFP.σ _ _ x₁) ∘hom IFP.σ _ _ y₁) pA .fst .PMor.f (Sum.inl x₁' , as)) .snd y₁'
          --   ≡ interpV Sigma₁ .fst ((IFP.σ _ _ x₁ ∘hom IFP.σ _ _ y₁) .fst pA) .fst .PMor.f (x₁' , as) .snd y₁' 
          -- foo pA as x₁ x₁' y₁ y₁' (yes p) (yes p₁) = {!!}
          -- foo pA as x₁ x₁' y₁ y₁' (yes p) (no ¬p) = {!!}
          -- foo pA as x₁ x₁' y₁ y₁' (no ¬p) q = {!!}


-}
