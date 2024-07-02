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
open import Semantics.Concrete.DoublePoset.DblPosetCombinators hiding (U)
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.KleisliFunctors k
open import Semantics.Concrete.DoublePoset.MonadCombinators k

open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Types k as Types hiding (U; F; _⟶_)
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
    ℓd₁ ℓd₂ ℓd₃  : Level

    ℓMA₁ ℓMA₂ ℓMA₃ : Level
    ℓMA₁' ℓMA₂' ℓMA₃' : Level
    ℓMB₁ ℓMB₂ ℓMB₃ : Level
    ℓMAᵢ ℓMAₒ ℓMBᵢ ℓMBₒ : Level

open ValTypeStr
open MonoidStr
open IsMonoidHom
open IsSemigroup
open IsMonoid

-- identity and composition for value and comp relations
module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} where
  private
    iA = A .snd .interpV
  IdRelV : VRelPP A A _
  IdRelV .fst = idPRel _
  IdRelV .snd .fst = corecPushV _ _ _ (idMon _) λ pA → Predom-IdSqH (iA .fst pA .fst)
  IdRelV .snd .snd = corecPullV _ _ _ (idMon _)λ pA → Predom-IdSqH (iA .fst pA .fst)

module _ {B : CompType ℓB ℓ≤B ℓ≈B ℓMB} where
  private
    iB = B .snd .snd .snd
  IdRelC : CRelPP B B _
  IdRelC .fst = idEDRel _
  IdRelC .snd .fst = corecPushC _ _ _ (idMon _) λ pB → ED-IdSqH (iB .fst pB .fst)
  IdRelC .snd .snd = corecPullC _ _ _ (idMon _)λ pB → ED-IdSqH (iB .fst pB .fst)

module _
  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁} {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂} {A₃ : ValType ℓA₃ ℓ≤A₃ ℓ≈A₃ ℓMA₃}
  (c₁ : VRelPP A₁ A₂ ℓc₁)
  (c₂ : VRelPP A₂ A₃ ℓc₂)
  where

  private
    iA₁ = A₁ .snd .interpV .fst
    iA₂ = A₂ .snd .interpV .fst
    iA₃ = A₃ .snd .interpV .fst

  ⊙V : VRelPP A₁ A₃ _
  ⊙V .fst = c₁ .fst ⊙ c₂ .fst
  ⊙V .snd .fst = corecPushV _ _ _ (pushV c₂ ∘hom pushV c₁) (λ pA₁ →
    CompSqH
      {cᵢ₁ = c₁ .fst}
      {cᵢ₂ = c₂ .fst}
      {cₒ₁ = c₁ .fst}
      {cₒ₂ = c₂ .fst}
      {f = iA₁ pA₁ .fst}{g = iA₂ (pushV c₁ .fst pA₁) .fst}
            {h = iA₃ (pushV c₂ .fst _) .fst}
      (pushVSq c₁ pA₁) (pushVSq c₂ _))
  ⊙V .snd .snd = corecPullV _ _ _ (pullV c₁ ∘hom pullV c₂) λ pA₃ →
    CompSqH
      {cᵢ₁ = c₁ .fst}
      {cᵢ₂ = c₂ .fst}
      {cₒ₁ = c₁ .fst}
      {cₒ₂ = c₂ .fst}
      {f = iA₁ (pullV c₁ .fst _) .fst}
      {g = iA₂ (pullV c₂ .fst pA₃) .fst}
      {h = iA₃ pA₃ .fst}
      (pullVSq c₁ _) (pullVSq c₂ pA₃)

module _
  {B₁ : CompType ℓB₁ ℓ≤B₁ ℓ≈B₁ ℓMB₁}
  {B₂ : CompType ℓB₂ ℓ≤B₂ ℓ≈B₂ ℓMB₂}
  {B₃ : CompType ℓB₃ ℓ≤B₃ ℓ≈B₃ ℓMB₃}
  (d₁ : CRelPP B₁ B₂ ℓd₁)
  (d₂ : CRelPP B₂ B₃ ℓd₂)
  where

  private
    iB₁ = B₁ .snd .snd .snd .fst
    iB₂ = B₂ .snd .snd .snd .fst
    iB₃ = B₃ .snd .snd .snd .fst

  ⊙C : CRelPP B₁ B₃ _
  ⊙C .fst = d₁ .fst ⊙ed d₂ .fst
  ⊙C .snd .fst = corecPushC _ _ _ (pushC d₂ ∘hom pushC d₁) (λ pB₁ →
    ED-CompSqH
      {ϕ₁ = iB₁ pB₁ .fst}
      {ϕ₂ = iB₂ _ .fst}
      {ϕ₃ = iB₃ _ .fst}
      (pushCSq d₁ _)
      (pushCSq d₂ _))
  ⊙C .snd .snd = corecPullC _ _ _ (pullC d₁ ∘hom pullC d₂) (λ pB₃ →
    ED-CompSqH
      {ϕ₁ = iB₁ _ .fst}{ϕ₂ = iB₂ _ .fst}{ϕ₃ = iB₃ pB₃ .fst}
      (pullCSq d₁ _) (pullCSq d₂ _))

module _  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁}{A₁' : ValType ℓA₁' ℓ≤A₁' ℓ≈A₁' ℓMA₁'}
          {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂}{A₂' : ValType ℓA₂' ℓ≤A₂' ℓ≈A₂' ℓMA₂'}
  where
  _×PP_ : (c₁ : VRelPP A₁ A₁' ℓc₁) (c₂ : VRelPP A₂ A₂' ℓc₂)
        → VRelPP (A₁ Types.× A₂) (A₁' Types.× A₂') _
  (c₁ ×PP c₂) .fst = c₁ .fst ×pbmonrel c₂ .fst
  (c₁ ×PP c₂) .snd .fst = elimSection _
    (corecVFact1 _ _ _ (i₁ ∘hom pushV c₁) λ pA₁ (a₁ , a₂) (a₁' , a₂') ×-rel →
      pushVSq c₁ pA₁ _ _ (×-rel .fst) , ×-rel .snd)
    (corecVFact1 _ _ _ (i₂ ∘hom pushV c₂) (λ pA₂ (a₁ , a₂) (a₁' , a₂') ×-rel →
      (×-rel .fst) , pushVSq c₂ pA₂ _ _ (×-rel .snd)))
  (c₁ ×PP c₂) .snd .snd = elimSection _
    (corecVFact2 _ _ _ (i₁ ∘hom pullV c₁) (λ pA₁' _ _ ×-rel →
      pullVSq c₁ pA₁' _ _ (×-rel .fst) , ×-rel .snd))
    (corecVFact2 _ _ _ (i₂ ∘hom pullV c₂) (λ pA₂' _ _ ×-rel →
      ×-rel .fst , pullVSq c₂ pA₂' _ _ (×-rel .snd)))

module _
  {A : ValType ℓA ℓ≤A ℓ≈A ℓMA}{A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  {B : CompType ℓB ℓ≤B ℓ≈B ℓMB}{B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
  where
  _⟶_ : VRelPP A A' ℓc → CRelPP B B' ℓd → CRelPP (A Types.⟶ B) (A' Types.⟶ B') _
  (c ⟶ d) .fst = c .fst ⟶rel d .fst
  (c ⟶ d) .snd .fst = elimSection _
    (corecCFact1 _ _ _ (i₁ ∘hom (pushV c ^opHom)) (λ pA f f' f~f' a a a~a' →
      f~f' _ _ (pushVSq c pA _ _ a~a')))
    (corecCFact1 _ _ _ (i₂ ∘hom pushC d) (λ pB f f' f~f' a a' a~a' →
      pushCSq d pB _ _ (f~f' _ _ a~a')))
  (c ⟶ d) .snd .snd = elimSection _
    (corecCFact2 _ _ _ (i₁ ∘hom (pullV c ^opHom)) (λ pA f f' f~f' a a a~a' →
      f~f' _ _ (pullVSq c pA _ _ a~a')))
    (corecCFact2 _ _ _ (i₂ ∘hom pullC d) (λ pB' f f' f~f' a a' a~a' →
      pullCSq d pB' _ _ (f~f' _ _ a~a')))

module _ {B : CompType ℓB ℓ≤B ℓ≈B ℓMB}{B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
  where
  private
    module B = ErrorDomainStr (B .snd .fst)
    module B' = ErrorDomainStr (B .snd .fst)
    open ErrorDomRel
  U : CRelPP B B' ℓd → VRelPP (Types.U B) (Types.U B') _
  U d .fst = U-rel (d .fst)
  U d .snd .fst = elimSection _
    (elimNat _ _ ((i₁ .fst 1 , (i₁ .fst 1 , λ b b' b~b' →
      d .fst .Rθ (next b) (next b') (next b~b'))) , refl))
    (corecVFact1 _ _ _ (i₂ ∘hom pushC d) (λ pB b b' b~b' → pushCSq d pB _ _ b~b'))
  U d .snd .snd = elimSection _
    (elimNat _ _ ((i₁ .fst 1 , i₁ .fst 1 , (λ b b' b~b' →
      d .fst .Rθ (next b) (next b') (next b~b'))) , refl))
    (corecVFact2 _ _ _ (i₂ ∘hom pullC d) (λ pB b b' b~b' → pullCSq d pB _ _ b~b'))

module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA}{A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  where
  open F-sq
  F : VRelPP A A' ℓc → CRelPP (Types.F A) (Types.F A') _
  F c .fst = F-rel (c .fst) where open F-rel
  F c .snd .fst = elimSection _
    (elimNat _ _ (((i₁ .fst 1) , i₁ .fst 1 , δ*Sq (c .fst)) , refl))
    (corecCFact1 _ _ _ (i₂ ∘hom pushV c) λ pA →
      F-sq (c .fst) (c .fst)
           (A .snd .interpV .fst pA .fst) (A' .snd .interpV .fst _ .fst)
           (pushVSq c pA))

  F c .snd .snd = elimSection _
    (elimNat _ _ (((i₁ .fst 1) , ((i₁ .fst 1) , (δ*Sq (c .fst)))) , refl))
    (corecCFact2 _ _ _ (i₂ ∘hom pullV c) (λ pA' →
      F-sq (c .fst) (c .fst)
           (A .snd .interpV .fst _ .fst) (A' .snd .interpV .fst _ .fst)
           (pullVSq c pA')))

-- TODO: inj-arr , inj-× , inj-nat
