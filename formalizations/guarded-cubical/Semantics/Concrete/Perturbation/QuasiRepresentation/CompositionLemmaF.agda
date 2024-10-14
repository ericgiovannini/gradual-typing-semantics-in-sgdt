{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
module Semantics.Concrete.Perturbation.QuasiRepresentation.CompositionLemmaF (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Monoid.Base

open import Common.Common

open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Relation as PRel
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.FreeErrorDomain k

open import Semantics.Concrete.Types k as Types
open import Semantics.Concrete.Perturbation.Relation k
open import Semantics.Concrete.Perturbation.Relation.Constructions k as Rel
open import Semantics.Concrete.Perturbation.QuasiRepresentation k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.Constructions k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.Composition k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.QuasiEquivalence k


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
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

    ℓMA₁ ℓMA₂ ℓMA₃ : Level
    ℓMB₁ ℓMB₂ ℓMB₃ : Level


open F-ob
open F-mor
open F-rel

module _
  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁}
  {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂}
  {A₃ : ValType ℓA₃ ℓ≤A₃ ℓ≈A₃ ℓMA₃}
  (c  : VRelPP A₁ A₂ ℓc)
  (c' : VRelPP A₂ A₃ ℓc')
  where

  private
    MA₁ = PtbV A₁
    MA₂ = PtbV A₂
    MA₃ = PtbV A₃
    module MA₁ = MonoidStr (MA₁ .snd)
    module MA₃ = MonoidStr (MA₃ .snd)

    MFA₁ = PtbC (Types.F A₁)
    MFA₃ = PtbC (Types.F A₃)
    module MFA₁ = MonoidStr (MFA₁ .snd)
    module MFA₃ = MonoidStr (MFA₃ .snd)
    
    iA₁ : _ → _
    iA₁ = fst ∘ interpV A₁ .fst

    iA₂ : _ → _
    iA₂ = fst ∘ interpV A₂ .fst

    iA₃ : _ → _
    iA₃ = fst ∘ interpV A₃ .fst

    iFA₁ : _ → _
    iFA₁ = fst ∘ interpC (Types.F A₁) .fst

    iFA₃ : _ → _
    iFA₃ = fst ∘ interpC (Types.F A₃) .fst

    𝔸₁ = ValType→Predomain A₁
    𝔸₂ = ValType→Predomain A₂
    𝔸₃ = ValType→Predomain A₃

    rA₁ = idPRel 𝔸₁
    rA₂ = idPRel 𝔸₂
    rA₃ = idPRel 𝔸₃

    rFA₁ = idEDRel (CompType→ErrorDomain (Types.F A₁))
    rFA₃ = idEDRel (CompType→ErrorDomain (Types.F A₃))

    |c|  = VRelPP→PredomainRel c
    |c'| = VRelPP→PredomainRel c'

  -- If Fc and Fc' are quasi-right-representable, then F(cc') is
  -- quasi-right-representable.
  module _
    (ρc   : LeftRepV A₁ A₂ |c|)
    (ρc'  : LeftRepV A₂ A₃ |c'|)
    (ρFc  : RightRepC (Types.F A₁) (Types.F A₂) (F-rel |c|))
    (ρFc' : RightRepC (Types.F A₂) (Types.F A₃) (F-rel |c'|))
    where

    repFcFc'→repFcc' :
      RightRepC (Types.F A₁) (Types.F A₃) (F-rel (|c| PRel.⊙ |c'|))
    repFcFc'→repFcc' = mkRightRepC (Types.F A₁) (Types.F A₃) (F-rel (|c| ⊙ |c'|))
      pFcc' δlFcc' DnRFcc' δrFcc' DnLFcc'
      where

      Fcc' : ErrorDomRel _ _ _
      Fcc' = F-rel (|c| PRel.⊙ |c'|)

      -- Data corresponding to Fc
      pFc   = projC _ _ _ ρFc
      δlFc  = δlpC  _ _ _ ρFc
      δrFc  = δrpC  _ _ _ ρFc
      DnRFc = DnRC  _ _ _ ρFc
      DnLFc = DnLC  _ _ _ ρFc

      -- Data corresponding to Fc'
      pFc'   = projC _ _ _ ρFc'
      δlFc'  = δlpC  _ _ _ ρFc'
      δrFc'  = δrpC  _ _ _ ρFc'
      DnRFc' = DnRC  _ _ _ ρFc'
      DnLFc' = DnLC  _ _ _ ρFc'

      -- Data corresponding to FcFc'
      FcFc' : ErrorDomRel _ _ _
      FcFc' =  F-rel |c| ⊙ed F-rel |c'|

      ρcomp-right : RightRepC (Types.F A₁) (Types.F A₃) FcFc'
      ρcomp-right = RightRepC-Comp (Rel.F c) (Rel.F c') ρFc ρFc'

      pcomp   = projC _ _ _ ρcomp-right
      δlcomp  = δlpC  _ _ _ ρcomp-right
      δrcomp  = δrpC  _ _ _ ρcomp-right
      DnRcomp = DnRC  _ _ _ ρcomp-right
      DnLcomp = DnLC  _ _ _ ρcomp-right
      

      -- Know: Fcc' and FcFc' have the same embedding, so are quasi-equivalent
      equiv : QuasiOrderEquivC (Types.F A₁) (Types.F A₃) Fcc' FcFc'
      equiv = eqEmb→quasiEquivC _ _
        (F-leftRep A₁ A₃ (|c| ⊙ |c'|) (LeftRepV-Comp c c' ρc ρc'))
        (LeftRepC-Comp (Rel.F c) (Rel.F c') (F-leftRep A₁ A₂ |c| ρc) (F-leftRep A₂ A₃ |c'| ρc'))
        (F-mor-pres-comp _ _) -- apply functoriality of F

      module equiv = QuasiOrderEquivC equiv

      -- Data corresponding to F(cc')

      -- Note: It appears that we do not need to transport along the fact that
      -- iFA₁ and iFA₃ preserve composition, because they do so definitionally.

      pFcc' : ErrorDomMor (F-ob 𝔸₃) (F-ob 𝔸₁)
      pFcc' = (iFA₁ equiv.δ₂) ∘ed pcomp ∘ed (iFA₃ equiv.δ₁')

      δlFcc' : ⟨ MFA₁ ⟩
      δlFcc' = equiv.δ₂ MFA₁.· δlcomp MFA₁.· equiv.δ₁

      DnRFcc' : ErrorDomSq Fcc' rFA₁ (iFA₁ δlFcc') pFcc'
      DnRFcc' = comp123
        where
          comp12 : ErrorDomSq Fcc' rFA₁ ((iFA₁ δlcomp) ∘ed (iFA₁ equiv.δ₁)) (pcomp ∘ed (iFA₃ equiv.δ₁'))
          comp12 = ED-CompSqV {d₁ = Fcc'} {d₂ = FcFc'} {d₃ = rFA₁} {ϕ₁ = iFA₁ equiv.δ₁} {ϕ₁' = iFA₃ equiv.δ₁'} {ϕ₂ = iFA₁ δlcomp} {ϕ₂' = pcomp}
            equiv.sq-d-d' DnRcomp

          comp123 : ErrorDomSq Fcc' rFA₁ ((iFA₁ equiv.δ₂) ∘ed (iFA₁ δlcomp) ∘ed (iFA₁ equiv.δ₁)) pFcc'
          comp123 = ED-CompSqV
            {d₁ = Fcc'} {d₂ = rFA₁} {d₃ = rFA₁}
            {ϕ₁ = (iFA₁ δlcomp) ∘ed (iFA₁ equiv.δ₁)} {ϕ₁' = pcomp ∘ed (iFA₃ equiv.δ₁')}
            {ϕ₂ = iFA₁ equiv.δ₂} {ϕ₂' = iFA₁ equiv.δ₂}
            comp12 (ED-IdSqH (iFA₁ equiv.δ₂))

      δrFcc' : ⟨ MFA₃ ⟩
      δrFcc' = equiv.δ₂' MFA₃.· δrcomp MFA₃.· equiv.δ₁'

      DnLFcc' : ErrorDomSq rFA₃ Fcc' pFcc' (iFA₃ δrFcc')
      DnLFcc' = comp123
        where
          comp12 : ErrorDomSq rFA₃ FcFc' (pcomp ∘ed (iFA₃ equiv.δ₁')) ((iFA₃ δrcomp) ∘ed (iFA₃ equiv.δ₁'))
          comp12 = ED-CompSqV {d₁ = rFA₃} {d₂ = rFA₃} {d₃ = FcFc'} {ϕ₁ = iFA₃ equiv.δ₁'} {ϕ₁' = iFA₃ equiv.δ₁'} {ϕ₂ = pcomp} {ϕ₂' = iFA₃ δrcomp}
            (ED-IdSqH (iFA₃ equiv.δ₁')) DnLcomp

          comp123 : ErrorDomSq rFA₃ Fcc' pFcc' ((iFA₃ equiv.δ₂') ∘ed (iFA₃ δrcomp) ∘ed (iFA₃ equiv.δ₁'))
          comp123 = ED-CompSqV
            {d₁ = rFA₃} {d₂ = FcFc'} {d₃ = Fcc'}
            {ϕ₁ = pcomp ∘ed (iFA₃ equiv.δ₁')} {ϕ₁' = (iFA₃ δrcomp) ∘ed (iFA₃ equiv.δ₁')}
            {ϕ₂ = iFA₁ equiv.δ₂} {ϕ₂' = iFA₃ equiv.δ₂'}
            comp12 equiv.sq-d'-d

          


    
    
  
