{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
module Semantics.Concrete.Perturbation.QuasiRepresentation.CompositionLemmaU (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Monoid.Base

open import Common.Common

open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.DPMorRelation as PRel
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k

open import Semantics.Concrete.Types k as Types
open import Semantics.Concrete.Perturbation.Relation.Alt k
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
  {B₁ : CompType ℓB₁ ℓ≤B₁ ℓ≈B₁ ℓMB₁}
  {B₂ : CompType ℓB₂ ℓ≤B₂ ℓ≈B₂ ℓMB₂}
  {B₃ : CompType ℓB₃ ℓ≤B₃ ℓ≈B₃ ℓMB₃}
  (d  : CRelPP B₁ B₂ ℓd)
  (d' : CRelPP B₂ B₃ ℓd')
  where

  private
    MB₁ = PtbC B₁
    MB₂ = PtbC B₂
    MB₃ = PtbC B₃
    module MB₁ = MonoidStr (MB₁ .snd)
    module MB₃ = MonoidStr (MB₃ .snd)

    MUB₁ = PtbV (Types.U B₁)
    MUB₃ = PtbV (Types.U B₃)
    module MUB₁ = MonoidStr (MUB₁ .snd)
    module MUB₃ = MonoidStr (MUB₃ .snd)
    
    iB₁ : _ → _
    iB₁ = fst ∘ interpC B₁ .fst

    iB₂ : _ → _
    iB₂ = fst ∘ interpC B₂ .fst

    iB₃ : _ → _
    iB₃ = fst ∘ interpC B₃ .fst

    iUB₁ : _ → _
    iUB₁ = fst ∘ interpV (Types.U B₁) .fst

    iUB₃ : _ → _
    iUB₃ = fst ∘ interpV (Types.U B₃) .fst

    𝔹₁ = CompType→ErrorDomain B₁
    𝔹₂ = CompType→ErrorDomain B₂
    𝔹₃ = CompType→ErrorDomain B₃

    rB₁ = idEDRel 𝔹₁
    rB₂ = idEDRel 𝔹₂
    rB₃ = idEDRel 𝔹₃

    rUB₁ = idPRel (ValType→Predomain (Types.U B₁))
    rUB₃ = idPRel (ValType→Predomain (Types.U B₃))

    |d|  = CRelPP→ErrorDomRel d
    |d'| = CRelPP→ErrorDomRel d'
    |dd'| = |d| ⊙ed |d'|


  -- If Ud and Ud' are quasi-left-representable, then U(dd') is
  -- quasi-left-representable.
  module _
    (ρd   : RightRepC B₁ B₂ |d|)
    (ρd'  : RightRepC B₂ B₃ |d'|)
    (ρUd  : LeftRepV (Types.U B₁) (Types.U B₂) (U-rel |d|))
    (ρUd' : LeftRepV (Types.U B₂) (Types.U B₃) (U-rel |d'|))
    where

    repUdUd'→repUdd' :
      LeftRepV (Types.U B₁) (Types.U B₃) (U-rel |dd'|)
    repUdUd'→repUdd' = mkLeftRepV (Types.U B₁) (Types.U B₃) (U-rel |dd'|)
      eUdd' δlUdd' UpRUdd' δrUdd' UpLUdd'
      where
      Udd' : PBRel _ _ _
      Udd' = U-rel |dd'|

      -- Data corresponding to Ud
      eUd   = embV _ _ _ ρUd
      δlUd  = δleV _ _ _ ρUd
      δrUd  = δreV _ _ _ ρUd
      UpLUd = UpLV _ _ _ ρUd
      UpRUd = UpRV _ _ _ ρUd


      -- Data corresponding to Ud'
      eUd'   = embV _ _ _ ρUd'
      δlUd'  = δleV _ _ _ ρUd'
      δrUd'  = δreV _ _ _ ρUd'
      UpLUd' = UpLV _ _ _ ρUd'
      UpRUd' = UpRV _ _ _ ρUd'


      -- Data corresponding to UdUd'
      UdUd' : PBRel _ _ _
      UdUd' =  U-rel |d| PRel.⊙ U-rel |d'|

      ρcomp-left : LeftRepV (Types.U B₁) (Types.U B₃) UdUd'
      ρcomp-left = LeftRepV-Comp (Rel.U d) (Rel.U d') ρUd ρUd'

      ecomp   = embV _ _ _ ρcomp-left
      δlcomp  = δleV _ _ _ ρcomp-left
      δrcomp  = δreV _ _ _ ρcomp-left
      UpLcomp = UpLV _ _ _ ρcomp-left
      UpRcomp = UpRV _ _ _ ρcomp-left


      -- Know: Udd' and UdUd' have the same projection, so are quasi-equivalent
      equiv : QuasiOrderEquivV (Types.U B₁) (Types.U B₃) Udd' UdUd'
      equiv = eqEmb→quasiEquivV _ _ (U-rightRep _ _ |dd'|  (RightRepC-Comp d d' ρd ρd'))
        (RightRepV-Comp (Rel.U d) (Rel.U d') (U-rightRep _ _ |d| ρd) (U-rightRep _ _ |d'| ρd'))
        refl -- U preserves composition definitionally    

      module equiv = QuasiOrderEquivV equiv
      sq-Udd'-UdUd' = equiv.sq-c-c'
      sq-UdUd'-Udd' = equiv.sq-c'-c

      -- Data corresponding to U(dd')

      eUdd' : PBMor (U-ob 𝔹₁) (U-ob 𝔹₃)
      eUdd' = iUB₃ equiv.δ₂' ∘p ecomp ∘p iUB₁ equiv.δ₁

      δlUdd' : ⟨ MUB₁ ⟩
      δlUdd' = equiv.δ₂ MUB₁.· δlcomp MUB₁.· equiv.δ₁

      UpRUdd' : PBSq rUB₁ Udd' (iUB₁ δlUdd') eUdd'
      UpRUdd' = CompSqV
        {c₁ = rUB₁} {c₂ = UdUd'} {c₃ = Udd'}
        {f₁ = (iUB₁ δlcomp ∘p iUB₁ equiv.δ₁)} {g₁ = (ecomp ∘p iUB₁ equiv.δ₁)}
        {f₂ = iUB₁ equiv.δ₂} {g₂ = iUB₃ equiv.δ₂'}
        comp12 sq-UdUd'-Udd'
        where
          comp12 : PBSq rUB₁ UdUd' (iUB₁ δlcomp ∘p iUB₁ equiv.δ₁) (ecomp ∘p iUB₁ equiv.δ₁)
          comp12 = CompSqV
            {c₁ = rUB₁} {c₂ = rUB₁} {c₃ = UdUd'}
            (Predom-IdSqH (iUB₁ equiv.δ₁)) UpRcomp

      δrUdd' : ⟨ MUB₃ ⟩
      δrUdd' = equiv.δ₂' MUB₃.· δrcomp MUB₃.· equiv.δ₁'

      UpLUdd' : PBSq Udd' rUB₃ eUdd' (iUB₃ δrUdd')
      UpLUdd' = CompSqV
        {c₁ = Udd'} {c₂ = rUB₃} {c₃ = rUB₃}
        {f₁ = (ecomp ∘p iUB₁ equiv.δ₁)} {g₁ = (iUB₃ δrcomp ∘p iUB₃ equiv.δ₁')}
        {f₂ = iUB₃ equiv.δ₂'} {g₂ = iUB₃ equiv.δ₂'}
        comp12 (Predom-IdSqH (iUB₃ equiv.δ₂'))
        where
          comp12 : PBSq Udd' rUB₃ (ecomp ∘p iUB₁ equiv.δ₁) (iUB₃ δrcomp ∘p iUB₃ equiv.δ₁')
          comp12 = CompSqV
            {c₁ = Udd'} {c₂ = UdUd'} {c₃ = rUB₃}           
            sq-Udd'-UdUd' UpLcomp          

          


{-

    repFdFd'→repFdd' = mkRightRepC (Types.F B₁) (Types.F B₃) (F-rel (|d| ⊙ |d'|))
      pFdd' δlFdd' DnRFdd' δrFdd' DnLFdd'
      where

      -- Data corresponding to F(cc')

      -- Note: It appears that we do not need to transport along the fact that
      -- iFB₁ and iFB₃ preserve composition, because they do so definitionally.

      pFcc' : ErrorDomMor (F-ob 𝔸₃) (F-ob 𝔸₁)
      pFcc' = (iFB₁ equiv.δ₂) ∘ed pcomp ∘ed (iFB₃ equiv.δ₁')

      δlFcc' : ⟨ MFB₁ ⟩
      δlFcc' = equiv.δ₂ MFB₁.· δlcomp MFB₁.· equiv.δ₁

      DnRFcc' : ErrorDomSq Fcc' rFB₁ (iFB₁ δlFcc') pFcc'
      DnRFcc' = comp123
        where
          comp12 : ErrorDomSq Fcc' rFB₁ ((iFB₁ δlcomp) ∘ed (iFB₁ equiv.δ₁)) (pcomp ∘ed (iFB₃ equiv.δ₁'))
          comp12 = ED-CompSqV {d₁ = Fcc'} {d₂ = FcFc'} {d₃ = rFB₁} {ϕ₁ = iFB₁ equiv.δ₁} {ϕ₁' = iFB₃ equiv.δ₁'} {ϕ₂ = iFB₁ δlcomp} {ϕ₂' = pcomp}
            equiv.sq-d-d' DnRcomp

          comp123 : ErrorDomSq Fcc' rFB₁ ((iFB₁ equiv.δ₂) ∘ed (iFB₁ δlcomp) ∘ed (iFB₁ equiv.δ₁)) pFcc'
          comp123 = ED-CompSqV
            {d₁ = Fcc'} {d₂ = rFB₁} {d₃ = rFB₁}
            {ϕ₁ = (iFB₁ δlcomp) ∘ed (iFB₁ equiv.δ₁)} {ϕ₁' = pcomp ∘ed (iFB₃ equiv.δ₁')}
            {ϕ₂ = iFB₁ equiv.δ₂} {ϕ₂' = iFB₁ equiv.δ₂}
            comp12 (ED-IdSqH (iFB₁ equiv.δ₂))

      δrFcc' : ⟨ MFB₃ ⟩
      δrFcc' = equiv.δ₂' MFB₃.· δrcomp MFB₃.· equiv.δ₁'

      DnLFcc' : ErrorDomSq rFB₃ Fcc' pFcc' (iFB₃ δrFcc')
      DnLFcc' = comp123
        where
          comp12 : ErrorDomSq rFB₃ FcFc' (pcomp ∘ed (iFB₃ equiv.δ₁')) ((iFB₃ δrcomp) ∘ed (iFB₃ equiv.δ₁'))
          comp12 = ED-CompSqV {d₁ = rFB₃} {d₂ = rFB₃} {d₃ = FcFc'} {ϕ₁ = iFB₃ equiv.δ₁'} {ϕ₁' = iFB₃ equiv.δ₁'} {ϕ₂ = pcomp} {ϕ₂' = iFB₃ δrcomp}
            (ED-IdSqH (iFB₃ equiv.δ₁')) DnLcomp

          comp123 : ErrorDomSq rFB₃ Fcc' pFcc' ((iFB₃ equiv.δ₂') ∘ed (iFB₃ δrcomp) ∘ed (iFB₃ equiv.δ₁'))
          comp123 = ED-CompSqV
            {d₁ = rFB₃} {d₂ = FcFc'} {d₃ = Fcc'}
            {ϕ₁ = pcomp ∘ed (iFB₃ equiv.δ₁')} {ϕ₁' = (iFB₃ δrcomp) ∘ed (iFB₃ equiv.δ₁')}
            {ϕ₂ = iFB₁ equiv.δ₂} {ϕ₂' = iFB₃ equiv.δ₂'}
            comp12 equiv.sq-d'-d

          
-}

    
    
  
