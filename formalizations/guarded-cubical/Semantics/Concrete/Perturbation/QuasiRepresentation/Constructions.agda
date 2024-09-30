{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
module Semantics.Concrete.Perturbation.QuasiRepresentation.Constructions (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Data.Nat

open import Common.Common
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions hiding (π1; π2 ; 𝔹)
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.KleisliFunctors k

open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Types k as Types
open import Semantics.Concrete.Perturbation.QuasiRepresentation k
open import Semantics.Concrete.Perturbation.Kleisli k as KPtb

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
   
    ℓc₁ ℓc₂ ℓc₃  : Level    

    ℓMA₁ ℓMA₂ ℓMA₃ : Level
    ℓMB₁ ℓMB₂ ℓMB₃ : Level
    ℓMA₁' ℓMA₂' : Level


open F-ob
open F-mor
open F-rel
open F-sq


-- The functor F preserves quasi-representability. Namely:
--
-- 1. If c is quasi-left-representable, then Fc is also quasi-left-representable.
-- 2. If c is quasi-right-representable, then Fc is also quasi-right-representable.
module _ (A  : ValType ℓA  ℓ≤A  ℓ≈A ℓMA) (A'  : ValType ℓA'  ℓ≤A'  ℓ≈A' ℓMA')
         (c : PBRel (ValType→Predomain A) (ValType→Predomain A') ℓc) where

  private
    MA  = PtbV A
    iA  = interpV A .fst
    MA' = PtbV A'
    iA' = interpV A' .fst

    𝔸  = ValType→Predomain A
    𝔸' = ValType→Predomain A'

    rA  = idPRel 𝔸
    rA' = idPRel 𝔸'


  -- Note: It seems that Agda is implicitly using the equivalence
  -- between the relations.  F (rA) and r_(FA). No transporting is needed.

  F-leftRep :
    LeftRepV A A' c →
    LeftRepC (Types.F A) (Types.F A') (F-rel c)
  F-leftRep ρc = mkLeftRepC (Types.F A) (Types.F A') (F-rel c) eFc δlFc UpRFc δrFc UpLFc
  -- Replacing the first two arguments with _'s increases the type-checking time significantly.
 
    where
      -- Data corresponding to c
      ec   = embV _ _ _ ρc
      δlc  = δleV _ _ _ ρc
      δrc  = δreV _ _ _ ρc
      UpLc = UpLV _ _ _ ρc
      UpRc = UpRV _ _ _ ρc

      -- Data corresponding to Fc
      eFc : ErrorDomMor (F-ob 𝔸) (F-ob 𝔸')
      eFc = F-mor ec

      δlFc : ⟨ NatM ⊕ MA ⟩
      δlFc = i₂ .fst δlc

      UpRFc : ErrorDomSq (F-rel (idPRel 𝔸)) (F-rel c) (F-mor (iA δlc .fst)) (F-mor ec)
      UpRFc = F-sq (idPRel 𝔸) c (iA δlc .fst) ec UpRc

      δrFc : ⟨ NatM ⊕ MA' ⟩
      δrFc = i₂ .fst δrc

      UpLFc : ErrorDomSq (F-rel c) (F-rel (idPRel 𝔸')) (F-mor ec) (F-mor (iA' δrc .fst))
      UpLFc = F-sq c (idPRel 𝔸') ec (iA' δrc .fst) UpLc


  F-rightRep :
    RightRepV A A' c →
    RightRepC (Types.F A) (Types.F A') (F-rel c)
  F-rightRep ρc = mkRightRepC (Types.F A) (Types.F A') (F-rel c) pFc δlFc DnRFc δrFc DnLFc
    where
      -- Data corresponding to c
      pc   = projV _ _ _ ρc
      δlc  = δlpV  _ _ _ ρc
      δrc  = δrpV  _ _ _ ρc
      DnRc = DnRV  _ _ _ ρc
      DnLc = DnLV  _ _ _ ρc
      
      -- Data corresponding to Fc
      pFc : ErrorDomMor (F-ob 𝔸') (F-ob 𝔸)
      pFc = F-mor pc

      δlFc : ⟨ NatM ⊕ MA ⟩
      δlFc = i₂ .fst δlc

      DnRFc : ErrorDomSq (F-rel c) (F-rel rA) (F-mor (iA δlc .fst)) pFc
      DnRFc = F-sq c rA (iA δlc .fst) pc DnRc

      δrFc : ⟨ NatM ⊕ MA' ⟩
      δrFc = i₂ .fst δrc

      DnLFc : ErrorDomSq (F-rel rA') (F-rel c) pFc (F-mor (iA' δrc .fst))
      DnLFc = F-sq rA' c pc (iA' δrc .fst) DnLc


-----------------------------------------------------------------------------------

-- The functor U preserves quasi-representability. Namely:
--
-- 1. If d is quasi-left-representable, then Ud is also quasi-left-representable.
-- 2. If d is quasi-right-representable, then Ud is also quasi-right-representable.

module _ (B  : CompType ℓB  ℓ≤B  ℓ≈B ℓMB) (B'  : CompType ℓB'  ℓ≤B'  ℓ≈B' ℓMB')
         (d : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd) where

  private
    MB  = PtbC B
    iB  = interpC B .fst
    MB' = PtbC B'
    iB' = interpC B' .fst

    𝔹  = CompType→ErrorDomain B
    𝔹' = CompType→ErrorDomain B'

    rB  = idEDRel 𝔹
    rB' = idEDRel 𝔹'

  U-leftRep :
    LeftRepC B B' d →
    LeftRepV (Types.U B) (Types.U B') (U-rel d)
  U-leftRep ρd = mkLeftRepV (Types.U B) (Types.U B') (U-rel d) eUd δlFc UpRFc δrFc UpLFc
    where
     
      -- Data corresponding to d
      ed   = embC _ _ _ ρd
      δld  = δleC _ _ _ ρd
      δrd  = δreC _ _ _ ρd
      UpLd = UpLC _ _ _ ρd
      UpRd = UpRC _ _ _ ρd

      -- Data corresponding to Ud
      eUd : PBMor (U-ob 𝔹) (U-ob 𝔹')
      eUd = U-mor ed

      δlFc : ⟨ NatM ⊕ MB ⟩
      δlFc = i₂ .fst δld

      UpRFc : PBSq (U-rel (idEDRel 𝔹)) (U-rel d) (U-mor (iB δld .fst)) (U-mor ed)
      UpRFc = U-sq (idEDRel 𝔹) d (iB δld .fst) ed UpRd

      δrFc : ⟨ NatM ⊕ MB' ⟩
      δrFc = i₂ .fst δrd

      UpLFc : PBSq (U-rel d) (U-rel (idEDRel 𝔹')) (U-mor ed) (U-mor (iB' δrd .fst))
      UpLFc = U-sq d (idEDRel 𝔹') ed (iB' δrd .fst) UpLd


  U-rightRep :
    RightRepC B B' d →
    RightRepV (Types.U B) (Types.U B') (U-rel d)
  U-rightRep ρd = mkRightRepV (Types.U B) (Types.U B') (U-rel d) pUd δlUd DnRUd δrUd DnLUd
    where

      -- Data corresponding to d
      pd   = projC _ _ _ ρd
      δld  = δlpC  _ _ _ ρd
      δrd  = δrpC  _ _ _ ρd
      DnRd = DnRC  _ _ _ ρd
      DnLd = DnLC  _ _ _ ρd

      -- Data corresponding to Ud
      pUd : PBMor (U-ob 𝔹') (U-ob 𝔹)
      pUd = U-mor pd

      δlUd : ⟨ NatM ⊕ MB ⟩
      δlUd = i₂ .fst δld

      DnRUd : PBSq (U-rel d) (U-rel rB) (U-mor (iB δld .fst)) pUd
      DnRUd = U-sq d rB (iB δld .fst) pd DnRd

      δrUd : ⟨ NatM ⊕ MB' ⟩
      δrUd = i₂ .fst δrd

      DnLUd : PBSq (U-rel rB') (U-rel d) pUd (U-mor (iB' δrd .fst))
      DnLUd = U-sq rB' d pd (iB' δrd .fst) DnLd


-----------------------------------------------------------------------------------

-- The functor × preserves quasi-representability.

module _
  {A₁  : ValType ℓA₁  ℓ≤A₁  ℓ≈A₁ ℓMA₁} {A₁'  : ValType ℓA₁'  ℓ≤A₁'  ℓ≈A₁' ℓMA₁'}
  {A₂  : ValType ℓA₂  ℓ≤A₂  ℓ≈A₂ ℓMA₂} {A₂'  : ValType ℓA₂'  ℓ≤A₂'  ℓ≈A₂' ℓMA₂'}
  (c₁ : PBRel (ValType→Predomain A₁) (ValType→Predomain A₁') ℓc₁)
  (c₂ : PBRel (ValType→Predomain A₂) (ValType→Predomain A₂') ℓc₂)
  where

  private
    MA₁  = PtbV A₁
    MA₁' = PtbV A₁'
    MA₂  = PtbV A₂
    MA₂' = PtbV A₂'

    iA₁  = interpV A₁ .fst
    iA₁' = interpV A₁' .fst
    iA₂  = interpV A₂ .fst
    iA₂' = interpV A₂' .fst

    𝔸₁  = ValType→Predomain A₁
    𝔸₁' = ValType→Predomain A₁'
    𝔸₂  = ValType→Predomain A₂
    𝔸₂' = ValType→Predomain A₂'

    rA₁  = idPRel 𝔸₁
    rA₁' = idPRel 𝔸₁'
    rA₂  = idPRel 𝔸₂
    rA₂' = idPRel 𝔸₂'

    i×  = interpV (A₁ Types.× A₂) .fst
    i×' = interpV (A₁' Types.× A₂') .fst

  
  ×-leftRep :
    LeftRepV A₁ A₁' c₁ →
    LeftRepV A₂ A₂' c₂ →
    LeftRepV (A₁ Types.× A₂) (A₁' Types.× A₂') (c₁ ×pbmonrel c₂)
  ×-leftRep ρ₁ ρ₂ = mkLeftRepV (A₁ × A₂) (A₁' × A₂') (c₁ ×pbmonrel c₂)
    e× δl× UpR× δr× UpL×
    where
      -- Data corresponding to c₁
      ec₁   = embV _ _ _ ρ₁
      δlc₁  = δleV _ _ _ ρ₁
      δrc₁  = δreV _ _ _ ρ₁
      UpLc₁ = UpLV _ _ _ ρ₁
      UpRc₁ = UpRV _ _ _ ρ₁

      -- Data corresponding to c₂
      ec₂   = embV _ _ _ ρ₂
      δlc₂  = δleV _ _ _ ρ₂
      δrc₂  = δreV _ _ _ ρ₂
      UpLc₂ = UpLV _ _ _ ρ₂
      UpRc₂ = UpRV _ _ _ ρ₂

      -- Data corresponding to c₁ × c₂
      e× : PBMor (𝔸₁ ×dp 𝔸₂) (𝔸₁' ×dp 𝔸₂')
      e×  = ec₁ ×mor ec₂

      δl× : ⟨ MA₁ ⊕ MA₂ ⟩
      δl× = (i₂ .fst δlc₂) FP.· (i₁ .fst δlc₁)

      -- In the definitions of UpR× and UpL×, Agda seems to be implicitly using the
      -- fact that rA₁' × rA₂' = r(A₁' × A₂').
      UpR× : PBSq (idPRel (𝔸₁ ×dp 𝔸₂)) (c₁ ×pbmonrel c₂) (i× δl× .fst) e×
      UpR× = CompSqV
        {c₁ = rA₁ ×pbmonrel rA₂} {c₂ = c₁ ×pbmonrel rA₂} {c₃ = c₁ ×pbmonrel c₂}
        {f₁ = (iA₁ δlc₁ .fst) ×mor Id} {g₁ = ec₁ ×mor Id}
        {f₂ = Id ×mor (iA₂ δlc₂ .fst)} {g₂ = Id ×mor ec₂}
        (UpRc₁ ×-Sq (Predom-IdSqV rA₂))
        ((Predom-IdSqV c₁) ×-Sq UpRc₂)

      δr× : ⟨ MA₁' ⊕ MA₂' ⟩
      δr× = (i₂ .fst δrc₂) FP.· (i₁ .fst δrc₁)

      UpL× : PBSq (c₁ ×pbmonrel c₂) (idPRel (𝔸₁' ×dp 𝔸₂')) e× (i×' δr× .fst)
      UpL× = CompSqV
        {c₁ = c₁ ×pbmonrel c₂} {c₂ = rA₁' ×pbmonrel c₂} {c₃ = rA₁' ×pbmonrel rA₂'}
        {f₁ = ec₁ ×mor Id} {g₁ = (iA₁' δrc₁ .fst) ×mor Id}
        {f₂ = Id ×mor ec₂} {g₂ = Id ×mor (iA₂' δrc₂ .fst)}
        (UpLc₁ ×-Sq (Predom-IdSqV c₂))
        ((Predom-IdSqV rA₁') ×-Sq UpLc₂)

-----------------------------------------------------------------------------------

-- The functor ⟶ preserves quasi-representability.

module _
  {A  : ValType ℓA  ℓ≤A  ℓ≈A  ℓMA} 
  {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  {B  : CompType ℓB  ℓ≤B  ℓ≈B  ℓMB}
  {B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
  (c  : PBRel (ValType→Predomain A) (ValType→Predomain A') ℓc)     
  
  (d  : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd)
  
  where

  private
    MA  = PtbV A
    iA  = interpV A .fst
    MA' = PtbV A'
    iA' = interpV A' .fst

    𝔸  = ValType→Predomain A
    𝔸' = ValType→Predomain A'

    rA  = idPRel 𝔸
    rA' = idPRel 𝔸'

    MB  = PtbC B
    iB  = interpC B .fst
    MB' = PtbC B'
    iB' = interpC B' .fst

    𝔹  = CompType→ErrorDomain B
    𝔹' = CompType→ErrorDomain B'

    rB  = idEDRel 𝔹
    rB' = idEDRel 𝔹'

    i-arr  = interpC (A  Types.⟶ B)  .fst
    i-arr' = interpC (A' Types.⟶ B') .fst


  RightRepArrow :
    (ρc : LeftRepV A A' c) →
    (ρd : RightRepC B B' d) →
    RightRepC (A Types.⟶ B) (A' Types.⟶ B') (c ⟶rel d)
  RightRepArrow ρc ρd = mkRightRepC (A Types.⟶ B) (A' Types.⟶ B') (c ⟶rel d)
    p-arrow δl-arrow {!!} δr-arrow {!DnL-arrow!}
    
    where
      -- Data corresponding to c
      ec   = embV _ _ _ ρc
      δlc  = δleV _ _ _ ρc
      δrc  = δreV _ _ _ ρc
      UpLc = UpLV _ _ _ ρc
      UpRc = UpRV _ _ _ ρc

      -- Data corresponding to d
      pd   = projC _ _ _ ρd
      δld  = δlpC  _ _ _ ρd
      δrd  = δrpC  _ _ _ ρd
      DnRd = DnRC  _ _ _ ρd
      DnLd = DnLC  _ _ _ ρd

      -- Data corresponding to c ⟶ d
      p-arrow : ErrorDomMor (𝔸' ⟶ob 𝔹') (𝔸 ⟶ob 𝔹)
      p-arrow = (Id ⟶mor pd) ∘ed (ec ⟶mor IdE) -- ec ⟶mor pd

      δl-arrow : ⟨ MA ^op ⊕ MB ⟩
      δl-arrow = (i₂ .fst δld) FP.· (i₁ .fst δlc)

      DnR-arrow : ErrorDomSq (c ⟶rel d) (rA ⟶rel rB) (i-arr δl-arrow .fst) p-arrow
      DnR-arrow = ED-CompSqV
        {d₁ = c ⟶rel d} {d₂ = rA ⟶rel d} {d₃ = rA ⟶rel rB}
        {ϕ₁ = (iA δlc .fst) ⟶mor IdE} {ϕ₁' = ec ⟶mor IdE}
        {ϕ₂ = Id ⟶mor (iB δld .fst)}  {ϕ₂' = Id ⟶mor pd}
        (UpRc ⟶sq (ED-IdSqV d))
        ((Predom-IdSqV rA) ⟶sq DnRd)

      δr-arrow : ⟨ MA' ^op ⊕ MB' ⟩
      δr-arrow = (i₂ .fst δrd) FP.· (i₁ .fst δrc)

      DnL-arrow : ErrorDomSq (rA' ⟶rel rB') (c ⟶rel d) p-arrow (i-arr' δr-arrow .fst)
      DnL-arrow = ED-CompSqV
        {d₁ = rA' ⟶rel rB'} {d₂ = c ⟶rel rB'} {d₃ = c ⟶rel d}
        {ϕ₁ = ec ⟶mor IdE} {ϕ₁' = (iA' δrc .fst) ⟶mor IdE}
        {ϕ₂ = Id ⟶mor pd}  {ϕ₂' = Id ⟶mor (iB' δrd .fst)}
        (UpLc ⟶sq (ED-IdSqV rB'))
        ((Predom-IdSqV c) ⟶sq DnLd)


-----------------------------------------------------------------------------------


-- If Fc is quasi-right-representable, and Ud is quasi-left-representable,
-- then U(c ⟶ d) is quasi-left representable.


module _
  {A  : ValType ℓA  ℓ≤A  ℓ≈A  ℓMA} 
  {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  {B  : CompType ℓB  ℓ≤B  ℓ≈B  ℓMB}
  {B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
  (c  : PBRel (ValType→Predomain A) (ValType→Predomain A') ℓc)     
  (d  : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd)
  where

  private
    𝔸 = ValType→Predomain A
    𝔸' = ValType→Predomain A'

    𝔹 = CompType→ErrorDomain B
    𝔹' = CompType→ErrorDomain B'

    MFA  = PtbC (Types.F A)
    MFA' = PtbC (Types.F A')
    MUB  = PtbV (Types.U B)
    MUB' = PtbV (Types.U B')

    iFA : _ → _
    iFA = fst ∘ interpC (Types.F A) .fst

    iFA' : _ → _
    iFA' = fst ∘ interpC (Types.F A') .fst

    iUB : _ → _
    iUB  = fst ∘ interpV (Types.U B) .fst

    iUB' : _ → _
    iUB' = fst ∘ interpV (Types.U B') .fst

    rA  = idPRel (ValType→Predomain A)
    rA' = idPRel (ValType→Predomain A')
    rB  = idEDRel (CompType→ErrorDomain B)
    rB' = idEDRel (CompType→ErrorDomain B')

    rFA  = idEDRel (CompType→ErrorDomain (Types.F A))
    rFA' = idEDRel (CompType→ErrorDomain (Types.F A'))

    rUB  = idPRel (ValType→Predomain (Types.U B))
    rUB' = idPRel (ValType→Predomain (Types.U B'))

    U-arrow  = Types.U (A Types.⟶ B)
    U-arrow' = Types.U (A' Types.⟶ B')

    module M-arrow  = MonoidStr (PtbV U-arrow .snd)
    module M-arrow' = MonoidStr (PtbV U-arrow' .snd)

    i-arrow : _ → _ 
    i-arrow  = fst ∘ interpV U-arrow  .fst

    i-arrow' : _ → _
    i-arrow' = fst ∘ interpV U-arrow' .fst

    LeftRepUArrow :
      (ρFc : RightRepC (Types.F A) (Types.F A') (F-rel c)) →
      (ρUd : LeftRepV (Types.U B) (Types.U B') (U-rel d)) →
      LeftRepV U-arrow U-arrow' (U-rel (c ⟶rel d))
    LeftRepUArrow ρFc ρUd = mkLeftRepV U-arrow U-arrow' (U-rel (c ⟶rel d))
      e-UArrow δl-UArrow {!!} {!!} {!!}
      where
      
      -- Data corresponding to Fc
      pFc   = projC _ _ _ ρFc
      δlFc  = δlpC  _ _ _ ρFc
      δrFc  = δrpC  _ _ _ ρFc
      DnRFc = DnRC  _ _ _ ρFc
      DnLFc = DnLC  _ _ _ ρFc

      -- Data corresponding to Ud
      eUd   = embV _ _ _ ρUd
      δlUd  = δleV _ _ _ ρUd
      δrUd  = δreV _ _ _ ρUd
      UpLUd = UpLV _ _ _ ρUd
      UpRUd = UpRV _ _ _ ρUd

      -- Data corresponding to U(c ⟶ d)
      e-UArrow : PBMor _ _
      e-UArrow = (pFc ⟶Kᴸ 𝔹') ∘p (𝔸 ⟶Kᴿ eUd)

      δl-UArrow : ⟨ PtbV U-arrow ⟩
      δl-UArrow =  (Kl-Arrow-Ptb-L A B .fst δlFc)
         M-arrow.· (Kl-Arrow-Ptb-R A B .fst δlUd)

      UpR-UArrow : PBSq (U-rel (rA ⟶rel rB)) (U-rel (c ⟶rel d)) (i-arrow δl-UArrow) e-UArrow
      UpR-UArrow = {!!}
        where
          sq1 : PBSq (U-rel (rA ⟶rel rB)) (U-rel (rA ⟶rel d)) (𝔸 ⟶Kᴿ iUB δlUd) (𝔸 ⟶Kᴿ eUd)
          sq1 = KlArrowMorphismᴿ-sq (idPRel 𝔸) {dᵢ = rB} {dₒ = d} {f = iUB δlUd} {g = eUd} UpRUd

          sq2 : PBSq (U-rel (rA ⟶rel d)) (U-rel (c ⟶rel d)) (iFA δlFc ⟶Kᴸ 𝔹) (pFc ⟶Kᴸ 𝔹')
          sq2 = KlArrowMorphismᴸ-sq {cᵢ = rA} {cₒ = c} (iFA δlFc) pFc {d = d} DnRFc

          sq-comp : PBSq (U-rel (rA ⟶rel rB)) (U-rel (c ⟶rel d)) ((iFA δlFc ⟶Kᴸ 𝔹) ∘p (𝔸 ⟶Kᴿ iUB δlUd)) e-UArrow
          sq-comp = CompSqV {c₁ = U-rel (rA ⟶rel rB)} {c₂ = U-rel (rA ⟶rel d)} {c₃ = U-rel (c ⟶rel d)}
                            {f₁ = 𝔸 ⟶Kᴿ iUB δlUd} {g₁ = 𝔸 ⟶Kᴿ eUd} {f₂ = iFA δlFc ⟶Kᴸ 𝔹} {g₂ = pFc ⟶Kᴸ 𝔹'}
                            sq1 sq2

          -- We need to use the fact that the following are equal:
          --
          -- 1. interpreting δlFc as a semantic perturbation on FA
          -- and then applying the Kleisli action on morphisms, i.e.,
          -- (iFA δlFc) ⟶Kᴸ 𝔹.
          --
          -- 2. first applying the Kleisli action on syntactic perturbations
          -- to obtain a syntactic perturbation of U(A ⟶ B), and then
          -- interpreting that as a semantic perturbation on U(A ⟶ B).
          





-- The functors Π and Σ preserve quasi-representability.




