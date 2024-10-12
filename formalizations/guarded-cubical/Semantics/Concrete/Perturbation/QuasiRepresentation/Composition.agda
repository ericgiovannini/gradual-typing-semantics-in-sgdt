{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
module Semantics.Concrete.Perturbation.QuasiRepresentation.Composition (k : Clock) where

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
open import Semantics.Concrete.Perturbation.Relation.Alt k
open import Semantics.Concrete.Perturbation.Relation.Constructions k
open import Semantics.Concrete.Perturbation.QuasiRepresentation k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.Constructions k

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

open IsMonoidHom


-- The composition of quasi-representable relations that satisfy push-pull
-- is quasi-representable.
--
-- More specifically:
--
-- If c : A₁ --|-- A₂ and c' : A₂ --|-- A₃ are quasi-left- (resp. right)-representable
-- and satisfy push-pull, then c ⊙ c' is quasi-left- (resp. right)-representable.
--
-- Likewise for computation relations d : B₁ --|-- B₂ and d' : B₂ --|-- B₃.

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

    iA₁ : _ → _
    iA₁ = fst ∘ interpV A₁ .fst

    iA₂ : _ → _
    iA₂ = fst ∘ interpV A₂ .fst

    iA₃ : _ → _
    iA₃ = fst ∘ interpV A₃ .fst

    𝔸₁ = ValType→Predomain A₁
    𝔸₂ = ValType→Predomain A₂
    𝔸₃ = ValType→Predomain A₃

    rA₁ = idPRel 𝔸₁
    rA₂ = idPRel 𝔸₂
    rA₃ = idPRel 𝔸₃

    |c|  = VRelPP→PredomainRel c
    |c'| = VRelPP→PredomainRel c'


  -- Composition of quasi-left-representations
  LeftRepV-Comp :
    LeftRepV A₁ A₂ |c| →
    LeftRepV A₂ A₃ |c'| →
    LeftRepV A₁ A₃ (|c| PRel.⊙ |c'|)
  LeftRepV-Comp ρc ρc' = mkLeftRepV A₁ A₃ (|c| PRel.⊙ |c'|)
    e-comp δl-comp UpR-comp δr-comp UpL-comp
    where

    -- Data corresponding to c
    ec   = embV _ _ _ ρc
    δlc  = δleV _ _ _ ρc
    δrc  = δreV _ _ _ ρc
    UpLc = UpLV _ _ _ ρc
    UpRc = UpRV _ _ _ ρc

    -- Data corresponding to c'
    ec'   = embV _ _ _ ρc'
    δlc'  = δleV _ _ _ ρc'
    δrc'  = δreV _ _ _ ρc'
    UpLc' = UpLV _ _ _ ρc'
    UpRc' = UpRV _ _ _ ρc'

    -- Data corresponding to c ⊙ c'
    e-comp : PMor 𝔸₁ 𝔸₃
    e-comp = ec' ∘p ec

    δl-comp : ⟨ MA₁ ⟩
    δl-comp = (pullV c .fst δlc') MA₁.· δlc

    UpR-comp : PSq rA₁ (|c| PRel.⊙ |c'|) (iA₁ δl-comp) e-comp
    UpR-comp = subst
      (λ z → PSq rA₁ (|c| PRel.⊙ |c'|) z e-comp)
      (sym (cong fst (interpV A₁ .snd .pres· (pullV c .fst δlc') δlc)))
      sq
      where
        α : PSq rA₁ (|c| PRel.⊙ rA₂) (Id ∘p (iA₁ δlc)) (Id ∘p ec)
        α = CompSqV {c₁ = rA₁} {c₂ = |c|} {c₃ = |c| PRel.⊙ rA₂} UpRc (sq-c-c⊙A' |c|)

        β : PSq (|c| PRel.⊙ rA₂) (|c| PRel.⊙ |c'|) (iA₁ (pullV c .fst δlc')) ec'
        β = CompSqH {f = iA₁ (pullV c .fst δlc')} {g = iA₂ δlc'} {h = ec'} (pullVSq c δlc') UpRc'

        sq : PSq rA₁ (|c| PRel.⊙ |c'|) (iA₁ (pullV c .fst δlc') ∘p (iA₁ δlc)) e-comp
        sq = CompSqV
          {c₁ = rA₁} {c₂ = |c| PRel.⊙ rA₂} {c₃ = |c| PRel.⊙ |c'|}
          {f₁ = Id ∘p (iA₁ δlc)} {g₁ = Id ∘p ec} {f₂ = iA₁ (pullV c .fst δlc')} {g₂ = ec'}
          α β

    δr-comp : ⟨ MA₃ ⟩
    δr-comp = δrc' MA₃.· (pushV c' .fst δrc)

    UpL-comp : PSq (|c| PRel.⊙ |c'|) rA₃ e-comp (iA₃ δr-comp)
    UpL-comp = subst
      (λ z → PSq (|c| PRel.⊙ |c'|) rA₃ e-comp z)
      (sym (cong fst (interpV A₃ .snd .pres· _ _)))
      sq
      where
        α : PSq (|c| PRel.⊙ |c'|) (rA₂ PRel.⊙ |c'|) ec (iA₃ (pushV c' .fst δrc))
        α = CompSqH
          {f = ec} {g = iA₂ δrc} {h = iA₃ (pushV c' .fst δrc)}
          UpLc (pushVSq c' δrc)

        β : _
        β = CompSqV
              {c₁ = rA₂ PRel.⊙ |c'|} {c₂ = |c'|} {c₃ = rA₃}
              (sq-idA⊙c-c |c'|) UpLc' 

        sq : PSq (|c| PRel.⊙ |c'|) rA₃ e-comp ((iA₃ δrc') ∘p (iA₃ (pushV c' .fst δrc))) 
        sq = CompSqV
          {c₁ = |c| PRel.⊙ |c'|} {c₂ = rA₂ PRel.⊙ |c'|} {c₃ = rA₃}
          {f₁ = ec}        {g₁ = iA₃ (pushV c' .fst δrc)}
          {f₂ = ec' ∘p Id} {g₂ = iA₃ δrc' ∘p Id}
          α β


  -- Composition of quasi-right-representations
  RightRepV-Comp :
    RightRepV A₁ A₂ |c| →
    RightRepV A₂ A₃ |c'| →
    RightRepV A₁ A₃ (|c| PRel.⊙ |c'|)
  RightRepV-Comp ρc ρc' = mkRightRepV A₁ A₃ (|c| PRel.⊙ |c'|)
    p-comp δl-comp DnR-comp δr-comp DnL-comp
    where
    
    -- Data corresponding to c
    pc  =  projV _ _ _ ρc
    δlc  = δlpV  _ _ _ ρc
    δrc  = δrpV  _ _ _ ρc
    DnRc = DnRV  _ _ _ ρc
    DnLc = DnLV  _ _ _ ρc

    -- Data corresponding to c'
    pc'   = projV _ _ _ ρc'
    δlc'  = δlpV  _ _ _ ρc'
    δrc'  = δrpV  _ _ _ ρc'
    DnRc' = DnRV  _ _ _ ρc'
    DnLc' = DnLV  _ _ _ ρc'

    -- Data corresponding to c ⊙ c'
    p-comp : PMor 𝔸₃ 𝔸₁
    p-comp = pc ∘p pc'

    δl-comp : ⟨ MA₁ ⟩
    δl-comp = δlc MA₁.· (pullV c .fst δlc')

    DnR-comp : PSq (|c| PRel.⊙ |c'|) rA₁ (iA₁ δl-comp) p-comp
    DnR-comp = subst
      (λ z → PSq (|c| PRel.⊙ |c'|) rA₁ z p-comp)
      (sym (cong fst (interpV A₁ .snd .pres· _ _)))
      sq
      where
        α : PSq (|c| PRel.⊙ |c'|) (|c| PRel.⊙ rA₂) (iA₁ (pullV c .fst δlc')) pc'
        α = CompSqH {f = iA₁ _} {g = iA₂ δlc'} {h = pc'} (pullVSq c δlc') DnRc'

        β : _
        β = CompSqV {c₁ = |c| PRel.⊙ rA₂} {c₂ = |c|} {c₃ = rA₁} (sq-c⊙A'-c |c|) DnRc

        sq : PSq (|c| PRel.⊙ |c'|) rA₁ ((iA₁ δlc) ∘p iA₁ (pullV c .fst δlc')) (pc ∘p pc')
        sq = CompSqV {c₁ = |c| PRel.⊙ |c'|} {c₂ = |c| PRel.⊙ rA₂} {c₃ = rA₁}
                     {f₁ = iA₁ (pullV c .fst δlc')} {g₁ = pc'}
                     {f₂ = iA₁ δlc ∘p Id} {g₂ = pc ∘p Id}
                      α β
        

    δr-comp : ⟨ MA₃ ⟩
    δr-comp = (pushV c' .fst δrc) MA₃.· δrc'

    DnL-comp : PSq rA₃ (|c| PRel.⊙ |c'|) p-comp (iA₃ δr-comp)
    DnL-comp = subst
      (λ z → PSq rA₃ (|c| PRel.⊙ |c'|) p-comp z)
      (sym (cong fst (interpV A₃ .snd .pres· _ _)))
      sq 
      where
        α : PSq rA₃ (rA₂ PRel.⊙ |c'|) (Id ∘p pc') (Id ∘p iA₃ δrc')
        α = CompSqV {c₁ = rA₃} {c₂ = |c'|} {c₃ = rA₂ PRel.⊙ |c'|} DnLc' (sq-c-idA⊙c |c'|)

        β : _
        β = CompSqH {f = pc} {g = iA₂ δrc} {h = iA₃ (pushV c' .fst δrc)} DnLc (pushVSq c' δrc)

        sq : PSq rA₃ ((|c| PRel.⊙ |c'|)) p-comp (iA₃ (pushV c' .fst δrc) ∘p (iA₃ δrc'))
        sq = CompSqV {c₁ = rA₃} {c₂ = rA₂ PRel.⊙ |c'|} {c₃ = |c| PRel.⊙ |c'|}
                     {f₁ = Id ∘p pc'} {g₁ = Id ∘p iA₃ δrc'}
                     {f₂ = pc} {g₂ = iA₃ (pushV c' .fst δrc)}
                     α β

    





----------------------------------------------------------------------




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

    iB₁ : _ → _
    iB₁ = fst ∘ interpC B₁ .fst

    iB₂ : _ → _
    iB₂ = fst ∘ interpC B₂ .fst

    iB₃ : _ → _
    iB₃ = fst ∘ interpC B₃ .fst

    𝔹₁ = CompType→ErrorDomain B₁
    𝔹₂ = CompType→ErrorDomain B₂
    𝔹₃ = CompType→ErrorDomain B₃

    rB₁ = idEDRel 𝔹₁
    rB₂ = idEDRel 𝔹₂
    rB₃ = idEDRel 𝔹₃

    |d|  = CRelPP→ErrorDomRel d
    |d'| = CRelPP→ErrorDomRel d'


  -- Composition of quasi-left-representations
  LeftRepC-Comp :
    LeftRepC B₁ B₂ |d| →
    LeftRepC B₂ B₃ |d'| →
    LeftRepC B₁ B₃ (|d| ⊙ed |d'|)
  LeftRepC-Comp ρd ρd' = mkLeftRepC B₁ B₃ (|d| ⊙ed |d'|)
    e-comp δl-comp UpR-comp δr-comp UpL-comp
    where

    -- Data corresponding to d
    ed   = embC _ _ _ ρd
    δld  = δleC _ _ _ ρd
    δrd  = δreC _ _ _ ρd
    UpLd = UpLC _ _ _ ρd
    UpRd = UpRC _ _ _ ρd

    -- Data corresponding to d'
    ed'   = embC _ _ _ ρd'
    δld'  = δleC _ _ _ ρd'
    δrd'  = δreC _ _ _ ρd'
    UpLd' = UpLC _ _ _ ρd'
    UpRd' = UpRC _ _ _ ρd'

    -- Data corresponding to d ⊙ d'
    e-comp : ErrorDomMor 𝔹₁ 𝔹₃
    e-comp = ed' ∘ed ed

    δl-comp : ⟨ MB₁ ⟩
    δl-comp = (pullC d .fst δld') MB₁.· δld

    UpR-comp : ErrorDomSq rB₁ (|d| ⊙ed |d'|) (iB₁ δl-comp) e-comp
    UpR-comp = subst
      (λ z → ErrorDomSq rB₁ (|d| ⊙ed |d'|) z e-comp)
      (sym (cong fst (interpC B₁ .snd .pres· (pullC d .fst δld') δld)))
      sq
      where
        α : ErrorDomSq rB₁ (|d| ⊙ed rB₂) (IdE ∘ed (iB₁ δld)) (IdE ∘ed ed)
        α = ED-CompSqV {d₁ = rB₁} {d₂ = |d|} {d₃ = |d| ⊙ed rB₂} UpRd (sq-d-d⊙idB' |d|)

        β : ErrorDomSq (|d| ⊙ed rB₂) (|d| ⊙ed |d'|) (iB₁ (pullC d .fst δld')) ed'
        β = ED-CompSqH {ϕ₁ = iB₁ (pullC d .fst δld')} {ϕ₂ = iB₂ δld'} {ϕ₃ = ed'} (pullCSq d δld') UpRd'

        sq : ErrorDomSq rB₁ (|d| ⊙ed |d'|) (iB₁ (pullC d .fst δld') ∘ed (iB₁ δld)) e-comp
        sq = ED-CompSqV
          {d₁ = rB₁} {d₂ = |d| ⊙ed rB₂} {d₃ = |d| ⊙ed |d'|}
          {ϕ₁ = IdE ∘ed (iB₁ δld)} {ϕ₁' = IdE ∘ed ed} {ϕ₂ = iB₁ (pullC d .fst δld')} {ϕ₂' = ed'}
          α β

    δr-comp : ⟨ MB₃ ⟩
    δr-comp = δrd' MB₃.· (pushC d' .fst δrd)

    UpL-comp : ErrorDomSq (|d| ⊙ed |d'|) rB₃ e-comp (iB₃ δr-comp)
    UpL-comp = subst
      (λ z → ErrorDomSq (|d| ⊙ed |d'|) rB₃ e-comp z)
      (sym (cong fst (interpC B₃ .snd .pres· _ _)))
      sq
      where
        α : ErrorDomSq (|d| ⊙ed |d'|) (rB₂ ⊙ed |d'|) ed (iB₃ (pushC d' .fst δrd))
        α = ED-CompSqH
          {ϕ₁ = ed} {ϕ₂ = iB₂ δrd} {ϕ₃ = iB₃ (pushC d' .fst δrd)}
          UpLd (pushCSq d' δrd)

        β : _
        β = ED-CompSqV
              {d₁ = rB₂ ⊙ed |d'|} {d₂ = |d'|} {d₃ = rB₃}
              (sq-idB⊙d-d |d'|) UpLd' 

        sq : ErrorDomSq (|d| ⊙ed |d'|) rB₃ e-comp ((iB₃ δrd') ∘ed (iB₃ (pushC d' .fst δrd))) 
        sq = ED-CompSqV
          {d₁ = |d| ⊙ed |d'|} {d₂ = rB₂ ⊙ed |d'|} {d₃ = rB₃}
          {ϕ₁ = ed}        {ϕ₁' = iB₃ (pushC d' .fst δrd)}
          {ϕ₂ = ed' ∘ed IdE} {ϕ₂' = iB₃ δrd' ∘ed IdE}
          α β


  -- Composition of quasi-right-representations
  RightRepC-Comp :
    RightRepC B₁ B₂ |d| →
    RightRepC B₂ B₃ |d'| →
    RightRepC B₁ B₃ (|d| ⊙ed |d'|)
  RightRepC-Comp ρd ρd' = mkRightRepC B₁ B₃ (|d| ⊙ed |d'|)
    p-comp δl-comp DnR-comp δr-comp DnL-comp
    where
    
    -- Data corresponding to d
    pd  =  projC _ _ _ ρd
    δld  = δlpC _ _ _ ρd
    δrd  = δrpC  _ _ _ ρd
    DnRd = DnRC  _ _ _ ρd
    DnLd = DnLC  _ _ _ ρd

    -- Data corresponding to d'
    pd'   = projC _ _ _ ρd'
    δld'  = δlpC  _ _ _ ρd'
    δrd'  = δrpC  _ _ _ ρd'
    DnRd' = DnRC  _ _ _ ρd'
    DnLd' = DnLC  _ _ _ ρd'

    -- Data corresponding to d ⊙ d'
    p-comp : ErrorDomMor 𝔹₃ 𝔹₁
    p-comp = pd ∘ed pd'

    δl-comp : ⟨ MB₁ ⟩
    δl-comp = δld MB₁.· (pullC d .fst δld')

    DnR-comp : ErrorDomSq (|d| ⊙ed |d'|) rB₁ (iB₁ δl-comp) p-comp
    DnR-comp = subst
      (λ z → ErrorDomSq (|d| ⊙ed |d'|) rB₁ z p-comp)
      (sym (cong fst (interpC B₁ .snd .pres· _ _)))
      sq
      where
        α : ErrorDomSq (|d| ⊙ed |d'|) (|d| ⊙ed rB₂) (iB₁ (pullC d .fst δld')) pd'
        α = ED-CompSqH {ϕ₁ = iB₁ _} {ϕ₂ = iB₂ δld'} {ϕ₃ = pd'} (pullCSq d δld') DnRd'

        β : _
        β = ED-CompSqV {d₁ = |d| ⊙ed rB₂} {d₂ = |d|} {d₃ = rB₁} (sq-d⊙idB'-d |d|) DnRd

        sq : ErrorDomSq (|d| ⊙ed |d'|) rB₁ ((iB₁ δld) ∘ed iB₁ (pullC d .fst δld')) (pd ∘ed pd')
        sq = ED-CompSqV {d₁ = |d| ⊙ed |d'|} {d₂ = |d| ⊙ed rB₂} {d₃ = rB₁}
                     {ϕ₁ = iB₁ (pullC d .fst δld')} {ϕ₁' = pd'}
                     {ϕ₂ = iB₁ δld ∘ed IdE} {ϕ₂' = pd ∘ed IdE}
                      α β
        

    δr-comp : ⟨ MB₃ ⟩
    δr-comp = (pushC d' .fst δrd) MB₃.· δrd'

    DnL-comp : ErrorDomSq rB₃ (|d| ⊙ed |d'|) p-comp (iB₃ δr-comp)
    DnL-comp = subst
      (λ z → ErrorDomSq rB₃ (|d| ⊙ed |d'|) p-comp z)
      (sym (cong fst (interpC B₃ .snd .pres· _ _)))
      sq 
      where
        α : ErrorDomSq rB₃ (rB₂ ⊙ed |d'|) (IdE ∘ed pd') (IdE ∘ed iB₃ δrd')
        α = ED-CompSqV {d₁ = rB₃} {d₂ = |d'|} {d₃ = rB₂ ⊙ed |d'|} DnLd' (sq-d-idB⊙d |d'|)

        β : _
        β = ED-CompSqH {ϕ₁ = pd} {ϕ₂ = iB₂ δrd} {ϕ₃ = iB₃ (pushC d' .fst δrd)} DnLd (pushCSq d' δrd)

        sq : ErrorDomSq rB₃ ((|d| ⊙ed |d'|)) p-comp (iB₃ (pushC d' .fst δrd) ∘ed (iB₃ δrd'))
        sq = ED-CompSqV {d₁ = rB₃} {d₂ = rB₂ ⊙ed |d'|} {d₃ = |d| ⊙ed |d'|}
                     {ϕ₁ = IdE ∘ed pd'} {ϕ₁' = IdE ∘ed iB₃ δrd'}
                     {ϕ₂ = pd} {ϕ₂' = iB₃ (pushC d' .fst δrd)}
                     α β

    
