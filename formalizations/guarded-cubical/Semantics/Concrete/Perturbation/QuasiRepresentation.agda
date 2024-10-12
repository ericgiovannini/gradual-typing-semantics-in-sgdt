{-

   A QuasiRepresentation of a relation between valtypes/comptypes is
   like it being representable, except there are perturbations instead
   of identities.

-}
{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
module Semantics.Concrete.Perturbation.QuasiRepresentation (k : Clock) where

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

module _ (A  : ValType ℓA  ℓ≤A  ℓ≈A ℓMA) (A'  : ValType ℓA'  ℓ≤A'  ℓ≈A' ℓMA')
         (c : PBRel (ValType→Predomain A) (ValType→Predomain A') ℓc)
  where
  private
    MA = PtbV A
    iA = interpV A .fst
    MA' = PtbV A'
    iA' = interpV A' .fst

    rA = idPRel (ValType→Predomain A)
    rA' = idPRel (ValType→Predomain A')
  LeftRepV : Type _
  LeftRepV =
    Σ[ e ∈ ValTypeMor A A' ]
    (Σ[ δl ∈ ⟨ MA ⟩ ] PBSq rA c (iA δl .fst) e)
    × (Σ[ δr ∈ ⟨ MA' ⟩ ] PBSq c rA' e (iA' δr .fst))

  mkLeftRepV :
    (e : ValTypeMor A A') →
    (δl : ⟨ MA ⟩) →
    PBSq rA c (iA δl .fst) e →
    (δr : ⟨ MA' ⟩) →
    PBSq c rA' e (iA' δr .fst) →
    LeftRepV
  mkLeftRepV e δl UpR δr UpL = e , (δl , UpR) , (δr , UpL)

  module _ (r : LeftRepV) where

    embV : ValTypeMor A A'
    embV = r .fst

    δleV : ⟨ MA ⟩
    δleV = r .snd .fst .fst

    UpRV : PBSq rA c (iA δleV .fst) embV
    UpRV = r .snd .fst .snd

    δreV : ⟨ MA' ⟩
    δreV = r .snd .snd .fst

    UpLV : PBSq c rA' embV (iA' δreV .fst)
    UpLV = r .snd .snd .snd


  RightRepV : Type _
  RightRepV =
    Σ[ p ∈ ValTypeMor A' A ]
    (Σ[ δl ∈ ⟨ MA ⟩ ] PBSq c rA (iA δl .fst) p)
    × (Σ[ δr ∈ ⟨ MA' ⟩ ] PBSq rA' c p (iA' δr .fst))

  mkRightRepV :
    (p : ValTypeMor A' A) →
    (δl : ⟨ MA ⟩) →
    PBSq c rA (iA δl .fst) p →
    (δr : ⟨ MA' ⟩) →
    PBSq rA' c p (iA' δr .fst) →
    RightRepV
  mkRightRepV p δl DnR δr DnL = p , (δl , DnR) , (δr , DnL)


  module _ (r : RightRepV) where

    projV : ValTypeMor A' A
    projV = r .fst

    δlpV : ⟨ MA ⟩
    δlpV = r .snd .fst. fst

    DnRV : PBSq c rA (iA δlpV .fst) projV
    DnRV = r .snd .fst .snd

    δrpV : ⟨ MA' ⟩
    δrpV = r .snd .snd .fst

    DnLV : PBSq rA' c projV (iA' δrpV .fst)
    DnLV = r .snd .snd .snd
    

module _ (B  : CompType ℓB  ℓ≤B  ℓ≈B ℓMB) (B'  : CompType ℓB'  ℓ≤B'  ℓ≈B' ℓMB')
         (d : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd)
  where

  private
    MB = B .snd .snd .fst
    iB = B .snd .snd .snd .fst
    rB = idEDRel (CompType→ErrorDomain B)
    MB' = B' .snd .snd .fst
    iB' = B' .snd .snd .snd .fst
    rB' = idEDRel (CompType→ErrorDomain B')

  LeftRepC : Type _
  LeftRepC =
    Σ[ e ∈ CompTypeMor B B' ]
    ((Σ[ δl ∈ ⟨ MB ⟩ ] ErrorDomSq rB d (iB δl .fst) e)
    × (Σ[ δr ∈ ⟨ MB' ⟩ ] ErrorDomSq d rB' e (iB' δr .fst)))

  mkLeftRepC :
    (e : CompTypeMor B B') →
    (δl : ⟨ MB ⟩) →
    ErrorDomSq rB d (iB δl .fst) e →
    (δr : ⟨ MB' ⟩) →
    ErrorDomSq d rB' e (iB' δr .fst) →
    LeftRepC
  mkLeftRepC e δl UpR δr UpL = e , (δl , UpR) , (δr , UpL)

  module _ (r : LeftRepC) where

    embC : CompTypeMor B B'
    embC = r .fst

    δleC : ⟨ MB ⟩
    δleC = r .snd .fst .fst

    UpRC : ErrorDomSq rB d (iB δleC .fst) embC
    UpRC = r .snd .fst .snd

    δreC : ⟨ MB' ⟩
    δreC = r .snd .snd .fst

    UpLC : ErrorDomSq d rB' embC (iB' δreC .fst)
    UpLC = r .snd .snd .snd



  RightRepC : Type _
  RightRepC =
    Σ[ p ∈ CompTypeMor B' B ]
    (Σ[ δl ∈ ⟨ MB ⟩ ] ErrorDomSq d rB (iB δl .fst) p)
    × (Σ[ δr ∈ ⟨ MB' ⟩ ] ErrorDomSq rB' d p (iB' δr .fst))

  mkRightRepC :
    (p : CompTypeMor B' B) →
    (δl : ⟨ MB ⟩) →
    ErrorDomSq d rB (iB δl .fst) p →
    (δr : ⟨ MB' ⟩) →
    ErrorDomSq rB' d p (iB' δr .fst) →
    RightRepC
  mkRightRepC p δl DnR δr DnL = p , (δl , DnR) , (δr , DnL)

  module _ (r : RightRepC) where

    projC : CompTypeMor B' B
    projC = r .fst

    δlpC : ⟨ MB ⟩
    δlpC = r .snd .fst. fst

    DnRC : ErrorDomSq d rB (iB δlpC .fst) projC
    DnRC = r .snd .fst .snd

    δrpC : ⟨ MB' ⟩
    δrpC = r .snd .snd .fst

    DnLC : ErrorDomSq rB' d projC (iB' δrpC .fst)
    DnLC = r .snd .snd .snd
