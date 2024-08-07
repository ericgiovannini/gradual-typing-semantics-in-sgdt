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

module _ (A  : ValType ℓA  ℓ≤A  ℓ≈A ℓMA) (A'  : ValType ℓA'  ℓ≤A'  ℓ≈A' ℓMA')
         (c : PBRel (ValType→Predomain A) (ValType→Predomain A') ℓc)
  where
  private
    MA = A .snd .PtbV
    iA = A .snd .interpV .fst
    MA' = A' .snd .PtbV
    iA' = A' .snd .interpV .fst

    rA = idPRel (ValType→Predomain A)
    rA' = idPRel (ValType→Predomain A')
  LeftRepV : Type _
  LeftRepV =
    Σ[ e ∈ ValTypeMor A A' ]
    (Σ[ δl ∈ ⟨ MA ⟩ ] PBSq rA c (iA δl .fst) e)
    × (Σ[ δr ∈ ⟨ MA' ⟩ ] PBSq c rA' e (iA' δr .fst))


  RightRepV : Type _
  RightRepV =
    Σ[ p ∈ ValTypeMor A' A ]
    (Σ[ δl ∈ ⟨ MA ⟩ ] PBSq c rA (iA δl .fst) p)
    × (Σ[ δr ∈ ⟨ MA' ⟩ ] PBSq rA' c p (iA' δr .fst))

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

  RightRepC : Type _
  RightRepC =
    Σ[ p ∈ CompTypeMor B' B ]
    (Σ[ δl ∈ ⟨ MB ⟩ ] ErrorDomSq d rB (iB δl .fst) p)
    × (Σ[ δr ∈ ⟨ MB' ⟩ ] ErrorDomSq rB' d p (iB' δr .fst))
