{-

  Type constructors for value and computation types.

-}

{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Common.Later

module Semantics.Concrete.Types.Constructions (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

import Cubical.Data.Nat as Nat
import Cubical.Data.Unit as Unit

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.Instances.Trivial as Trivial
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct as FP

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Constructions
  renaming (ℕ to ∣ℕ∣; flat to flatDP)
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Types.Base k

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓ≤' ℓ≈' ℓM' : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓc ℓd : Level

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

open ValTypeStr

flat : hSet ℓ → ValType ℓ ℓ ℓ ℓ-zero
flat X = mkValType (flatDP X) TrivialMonoid Trivial.rec

ℕ : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
ℕ = flat (Nat.ℕ , Nat.isSetℕ)

U : CompType ℓ ℓ≤ ℓ≈ ℓM → ValType ℓ ℓ≤ ℓ≈ ℓM
U B = mkValType (U-ob (CompType→ErrorDomain B)) M-UB i-UB where
  M-UB = NatM ⊕ B .snd .snd .fst

  i-UB : MonoidHom _ _
  i-UB = FP.rec (NatM→.h _ (δB-as-PrePtb _)) (CEndo-B→Endo-UB ∘hom B .snd .snd .snd)

Unit : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
Unit = flat (Unit.Unit , Unit.isSetUnit)

_×_ : ValType ℓ ℓ≤ ℓ≈ ℓM
    → ValType ℓ' ℓ≤' ℓ≈' ℓM'
    → ValType _ _ _ _
A × A' = mkValType (ValType→Predomain A ×dp ValType→Predomain A') M-× i-× where
  M-× = A .snd .PtbV ⊕ A' .snd .PtbV
  i-× = FP.rec (×A-PrePtb ∘hom A .snd .interpV) (A×-PrePtb ∘hom A' .snd .interpV)

F : ValType ℓ ℓ≤ ℓ≈ ℓM → CompType ℓ (ℓ-max ℓ ℓ≤) (ℓ-max ℓ ℓ≈) ℓM
F A = mkCompType (F-ob (ValType→Predomain A)) M-FA iFA where
  open F-ob
  M-FA = NatM ⊕ A .snd .PtbV
  iFA = FP.rec (NatM→.h _ (δ*FA-as-PrePtb _)) (Endo-A→CEndo-FA ∘hom A .snd .interpV)

_⟶_ : ValType ℓ ℓ≤ ℓ≈ ℓM
      → CompType ℓ' ℓ≤' ℓ≈' ℓM'
      → CompType
          (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈) ℓ') ℓ≤') ℓ≈')
          (ℓ-max ℓ ℓ≤')
          (ℓ-max (ℓ-max ℓ ℓ≈) ℓ≈')
          (ℓ-max ℓM ℓM')
A ⟶ B =
  mkCompType (ValType→Predomain A ⟶ob CompType→ErrorDomain B) M-Arrow i-Arrow
  where
  M-Arrow = (A .snd .PtbV  ^op) ⊕ B .snd .snd .fst
  i-Arrow = FP.rec
    (A⟶-PrePtb ∘hom (A .snd .interpV ^opHom))
    (⟶B-PrePtb ∘hom (B .snd .snd .snd))

-- -- TODO: dyn
-- -- dyn : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
-- -- dyn = mkValType Dyn PtbD ι-dyn where
-- --   open DynDef

