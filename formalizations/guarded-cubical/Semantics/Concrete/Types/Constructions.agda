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
open import Cubical.Foundations.Function

import Cubical.Data.Nat as Nat
import Cubical.Data.Unit as Unit
open import Cubical.Relation.Nullary

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.Instances.Trivial as Trivial
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.FreeProduct.Indexed as IFP

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Constructions
  renaming (ℕ to ∣ℕ∣; flat to flatDP)
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Types.Base k

open import Semantics.Concrete.Dyn k
open import Semantics.Concrete.DynPerturb k

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

-- open ValTypeStr

flat : hSet ℓ → ValType ℓ ℓ ℓ ℓ-zero
flat X = mkValType (flatDP X) TrivialMonoid Trivial.rec

ℕ : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
ℕ = flat (Nat.ℕ , Nat.isSetℕ)

U : CompType ℓ ℓ≤ ℓ≈ ℓM → ValType ℓ ℓ≤ ℓ≈ ℓM
U B = mkValType (U-ob (CompType→ErrorDomain B)) M-UB i-UB where
  M-UB = NatM FP.⊕ B .snd .snd .fst

  i-UB : MonoidHom _ _
  i-UB = FP.rec (NatM→.h _ (δB-as-PrePtb _)) (CEndo-B→Endo-UB ∘hom B .snd .snd .snd)

Unit : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
Unit = flat (Unit.Unit , Unit.isSetUnit)

_×_ : ValType ℓ ℓ≤ ℓ≈ ℓM
    → ValType ℓ' ℓ≤' ℓ≈' ℓM'
    → ValType _ _ _ _
A × A' = mkValType (ValType→Predomain A ×dp ValType→Predomain A') M-× i-× where
  M-× = PtbV A FP.⊕ PtbV A'
  i-× = FP.rec (×A-PrePtb ∘hom interpV A) (A×-PrePtb ∘hom interpV A')

F : ValType ℓ ℓ≤ ℓ≈ ℓM → CompType ℓ (ℓ-max ℓ ℓ≤) (ℓ-max ℓ ℓ≈) ℓM
F A = mkCompType (F-ob (ValType→Predomain A)) M-FA iFA where
  open F-ob
  M-FA = NatM FP.⊕ PtbV A
  iFA = FP.rec (NatM→.h _ (δ*FA-as-PrePtb _)) (Endo-A→CEndo-FA ∘hom interpV A)

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
  M-Arrow = (PtbV A ^op) FP.⊕ B .snd .snd .fst
  i-Arrow = FP.rec
    (A⟶-PrePtb ∘hom (interpV A ^opHom))
    (⟶B-PrePtb ∘hom interpC B)

dyn' : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
dyn' = mkValType Dyn' PtbD ι-dyn' where
  open DynDef
  open Guarded (next Dyn)

dyn : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
dyn = mkValType Dyn PtbD ι-dyn where
  open DynDef


-- Sigma and Pi

DiscreteTy : (ℓ : Level) → Type (ℓ-suc ℓ)
DiscreteTy ℓ = Σ[ X ∈ Type ℓ ] (Discrete X)

ΣV : (X : DiscreteTy ℓX) →
  {ℓ ℓ≤ ℓ≈ ℓM : Level} →
  (B : ⟨ X ⟩ → ValType ℓ ℓ≤ ℓ≈ ℓM) →
  ValType (ℓ-max ℓX ℓ) (ℓ-max ℓX ℓ≤) (ℓ-max ℓX ℓ≈) (ℓ-max ℓX ℓM)
ΣV (X , dec) B = mkValType (ΣP (X , isSetX) (ValType→Predomain ∘ B)) M-Σ i-Σ
  where
  isSetX = Discrete→isSet dec
  M-Σ = IFP.⊕ᵢ X (PtbV ∘ B)
  i-Σ =
    IFP.rec X (PtbV ∘ B) _ int
    where
      int : (x : X) → MonoidHom (PtbV (B x)) _
      int x = (Σ-PrePtb (X , isSetX) dec x) ∘hom (interpV (B x))
      

ΠV : (X : DiscreteTy ℓX) →
  {ℓ ℓ≤ ℓ≈ ℓM : Level} →
  (B : ⟨ X ⟩ → ValType ℓ ℓ≤ ℓ≈ ℓM) →
  ValType (ℓ-max ℓX ℓ) (ℓ-max ℓX ℓ≤) (ℓ-max ℓX ℓ≈) (ℓ-max ℓX ℓM)
ΠV (X , dec) B = mkValType (ΠP X (ValType→Predomain ∘ B)) M-Π i-Π
  where
  M-Π = IFP.⊕ᵢ X (PtbV ∘ B)
  i-Π = IFP.rec X (PtbV ∘ B) _ int
    where
      -- int' : X → ⟨ Endo (ΠP X (λ x → ValType→Predomain (B x))) ⟩
      -- int' x = Π-PrePtb X dec x .fst {!!} -- interpV (B x)

      int : (x : X) → MonoidHom (PtbV (B x)) _
      int x = (Π-PrePtb X dec x) ∘hom (interpV (B x))


module _ {k : Clock} where

  open Clocked k
  open IsMonoidHom

  V▹ : ValType ℓ ℓ≤ ℓ≈ ℓM → ValType ℓ ℓ≤ ℓ≈ ℓM
  V▹ A = mkValType (PB▹ (ValType→Predomain A)) MA h
    where
      MA = PtbV A
      iA = interpV A

      h : MonoidHom MA (Endo (PB▹ ValType→Predomain A))
      h = PrePtb▹ ∘hom iA
      
      
