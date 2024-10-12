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
open import Cubical.Foundations.Transport

import Cubical.Data.Nat as Nat
import Cubical.Data.Unit as Unit
import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool
open import Cubical.Data.Sigma using (≡-× ; ΣPathP)
open import Cubical.Relation.Nullary

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.Instances.Trivial as Trivial
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeMonoid as Free
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.FreeProduct.Indexed as IFP

open import Common.Common

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Constructions
  renaming (ℕ to ∣ℕ∣; flat to flatDP)
open import Semantics.Concrete.Predomain.Combinators hiding (U)
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Perturbation.Semantic k
open import Semantics.Concrete.Types.Base k

open import Semantics.Concrete.LaterMonoid k

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓ≤' ℓ≈' ℓM' : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓc ℓd : Level

    ℓA₁  ℓ≤A₁  ℓ≈A₁  ℓMA₁  : Level
    ℓA₁' ℓ≤A₁' ℓ≈A₁' ℓMA₁' : Level
    ℓA₂  ℓ≤A₂  ℓ≈A₂  ℓMA₂  : Level
    ℓA₂' ℓ≤A₂' ℓ≈A₂' ℓMA₂' : Level

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

-- open ValTypeStr

flat : hSet ℓ → ValType ℓ ℓ ℓ ℓ-zero
flat X = mkValType (flatDP X) TrivialMonoid Trivial.rec

ℕ : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
ℕ = flat (Nat.ℕ , Nat.isSetℕ)

U : CompType ℓ ℓ≤ ℓ≈ ℓM → ValType ℓ ℓ≤ ℓ≈ ℓM
U B = mkValType (U-ob (CompType→ErrorDomain B)) M-UB i-UB where
  -- M-UB = NatM FP.⊕ B .snd .snd .fst
  M-UB = FM-1 FP.⊕ B .snd .snd .fst

  i-UB : MonoidHom _ _
  -- i-UB = FP.rec (NatM→.h _ (δB-as-SemPtb _)) (CEndo-B→Endo-UB ∘hom B .snd .snd .snd)
  i-UB = FP.rec (FM-1-rec _ (δB-as-SemPtb _)) (CEndo-B→Endo-UB ∘hom B .snd .snd .snd)

{-
U' : CompType ℓ ℓ≤ ℓ≈ ℓM → ValType ℓ ℓ≤ ℓ≈ ℓM
U' B = mkValType (U-ob (CompType→ErrorDomain B)) M-UB i-UB where
  MB = PtbC B
  iB = interpC B
  M-UB = NatM FP.⊕ MB FP.⊕ (Monoid▹ MB)

  i-UB : MonoidHom _ _
  i-UB = FP.rec
    (NatM→.h _ (δB-as-SemPtb _))
    (FP.rec (CEndo-B→Endo-UB ∘hom iB) ({!!} ∘hom monoidhom▹ iB))

  |B| = CompType→ErrorDomain B

  test : MonoidHom (Monoid▹ (CEndo (CompType→ErrorDomain B))) (Endo (U-ob (CompType→ErrorDomain B)))
  test .fst m~ .fst .PBMor.f b = |B| .snd .ErrorDomainStr.θ .PBMor.f λ t → m~ t .fst .ErrorDomMor.fun b
  test .fst m~ .fst .PBMor.isMon = {!!}
  test .fst m~ .fst .PBMor.pres≈ = {!!}
  test .fst m~ .snd = {!!}
  test .snd .IsMonoidHom.presε = SemPtb≡ _ _ (funExt (λ x → {!refl!}))
  test .snd .IsMonoidHom.pres· = {!!}
-}

Unit : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
Unit = flat (Unit.Unit , Unit.isSetUnit)

_×_ : ValType ℓ ℓ≤ ℓ≈ ℓM
    → ValType ℓ' ℓ≤' ℓ≈' ℓM'
    → ValType _ _ _ _
A × A' = mkValType (ValType→Predomain A ×dp ValType→Predomain A') M-× i-× where
  M-× = PtbV A FP.⊕ PtbV A'
  i-× = FP.rec (×A-SemPtb ∘hom interpV A) (A×-SemPtb ∘hom interpV A')

F : ValType ℓ ℓ≤ ℓ≈ ℓM → CompType ℓ (ℓ-max ℓ ℓ≤) (ℓ-max ℓ ℓ≈) ℓM
F A = mkCompType (F-ob (ValType→Predomain A)) M-FA iFA where
  open F-ob
  -- M-FA = NatM FP.⊕ PtbV A
  -- iFA = FP.rec (NatM→.h _ (δ*FA-as-SemPtb _)) (Endo-A→CEndo-FA ∘hom interpV A)
  M-FA = FM-1 FP.⊕ PtbV A
  iFA = FP.rec (FM-1-rec _ ((δ*FA-as-SemPtb _))) ((Endo-A→CEndo-FA ∘hom interpV A))

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
    (A⟶-SemPtb ∘hom (interpV A ^opHom))
    (⟶B-SemPtb ∘hom interpC B)

_⊎_ : ValType ℓ ℓ≤ ℓ≈ ℓM
    → ValType ℓ' ℓ≤' ℓ≈' ℓM'
    → ValType (ℓ-max ℓ ℓ') (ℓ-max ℓ≤ ℓ≤') (ℓ-max ℓ≈ ℓ≈') (ℓ-max ℓM ℓM')
A ⊎ A' = mkValType ((ValType→Predomain A) ⊎p (ValType→Predomain A')) M-Sum i-Sum
  where
  M-Sum = (PtbV A) FP.⊕ (PtbV A')
  i-Sum = FP.rec
    (⊎A-SemPtb ∘hom interpV A)
    (A⊎-SemPtb ∘hom interpV A')


-- Sigma and Pi

DiscreteTy : (ℓ : Level) → Type (ℓ-suc ℓ)
DiscreteTy ℓ = Σ[ X ∈ Type ℓ ] (Discrete X)

module _
  (X : DiscreteTy ℓX)
  {ℓ ℓ≤ ℓ≈ ℓM : Level}
  (B : ⟨ X ⟩ → ValType ℓ ℓ≤ ℓ≈ ℓM) where

  isSetX : isSet (X .fst)
  isSetX = Discrete→isSet (X .snd)

  P-Σ = ΣP (⟨ X ⟩ , isSetX) (ValType→Predomain ∘ B)

  M-Σ : Monoid (ℓ-max ℓX ℓM)
  M-Σ = IFP.⊕ᵢ (X .fst) (PtbV ∘ B)

  i-Σ : MonoidHom (⊕ᵢ ⟨ X ⟩ (λ x → PtbV (B x))) (Endo P-Σ)
  i-Σ =
    IFP.rec ⟨ X ⟩ (PtbV ∘ B) _ int
    where
      int : (x : ⟨ X ⟩) → MonoidHom (PtbV (B x)) (Endo P-Σ)
      int x = (Σ-SemPtb (⟨ X ⟩ , isSetX) (X .snd) x) ∘hom (interpV (B x))

  ΣV : 
    ValType (ℓ-max ℓX ℓ) (ℓ-max ℓX ℓ≤) (ℓ-max ℓX ℓ≈) (ℓ-max ℓX ℓM)
  ΣV = mkValType P-Σ M-Σ i-Σ
    

module _
  (X : DiscreteTy ℓX)
  {ℓ ℓ≤ ℓ≈ ℓM : Level}
  (B : ⟨ X ⟩ → ValType ℓ ℓ≤ ℓ≈ ℓM) where

  P-Π = (ΠP ⟨ X ⟩ (ValType→Predomain ∘ B))

  M-Π : Monoid (ℓ-max ℓX ℓM)
  M-Π = IFP.⊕ᵢ ⟨ X ⟩ (PtbV ∘ B)

  i-Π : MonoidHom (⊕ᵢ ⟨ X ⟩ (λ x → PtbV (B x))) (Endo P-Π)
  i-Π = IFP.rec ⟨ X ⟩ (PtbV ∘ B) _ int
    where
      -- int' : X → ⟨ Endo (ΠP X (λ x → ValType→Predomain (B x))) ⟩
      -- int' x = Π-SemPtb X dec x .fst {!!} -- interpV (B x)

      int : (x : ⟨ X ⟩) → MonoidHom (PtbV (B x)) (Endo P-Π)
      int x = (Π-SemPtb ⟨ X ⟩ (X .snd) x) ∘hom (interpV (B x))

  ΠV : 
    ValType (ℓ-max ℓX ℓ) (ℓ-max ℓX ℓ≤) (ℓ-max ℓX ℓ≈) (ℓ-max ℓX ℓM)
  ΠV = mkValType P-Π M-Π i-Π




module _ where

  open Clocked k
  open IsMonoidHom

  V▹ : ValType ℓ ℓ≤ ℓ≈ ℓM → ValType ℓ ℓ≤ ℓ≈ ℓM
  V▹ A = mkValType (P▹ (ValType→Predomain A)) MA h
    where
      MA = PtbV A
      iA = interpV A

      h : MonoidHom MA (Endo (P▹ ValType→Predomain A))
      h = SemPtb▹ ∘hom iA



module _ where

  open Clocked k
  open IsMonoidHom

  V▸ : ▹ k , (ValType ℓ ℓ≤ ℓ≈ ℓM) → ValType ℓ ℓ≤ ℓ≈ ℓM
  V▸ A~ = mkValType
    (P▸ (λ t → ValType→Predomain (A~ t)))
    (Monoid▸ (λ t → PtbV (A~ t)))
    (Endo▸ ∘hom (monoidhom▸ (λ t → interpV (A~ t))))


{-

module _ where

  private
    ▹_ : Type ℓ -> Type ℓ
    ▹ A = ▹_,_ k A

  open import Common.LaterProperties
  open Clocked k

  M▸ : ▹ Monoid ℓ -> Monoid ℓ
  M▸ M~ = makeMonoid {M = ▸ (λ t -> ⟨ M~ t ⟩)}
    (λ t → M~ t .snd .MonoidStr.ε)
    (λ x~ y~ t → M~ t .snd .MonoidStr._·_ (x~ t) (y~ t))
    (isSet▸ (λ t -> is-set (M~ t .snd)))
    (λ x~ y~ z~ ->
      later-ext (λ t -> ·Assoc (M~ t .snd) (x~ t) (y~ t) (z~ t)))
    (λ x~ -> later-ext (λ t → ·IdR (M~ t .snd) (x~ t)))
    (λ x~ -> later-ext λ t → ·IdL (M~ t .snd) (x~ t))
    where
      open MonoidStr
    
  C▸ : ▹ CompType ℓ ℓ≤ ℓ≈ ℓM → CompType ℓ ℓ≤ ℓ≈ ℓM
  C▸ B~ = mkCompType ED M h
    where
      ED : ErrorDomain _ _ _
      ED = ED▸ (λ t → CompType→ErrorDomain (B~ t))

      M : Monoid _
      M = M▸ (λ t → PtbC (B~ t))
      
      h : MonoidHom M (CEndo ED)
      h .fst m~ .fst .ErrorDomMor.f .PBMor.f x~ t = interpC (B~ t) .fst (m~ t) .fst .ErrorDomMor.fun (x~ t)
      h .fst m~ .fst .ErrorDomMor.f .PBMor.isMon x≤y t = interpC (B~ t) .fst (m~ t) .fst .ErrorDomMor.isMon (x≤y t)
      h .fst m~ .fst .ErrorDomMor.f .PBMor.pres≈ x≈y t = interpC (B~ t) .fst (m~ t) .fst .ErrorDomMor.pres≈ (x≈y t)
      h .fst m~ .fst .ErrorDomMor.f℧ = later-ext (λ t → interpC (B~ t) .fst (m~ t) .fst .ErrorDomMor.f℧)
      h .fst m~ .fst .ErrorDomMor.fθ x~ = {!!}
      h .fst m~ .snd x x' x₁ t = {!!}
      h .snd = {!!}
-}

-- -- x~ t = interpC (B~ t) .fst (m~ t) .fst .ErrorDomMor.fun {!!}
