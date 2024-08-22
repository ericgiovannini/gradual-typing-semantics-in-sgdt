{-

  Defines our final notion of value and computation type, which are
  predomains/domains respectively that are additionally equipped with
  a monoid of *syntactic perturbations* with an interpretation as
  semantic perturbations.

  Additionally defines homomorphisms thereof as homomorphisms of the
  underlying (pre)domain.

-}

{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Common.Later

module Semantics.Concrete.Types.Base (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Monoid.Base

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.Predomains.PrePerturbations k

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
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

open PBMor


---------------------------------------------------------------
-- Value Types
---------------------------------------------------------------

-- A value type is a predomain A along with a monoid of perturbations on A.

record ValTypeStr {ℓ : Level} (ℓ≤ ℓ≈ ℓM : Level) (A : Type ℓ) :
  Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) (ℓ-max ℓ≈ ℓM))) where

  no-eta-equality

  constructor valtypestr

  field
    is-poset-with-bisim : PosetBisimStr ℓ≤ ℓ≈ A

  open PosetBisimStr is-poset-with-bisim public
  predomain : PosetBisim ℓ ℓ≤ ℓ≈
  predomain = A , is-poset-with-bisim

  field
    PtbV : Monoid ℓM
    interpV : MonoidHom PtbV (Endo predomain)


  ι : ⟨ PtbV ⟩ → PBMor predomain predomain
  ι p = interpV .fst p .fst

ValType : ∀ ℓ ℓ≤ ℓ≈ ℓM → Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) (ℓ-max ℓ≈ ℓM)))
ValType ℓ ℓ≤ ℓ≈ ℓM = TypeWithStr ℓ (ValTypeStr ℓ≤ ℓ≈ ℓM)

ValType→Predomain : {ℓ ℓ≤ ℓ≈ ℓM : Level} → ValType ℓ ℓ≤ ℓ≈ ℓM → PosetBisim ℓ ℓ≤ ℓ≈
ValType→Predomain A = ⟨ A ⟩ , (A .snd .is-poset-with-bisim)
  where open ValTypeStr

PtbV : ValType ℓ ℓ≤ ℓ≈ ℓM → Monoid ℓM
PtbV A = A .snd .ValTypeStr.PtbV

interpV : (A : ValType ℓ ℓ≤ ℓ≈ ℓM) →
  MonoidHom (PtbV A) (Endo (ValType→Predomain A))
interpV A = A .snd .ValTypeStr.interpV

mkValType :
  (A : PosetBisim ℓ ℓ≤ ℓ≈)
  → (PtbV : Monoid ℓM)
  → MonoidHom PtbV (Endo A)
  → ValType ℓ ℓ≤ ℓ≈ ℓM
mkValType A P ι = ⟨ A ⟩ , (valtypestr (A .snd) P ι)

-- Vertical morphisms of value types
-------------------------------------

-- A vertical morphism of value types is simply a morphism of the
-- underlying predomain structures.

ValTypeMor :
  (Aᵢ : ValType ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ ℓMAᵢ)
  (Aₒ : ValType ℓAₒ ℓ≤Aₒ ℓ≈Aₒ ℓMAₒ) →
  Type ((ℓ-max (ℓ-max ℓAᵢ (ℓ-max ℓ≤Aᵢ ℓ≈Aᵢ)) (ℓ-max ℓAₒ (ℓ-max ℓ≤Aₒ ℓ≈Aₒ))))
ValTypeMor Aᵢ Aₒ = PBMor (ValType→Predomain Aᵢ) (ValType→Predomain Aₒ)

---------------------------------------------------------------
-- Computation Types
---------------------------------------------------------------

-- Computation types are defined to be error domains with additional
-- structure, namely a monoid of perturbations. This is analogous to
-- how value types are defined to be predomains (posets with
-- bisimilarity) along with a monoid of perturbations.

-- Another choice would have been to define a computation type as a
-- value type B along with the additional structure corresponding to
-- error domains, i.e., a bottom element ℧B : B and a morphism
-- θB : (▹ B) → B.  This definition may seem distinct from the first
-- one: the θB is a morphism of *value types*, i.e., (▹ B)
-- is a value type and so has a monoid of perturbations. Meanwhile in
-- the first definition, (▹ B) is merely a predomain and so does not
-- have a monoid of perturbations.
--
-- However, since the vertical morphisms of value types are simply
-- vertical morphisms of the underlying predomain, there is actually
-- no difference.

CompTypeStr : ∀ {ℓ} ℓ≤ ℓ≈ ℓM → (B : Type ℓ) → Type _
CompTypeStr ℓ≤ ℓ≈ ℓM B =
  Σ[ B-err-dom ∈ ErrorDomainStr ℓ≤ ℓ≈ B ]
  Σ[ PtbC ∈ Monoid ℓM ]
  MonoidHom PtbC (CEndo (B , B-err-dom))

CompType : ∀ ℓ ℓ≤ ℓ≈ ℓM → Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) (ℓ-max ℓ≈ ℓM)))
CompType ℓ ℓ≤ ℓ≈ ℓM = TypeWithStr ℓ (CompTypeStr ℓ≤ ℓ≈ ℓM)

mkCompType
  : (B : ErrorDomain ℓ ℓ≤ ℓ≈)
  → (PtbC : Monoid ℓM)
  → MonoidHom PtbC (CEndo B)
  → CompType ℓ ℓ≤ ℓ≈ ℓM
mkCompType B PtbC ι = ⟨ B ⟩ , ((B .snd) , (PtbC , ι))

CompType→ErrorDomain : {ℓ ℓ≤ ℓ≈ ℓM : Level} →
  CompType ℓ ℓ≤ ℓ≈ ℓM → ErrorDomain ℓ ℓ≤ ℓ≈
CompType→ErrorDomain B = ⟨ B ⟩ , B .snd .fst

PtbC : CompType ℓ ℓ≤ ℓ≈ ℓM → Monoid ℓM
PtbC B = B .snd .snd .fst

interpC : (B : CompType ℓ ℓ≤ ℓ≈ ℓM) →
  MonoidHom (PtbC B) (CEndo (CompType→ErrorDomain B))
interpC B = B .snd .snd .snd


-- Vertical morphisms of computation types
-------------------------------------------

-- A vertical morphism of computation types is simply a morphism of the
-- underlying error domain structures.

CompTypeMor :
  (Bᵢ : CompType ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ ℓMBᵢ)
  (Bₒ : CompType ℓBₒ ℓ≤Bₒ ℓ≈Bₒ ℓMBₒ) →
  Type ((ℓ-max (ℓ-max ℓBᵢ (ℓ-max ℓ≤Bᵢ ℓ≈Bᵢ)) (ℓ-max ℓBₒ (ℓ-max ℓ≤Bₒ ℓ≈Bₒ))))
CompTypeMor Bᵢ Bₒ =
  ErrorDomMor (CompType→ErrorDomain Bᵢ) (CompType→ErrorDomain Bₒ)


ObliqueMor :
  (A : ValType ℓA ℓ≤A ℓ≈A ℓMA)
  (B : CompType ℓB ℓ≤B ℓ≈B ℓMB)
  → Type _
ObliqueMor A B = PBMor (ValType→Predomain A) (U-ob (CompType→ErrorDomain B))
