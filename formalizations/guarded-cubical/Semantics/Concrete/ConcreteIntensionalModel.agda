{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.ConcreteIntensionalModel (k : Clock) where

open import Common.Common
open import Common.LaterProperties

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function hiding (_$_)

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct

open import Cubical.Data.Sigma


open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions hiding (𝔹)
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.DblPosetCombinators

open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.Dyn k

open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Predomains.Perturbations k
open import Semantics.Concrete.Predomains.QuasiRepresentation k

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

-- Horizontal morphisms of value types
---------------------------------------

-- Horizontal morphisms of value types are monotone relations between
-- the underlying predomains that are additionally quasi-representable
-- and have a push-pull structure.


open F-ob

module _ (A  : ValType ℓA  ℓ≤A  ℓ≈A  ℓMA)
  (A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA')
  (ℓc : Level) where
  
  ValTypeRel : Type _
  ValTypeRel =
    Σ[ c ∈ PBRel 𝔸 𝔸' ℓc ]
    Σ[ Πc ∈ PushPullV 𝔸 MA iA 𝔸' MA' iA' c ]
    Σ[ ρᴸ ∈ LeftRepV 𝔸  MA iA 𝔸' MA' iA' c Πc ]
    RightRepC (F-ob 𝔸) Ptb-FA.M-FA Ptb-FA.iFA
              (F-ob 𝔸') Ptb-FA'.M-FA  Ptb-FA'.iFA
              (F-rel c) let open F-PushPull c Πc in F-PushPull
    where
    module A = ValTypeStr (A .snd)
    module A' = ValTypeStr (A' .snd)
    𝔸 = ValType→Predomain A
    𝔸' = ValType→Predomain A'
    MA  = A.PtbV
    MA' = A'.PtbV
    iA  = A.interpV
    iA' = A'.interpV

    open F-ob
    open F-mor
    open F-rel

    module Ptb-FA  = F-Ptb MA  iA
    module Ptb-FA' = F-Ptb MA' iA'

module _ {A  : ValType ℓA  ℓ≤A  ℓ≈A  ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'} where

  emb : ∀ {ℓc} → ValTypeRel A A' ℓc → ValTypeMor A A'
  emb R = R .snd .snd .fst .LeftRepV.e

  ValTypeRel≈ : ∀ {ℓc ℓc'} → ValTypeRel A A' ℓc → ValTypeRel A A' ℓc' → Type _
  ValTypeRel≈ R R' =
    (emb R ≡ emb R')
    × (R .snd .snd .snd .RightRepC.p ≡ R' .snd .snd .snd .RightRepC.p)

-- Identity horizontal morphism


-- Composition of horizontal morphisms



-- Horizontal morphisms of computation types
---------------------------------------------

-- Horizontal morphisms of computation types are error domain relations between
-- the underlying error domains that are additionally quasi-representable
-- and have a push-pull structure.
module _ (B  : CompType ℓB  ℓ≤B  ℓ≈B  ℓMB)
  (B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB')
  (ℓc : Level) where

  private

    𝔹  = CompType→ErrorDomain B
    𝔹' = CompType→ErrorDomain B'

    MB  = B .snd .snd .fst
    MB' = B' .snd .snd .fst
    iB  = B .snd .snd .snd
    iB' = B' .snd .snd .snd

    module Ptb-UB = U-Ptb MB iB
    module Ptb-UB' = U-Ptb MB' iB'

  CompTypeRel : Type _
  CompTypeRel =
    Σ[ d ∈ ErrorDomRel 𝔹 𝔹' ℓc ]
    Σ[ Πd ∈ PushPullC 𝔹 MB iB 𝔹' MB' iB' d ]
    Σ[ ρᴿ ∈ RightRepC 𝔹 MB iB 𝔹' MB' iB' d Πd ]
    LeftRepV (U-ob 𝔹) Ptb-UB.M-UB Ptb-UB.iUB (U-ob 𝔹') Ptb-UB'.M-UB Ptb-UB'.iUB
      (U-rel d)
      (let open U-PushPull d Πd in U-PushPull)
