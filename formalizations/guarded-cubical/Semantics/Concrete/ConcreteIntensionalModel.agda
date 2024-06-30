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



-- Squares for value types
--------------------------

-- The squares for value types are simply predomain squares involving
-- the respective predomain morphisms and relations.

-- module _  where
--   ValTypeSq :
--     {Aᵢ  : ValType ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  ℓMAᵢ}
--     {Aᵢ' : ValType ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' ℓMAᵢ'}
--     {Aₒ  : ValType ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  ℓMAₒ}
--     {Aₒ' : ValType ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' ℓMAₒ'} →
--     (cᵢ  : ValTypeRel Aᵢ Aᵢ' ℓcᵢ) →
--     (cₒ  : ValTypeRel Aₒ Aₒ' ℓcₒ) →
--     (f   : ValTypeMor Aᵢ  Aₒ) →
--     (g   : ValTypeMor Aᵢ' Aₒ') →
--     Type (ℓ-max (ℓ-max ℓAᵢ ℓAᵢ') (ℓ-max ℓcᵢ ℓcₒ))
--   ValTypeSq cᵢ cₒ f g = PBSq (cᵢ .ValTypeRel.c) (cₒ .ValTypeRel.c) f g



-- That means we get the following:
--
-- Vertical Identity squares (id ⊑ id)
-- Horizontal identity squares (f ⊑ f)
-- Veritcal composition of squares
-- Horizontal composition of squares
-- A notion of Quasi-order-equivalence of two horizontal morphisms

{-



-- Horizontal morphisms of computation types
---------------------------------------------

-- Horizontal morphisms of computation types are error domain relations between
-- the underlying error domains that are additionally quasi-representable
-- and have a push-pull structure.

record CompTypeRel
  (B  : CompType ℓB  ℓ≤B  ℓ≈B  ℓMB)
  (B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB')
  (ℓd : Level) : Type
    (ℓ-max (ℓ-max (ℓ-max ℓB ℓ≤B) (ℓ-max ℓ≈B ℓMB))
    (ℓ-max (ℓ-max ℓB' ℓ≤B') (ℓ-max (ℓ-max ℓ≈B' ℓMB') (ℓ-suc ℓd)))) where

  no-eta-equality

  module B  = CompTypeStr (B  .snd)
  module B' = CompTypeStr (B' .snd)

  𝔹  = CompType→ErrorDom B
  𝔹' = CompType→ErrorDom B'

  MB  = B.PtbC
  MB' = B'.PtbC
  iB  = B.interpC
  iB' = B'.interpC

  -- module Ptb-UB = U-Ptb MB iB
  -- module Ptb-UB' = U-Ptb MB' iB'

  field
    d  : ErrorDomRel 𝔹 𝔹' ℓd
    Πd : PushPullC 𝔹 MB iB 𝔹' MB' iB' d

  open U-PushPull d Πd

  field
    ρᴿ : RightRepC 𝔹 MB iB 𝔹' MB' iB' d Πd
    ρᴸ : LeftRepV (U-ob 𝔹)  M-UB  iUB
                  (U-ob 𝔹') M-UB' iUB'
                  (U-rel d) U-PushPull
    -- ρᴸ : LeftRepV (U-ob 𝔹) Ptb-UB.M-UB Ptb-UB.iUB (U-ob 𝔹') Ptb-UB'.M-UB Ptb-UB'.iUB (U-rel d) U-PushPull


-- Identity horizontal morphism

-- Composition of horizontal morphisms

-- Computation squares
-}

---------------------------------------------------------------
-- Functors
---------------------------------------------------------------

-----------
-- Arrow
-----------


--------
-- F
--------



--------
-- U
--------



--------
-- Times
--------



-- Lax functoriality of F, U, arrow, and times



-- Kleisli Functors




---------------------------------------------------------------
-- The dynamic type + horizontal morphisms
---------------------------------------------------------------














-- record ValType (ℓ ℓ' ℓ'' ℓ''' : Level) :
--   Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max (ℓ-suc ℓ'') (ℓ-suc ℓ'''))) where

--   field
--     X       : PosetBisim ℓ ℓ' ℓ''
--     Perturb : Monoid  ℓ'''
--     perturb : MonoidHom Perturb (Endo X)

--   open PosetBisimStr (X .snd) public

-- open ValType


{-
-- Later for value types

module _ {k : Clock} where

  private
    ▹_ : Type ℓ -> Type ℓ
    ▹ A = ▹_,_ k A

  open ValTypeStr

-}

{-
  -- Theta for monoids
  module _ (M~ : ▹ Monoid ℓM) where

    module _ (@tick t : Tick k) where
      module M = MonoidStr (M~ t .snd)
      M = M~ t

      ε : ⟨ M ⟩
      ε = M.ε

      compose : ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
      compose m1 m2 = M._·_ m1 m2

      isSetM = M.is-set
      ·AssocM = M.·Assoc
      ·IdRM = M.·IdR
      ·IdLM = M.·IdL

    Monoid▸ :  Monoid ℓM
    Monoid▸ = makeMonoid
      {M = ▸ (λ t → ⟨ M~ t ⟩)}
      ε
      (λ m1~ m2~ t → compose t (m1~ t) (m2~ t))
      (isSet▸ (λ t → isSetM t))
      (λ m1~ m2~ m3~ → later-ext λ t → ·AssocM t (m1~ t) (m2~ t) (m3~ t))
      (λ m → later-ext (λ t → ·IdRM t (m t)))
      (λ m → later-ext (λ t → ·IdLM t (m t)))

  open IsMonoidHom

  -- Turning a "later" homomorphism of monoids h : (▸_t (M~ t) → (N~ t))
  -- into a homomorphism ▸h : (Monoid▸ M~) (Monoid▸ N~)
  hom▸ : {M~ : ▹ Monoid ℓ} {N~ : ▹ Monoid ℓ'}
    (f~ : ▸ (λ t -> MonoidHom (M~ t) (N~ t))) ->
    MonoidHom (Monoid▸ M~) (Monoid▸ N~)
  hom▸ {M~ = M~} {N~ = N~} f~ .fst = λ m~ -> λ t -> (f~ t .fst) (m~ t)
  hom▸ {M~ = M~} {N~ = N~} f~ .snd .presε =
    later-ext (λ t -> f~ t .snd .presε)
  hom▸ {M~ = M~} {N~ = N~} f~ .snd .pres· x~ y~ =
    later-ext (λ t -> f~ t .snd .pres· (x~ t) (y~ t))

  open Clocked k

  -- We can turn a "later" pre-perturbation f : ▸_t (PrePtb (X~ t))
  -- into a pre-perturbation ▸f : PrePtb (PB▸ X~).
  -- Moreover, the transformation is a homomorphism of monoids.
  ▸Endo : {X~ : ▹ PosetBisim ℓ ℓ≤ ℓ≈} ->
    MonoidHom (Monoid▸ (λ t -> (Endo (X~ t)))) (Endo (PB▸ X~))

  -- First we contruct the underlying morphism using PBMor▸
  ▸Endo {X~ = X~} .fst f~ .fst = PBMor▸ (λ t → f~ t .fst)

  -- Now we show that the resulting morphism is bisimilar to the identity
  -- on (PB▸ X~).
  ▸Endo {X~ = X~} .fst f~ .snd =
    λ x1~ x2~ x1~≈x2~ → (λ t → (f~ t .snd) (x1~ t) (x2~ t) (x1~≈x2~ t))

  -- So far we've constructed an element in Endo (PB▸ X~), i.e., a morphism
  -- bisimilar to the identity.
  -- Now we need to show this process preserves identity and multiplication.
  ▸Endo {X~ = X~} .snd .presε = refl
  ▸Endo {X~ = X~} .snd .pres· f~ g~ = refl


  -- Theta for value types
  P▸ : ▹ ValType ℓ ℓ≤ ℓ≈ ℓM → ValType ℓ ℓ≤ ℓ≈ ℓM
  P▸ X~ .fst = ▸ (λ t → ⟨ X~ t ⟩)
  P▸ X~ .snd .is-poset-with-bisim = {!!}
  P▸ X~ .snd .PtbV = Monoid▸ (λ t → X~ t .snd .PtbV)
  P▸ X~ .snd .interpV = {!!}

  -- Later for value types
  P▹ : ValType ℓ ℓ≤ ℓ≈ ℓM → ValType ℓ ℓ≤ ℓ≈ ℓM
  P▹ A = P▸ (next A)

-}
-- (▸ (λ t → ⟨ X t ⟩)) ,
--             (valtypestr
--               is-set-later ord
--               (isorderingrelation ord-prop-valued ord-refl ord-trans ord-antisym)
--               bisim
--               (isper bisim-refl bisim-sym bisim-prop-valued))







-- Push-pull structures

{-
record PushPullV
  (A : ValType ℓA ℓ≤A ℓ≈A ℓMA) (A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA')
  (c : PBRel (ValType→PosetBisim A) (ValType→PosetBisim A') ℓc) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓMA ℓMA')) ℓc) where

  module A  = ValTypeStr (A  .snd)
  module A' = ValTypeStr (A' .snd)

  𝔸  = ValType→PosetBisim A
  𝔸' = ValType→PosetBisim A'

  field
    push : (pᴸ : ⟨ A.PtbV ⟩) →
      Σ[ pᴿ ∈ ⟨ A'.PtbV ⟩ ] PBSq c c (A.ι pᴸ) (A'.ι pᴿ)
    pull : (pᴿ : ⟨ A'.PtbV ⟩) →
      Σ[ pᴸ ∈ ⟨ A.PtbV ⟩ ] PBSq c c (A.ι pᴸ) (A'.ι pᴿ)

-}
