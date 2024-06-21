{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomains.Predomains (k : Clock) where

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

open import Cubical.Data.Sigma


-- open import Cubical.Relation.Binary.Order.Poset
-- open import Common.Poset.Convenience
-- open import Common.Poset.Constructions
-- open import Common.Poset.Monotone
-- open import Semantics.MonotoneCombinators

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.DblPosetCombinators

open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k

open import Semantics.Concrete.Predomains.Perturbations k

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓc ℓd : Level

  variable
    ℓX ℓY ℓR : Level

open PBMor


---------------------------------------------------------------
-- Value Types
---------------------------------------------------------------


-- record ValType (ℓ ℓ' ℓ'' ℓ''' : Level) :
--   Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max (ℓ-suc ℓ'') (ℓ-suc ℓ'''))) where

--   field
--     X       : PosetBisim ℓ ℓ' ℓ''
--     Perturb : Monoid  ℓ'''
--     perturb : MonoidHom Perturb (Endo X)

--   open PosetBisimStr (X .snd) public

-- open ValType


record ValTypeStr {ℓ : Level} (ℓ≤ ℓ≈ ℓM : Level) (A : Type ℓ) :
  Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) (ℓ-max ℓ≈ ℓM))) where

  constructor valtypestr

  field
    is-poset-with-bisim : PosetBisimStr ℓ≤ ℓ≈ A
    PtbV : Monoid ℓM
    interpV : MonoidHom PtbV (Endo (A , is-poset-with-bisim))

  open PosetBisimStr is-poset-with-bisim public
  posetWithBisim : PosetBisim ℓ ℓ≤ ℓ≈
  posetWithBisim = A , is-poset-with-bisim

  ι : ⟨ PtbV ⟩ → PBMor posetWithBisim posetWithBisim
  ι p = interpV .fst p .fst

  

ValType : ∀ ℓ ℓ≤ ℓ≈ ℓM → Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) (ℓ-max ℓ≈ ℓM)))
ValType ℓ ℓ≤ ℓ≈ ℓM = TypeWithStr ℓ (ValTypeStr ℓ≤ ℓ≈ ℓM)

ValType→PosetBisim : {ℓ ℓ≤ ℓ≈ ℓM : Level} → ValType ℓ ℓ≤ ℓ≈ ℓM → PosetBisim ℓ ℓ≤ ℓ≈
ValType→PosetBisim A = ⟨ A ⟩ , (A .snd .is-poset-with-bisim)
  where open ValTypeStr




-- Later for value types

module _ {k : Clock} where

  private
    ▹_ : Type ℓ -> Type ℓ
    ▹ A = ▹_,_ k A

  open ValTypeStr


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


-- (▸ (λ t → ⟨ X t ⟩)) ,
--             (valtypestr
--               is-set-later ord
--               (isorderingrelation ord-prop-valued ord-refl ord-trans ord-antisym)
--               bisim
--               (isper bisim-refl bisim-sym bisim-prop-valued))



-- Vertical morphisms
---------------------

-- A vertical morphism of value types is simply a morphism of the
-- underlying poset-with-bisimilarity structures.

ValTypeMor : {ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ ℓMAᵢ
                ℓAₒ ℓ≤Aₒ ℓ≈Aₒ ℓMAₒ : Level} →
  (Aᵢ : ValType ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ ℓMAᵢ)
  (Aₒ : ValType ℓAₒ ℓ≤Aₒ ℓ≈Aₒ ℓMAₒ) →
  Type ((ℓ-max (ℓ-max ℓAᵢ (ℓ-max ℓ≤Aᵢ ℓ≈Aᵢ)) (ℓ-max ℓAₒ (ℓ-max ℓ≤Aₒ ℓ≈Aₒ))))
ValTypeMor Aᵢ Aₒ = PBMor (ValType→PosetBisim Aᵢ) (ValType→PosetBisim Aₒ)




-- Horizontal morphisms
-----------------------

-- To define the horizontal morphisms of value types, we need the notion of
-- a quasi-representation.
-- This informally states that the squares necessary for graduality commute,
-- up to the insertions of specified perturbations.

-- Left quasi-representation of a relation
----------------------------------------------------
record LeftRep
  (X : Type ℓX)
  (Y : Type ℓY)
  (R : X → Y → Type ℓR) :
  Type {!!} where

  field

  -- module A  = ValTypeStr (A  .snd)
  -- module A' = ValTypeStr (A' .snd)
  
  -- 𝔸  = ValType→PosetBisim A
  -- 𝔸' = ValType→PosetBisim A'

  -- field
  --   e : PBMor 𝔸 𝔸'
  --   δl : ⟨ A.Ptb ⟩
  --   δr : ⟨ A'.Ptb ⟩

    --  UpL:                   UpR:
    --
    --        c                   ⊑A
    --   A o----* A'          A o----* A
    --   |        |           |        |
    -- e |        | δr    δl  |        | e
    --   v        v           v        v
    --   A' o---* A'          A o----* A'
    --       ⊑A'                  c

    -- UpL : PBSq c {!!} e {!!}
    --UpL : TwoCell (MonRel.R R) (rel 𝕐) (MonFun.f e) (MonFun.f (ptb-fun Y δY))
    --UpR : TwoCell (rel 𝕏) (MonRel.R R) (MonFun.f (ptb-fun X δX)) (MonFun.f e)






-- Horizontal morphisms of value types: quasi-representable, monotone
-- relations with push-pull structures
module _ (A : ValType ℓA ℓ≤A ℓ≈A ℓMA) (A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA') (ℓR : Level) where

  record ValTypeRel : Type {!!} where

    module A  = ValTypeStr (A  .snd)
    module A' = ValTypeStr (A' .snd)

    𝔸  = ValType→PosetBisim A
    𝔸' = ValType→PosetBisim A'

    field
      R : PBRel 𝔸 𝔸' ℓR
      e : PBMor 𝔸 𝔸'
      δle : ⟨ A.Ptb ⟩
      δre : ⟨ A'.Ptb ⟩
      UpL : PBSq R (idRel {ℓo = ℓR} 𝔸') e (A'.ι δre) -- (MonRel.R R) (rel 𝕐) (MonFun.f e) (MonFun.f (ptb-fun Y δY))
      UpR : PBSq (idRel {ℓo = ℓR} 𝔸) R (A.ι δle) e -- (rel 𝕏) (MonRel.R R) (MonFun.f (ptb-fun X δX)) (MonFun.f e)
      δrp : ⟨ NatM ×M A'.Ptb ⟩
      δlp : ⟨ NatM ×M A.Ptb ⟩



-- Identity horizontal morphism


-- Composition of horizontal morphisms


-- Squares for value types
--------------------------

module _ {
    ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  ℓMAᵢ
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' ℓMAᵢ'
    ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  ℓMAₒ 
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' ℓMAₒ'
    ℓcᵢ ℓcₒ : Level} where
  ValTypeSq :
    {Aᵢ  : ValType ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  ℓMAᵢ}
    {Aᵢ' : ValType ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' ℓMAᵢ'}
    {Aₒ  : ValType ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  ℓMAₒ}
    {Aₒ' : ValType ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' ℓMAₒ'} →
    (cᵢ  : ValTypeRel Aᵢ Aᵢ' ℓcᵢ) →
    (cₒ  : ValTypeRel Aₒ Aₒ' ℓcₒ) →
    (f   : ValTypeMor Aᵢ  Aₒ) →
    (g   : ValTypeMor Aᵢ' Aₒ') →
    Type (ℓ-max (ℓ-max ℓAᵢ ℓAᵢ') (ℓ-max ℓcᵢ ℓcₒ))
  ValTypeSq cᵢ cₒ f g = PBSq (cᵢ .ValTypeRel.R) (cₒ .ValTypeRel.R) f g


--ValTypeSq : ?
--ValTypeSq c₁ c₂ f g


-- Quasi-order-equivalence of two horizontal morphisms


-- Vertical Identity square (id ⊑ id)


-- Horizontal identity square (f ⊑ f)


-- Veritcal composition of squares


-- Horizontal composition of squares


-- Squares form a monoid




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
-- θB : (▹ B) → B.  But this definition is distinct from the first
-- definition: the θB is a morphism of *value types*, i.e., (▹ B)
-- is a value type and so has a monoid of perturbations. Whereas in
-- the first definition, (▹ B) is merely a predomain and so does not
-- have a monoid of perturbations.


module _ {k : Clock} where

  record CompTypeStr {ℓ : Level} (ℓ≤ ℓ≈ ℓM : Level) (B : Type ℓ) :
    Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) (ℓ-max ℓ≈ ℓM))) where

    field
      is-error-domain : ErrorDomainStr k ℓ≤ ℓ≈ B
      
    open ErrorDomainStr is-error-domain public
    ErrDom : ErrorDomain k ℓ ℓ≤ ℓ≈
    ErrDom = B , is-error-domain
  
    field
      Ptb : Monoid ℓM
      hom : MonoidHom Ptb (Endo (B , is-predomain)) -- TODO this is wrong.
      -- It needs to be the monoid of error-domain endomorphisms on B
      
      -- TODO the monoid needs to contain a distinguished element that
      -- maps to the delay morphism δB = θB ∘ next

  CompType : ∀ ℓ ℓ≤ ℓ≈ ℓM → Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) (ℓ-max ℓ≈ ℓM)))
  CompType ℓ ℓ≤ ℓ≈ ℓM = TypeWithStr ℓ (CompTypeStr ℓ≤ ℓ≈ ℓM)

  CompType→ValType : {ℓ ℓ≤ ℓ≈ ℓM : Level} → CompType ℓ ℓ≤ ℓ≈ ℓM → ValType ℓ ℓ≤ ℓ≈ ℓM
  CompType→ValType B = {!!}
    where open CompTypeStr


-- Vertical morphisms of error domains



-- Horizontal morphisms of error domains


-- Identity horizontal morphism


-- Free composition of error domain relations


-- Universal property of the free composition


-- Error domain squares


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






