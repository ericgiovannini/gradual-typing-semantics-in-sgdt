{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.Dyn (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Relation.Binary.Base

open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

 -- open import Cubical.Algebra.Monoid.FreeProduct


open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Constructions renaming (ℕ to NatP)
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare

open import Semantics.Concrete.DoublePoset.FreeErrorDomain k



private
  variable
    ℓ ℓ' : Level
    ℓA ℓ≤A ℓ≈A : Level
    ℓ≤ ℓ≈ : Level

  ▹_ : {ℓ : Level} → Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

open BinaryRelation
open LiftPredomain
open Clocked k

module DynDef {ℓ : Level} where

 -- The underlying inductive type on which Dyn will be based.
 -- 
 -- If we say X : PosetBisim ℓ here, then Agda gets stuck when
 -- type-checking the line `unfold-Dyn = fix-eq Guarded.Dyn'`
 -- (this happened with lossy-unification turned off; not tried
 --  when it is turned on)
  data DynTy (X : Type ℓ) : Type ℓ where

    nat : ℕ → DynTy X
    prod : DynTy X → DynTy X → DynTy X
    fun : X → DynTy X
    -- TODO should we add is-set?

  nat-injective : ∀ {X : Type ℓ} n m →
    (nat {X = X} n ≡ nat m) → n ≡ m
  nat-injective {X = X} n m eq = cong aux eq
    where
      aux : DynTy X → ℕ
      aux (nat n) = n
      aux (prod d₁ d₂) = 0
      aux (fun x) = 0
  
  prod-injective : ∀ {X : Type ℓ} d₁ d₂ d₁' d₂' →
    (prod {X = X} d₁ d₂) ≡ (prod d₁' d₂') → ((d₁ ≡ d₁') × (d₂ ≡ d₂'))
  prod-injective {X = X} d₁ d₂ d₁' d₂' eq = (cong fst (cong aux eq)) , (cong snd (cong aux eq))
    where
      aux : DynTy X → (DynTy X × DynTy X)
      aux (nat n) = (d₁ , d₂)
      aux (prod d₁'' d₂'') = (d₁'' , d₂'')
      aux (fun x) = (d₁ , d₂)
  
  fun-injective : {X : Type ℓ} →
    ∀ (x y : X) → fun x ≡ fun y → x ≡ y
  fun-injective {X = X} x y eq = cong aux eq
    where
      aux : DynTy X → X
      aux (nat n) = x
      aux (prod d₁ d₂) = x
      aux (fun x') = x'
      

  DynTyIso : ∀ X → Iso (DynTy X) ((ℕ ⊎ (DynTy X × DynTy X)) ⊎ X)
  DynTyIso X = iso
    (λ { (nat n) → inl (inl n) ;
         (prod d₁ d₂) → inl (inr (d₁ , d₂)) ;
         (fun x) → inr x })
    (λ { (inl (inl n)) → nat n ;
         (inl (inr (d₁ , d₂))) → prod d₁ d₂ ;
         (inr x) → fun x})
    (λ { (inl (inl n)) → refl ; (inl (inr pair)) → refl ; (inr x) → refl})
    (λ { (nat n) → refl ; (prod d₁ d₂) → refl ; (fun x) → refl})


  -- Defining Dyn as a predomain under the assumption of a
  -- later-predomain D~.
  module Guarded (D~ : ▹ (PosetBisim ℓ ℓ ℓ)) where

    Fun = ⟨ PB▸ (λ t → (D~ t) ==> 𝕃 (D~ t)) ⟩
    module Fun = PosetBisimStr (PB▸ (λ t → (D~ t) ==> 𝕃 (D~ t)) .snd)

    open IsOrderingRelation

    --------------------------------
    -- The ordering relation on dyn
    --------------------------------
    data _⊑d_ : DynTy Fun → DynTy Fun → Type ℓ where
      ⊑-nat : ∀ {n m} → n ≡ m → (nat n) ⊑d (nat m)
      ⊑-prod : ∀ {d₁ d₂ d₁' d₂'} → (d₁ ⊑d d₁') → (d₂ ⊑d d₂') →
        (prod d₁ d₂) ⊑d (prod d₁' d₂')
      ⊑-fun : ∀ {f~ g~} → f~ Fun.≤ g~ → (fun f~) ⊑d (fun g~)

    ⊑d-prop : isPropValued _⊑d_
    ⊑d-prop .(nat n) .(nat m) (⊑-nat {n} {m} p) (⊑-nat .{n} .{m} q) =
      λ i → ⊑-nat (isSetℕ n m p q i)
    ⊑d-prop .(prod d₁ d₂) .(prod d₁' d₂')
      (⊑-prod {d₁} {d₂} {d₁'} {d₂'} p q) (⊑-prod .{d₁} .{d₂} .{d₁'} .{d₂'} p' q') =
      λ i → ⊑-prod (⊑d-prop d₁ d₁' p p' i) (⊑d-prop d₂ d₂' q q' i)
    ⊑d-prop .(fun f~) .(fun g~) (⊑-fun {f~} {g~} p) (⊑-fun .{f~} .{g~} q) =
      λ i → ⊑-fun (Fun.is-prop-valued f~ g~ p q i)

    ⊑d-refl : isRefl _⊑d_
    ⊑d-refl (nat n) = ⊑-nat refl
    ⊑d-refl (prod d₁ d₂) = ⊑-prod (⊑d-refl d₁) (⊑d-refl d₂)
    ⊑d-refl (fun f~) = ⊑-fun (Fun.is-refl f~)

    ⊑d-trans : isTrans _⊑d_
    ⊑d-trans .(nat _) .(nat _) .(nat _) (⊑-nat eq1) (⊑-nat eq2) =
      ⊑-nat (eq1 ∙ eq2)
    ⊑d-trans .(prod _ _) .(prod _ _) .(prod _ _)
     (⊑-prod {d₁} {d₂} {d₁'} {d₂'} p q) (⊑-prod .{d₁'} .{d₂'} {d₁''} {d₂''} p' q') =
     ⊑-prod (⊑d-trans d₁ d₁' d₁'' p p') (⊑d-trans d₂ d₂' d₂'' q q')
    ⊑d-trans .(fun _) .(fun _) .(fun _) (⊑-fun {f~} {g~} p) (⊑-fun .{g~} {h~} q) =
      ⊑-fun (Fun.is-trans f~ g~ h~ p q)

    ⊑d-antisym : isAntisym _⊑d_
    ⊑d-antisym .(nat _) .(nat _) (⊑-nat eq1) (⊑-nat eq2) =
      cong nat eq1
    ⊑d-antisym .(prod _ _) .(prod _ _) (⊑-prod p q) (⊑-prod p' q') =
      cong₂ prod (⊑d-antisym _ _ p p') (⊑d-antisym _ _ q q')
    ⊑d-antisym .(fun _) .(fun _) (⊑-fun p) (⊑-fun q) =
      cong fun (Fun.is-antisym _ _ p q)


    ------------------------------------
    -- The bisimilarity relation on dyn
    ------------------------------------
    data _≈d_ : DynTy Fun → DynTy Fun → Type ℓ where
      ≈-nat : ∀ {n m} → n ≡ m → (nat n) ≈d (nat m)
      ≈-prod : ∀ {d₁ d₂ d₁' d₂'} → (d₁ ≈d d₁') → (d₂ ≈d d₂') →
        (prod d₁ d₂) ≈d (prod d₁' d₂')
      ≈-fun : ∀ {f~ g~} → f~ Fun.≈ g~ → (fun f~) ≈d (fun g~)

    ≈d-prop : isPropValued _≈d_
    ≈d-prop .(nat n) .(nat m) (≈-nat {n} {m} p) (≈-nat .{n} .{m} q) =
      λ i → ≈-nat (isSetℕ n m p q i)
    ≈d-prop .(prod d₁ d₂) .(prod d₁' d₂')
      (≈-prod {d₁} {d₂} {d₁'} {d₂'} p q) (≈-prod .{d₁} .{d₂} .{d₁'} .{d₂'} p' q') =
      λ i → ≈-prod (≈d-prop d₁ d₁' p p' i) (≈d-prop d₂ d₂' q q' i)
    ≈d-prop .(fun f~) .(fun g~) (≈-fun {f~} {g~} p) (≈-fun .{f~} .{g~} q) =
      λ i → ≈-fun (Fun.is-prop-valued-Bisim f~ g~ p q i)

    ≈d-refl : isRefl _≈d_
    ≈d-refl (nat n) = ≈-nat refl
    ≈d-refl (prod d₁ d₂) = ≈-prod (≈d-refl d₁) (≈d-refl d₂)
    ≈d-refl (fun f~) = ≈-fun (Fun.is-refl-Bisim f~)

    ≈d-sym : isSym _≈d_
    ≈d-sym .(nat n) .(nat m) (≈-nat {n} {m} p) = ≈-nat (sym p)
    ≈d-sym .(prod d₁ d₂) .(prod d₁' d₂')
      (≈-prod {d₁} {d₂} {d₁'} {d₂'} p q) = ≈-prod (≈d-sym _ _ p) (≈d-sym _ _ q)
    ≈d-sym .(fun f~) .(fun g~) (≈-fun {f~} {g~} p) = ≈-fun (Fun.is-sym f~ g~ p)
  

    --------------------------
    -- Defining the predomain
    --------------------------

    -- We take the type of Dyn' to be the type DynTy defined above,
    -- instantiated with the type of later predomain morphisms from
    -- (D~ t) to 𝕃 (D~ t).
    Dyn' : PosetBisim ℓ ℓ ℓ
    -- PosetBisim (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈) (ℓ-max ℓ ℓ≤) (ℓ-max ℓ ℓ≈)
    Dyn' .fst = DynTy ⟨ PB▸ (λ t → (D~ t) ==> 𝕃 (D~ t)) ⟩
    Dyn' .snd = posetbisimstr {!!} _⊑d_ {!!} _≈d_ {!!}
    -- posetbisimstr set ord isOrd bisim isBisim
      where

        set : isSet (DynTy Fun)
        set = {!!}
        -- set (nat n) (nat m) p q = {!!}
        -- set (nat n) (prod d₂ d₃) p q = {!!}
        -- set (nat n) (fun g~) p q = {!!}
        -- set (prod d₁ d₂) (nat x) p q = {!!}
        -- set (prod d₁ d₂) (prod d₁' d₂') p q = {!!}
        -- set (prod d₁ d₂) (fun x) p q = {!!}
        -- set (fun x) d₂ p q = {!!}

        -- Ordering relation and properties
{-
        ord : DynTy Fun → DynTy Fun → Type ℓ
        ord (nat n) (nat m) = Lift (n ≡ m)
        ord (prod d₁ d₂) (prod d₁' d₂') = (ord d₁ d₁') × (ord d₂ d₂')
        ord (fun f~) (fun g~) = f~ Fun.≤ g~
        ord _ _ = ⊥*

        ord-refl : isRefl ord
        ord-refl (nat n) = lift refl
        ord-refl (prod d₁ d₂) = (ord-refl d₁) , (ord-refl d₂)
        ord-refl (fun f~) = Fun.is-refl f~

        ord-prop-valued : isPropValued ord
        ord-prop-valued (nat n) (nat m) p q =
          let is-prop = isOfHLevelLift 1 (isSetℕ n m) in is-prop p q
          -- also works:
          -- λ i → lift (isSetℕ n m (lower p) (lower q) i)
        ord-prop-valued (prod d₁ d₂) (prod d₁' d₂') =
          isProp× (ord-prop-valued d₁ d₁') (ord-prop-valued d₂ d₂')
        ord-prop-valued (fun f~) (fun g~) = Fun.is-prop-valued f~ g~

        ord-trans : isTrans ord
        ord-trans (nat n) (nat m) (nat p) (lift eq1) (lift eq2) = lift (eq1 ∙ eq2)
        ord-trans (prod d₁ d₂) (prod d₁' d₂') (prod d₁'' d₂'')
                  (d₁≤d₁' , d₂≤d₂') (d₁'≤d₁'' , d₂'≤d₂'') =
                  ord-trans d₁ d₁' d₁'' d₁≤d₁' d₁'≤d₁'' ,
                  ord-trans d₂ d₂' d₂'' d₂≤d₂' d₂'≤d₂''
        ord-trans (fun f~) (fun g~) (fun h~) = Fun.is-trans f~ g~ h~

        ord-antisym : isAntisym ord
        ord-antisym (nat n) (nat m) p q = cong nat (lower p)
        ord-antisym (prod d₁ d₂) (prod d₁' d₂') p q = {!!}
        ord-antisym (fun f~) (fun g~) f~≤g~ g~≤f~ =
          cong fun (Fun.is-antisym f~ g~ f~≤g~ g~≤f~)

        isOrd : IsOrderingRelation ord
        isOrd .is-prop-valued = ord-prop-valued
        isOrd .is-refl = ord-refl
        isOrd .is-trans = ord-trans
        isOrd .is-antisym = ord-antisym


        -- Bisimilarity relation and properties

        bisim : DynTy Fun → DynTy Fun → Type ℓ
        bisim (nat n) (nat m) = Lift (n ≡ m)
        bisim (prod d₁ d₂) (prod d₁' d₂') = (bisim d₁ d₁') × (bisim d₂ d₂')
        bisim (fun f~) (fun g~) = f~ Fun.≈ g~
        bisim _ _ = ⊥*

        bisim-refl : isRefl bisim
        bisim-refl (nat n) = lift refl
        bisim-refl (prod d₁ d₂) = (bisim-refl d₁) , (bisim-refl d₂)
        bisim-refl (fun f~) = Fun.is-refl-Bisim f~

        bisim-sym : isSym bisim
        bisim-sym = {!!}

        bisim-prop : isPropValued bisim
        bisim-prop = {!!}

        isBisim : IsBisim bisim
        isBisim .IsBisim.is-refl = bisim-refl
        isBisim .IsBisim.is-sym = bisim-sym
        isBisim .IsBisim.is-prop-valued = bisim-prop

-}


  -- We define the predomain Dyn using guarded fixpoint:
  Dyn : PosetBisim ℓ ℓ ℓ
  Dyn = fix Guarded.Dyn'

  unfold-Dyn : Dyn ≡ Guarded.Dyn' (next Dyn)
  unfold-Dyn = fix-eq Guarded.Dyn'

  Dyn→Dyn' : PBMor Dyn (Guarded.Dyn' (next Dyn))
  Dyn→Dyn' = mTransport unfold-Dyn

  Dyn'→Dyn : PBMor (Guarded.Dyn' (next Dyn)) Dyn
  Dyn'→Dyn = mTransport (sym unfold-Dyn)

  unfold-fold :  Dyn'→Dyn ∘p Dyn→Dyn' ≡ Id
  unfold-fold = eqPBMor _ _ (funExt (λ d → transport⁻Transport (λ i → ⟨ unfold-Dyn i ⟩) d ))
  -- transport⁻Transport unfold-Dyn d

  fold-unfold :  Dyn→Dyn' ∘p Dyn'→Dyn ≡ Id
  fold-unfold = eqPBMor _ _ (funExt λ d → transportTransport⁻ (λ i → ⟨ unfold-Dyn i ⟩) d)
  -- transportTransport⁻ unfold-Dyn d'


  -- We can show an equality involving the underlying type of dyn:
  Dyn-Ty : ⟨ Dyn ⟩ ≡ DynTy (▹ (PBMor Dyn (𝕃 Dyn)))
  Dyn-Ty = cong ⟨_⟩ unfold-Dyn

  -- But we can't easily show that Dyn is isomorphic *as a predomain*
  -- to (ℕ + (Dyn × Dyn) + ▹ (Dyn -> 𝕃 Dyn)).
  

  ----------------------
  -- Embeddings for dyn
  ----------------------
  module Embeddings where

    open PBMor

    open Guarded (next Dyn)

    -- emb-nat' : ℕ → ⟨ Dyn' ⟩
    -- emb-nat' n = nat n

    -- emb-prod' : ⟨ Dyn' ⟩ → ⟨ Dyn' ⟩ → ⟨ Dyn' ⟩
    -- emb-prod' d₁ d₂ = prod d₁ d₂

    -- emb-fun' : (▹ (PBMor Dyn (𝕃 Dyn))) → ⟨ Dyn' ⟩
    -- emb-fun' = fun

    emb-nat' : PBMor NatP Dyn'
    emb-nat' .f = nat
    emb-nat' .isMon n≡m = ⊑-nat n≡m
    emb-nat' .pres≈ n≡m = ≈-nat n≡m

    emb-times' : PBMor (Dyn' ×dp Dyn') Dyn'
    emb-times' .f (d₁ , d₂) = prod d₁ d₂
    emb-times' .isMon (p , q) = ⊑-prod p q
    emb-times' .pres≈ (p , q) = ≈-prod p q

    -- Note that this is not the same as the fun constructor,
    -- since that takes a **later** function.
    emb-arr' : PBMor (Dyn ==> 𝕃 Dyn) Dyn'
    emb-arr' .f g = fun (next g)
    emb-arr' .isMon g₁≤g₂ = ⊑-fun (λ t → g₁≤g₂)
    emb-arr' .pres≈ g₁≈g₂ = ≈-fun (λ t → g₁≈g₂)


  -----------------------------------
  -- Eliminator and recursor for Dyn
  -----------------------------------
  module ElimDyn where

   open Embeddings
   open Guarded (next (Dyn))
   open PBMor

   -- Because we don't have a notion of "dependent predomain", we can't
   -- talk about "dependent predomain morphisms", and thus we can only
   -- formulate an eliminator at the level of types.
   elimDyn : ∀ (A : ⟨ Dyn' ⟩ → Type ℓ) →
      (caseNat  : ∀ (n : ℕ)                           → A (nat n))       →
      (caseProd : ∀ (d₁ d₂ : ⟨ Dyn' ⟩) → A d₁ → A d₂  → A (prod d₁ d₂))  →
      (caseFun  : ∀ (f~ : (▹ (PBMor Dyn (𝕃 Dyn))))    → A (fun f~))      →
      (∀ (d : ⟨ Dyn' ⟩) → A d)
   elimDyn A caseNat caseProd caseFun = aux
     where
       aux : (d : ⟨ Dyn' ⟩) → A d
       aux (nat n) = caseNat n
       aux (prod d₁ d₂) = caseProd d₁ d₂ (aux d₁) (aux d₂)
       aux (fun f~) = caseFun f~


  module RecDyn where
    open Guarded (next (Dyn))
    open PBMor

    recDyn : ∀ {A : PosetBisim ℓA ℓ≤A ℓ≈A} →
       (caseNat  : PBMor NatP A) →
       (caseProd : PBMor (Dyn' ×dp Dyn') A) →
       (caseFun  : PBMor (PB▹ (Dyn ==> 𝕃 Dyn)) A) →
       PBMor Dyn' A
    recDyn {A = A} caseNat caseProd caseFun = aux
      where
        module caseNat  = PBMor caseNat
        module caseProd = PBMor caseProd
        module caseFun  = PBMor caseFun

        aux : PBMor Dyn' A
        aux .f (nat n) = caseNat $ n
        aux .f (prod d₁ d₂) = caseProd $ (d₁ , d₂)
        aux .f (fun f~) = caseFun $ f~

        aux .isMon (Guarded.⊑-nat eq)   = caseNat.isMon eq
        aux .isMon (Guarded.⊑-prod p q) = caseProd.isMon (p , q)
        aux .isMon (Guarded.⊑-fun p)    = caseFun.isMon p

        aux .pres≈ (Guarded.≈-nat eq)   = caseNat.pres≈ eq
        aux .pres≈ (Guarded.≈-prod p q) = caseProd.pres≈ (p , q)
        aux .pres≈ (Guarded.≈-fun p)    = caseFun.pres≈ p


----------------
-- Projections
---------------

  module Projections where

    open Guarded (next Dyn)
    open RecDyn
    open ClockedCombinators k

    proj-nat : PBMor Dyn' (𝕃 NatP)
    proj-nat = recDyn (η-mor) (K _ ℧) (K _ ℧)

    proj-times : PBMor Dyn' (𝕃 (Dyn' ×dp Dyn'))
    proj-times = recDyn (K _ ℧) (η-mor) (K _ ℧)

    proj-arr : PBMor Dyn' (𝕃 (Dyn ==> 𝕃 Dyn))
    proj-arr = recDyn (K _ ℧) (K _ ℧) ((θ-mor) ∘p (Map▹ (η-mor)))
    --
    -- To project in the case of a later-function g~, we return
    -- θ (λ t → η (g~ t)), which can also be written as θ (Map▹ η g~).
    --
    -- Rather than proving manually that this defines a morphism of
    -- predomains, we observe that we can express this as a
    -- composition of the predomain morphism θ composed with (Map▹ η)

-------------------------------------------------------
-- Heterogeneous relations inj-nat, inj-times, inj-arr
-------------------------------------------------------

  module Relations where

    open Guarded (next Dyn)
    open Embeddings
    open PBRel

    inj-nat : PBRel NatP Dyn' ℓ
    inj-nat = functionalRel emb-nat' Id (idPRel Dyn')

    inj-times : PBRel (Dyn' ×dp Dyn') Dyn' ℓ
    inj-times = functionalRel emb-times' Id (idPRel Dyn')

    inj-arr : PBRel (Dyn ==> 𝕃 Dyn) Dyn' ℓ
    inj-arr = functionalRel emb-arr' Id (idPRel Dyn')
