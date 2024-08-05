{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.ParameterizedDyn (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary

open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Bool
open import Cubical.Data.Sum

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More

open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Constructions renaming (ℕ to NatP)
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Types.Base


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

module _ {ℓ : Level}
  (S : Type ℓ-zero) (P : S → Type ℓ-zero)
  (dec-eq-S : ∀ (s s' : S) → Dec (s ≡ s'))
  (isSetS : isSet S)
  where
  

  -- The underlying type of Dyn
  data DynTy (X : Type ℓ) : Type ℓ where
    guarded : X → DynTy X
    unguarded : ∀ s → (P s → DynTy X) → DynTy X

  -- Elim principle
  DynInd : {X : Type ℓ} → {B : DynTy X → Type ℓ'} →
    ((x : X) → B (guarded x)) →
    (∀ {s} {ds : P s → DynTy X} →
      (bs : ((p : P s) → B (ds p))) →
      B (unguarded s ds)) →
    (d : DynTy X) → B d
  DynInd g* u* (guarded x) = g* x
  DynInd {B = B} g* u* (unguarded s ds) =
    u* (λ p → DynInd {B = B} g* u* (ds p))

  module _ (X : PosetBisim ℓ ℓ ℓ) where

    private
      |D| = DynTy ⟨ X ⟩ 
      module X = PosetBisimStr (X .snd)

    -- ordering
    data _⊑d_ : |D| → |D| → Type ℓ where
      ⊑guarded : ∀ x y → x X.≤ y → guarded x ⊑d guarded y
      ⊑unguarded : ∀ s ds es →
        (∀ (p : P s) → (ds p ⊑d es p)) →
        unguarded s ds ⊑d unguarded s es

    -- lem : ∀ s ds y → unguarded s ds ⊑d y → 

    -- properties
    ⊑d-prop : isPropValued _⊑d_
    ⊑d-prop .(guarded x) .(guarded y) (⊑guarded x y v) (⊑guarded .x .y w) i =
      ⊑guarded _ _ (X.is-prop-valued _ _ v w i)
    ⊑d-prop .(unguarded s ds) .(unguarded s es)
            (⊑unguarded s ds es ds⊑es) y = {!!} -- (⊑unguarded s ds es ds⊑es') i = {!!}
            -- Green slime here

    ⊑d-refl : isRefl _⊑d_
    ⊑d-refl (guarded x)      = ⊑guarded x x (X.is-refl x)
    ⊑d-refl (unguarded s ds) = ⊑unguarded s ds ds (λ p → ⊑d-refl (ds p))

    ⊑d-trans : isTrans _⊑d_
    ⊑d-trans (guarded _) (guarded _) (guarded _) (⊑guarded ._ ._ v) (⊑guarded ._ ._ w) =
      ⊑guarded _ _ (X.is-trans _ _ _ v w)
    ⊑d-trans
      (unguarded s ds) (unguarded .s ds') (unguarded .s ds'')
      (⊑unguarded s _ _ H) (⊑unguarded s _ _ H') =
        ⊑unguarded s ds ds'' (λ p → ⊑d-trans (ds p) (ds' p) (ds'' p) (H p) (H' p))

    ⊑d-antisym : isAntisym _⊑d_
    ⊑d-antisym .(guarded x) .(guarded y) (⊑guarded x y x⊑y) (⊑guarded .y .x y⊑x) =
      cong guarded (X.is-antisym x y x⊑y y⊑x)
    ⊑d-antisym .(unguarded s ds) .(unguarded s es) (⊑unguarded s ds es x) d'⊑d = {!d'⊑d!}

    -- bisimilarity
    data _≈d_ : |D| → |D| → Type ℓ where
      ≈guarded : ∀ x y → x X.≈ y → guarded x ≈d guarded y
      ≈unguarded : ∀ s s' ds es →
        (eq : s ≡ s') →
        (∀ (p : P s) (p' : P s') (path : PathP (λ i → P (eq i)) p p') → (ds p ≈d es p')) →
        unguarded s ds ≈d unguarded s' es


    ≈d-refl : isRefl _≈d_
    ≈d-refl (guarded x) = {!!}
    ≈d-refl (unguarded s ds) = ≈unguarded s s ds ds refl
      (λ p p' path → subst (λ p'' → ds p ≈d ds p'') path (≈d-refl (ds p)))

    ≈d-prop : isPropValued _≈d_
    ≈d-prop .(guarded x) .(guarded y) (≈guarded x y x₁) (≈guarded .x .y x₂) = {!!}
    ≈d-prop .(unguarded s ds) .(unguarded s' es)
             (≈unguarded s s' ds es eq H1) (≈unguarded .s .s' .ds .es eq' H2) i =
      ≈unguarded s s' ds es
        (isSetS s s' eq eq' i)
        (λ p p' path → ≈d-prop (ds p) (es p') (H1 p p' (subst (λ pf → PathP (λ j → P (pf j)) p p') {!!} path)) (H2 p p' {!!}) i)


   
    -- isSet
    isSetDynTy : isSet (DynTy ⟨ X ⟩)
    isSetDynTy = {!!}

    -------------------------------------
    -- Defining the predomain structure:
    -------------------------------------
    DynPredom : PosetBisim ℓ ℓ ℓ
    DynPredom .fst = |D|
    DynPredom .snd = posetbisimstr isSetDynTy
      _⊑d_ (isorderingrelation ⊑d-prop ⊑d-refl ⊑d-trans ⊑d-antisym)
      _≈d_ (isbisim {!!} {!!} {!!})


  module _ (C : ▹ (PosetBisim ℓ ℓ ℓ) → PosetBisim ℓ ℓ ℓ) where
    -- e.g. C D~ = ▸ₜ((D~ t) => 𝕃 (D~ t))
    -- or C D~ = ((▸ D~) ==> 𝕃 (▸ D~))

    D : PosetBisim ℓ ℓ ℓ
    D = fix (λ D~ → DynPredom (C D~))

    D' : PosetBisim ℓ ℓ ℓ
    D' = DynPredom (C (next D))

    unfold-D : D ≡ D'
    unfold-D = fix-eq (λ D~ → DynPredom (C D~))

    D→D' : PBMor D D'
    D→D' = mTransport unfold-D

    -------------------------
    -- Perturbations for Dyn
    -------------------------
    module _ (S'gen S'co S'op : Type ℓ-zero)             
      where

      data |PtbD| : Type ℓ-zero where
        ⟦_,_⟧u : ∀ {s}  → (p : P  s) → |PtbD| → |PtbD|
        ⟦_,_⟧1 : S'gen → |PtbD|
        ⟦_,_⟧+ : S'co → |PtbD| → |PtbD|
        ⟦_,_⟧- : S'op → |PtbD| → |PtbD|
        
        -- composition, identity, and equations
        _·_ : |PtbD| → |PtbD| → |PtbD|
        ε : |PtbD|

        id-u : ∀ s (p : P s) → ⟦ p , ε ⟧u  ≡ ε
        comp-u : ∀ s (p : P s) x y → ⟦ p , x · y ⟧u ≡ (⟦ p , x ⟧u · ⟦ p , y ⟧u)

        id+ : ∀ {s} → ⟦ s , ε ⟧+ ≡ ε
        comp+ : ∀ {s} m m' → ⟦ s , m · m' ⟧+ ≡ ⟦ s , m ⟧+ · ⟦ s , m' ⟧+

        id- : ∀ {s} → ⟦ s , ε ⟧- ≡ ε
        comp- : ∀ {s} m m' → ⟦ s , m · m' ⟧- ≡ ⟦ s , m' ⟧- · ⟦ s , m ⟧-

        identityᵣ : ∀ x → x · ε ≡ x
        identityₗ  : ∀ x → ε · x ≡ x
        assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
        trunc : isSet |PtbD|

       -- Recursion principle
       

      PtbD : Monoid ℓ-zero
      PtbD = makeMonoid {M = |PtbD|} ε _·_ trunc assoc identityᵣ identityₗ

      -----------------------------------
      -- Interpretation as endomorphisms
      -----------------------------------

      module _ (i1 : S'gen → ⟨ Endo (C (next D)) ⟩)
               (i+ : S'co → MonoidHom (Endo (C (next D))) (Endo D))
               (i- : S'op → MonoidHom ((Endo (C (next D))) ^op) (Endo D))
        where

        interp-unguarded' : ∀ s (p : P s) → (⟨ D' ⟩ → ⟨ D' ⟩) → (⟨ D' ⟩ → ⟨ D' ⟩)
        interp-unguarded' s p δ (guarded x) = guarded x -- leave the input unchanged
        interp-unguarded' s p δ (unguarded s' ds) = aux (dec-eq-S s s')
          where
            aux : _ → _
            aux (yes eq) = δ (ds (subst P eq p)) -- perturb the p-child
            aux (no ¬eq) = unguarded s' ds       -- leave the input unchanged

        interp-unguarded : ∀ s (p : P s) → ⟨ Endo D' ⟩ → ⟨ Endo D' ⟩
        interp-unguarded s p δ .fst .PBMor.f = interp-unguarded' s p (δ .fst .PBMor.f)
        interp-unguarded s p δ .fst .PBMor.isMon = {!!}
        interp-unguarded s p δ .fst .PBMor.pres≈ = {!!}
        interp-unguarded s p δ .snd = {!!}

        -- use recursion principle to define the guarded interpretation
        interp-guarded' : ∀ s' → (⟨ D' ⟩ → ⟨ D' ⟩) → (⟨ D' ⟩ → ⟨ D' ⟩)
        interp-guarded' s' δ (guarded x) = guarded {!!}
        interp-guarded' s' δ (unguarded s x) = unguarded s x

        interp : MonoidHom PtbD (Endo D)
        interp = {!!}


    -- Relations, push-pull, and quasi-representability
    inj-unguarded : PBRel {!!} D' {!!}
