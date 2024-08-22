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
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary

open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Bool
open import Cubical.Data.Sum as Sum

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.FreeMonoid as Free
open import Cubical.Algebra.Monoid.Displayed.Instances.Sigma

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
      ⊑unguarded : ∀ s s' ds es →
        (eq : s ≡ s') →
        (∀ (p : P s) (p' : P s') (path : PathP (λ i → P (eq i)) p p') → (ds p ⊑d es p')) →
        unguarded s ds ⊑d unguarded s' es


    -- properties
    ⊑d-prop : isPropValued _⊑d_
    ⊑d-prop .(guarded x) .(guarded y) (⊑guarded x y v) (⊑guarded .x .y w) i =
      ⊑guarded _ _ (X.is-prop-valued _ _ v w i)
    ⊑d-prop .(unguarded s ds) .(unguarded s' es)
            (⊑unguarded s s' ds es eq ds⊑es) (⊑unguarded s s' ds es eq' ds⊑es') i =
            ⊑unguarded s s' ds es (lem1 i) (lem2 i)
            where
              lem1 : eq ≡ eq'
              lem1 = isSetS s s' eq eq'
              
              lem2 : PathP
                      (λ i →
                        (p : P s) (p' : P s') (path : PathP (λ j → P (lem1 i j)) p p') → ds p ⊑d es p')
                     ds⊑es ds⊑es'
              lem2 i' p p' path = ⊑d-prop (ds p) (es p') (ds⊑es p p' aux) (ds⊑es' p p' {!!}) i'
                where
                  aux : PathP (λ i → P (eq i)) p p'
                  aux = transport (λ j → PathP (λ i → P (isSetS s s' eq {!!} i {!i!})) p p') path
                  --subst (λ (e : s ≡ s') → PathP (λ j → P (e j)) p p') {!!} path


    ⊑d-refl : isRefl _⊑d_
    ⊑d-refl (guarded x)      = ⊑guarded x x (X.is-refl x)
    ⊑d-refl (unguarded s ds) = ⊑unguarded s s ds ds refl
      (λ p p' path → subst (λ v → ds p ⊑d ds v) path (⊑d-refl (ds p)))

    ⊑d-trans : isTrans _⊑d_
    ⊑d-trans (guarded _) (guarded _) (guarded _) (⊑guarded ._ ._ v) (⊑guarded ._ ._ w) =
      ⊑guarded _ _ (X.is-trans _ _ _ v w)
    ⊑d-trans
      (unguarded s₁ ds₁) (unguarded .s₂ ds₂) (unguarded .s₃ ds₃)
      (⊑unguarded s₁ s₂ _ _ eq H) (⊑unguarded s₂ s₃ _ _ eq' H') =
        ⊑unguarded s₁ s₃ ds₁ ds₃ (eq ∙ eq') aux
        where
          aux : _
          aux p₁ p₃ path = ⊑d-trans (ds₁ p₁) (ds₂ p₂) (ds₃ p₃) (H p₁ p₂ (toPathP refl)) (H' p₂ p₃ lem) where
          
            p₂ : P s₂
            p₂ = subst P eq p₁

            lem : PathP (λ i → P (eq' i)) p₂ p₃
            lem = {!!}
          
    ⊑d-antisym : isAntisym _⊑d_
    ⊑d-antisym .(guarded x) .(guarded y) (⊑guarded x y x⊑y) (⊑guarded .y .x y⊑x) =
      cong guarded (X.is-antisym x y x⊑y y⊑x)
    ⊑d-antisym .(unguarded s ds) .(unguarded s' es) (⊑unguarded s s' ds es eq H) (⊑unguarded .s' .s .es .ds eq' H') =
      cong₂ unguarded eq (λ i x → {!ds!})

    -- bisimilarity
    data _≈d_ : |D| → |D| → Type ℓ where
      ≈guarded : ∀ x y → x X.≈ y → guarded x ≈d guarded y
      ≈unguarded : ∀ s s' ds es →
        (eq : s ≡ s') →
        (∀ (p : P s) (p' : P s') (path : PathP (λ i → P (eq i)) p p') → (ds p ≈d es p')) →
        unguarded s ds ≈d unguarded s' es


    ≈d-refl : isRefl _≈d_
    ≈d-refl (guarded x) = ≈guarded x x (X.is-refl-Bisim x)
    ≈d-refl (unguarded s ds) = ≈unguarded s s ds ds refl
      (λ p p' path → subst (λ p'' → ds p ≈d ds p'') path (≈d-refl (ds p)))

    ≈d-sym : isSym _≈d_
    ≈d-sym = {!!}

    ≈d-prop : isPropValued _≈d_
    ≈d-prop .(guarded x) .(guarded y) (≈guarded x y v) (≈guarded .x .y w) i =
      ≈guarded _ _ (X.is-prop-valued-Bisim _ _ v w i)
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
      _≈d_ (isbisim ≈d-refl ≈d-sym ≈d-prop)


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

    D'→D : PBMor D' D
    D'→D = mTransport (sym unfold-D)

    unfold-fold :  D'→D ∘p D→D' ≡ Id
    unfold-fold = eqPBMor _ _ (funExt (λ d → transport⁻Transport (λ i → ⟨ unfold-D i ⟩) d ))

    fold-unfold :  D→D' ∘p D'→D ≡ Id
    fold-unfold = eqPBMor _ _ (funExt λ d → transportTransport⁻ (λ i → ⟨ unfold-D i ⟩) d)

    -------------------------
    -- Perturbations for Dyn
    -------------------------
    module _ (S'gen S'co S'op : Type ℓ-zero)             
      where

      PtbD : Monoid ℓ-zero
      PtbD = Free.FM S'gen ((Σ[ s ∈ S ] P s) ⊎ S'co) S'op

      -----------------------------------
      -- Interpretation as endomorphisms
      -----------------------------------

      module _ (i-gen : S'gen → ⟨ Endo (C (next D)) ⟩)
               (i-co  : S'co  → MonoidHom (Endo D)       (Endo (C (next D))))
               (i-op  : S'op  → MonoidHom ((Endo D) ^op) (Endo (C (next D))))
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

        i-unguarded : ∀ s (p : P s) → MonoidHom (Endo D) (Endo D)
        i-unguarded s p = {!!}

        -- use recursion principle to define the guarded interpretation
        interp-guarded' : ∀ s' → (⟨ D' ⟩ → ⟨ D' ⟩) → (⟨ D' ⟩ → ⟨ D' ⟩)
        interp-guarded' s' δ (guarded x) = guarded {!!}
        interp-guarded' s' δ (unguarded s x) = unguarded s x

        interp-guarded : MonoidHom (Endo (C (next D))) (Endo D)
        interp-guarded = {!!}
          where
            aux : ⟨ Endo (C (next D)) ⟩ → ⟨ Endo D' ⟩
            aux δ .fst .PBMor.f (guarded x) = guarded (δ .fst .PBMor.f x) -- perturb the input
            aux δ .fst .PBMor.f (unguarded s x) = unguarded s x -- leave the input unchanged

        interp : MonoidHom PtbD (Endo D)
        interp = Free.rec _ _ _ (Endo D)
          -- gen case
          (interp-guarded .fst ∘ i-gen)

          -- covariant cases
          (Sum.rec
            (λ {(s , p) → i-unguarded s p})
            (λ s → interp-guarded ∘hom i-co s))

          -- contravariant case
          (λ s → interp-guarded ∘hom i-op s)

    -- Relations, push-pull, and quasi-representability
    inj-unguarded : PBRel (ΣP (S , isSetS) (λ s → ΠP (P s) (λ p → D'))) D' ℓ-zero
    inj-unguarded = {!!}

    inj-guarded : PBRel {!!} {!!} {!!}
    inj-guarded = {!!}
