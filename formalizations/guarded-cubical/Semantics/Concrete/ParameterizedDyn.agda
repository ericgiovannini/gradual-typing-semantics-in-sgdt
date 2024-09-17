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
open import Cubical.Foundations.Transport.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary

open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.Instances.CartesianProduct as Cart hiding (_×_)
open import Cubical.Algebra.Monoid.Instances.Trivial as Trivial
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.FreeMonoid as Free
open import Cubical.Algebra.Monoid.FreeProduct.Indexed as Indexed
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Sigma
open import Cubical.Algebra.Monoid.Displayed.Instances.Reindex


open import Common.Common
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Constructions renaming (ℕ to NatP)
open import Semantics.Concrete.DoublePoset.DblPosetCombinators hiding (U)
open import Semantics.Concrete.DoublePoset.Morphism hiding (_$_)
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k


open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Types k as Ty hiding (Unit ; _×_)
open import Semantics.Concrete.Perturbation.Relation.Alt k
open import Semantics.Concrete.Perturbation.QuasiRepresentation k
open import Semantics.Concrete.Relations k


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

-- DiscreteTy : (ℓ : Level) → Type (ℓ-suc ℓ)
-- DiscreteTy ℓ = Σ[ X ∈ Type ℓ ] (Discrete X)

module _ {ℓ : Level}
  (S : DiscreteTy ℓ-zero) (P : ⟨ S ⟩ → DiscreteTy ℓ-zero)
  where

  |P| = fst ∘ P

  |S| = ⟨ S ⟩
  dec-eq-S = S .snd

  dec-eq-P : ∀ s → _
  dec-eq-P s = P s .snd

  isSetS : isSet |S|
  isSetS = Discrete→isSet (S .snd)

  S-set : hSet ℓ-zero
  S-set = (|S| , isSetS)


  -- The underlying type of Dyn
  data DynTy (X : Type ℓ) : Type ℓ where
    guarded : X → DynTy X
    unguarded : ∀ s → (|P| s → DynTy X) → DynTy X

  unguarded≡ : ∀ {X : Type ℓ}{s t}{ds : |P| s → DynTy X}{es : |P| t → DynTy X}
    → (s≡ : Path |S| s t)
    → PathP (λ i → |P| (s≡ i) → DynTy X) ds es
    → unguarded s ds ≡ unguarded t es
  unguarded≡ s≡ cs≡ i = unguarded (s≡ i) (cs≡ i)

  -- Elim principle
  DynInd : {X : Type ℓ} → {B : DynTy X → Type ℓ'} →
    ((x : X) → B (guarded x)) →
    (∀ {s} {ds : |P| s → DynTy X} →
      (bs : ((p : |P| s) → B (ds p))) →
      B (unguarded s ds)) →
    (d : DynTy X) → B d
  DynInd g* u* (guarded x) = g* x
  DynInd {B = B} g* u* (unguarded s ds) =
    u* (λ p → DynInd {B = B} g* u* (ds p))


  module _ (X : Type ℓ) where

{-
    module _ {B : DynTy X → Type ℓ'}
      (s : |S|) (p : |P| s)
      (g : (∀ x → B (guarded x)))
      (u-eq-s-p : (∀ s' ds (s≡s' : s ≡ s') (bs : (p' : |P| s') (p≡p' : PathP (λ i → |P| (s≡s' i)) p p') → B (ds p')) → B (unguarded s' ds)))
      (u-eq-s-neq-p : ∀ s' ds (s≡s' : s ≡ s') (bs : (p' : |P| s') (p≢p' : ¬ (PathP (λ i → |P| (s≡s' i)) p p')) → B (ds p')) → B (unguarded s' ds))
      (u-neq-s : ∀ s' ds (s≢s' : ¬ (s ≡ s')) (bs : (p' : |P| s') → B (ds p')) → B (unguarded s' ds)) where

      -- Combinator for defining a function on Dyn using the decidable equality of S and P
-}    

  -- -- Isomorphism with IW Tree
  -- data GuardedOrUnguarded : Type ℓ-zero where
  --   G : GuardedOrUnguarded
  --   U : GuardedOrUnguarded

  module _ (X : Type ℓ) where

    Shape : Type ℓ
    Shape = X ⊎ |S|
      
    Pos : Shape → Type ℓ-zero
    Pos (inl _) = ⊥
    Pos (inr s) = |P| s
  
    DynAsTree : Type ℓ
    DynAsTree = IW {X = Unit} (λ _ → Shape) (λ _ → Pos) (λ _ _ _ → tt) tt

    Dyn→Tree : DynTy X → DynAsTree
    Dyn→Tree (guarded x) = node (inl x) ⊥.rec
    Dyn→Tree (unguarded s ds) = node (inr s) subtrees
      where
        subtrees : |P| s → DynAsTree
        subtrees p = Dyn→Tree (ds p)

    Tree→Dyn : DynAsTree → DynTy X
    Tree→Dyn (node (inl x) subtree) = guarded x
    Tree→Dyn (node (inr s) subtree) = unguarded s aux
      where
        aux : |P| s → DynTy X
        aux p = Tree→Dyn (subtree p)

    -- Showing DynTy X is a Set
    retr : retract Dyn→Tree Tree→Dyn
    retr (guarded x) = refl
    retr (unguarded s ds) =
      cong₂ unguarded refl (funExt (λ p → retr (ds p)))

    isSetDynAsTree : isSet X → isSet DynAsTree
    isSetDynAsTree isSetX = isOfHLevelSuc-IW 1 (λ _ → isSetShape) tt
      where
        isSetShape : isSet Shape
        isSetShape = isSet⊎ isSetX isSetS

    isSetDynTy : isSet X → isSet (DynTy X)
    isSetDynTy isSetX =
      isSetRetract Dyn→Tree Tree→Dyn retr (isSetDynAsTree isSetX)

  module _ (X : PosetBisim ℓ ℓ ℓ) where

    private
      |D| = DynTy ⟨ X ⟩
      module X = PosetBisimStr (X .snd)

    -- ordering
    data _⊑d_ : |D| → |D| → Type ℓ where
      ⊑guarded : ∀ x y → x X.≤ y → guarded x ⊑d guarded y
      ⊑unguarded : ∀ s s' ds es →
        (eq : s ≡ s') →
        (∀ (p : |P| s) (p' : |P| s') (path : PathP (λ i → |P| (eq i)) p p') → (ds p ⊑d es p')) →
        unguarded s ds ⊑d unguarded s' es

    ⊑Idx : Type ℓ
    ⊑Idx = |D| × |D|

    ⊑Shape : |D| × |D| → Type ℓ
    ⊑Shape ((guarded x) , (guarded y)) = x X.≤ y
    ⊑Shape ((unguarded s ds) , (unguarded s' es)) = Lift (s ≡ s')
    ⊑Shape _ = ⊥*
      
    ⊑Pos : ∀ d → (⊑Shape d) → Type ℓ-zero
    ⊑Pos (guarded x , guarded y) _ = ⊥
    ⊑Pos (unguarded s ds , unguarded s' es) (lift s≡s') =
      Σ[ p ∈ |P| s ] Σ[ p' ∈ |P| s' ] PathP (λ i → |P| (s≡s' i)) p p'

    ⊑InD : ∀ d → (s : ⊑Shape d) → ⊑Pos d s → |D| × |D|
    ⊑InD (guarded x , guarded y) s p =
      guarded x , guarded y -- This can be anything. It's never used because ⊑Pos will be ⊥.
    ⊑InD (unguarded s₁ ds , unguarded s₂ es) eq (p , p' , path) =
      (ds p , es p')
  
    ⊑d-AsTree : |D| × |D| → Type ℓ
    ⊑d-AsTree = IW {X = |D| × |D|} ⊑Shape ⊑Pos ⊑InD

    ⊑d→Tree : ∀ d d' → d ⊑d d' → ⊑d-AsTree (d , d')
    ⊑d→Tree .(guarded x) .(guarded y) (⊑guarded x y x≤y) =
      node x≤y ⊥.rec
    ⊑d→Tree .(unguarded s ds) .(unguarded s' es) (⊑unguarded s s' ds es eq ds⊑es) =
      node (lift eq) subtrees
      where
        subtrees : (pos : ⊑Pos (unguarded s ds , unguarded s' es) (lift eq)) →
                   IW ⊑Shape ⊑Pos ⊑InD (⊑InD (unguarded s ds , unguarded s' es) (lift eq) pos)
        subtrees (p , p' , path) = ⊑d→Tree (ds p) (es p') (ds⊑es p p' path)

    Tree→⊑d : ∀ d d' → ⊑d-AsTree (d , d') → d ⊑d d'
    Tree→⊑d (guarded x) (guarded y) (node x≤y subtree) =
      ⊑guarded x y x≤y
    Tree→⊑d (unguarded s ds) (unguarded s' es) (node (lift s≡s') subtree) =
      ⊑unguarded s s' ds es s≡s' aux
      where
        aux : (p : |P| s) (p' : |P| s') (path : PathP (λ i → |P| (s≡s' i)) p p') →
          ds p ⊑d es p'
        aux p p' path = Tree→⊑d (ds p) (es p') (subtree (p , p' , path))

    retr⊑ : ∀ d d' → retract (⊑d→Tree d d') (Tree→⊑d d d')
    retr⊑ _ _ (⊑guarded x y x≤y) = refl
    retr⊑ _ _ (⊑unguarded s s' ds es eq ds⊑es) =
      λ i → ⊑unguarded s s' ds es eq (λ p p' path → retr⊑ (ds p) (es p') (ds⊑es p p' path) i)
    

    isProp⊑dTree : ∀ d d' → isProp (⊑d-AsTree (d , d'))
    isProp⊑dTree d d' = isPropIW isPropShape (d , d')
      where
        isPropShape : (dd' : |D| × |D|) → isProp (⊑Shape dd')
        isPropShape (guarded x , guarded y) = X.is-prop-valued x y
        isPropShape (guarded x , unguarded s ds) = isProp⊥*
        isPropShape (unguarded s ds , guarded x) = isProp⊥*
        isPropShape (unguarded s ds , unguarded s' es) = isOfHLevelLift 1 (isSetS s s')

    -- properties
    ⊑d-prop : isPropValued _⊑d_
    ⊑d-prop d d' = isPropRetract (⊑d→Tree d d') (Tree→⊑d d d') (retr⊑ d d') (isProp⊑dTree d d')

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
          aux p₁ p₃ path =
            ⊑d-trans (ds₁ p₁) (ds₂ p₁₂) (ds₃ p₃) (H p₁ p₁₂ (toPathP refl)) (H' p₁₂ p₃ lem) where

            p₁₂ : |P| s₂
            p₁₂ = subst |P| eq p₁

            path' : (transport (λ i → |P| ((eq ∙ eq') i)) p₁) ≡ p₃
            path' = fromPathP path

            path'' : (transport (λ i → |P| (eq' i)) p₁₂) ≡ p₃
            path'' = sym (transportComposite (cong |P| eq) (cong |P| eq') p₁)
              ∙ cong₂ transport (sym (congFunct |P| eq eq')) refl
              ∙ path'

            lem : PathP (λ i → |P| (eq' i)) p₁₂ p₃
            lem = toPathP path''

    ⊑d-antisym : isAntisym _⊑d_
    ⊑d-antisym (guarded x) (guarded y) (⊑guarded _ _ x⊑y) (⊑guarded _ _ y⊑x) =
      cong guarded (X.is-antisym x y x⊑y y⊑x)
    ⊑d-antisym (unguarded s ds) (unguarded s' es)
      (⊑unguarded _ _ _ _ s≡s' ds⊑es)
      (⊑unguarded _ _ _ _ s'≡s es⊑ds) =
      unguarded≡ s≡s'
        (toPathP $ funExt λ p' →
          (λ i → transp-ds-simplify i p')
          ∙ λ i → ds'≡es p' i)
      where
        transp-ds-simplify :
          (transport (λ i → |P| (s≡s' i) → DynTy ⟨ X ⟩) ds)
          ≡ (ds ∘ subst |P| (sym s≡s'))
        transp-ds-simplify = fromPathP (funDomTransp |P| s≡s' ds)

        module _ (p' : |P| s') where
          ds'⊑es : ds (subst⁻ |P| s≡s' p') ⊑d es p'
          ds'⊑es = ds⊑es _ _ (symP (subst⁻-filler |P| s≡s' p'))

          es⊑ds' : es p' ⊑d ds (subst⁻ |P| s≡s' p')
          es⊑ds' = subst (λ s≡s' → es p' ⊑d ds (subst⁻ |P| s≡s' p'))
            (isSetS _ _ _ _)
            (es⊑ds _ _ (subst-filler |P| s'≡s p'))

          ds'≡es : ds (subst⁻ |P| s≡s' p') ≡ es p'
          ds'≡es = ⊑d-antisym _ _ ds'⊑es es⊑ds'

    -- bisimilarity
    data _≈d_ : |D| → |D| → Type ℓ where
      ≈guarded : ∀ x y → x X.≈ y → guarded x ≈d guarded y
      ≈unguarded : ∀ s s' ds es →
        (eq : s ≡ s') →
        (∀ (p : |P| s) (p' : |P| s') (path : PathP (λ i → |P| (eq i)) p p') → (ds p ≈d es p')) →
        unguarded s ds ≈d unguarded s' es

    -- TODO show that this is isomorphic to an IW Tree, and show that that IW tree is a Prop

    ≈d-refl : isRefl _≈d_
    ≈d-refl (guarded x) = ≈guarded x x (X.is-refl-Bisim x)
    ≈d-refl (unguarded s ds) = ≈unguarded s s ds ds refl
      (λ p p' path → subst (λ p'' → ds p ≈d ds p'') path (≈d-refl (ds p)))

    ≈d-sym : isSym _≈d_
    ≈d-sym _ _ (≈guarded x y x≈y) = ≈guarded y x (X.is-sym x y x≈y)
    ≈d-sym _ _ (≈unguarded s s' ds es eq ds≈es) =
      ≈unguarded s' s es ds (sym eq) (λ p p' path → ≈d-sym (ds p') (es p) (ds≈es p' p (symP path)))

    ≈d-prop : isPropValued _≈d_
    ≈d-prop = {!!}


    -------------------------------------
    -- Defining the predomain structure:
    -------------------------------------
    DynPredom : PosetBisim ℓ ℓ ℓ
    DynPredom .fst = |D|
    DynPredom .snd = posetbisimstr (isSetDynTy ⟨ X ⟩ X.is-set)
      _⊑d_ (isorderingrelation ⊑d-prop ⊑d-refl ⊑d-trans ⊑d-antisym)
      _≈d_ (isbisim ≈d-refl ≈d-sym ≈d-prop)


  module _ (C : ▹ (PosetBisim ℓ ℓ ℓ) → PosetBisim ℓ ℓ ℓ) where
          --  (C' : ▹ (ValType ℓ ℓ ℓ ℓ-zero) → ValType ℓ ℓ ℓ ℓ-zero) where
    -- e.g. C D~ = ▸ₜ((D~ t) => 𝕃 (D~ t))
    -- or C D~ = ((▸ D~) ==> 𝕃 (▸ D~))

    D : PosetBisim ℓ ℓ ℓ
    D = fix (λ D~ → DynPredom (C D~))

    D' : PosetBisim ℓ ℓ ℓ
    D' = DynPredom (C (next D))

    -- Unfolding
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

    -- Identity relation on Dyn
    rD' : PBRel D' D' ℓ
    rD' = idPRel D'

    _⊑D'_ = rD' .PBRel.R
    _≈D'_ = _≈d_ (C (next D))


--  module _ (C : ▹ (ValType ℓ ℓ ℓ ℓ-zero) → ValType ℓ ℓ ℓ ℓ-zero) where

    ----------------------------------------------
    -- Perturbations for Dyn and for C (next Dyn)
    ----------------------------------------------
    module _ (S'gen S'co S'op : Type ℓ-zero)
      --(PtbCD : Monoid ℓ-zero)
      --(iCD : MonoidHom PtbCD (Endo (C (next D))))
      where

      PtbD : Monoid ℓ-zero
      PtbD = Free.FM S'gen ((Σ[ s ∈ |S| ] |P| s) ⊎ S'co) S'op

      GuardedShapes : Type
      GuardedShapes = (S'gen ⊎ S'co) ⊎ S'op

      GuardedShapes→Monoid : GuardedShapes → Monoid _
      GuardedShapes→Monoid (inl (inl s-gen)) = NatM
      GuardedShapes→Monoid (inl (inr s-co)) = PtbD
      GuardedShapes→Monoid (inr s-op) = PtbD ^op

      PtbCD : Monoid ℓ-zero
      PtbCD = ⊕ᵢ GuardedShapes GuardedShapes→Monoid
         

      -----------------------------------
      -- Interpretation as endomorphisms
      -----------------------------------

      module _ (i-gen : S'gen → ⟨ Endo (C (next D)) ⟩)
               (i-co  : S'co  → MonoidHom (Endo D)       (Endo (C (next D))))
               (i-op  : S'op  → MonoidHom ((Endo D) ^op) (Endo (C (next D))))
        where

        open PBMor


        -- We split this out into its own helper function so that we
        -- can reason about it when proving monotonicity of the
        -- interpretation function.
        iU-helper :
           ∀ s (p : |P| s) (|δ| : ⟨ D' ⟩ → ⟨ D' ⟩)
           s' (ds : |P| s' → DynTy ⟨ C (next D) ⟩)
           (eq? : Dec (s ≡ s')) → ⟨ D' ⟩
        iU-helper s p |δ| s' ds (yes eq) = unguarded s'
          (λ p' → decRec 
            (λ p≡p' → |δ| (ds p')) -- perturb the p'-child since p = p'
            (λ _ → ds p') -- leave the input unchanged
            (dec-eq-P s' (subst _ eq p) p')) 
          -- |δ| (ds (subst |P| eq p)) -- perturb the p-child
        iU-helper s p |δ| s' ds (no ¬eq) = unguarded s' ds  -- leave the input unchanged

        |iU| : ∀ s (p : |P| s) → (⟨ D' ⟩ → ⟨ D' ⟩) → (⟨ D' ⟩ → ⟨ D' ⟩)
        |iU| s p |δ| (guarded x) = guarded x -- leave the input unchanged
        |iU| s p |δ| (unguarded s' ds) = iU-helper s p |δ| s' ds (dec-eq-S s s')
         
        iU-mon : ∀ s p (δ : ⟨ Endo D' ⟩) → monotone (|iU| s p (δ .fst .PBMor.f))
        iU-mon s p δ (⊑guarded x y x≤y) = ⊑guarded x y x≤y
        iU-mon s p δ (⊑unguarded s₁ s₂ ds es s₁≡s₂ ds⊑es) = aux (dec-eq-S s s₁) (dec-eq-S s s₂)
          where
            |δ| = δ .fst .f

            aux : (s≡s₁? : Dec (s ≡ s₁)) → (s≡s₂? : Dec (s ≡ s₂)) →
              iU-helper s p |δ| s₁ ds s≡s₁? ⊑D' iU-helper s p |δ| s₂ es s≡s₂?
            aux (yes s≡s₁) (yes s≡s₂) =
              ⊑unguarded s₁ s₂ _ _ s₁≡s₂ λ p₁ p₂ p₁≡p₂ →
                aux2 p₁ p₂ p₁≡p₂ (dec-eq-P s₁ (subst _ s≡s₁ p) p₁) (dec-eq-P s₂ (subst _ s≡s₂ p) p₂) 
              -- δ .fst .isMon (ds⊑es (subst |P| s≡s₁ p) (subst |P| s≡s₂ p) (λ i → subst |P| (lem i) p))
              where
                lem : PathP (λ i → (s ≡ (s₁≡s₂ i))) s≡s₁ s≡s₂
                lem = isProp→PathP (λ i → isSetS s (s₁≡s₂ i)) s≡s₁ s≡s₂

                lem2 : (s≡s₁ ∙ s₁≡s₂) ≡ s≡s₂
                lem2 = isSetS s s₂ (s≡s₁ ∙ s₁≡s₂) s≡s₂

                aux2 : ∀ p₁ p₂ p₁≡p₂ →
                  (p≡p₁? : Dec ((subst _ s≡s₁ p) ≡ p₁)) →
                  (p≡p₂? : Dec ((subst _ s≡s₂ p) ≡ p₂)) →
                  decRec _ _ p≡p₁? ⊑D' decRec _ _ p≡p₂?
                aux2 p₁ p₂ p₁≡p₂ (yes p≡p₁) (yes p≡p₂) = δ .fst .isMon (ds⊑es p₁ p₂ p₁≡p₂)
                aux2 p₁ p₂ p₁≡p₂ (yes p≡p₁) (no p≢p₂) = ⊥.rec (p≢p₂ (fromPathP (path)))
                  where
                    path : PathP (λ i → |P| (s≡s₂ i)) p p₂
                    path = transport
                             (λ i → PathP (λ j → |P| (lem2 i j)) p p₂)
                             (compPathP' {B = |P|} (toPathP p≡p₁) p₁≡p₂)
                aux2 p₁ p₂ p₁≡p₂ (no p≢p₁) (yes p≡p₂) = ⊥.rec (p≢p₁ {!!})
                aux2 p₁ p₂ p₁≡p₂ (no _) (no _) = ds⊑es p₁ p₂ p₁≡p₂
               
            -- impossible because s₁ ≡ s₂
            aux (yes s≡s₁) (no s≢s₂) = ⊥.rec (s≢s₂ (s≡s₁ ∙ s₁≡s₂))

            -- impossible because s₁ ≡ s₂
            aux (no s≢s₁) (yes s≡s₂) = ⊥.rec (s≢s₁ (s≡s₂ ∙ sym s₁≡s₂))
            
            aux (no _) (no _) = ⊑unguarded s₁ s₂ ds es s₁≡s₂ ds⊑es

        -- Same principle as with the monotonicity proof above
        iU-pres≈ : ∀ s p (δ : ⟨ Endo D' ⟩) → preserve≈ (|iU| s p (δ .fst. PBMor.f))
        iU-pres≈ = {!!}



        -- iU-PredomMor :  ∀ s (p : |P| s) → ⟨ Endo D' ⟩ → ⟨ Endo D' ⟩
        -- interp-unguarded s p δ .fst .PBMor.f = |iU| s p (δ .fst .PBMor.f)
        -- interp-unguarded s p δ .fst .PBMor.isMon = iU-mon s p δ

        iU≈Id : ∀ s p (δ : ⟨ Endo D' ⟩) → (|iU| s p (δ .fst .PBMor.f)) ≈fun id
        iU≈Id s p δ _ _ (≈guarded x y x≈y) = ≈guarded x y x≈y
        iU≈Id s p δ _ _ (≈unguarded s₁ s₂ ds es s₁≡s₂ ds≈es) = aux (dec-eq-S s s₁) (dec-eq-S s s₂)
          where
           |δ| = δ .fst .f
           
           aux : (s≡s₁? : Dec (s ≡ s₁)) → (s≡s₂? : Dec (s ≡ s₂)) →
              iU-helper s p |δ| s₁ ds s≡s₁? ≈D' unguarded s₂ es
           aux (yes s≡s₁) (yes s≡s₂) =
             ≈unguarded s₁ s₂ _ _ s₁≡s₂ (λ p₁ p₂ p₁≡p₂ → aux2 p₁ p₂ p₁≡p₂ (dec-eq-P s₁ _ p₁))
             where
                aux2 : ∀ p₁ p₂ p₁≡p₂ →
                  (p≡p₁? : Dec ((subst _ s≡s₁ p) ≡ p₁)) →                
                  decRec _ _ p≡p₁? ≈D' es p₂
                aux2 p₁ p₂ p₁≡p₂ (yes p≡p₁) = δ .snd (ds p₁) (es p₂) (ds≈es p₁ p₂ p₁≡p₂)              
                aux2 p₁ p₂ p₁≡p₂ (no _) = ds≈es p₁ p₂ p₁≡p₂
           aux (yes s≡s₁) (no s≢s₂) = ⊥.rec (s≢s₂ (s≡s₁ ∙ s₁≡s₂))
           aux (no s≢s₁) (yes s≡s₂) = ⊥.rec (s≢s₁ (s≡s₂ ∙ sym s₁≡s₂))
           aux (no _) (no _) = ≈unguarded s₁ s₂ ds es s₁≡s₂ ds≈es

        iU-Id : ∀ s p d → |iU| s p id d ≡ d
        iU-Id s p (guarded x) = refl
        iU-Id s p (unguarded s' ds) = aux (dec-eq-S s s')
          where
            aux : (s≡s'? : Dec (s ≡ s')) →
              iU-helper s p id s' ds s≡s'? ≡ unguarded s' ds
            aux (yes s≡s') = cong₂ unguarded refl (funExt (λ p' → aux2 p' (dec-eq-P s' _ p')))
              where
                aux2 : ∀ p' →
                  (p≡p' : Dec ((subst _ s≡s' p) ≡ p')) →
                  (decRec _ _ p≡p') ≡ ds p'
                aux2 p' (yes p≡p') = refl
                aux2 p' (no _) = refl
            aux (no neq) = refl

        iU-Comp : ∀ s p (|δ| |δ'| : ⟨ D' ⟩ → ⟨ D' ⟩) d →
          |iU| s p (|δ| ∘ |δ'|) d ≡ (|iU| s p |δ|) (|iU| s p |δ'| d)
        iU-Comp s p |δ| |δ'| (guarded x) = refl
        iU-Comp s p |δ| |δ'| (unguarded s' ds) = aux (dec-eq-S s s')
          where
            aux : (s≡s'? : Dec (s ≡ s')) →
              iU-helper s p (|δ| ∘ |δ'|) s' ds s≡s'? ≡
              |iU| s p |δ| (iU-helper s p |δ'| s' ds s≡s'?)
            aux (yes s≡s') = aux2 (dec-eq-S s s')
              where
                aux2 : ∀ (eq? : Dec (s ≡ s')) →
                  unguarded s' (λ p' → decRec
                    (λ p≡p' → (|δ| ∘ |δ'|) (ds p'))
                    (λ _ → ds p')
                    (dec-eq-P s' (subst (λ v → P v .fst) s≡s' p) p')) ≡
                  iU-helper s p |δ| s' (λ p' → decRec
                    (λ p≡p' → |δ'| (ds p'))
                    (λ _ → ds p')
                    (dec-eq-P s' (subst (λ v → P v .fst) s≡s' p) p'))                    
                  eq?
                aux2 (yes eq) =
                  transport
                    refl
                    (cong₂ unguarded refl (funExt (λ p' → {!!})))
                  where
                    aux3 : ∀ p' (p≡p'? : Dec ((subst _ eq p) ≡ p')) →
                      decRec (λ p≡p' → (|δ| ∘ |δ'|) (ds p')) (λ _ → ds p') p≡p'? ≡
                      decRec (λ p≡p' → |δ| (decRec (λ p≡p'' → |δ'| (ds p')) (λ _ → ds p') (dec-eq-P s' (subst (λ v → P v .fst) s≡s' p) p')))
                             (λ _ →          decRec (λ p≡p' → |δ'| (ds p')) (λ _ → ds p') (dec-eq-P s' (subst (λ v → P v .fst) s≡s' p) p'))
                             p≡p'?
                    aux3 p' (yes p≡p') = {!!}
                    aux3 p' (no p≢p') = {!!}
                aux2 (no neq) = ⊥.rec (neq s≡s')
            aux (no s≢s') = aux2 (dec-eq-S s s')
              where
                aux2 : ∀ (eq? : Dec (s ≡ s')) →
                  unguarded s' ds ≡ iU-helper s p |δ| s' ds eq?
                aux2 (yes eq) = ⊥.rec (s≢s' eq)
                aux2 (no neq) = refl

        interp-unguarded : ∀ s (p : |P| s) → ⟨ Endo D' ⟩ → ⟨ Endo D' ⟩
        interp-unguarded s p δ .fst .PBMor.f = |iU| s p (δ .fst .PBMor.f)
        interp-unguarded s p δ .fst .PBMor.isMon = iU-mon s p δ
        interp-unguarded s p δ .fst .PBMor.pres≈ = iU-pres≈ s p δ
        interp-unguarded s p δ .snd = iU≈Id s p δ

        i-unguarded : ∀ s (p : |P| s) → MonoidHom (Endo D') (Endo D')
        i-unguarded s p .fst = interp-unguarded s p
        i-unguarded s p .snd .IsMonoidHom.presε =
          PrePtb≡ _ _ (funExt (λ d → iU-Id s p d))
        i-unguarded s p .snd .IsMonoidHom.pres· δ δ' =
          PrePtb≡ _ _ (funExt (λ d → iU-Comp s p (δ .fst .PBMor.f) (δ' .fst .PBMor.f) d))

        -- use recursion principle to define the guarded interpretation
       
        interp-guarded : MonoidHom (Endo (C (next D))) (Endo D')
        interp-guarded = aux , monoidequiv aux-id aux-comp 
          where
            interp-guarded' : ⟨ Endo (C (next D)) ⟩ → (⟨ D' ⟩ → ⟨ D' ⟩)
            interp-guarded' δ (guarded x) = guarded (δ .fst .PBMor.f x) -- perturb the input
            interp-guarded' δ (unguarded s x) = unguarded s x -- leave the input unchanged

            aux : ⟨ Endo (C (next D)) ⟩ → ⟨ Endo D' ⟩
            aux δ .fst .PBMor.f = interp-guarded' δ
            aux δ .fst .isMon (⊑guarded x y x≤y) = ⊑guarded _ _ (δ .fst .isMon x≤y)
            aux δ .fst .isMon (⊑unguarded s s' ds es eq ds⊑es) = ⊑unguarded s s' ds es eq ds⊑es
            aux δ .fst .pres≈ (≈guarded x y x≈y) = ≈guarded _ _ (δ .fst .pres≈ x≈y)
            aux δ .fst .pres≈ (≈unguarded s s' ds es eq ds≈es) = ≈unguarded s s' ds es eq ds≈es
            aux δ .snd _ _ (≈guarded x y x≈y) = ≈guarded (δ .fst .f x) y (δ .snd x y x≈y)
            aux δ .snd _ _ (≈unguarded s s' ds es eq ds≈es) = ≈unguarded s s' ds es eq ds≈es

            aux-id : aux PrePtbId ≡ PrePtbId
            aux-id = PrePtb≡ _ _ (funExt (λ {
              (guarded x) → refl ;
              (unguarded s ds) → refl} ))

            aux-comp : ∀ δ δ' → aux (PrePtb∘ δ δ') ≡ PrePtb∘ (aux δ) (aux δ')
            aux-comp δ δ' = PrePtb≡ _ _ (funExt (λ {
              (guarded x) → refl ;
              (unguarded s ds) → refl}))


        -- TODO: complete these
        EndoD'→EndoD : MonoidHom (Endo D') (Endo D)
        EndoD'→EndoD = {!!}

        EndoD→EndoD' : MonoidHom (Endo D) (Endo D')
        EndoD→EndoD' = {!!}

        
        -- Interpretation of the syntactic perturbations as semantic
        -- perturbations, using the recursion principle for the free monoid.
        ---------------------------------------------------------------------
        interpDyn' : MonoidHom PtbD (Endo D')
        interpDyn' = Free.rec _ _ _ (Endo D')
          -- gen case
          (interp-guarded .fst ∘ i-gen)

          -- covariant cases
          (Sum.rec
            (λ {(s , p) → i-unguarded s p})
            (λ s → interp-guarded ∘hom (i-co s) ∘hom EndoD'→EndoD)) -- interp-guarded ∘hom i-co s))

          -- contravariant case
          (λ s → interp-guarded ∘hom (i-op s) ∘hom (EndoD'→EndoD ^opHom)) -- interp-guarded ∘hom i-op s)

        interpDyn : MonoidHom PtbD (Endo D)
        interpDyn = EndoD'→EndoD ∘hom interpDyn'

        -- Interpretation of the syntactic perturbations of C (next D)
        interpCD : MonoidHom PtbCD (Endo (C (next D)))
        interpCD = Indexed.rec _ _ (Endo (C (next D))) shape→hom
          where
            shape→hom : _
            shape→hom (inl (inl s)) = NatM→.h _ (i-gen s)
            shape→hom (inl (inr s)) = (i-co s) ∘hom interpDyn
            shape→hom (inr s)       = (i-op s) ∘hom (interpDyn ^opHom)

        --------------------
        -- Dyn as a ValType
        --------------------
        DV' : ValType ℓ ℓ ℓ ℓ-zero
        DV' = mkValType D' PtbD interpDyn'

        DV : ValType ℓ ℓ ℓ ℓ-zero
        DV = mkValType D PtbD interpDyn


      ----------------------------------------------------
      -- Relations, push-pull, and quasi-representability
      ----------------------------------------------------

        Σ-Unguarded : PosetBisim _ _ _
        Σ-Unguarded = (ΣP S-set (λ s → ΠP (|P| s) (λ p → D')))

        Σ-Unguarded-V : ValType ℓ ℓ ℓ ℓ-zero
        Σ-Unguarded-V = Ty.ΣV S (λ s → Ty.ΠV (P s) (λ p → DV'))

        iΣ : ⟨ PtbV Σ-Unguarded-V ⟩ → PBMor _ _
        iΣ m = interpV (Σ-Unguarded-V) .fst m .fst

        Guarded-V : ValType ℓ ℓ ℓ ℓ-zero
        Guarded-V = mkValType (C (next D)) PtbCD interpCD

        -- Unguarded and guarded embedding morphisms:
        emb'-unguarded : PBMor Σ-Unguarded D'
        emb'-unguarded .PBMor.f (s , ds) = unguarded s ds
        emb'-unguarded .PBMor.isMon {x = (s , ds)} {y = (s' , es)} (s≡s' , ds⊑es) =
          ⊑unguarded s s' ds es s≡s' aux
          where
            aux : ∀ p p' path → (ds p) ⊑D' (es p')
            aux p p' path = transport
              (λ i → eq1 (~ i) (path (~ i)) ⊑D' es p')
              (ds⊑es p')
              where
                eq1 : PathP
                  (λ i → ⟨ ΠP (|P| (s≡s' i)) (λ _ → D') ⟩)
                  ds
                  (subst (λ x → ⟨ ΠP (|P| x) (λ _ → D') ⟩) s≡s' ds)
                eq1 = subst-filler _ s≡s' ds
        emb'-unguarded .PBMor.pres≈ {x = (s , ds)} {y = (s' , es)} (s≡s' , ds≈es) =
          ≈unguarded s s' ds es s≡s' aux
          where
            aux : ∀ p p' path → (ds p) ≈D' (es p')
            aux p p' path = transport
              (λ i → eq1 (~ i) (path (~ i)) ≈D' es p')               
              (ds≈es p')
              where
                eq1 : PathP
                  (λ i → ⟨ ΠP (|P| (s≡s' i)) (λ _ → D') ⟩)
                  ds
                  (subst (λ x → ⟨ ΠP (|P| x) (λ _ → D') ⟩) s≡s' ds)                
                eq1 = subst-filler _ s≡s' ds


        emb'-guarded : PBMor (C (next D)) D'
        emb'-guarded .PBMor.f = guarded
        emb'-guarded .PBMor.isMon x≤y = ⊑guarded _ _ x≤y
        emb'-guarded .PBMor.pres≈ x≈y = ≈guarded _ _ x≈y

        -- Unguarded and guarded predomain relations
        inj-unguarded : PBRel Σ-Unguarded D' ℓ
        inj-unguarded = functionalRel emb'-unguarded Id rD'

        inj-guarded : PBRel (C (next D)) D' ℓ
        inj-guarded = functionalRel emb'-guarded Id rD'



        -- Push-pull for inj-unguarded
        -------------------------------
        inj-unguarded-PP : VRelPP Σ-Unguarded-V DV' ℓ
        inj-unguarded-PP .fst = inj-unguarded

        -- push
        inj-unguarded-PP .snd .fst =
          Indexed.elim
            (S .fst)
            (λ s → PtbV (ΠV (P s) (λ p → DV')))
            (Σl (VRelPtb Σ-Unguarded-V DV' inj-unguarded))
            push-s -- suffices to define a push for each s
          where
            Π-D : ∀ s' → ValType ℓ ℓ ℓ ℓ-zero
            Π-D s' = ΠV (P s') (λ p → DV')
            
            push-s : ∀ s → LocalSection (σ _ _ s) (Σl (VRelPtb Σ-Unguarded-V DV' _))
            push-s s = corecL
              push-hom
              (Indexed.elimLocal ⟨ P s ⟩ (λ _ → PtbV DV') _ (Cart.corec (σ ⟨ S ⟩ (λ s' → PtbV (Π-D s')) s) push-hom) {!!})
              where                
                push-hom : MonoidHom (PtbV (Π-D s)) PtbD
                push-hom = Indexed.rec _ _ _ (λ p → Free.coHom _ _ _ (inl (s , p)))

                ptb-Ps : ∀ p → MonoidHom PtbD (PtbV (Π-D s))
                ptb-Ps p = σ ⟨ P s ⟩ (λ _ → PtbV DV') p
                
                push-ps : ∀ (p : |P| s) → LocalSection
                  ((Cart.corec (σ ⟨ S ⟩ (PtbV ∘ Π-D) s) push-hom) ∘hom (ptb-Ps p))
                  (VRelPtb Σ-Unguarded-V DV' inj-unguarded)
                push-ps p = corecVRelPtb push-sq
                -- (λ pD → λ { (s₁ , ds) .(unguarded s₂ es) (⊑unguarded .s₁ s₂ .ds es s₁≡s₂ ds⊑es) → {!!}})
                  where
                    opaque
                      unfolding Indexed.σ Indexed.rec Indexed.elim
                      push-sq : ∀ (pD : ⟨ PtbD ⟩) → -- VRelPtbSq Σ-Unguarded-V DV' inj-unguarded {!!} {!!}
                        VRelPtbSq Σ-Unguarded-V DV' inj-unguarded
                          (σ ⟨ S ⟩ (PtbV ∘ Π-D) s .fst (ptb-Ps p .fst pD))
                          (push-hom .fst (ptb-Ps p .fst pD))               
                      push-sq pD (s₁ , ds) .(unguarded s₂ es) (⊑unguarded .s₁ s₂ .ds es s₁≡s₂ ds⊑es) =
                        -- aux s₁ s₂ s₁≡s₂ (dec-eq-S s s₂) -- ⊑unguarded ? ? ? ? ? ?
                        aux (dec-eq-S s s₁) (dec-eq-S s s₂)        
                          where
                            aux : -- ∀ (s₁ : |S|) (ds : ⟨ Π-D s₁ ⟩)
                                  --   (s₂ : |S|) (es : |P| s₂ → ⟨ D' ⟩)
                                  --   (s₁≡s₂ : s₁ ≡ s₂)
                                    ∀ (s≡s₁? : Dec (s ≡ s₁)) (s≡s₂? : Dec (s ≡ s₂)) →
                              inj-unguarded .PBRel.R
                                (iΣ (σ ⟨ S ⟩ (PtbV ∘ Π-D) s .fst (ptb-Ps p .fst pD)) .PBMor.f (s₁ , ds) )
                                (iU-helper s p (interpDyn' .fst pD .fst .PBMor.f) s₂ es s≡s₂?)
                                -- (interpDyn' .fst (push-hom .fst (ptb-Ps p .fst pD)) .fst .PBMor.f (unguarded s₂ es))
                            aux (yes s≡s₁) (yes s≡s₂) =
                              ⊑unguarded s₁ s₂ {!!} {!!} s₁≡s₂ (λ p₁ p₂ path →
                                aux2 p₁ p₂ path (dec-eq-P s₁ (subst _ s≡s₁ p) p₁) (dec-eq-P s₂ (subst _ s≡s₂ p) p₂) (dec-eq-S s s₁))
                                where
                                  aux2 : ∀ (p₁ : |P| s₁) (p₂ : |P| s₂) (path : PathP (λ i → |P| (s₁≡s₂ i)) p₁ p₂)
                                           (p≡p₁? : Dec ((subst _ s≡s₁ p) ≡ p₁))
                                           (p≡p₂? : Dec ((subst _ s≡s₂ p) ≡ p₂)) →
                                           (s≡s₁? : Dec (s ≡ s₁)) →
                                    -- iΣ (σ ⟨ S ⟩ (PtbV ∘ Π-D) s .fst (ptb-Ps p .fst pD)) .f (s₁ , ds) .snd p₁ ⊑D'                                   
                                    ((decRec
                                      (λ p≡p' →
                                        subst (λ z → ⟨ Endo (ValType→Predomain (ΠV (P z) (λ _ → DV'))) ⟩)
                                        p≡p' (fst (interpV (ΠV (P s) (λ _ → DV'))) (ptb-Ps p .fst pD)))
                                      (λ _ → PrePtbId)
                                      s≡s₁?) .fst .PBMor.f ds p₁)
                                      ⊑D' (decRec (λ p≡p' → interpDyn' .fst pD .fst .f (es p₂)) (λ _ → es p₂) p≡p₂?)         
                                  aux2 p₁ p₂ path (yes p≡p₁) (yes p≡p₂) (yes s≡s₁) =
                                    transport (cong₂ _⊑D'_ {!lem!} refl) (interpDyn' .fst pD .fst .PBMor.isMon (ds⊑es p₁ p₂ path))
                                      where
                                        goal : interpDyn' .fst pD .fst .f (ds p₁) ≡
                                         (subst (λ z → ⟨ Endo (ValType→Predomain (ΠV (P z) (λ _ → DV'))) ⟩)
                                                s≡s₁ (fst (interpV (ΠV (P s) (λ _ → DV'))) (ptb-Ps p .fst pD))) .fst .f ds p₁
                                        goal = sym {!!}

                                        lem1 : interpDyn' .fst pD .fst .f (ds p₁) ≡
                                               interpV (Π-D s) .fst (ptb-Ps p .fst pD) .fst .PBMor.f (subst (λ s'' → |P| s'' → ⟨ D' ⟩) {!!} ds) p
                                        lem1 = {!refl!}

                                        lem2 : PathP (λ i → ⟨ Endo (ValType→Predomain (Π-D (s≡s₁ i))) ⟩)
                                          (interpV (Π-D s) .fst (ptb-Ps p .fst pD))
                                          (subst (λ s'' → ⟨ Endo (ValType→Predomain (Π-D s'')) ⟩)
                                                 s≡s₁
                                                 (interpV (Π-D s) .fst (ptb-Ps p .fst pD)))
                                        lem2 = subst-filler
                                          (λ s'' → ⟨ Endo (ValType→Predomain (Π-D s'')) ⟩)
                                          s≡s₁
                                          (interpV (Π-D s) .fst (ptb-Ps p .fst pD))
                                  aux2 p₁ p₂ path _ (no p≡p₂) (no s≢s₁) = ds⊑es p₁ p₂ path
                                
                            aux (yes s≡s₁) (no s≢s₂) = ⊥.rec (s≢s₂ (s≡s₁ ∙ s₁≡s₂))
                            aux (no s≢s₁) (yes s≡s₂) = ⊥.rec (s≢s₁ (s≡s₂ ∙ (sym s₁≡s₂)))
                            aux (no s≢s₁) (no s≢s₂) =
                              ⊑unguarded s₁ s₂ {!!} es s₁≡s₂ (λ p₁ p₂ path → {!!})


                            
                                                             

        -- pull
        inj-unguarded-PP .snd .snd = {!!}


        -- Push-pull for inj-guarded
        -----------------------------
        inj-guarded-PP : VRelPP Guarded-V DV' ℓ
        inj-guarded-PP .fst = inj-guarded
        
        -- push
        inj-guarded-PP .snd .fst =
          Indexed.elim GuardedShapes GuardedShapes→Monoid
            (Σl (VRelPtb Guarded-V DV' inj-guarded)) push-s
          where     
              push-s : (x : GuardedShapes) →
                LocalSection
                  (σ GuardedShapes GuardedShapes→Monoid x)
                  (Σl (VRelPtb Guarded-V DV' inj-guarded))
              push-s (inl (inl s-gen)) =
                elimNatLS _ _ ((Free.gen _ _ _ s-gen) , (Sq→VRelPtb _ _ _ sq))
                -- corecL {Mᴰ = {!VRelPtb ? ? ?!}} (NatM→.h PtbD (Free.gen _ _ _ s-gen)) (corecVRelPtb {!λ n !})
                where
                  opaque
                    unfolding Indexed.rec Indexed.elim
                    sq : VRelPtbSq Guarded-V DV' inj-guarded
                      (σ _ _ (inl (inl s-gen)) .fst 1) (Free.gen _ _ _ s-gen)
                    sq x .(guarded y) (⊑guarded .x y x≤y) =
                      ⊑guarded
                        (i-gen s-gen .fst .f x)
                        (i-gen s-gen .fst .f y)
                        (i-gen s-gen .fst .PBMor.isMon x≤y)                   
              
              push-s (inl (inr s-co)) =
                corecL (Free.coHom _ _ _ (inr s-co)) (corecVRelPtb (λ pD → sq pD))
                where
                  opaque
                    unfolding Indexed.rec Indexed.elim
                    sq : (pD : ⟨ PtbD ⟩) →
                      VRelPtbSq Guarded-V DV' inj-guarded
                        (σ _ _ (inl (inr s-co)) .fst pD) (Free.coHom _ _ _ (inr s-co) .fst pD)
                    sq pD x .(guarded y) (⊑guarded .x y x≤y) =
                      ⊑guarded
                        (i-co s-co .fst (interpDyn .fst pD) .fst .PBMor.f x) -- (interpCD .fst _ .fst .PBMor.f x)
                        (i-co s-co .fst (interpDyn .fst pD) .fst .PBMor.f y)
                        (i-co s-co .fst (interpDyn .fst pD) .fst .PBMor.isMon x≤y)
                  
              push-s (inr s-op) =
                corecL (Free.opHom _ _ _ s-op) (corecVRelPtb (λ pD → sq pD))
                where
                  opaque
                    unfolding Indexed.rec Indexed.elim
                    sq : (pD : ⟨ PtbD ⟩) →
                      VRelPtbSq Guarded-V DV' inj-guarded
                        (σ _ _ (inr s-op) .fst pD) (Free.opHom _ _ _ s-op .fst pD)
                    sq pD x .(guarded y) (⊑guarded .x y x≤y) =
                      ⊑guarded
                        (i-op s-op .fst (interpDyn .fst pD) .fst .PBMor.f x)
                        (i-op s-op .fst (interpDyn .fst pD) .fst .PBMor.f y)
                        (i-op s-op .fst (interpDyn .fst pD) .fst .PBMor.isMon x≤y)

        -- pull
        inj-guarded-PP .snd .snd =
          Free.elimCases _ _ _ Σmonoid pull-gen pull-co {!!}
          where
            z : S'gen → ⟨ PtbCD ⟩
            z s-gen = Indexed.σ GuardedShapes GuardedShapes→Monoid (inl (inl s-gen)) .fst 1

            Σmonoid : Monoidᴰ PtbD ℓ
            Σmonoid = (Σr (VRelPtb Guarded-V DV' inj-guarded))
            opaque
              unfolding Indexed.σ Indexed.rec Indexed.elim

              -- Generator case
              pull-gen : (s-gen : S'gen) →
                Monoidᴰ.eltᴰ Σmonoid (Free.gen _ _ _ s-gen)
              pull-gen s-gen = (z s-gen) , (Sq→VRelPtb Guarded-V DV' inj-guarded sq)
                where
                  sq : VRelPtbSq Guarded-V DV' inj-guarded (z s-gen) (Free.gen _ _ _ s-gen)
                  sq x .(guarded y) (⊑guarded .x y x≤y) =
                    ⊑guarded (i-gen s-gen .fst .f x) (i-gen s-gen .fst .f y) (i-gen s-gen .fst .PBMor.isMon x≤y)

              -- Covariant cases (corresponding to the unguarded perturbations as well as
              -- the covariant guarded perturbations)
              pull-co : (b : (Σ[ s ∈ |S| ] (|P| s)) ⊎ S'co) →
                LocalSection
                  (coHom S'gen (Σ-syntax |S| |P| ⊎ S'co) S'op b)
                  Σmonoid
              pull-co (inl (s , p)) =
               
                corecR
                  ε-hom -- Goal: Monoid Hom PtbD PtbCD. Map everything to the identity element of PtbCD
                  (corecVRelPtb (λ ptb → λ { x .(guarded y) (⊑guarded .x y xRy) → ⊑guarded x y xRy}))
                
              pull-co (inr s-co) =
                corecR {ϕ' = coHom S'gen _ _ (inr s-co)}
                  (Indexed.σ GuardedShapes GuardedShapes→Monoid (inl (inr s-co))) -- Goal: MonoidHom PtbD PtbCD
                  (corecVRelPtb (λ pD → λ { x .(guarded y) (⊑guarded .x y x≤y) →
                    ⊑guarded
                      (i-co s-co .fst (interpDyn .fst pD) .fst .f x)
                      (i-co s-co .fst (interpDyn .fst pD) .fst .f y)
                      (i-co s-co .fst (interpDyn .fst pD) .fst .PBMor.isMon x≤y)}))


              -- Contravariant case
              pull-op : {!!}
              pull-op = {!!}


        -- Quasi-Representability
        --------------------------
        inj-unguarded-VRel : ValRel Σ-Unguarded-V DV' ℓ
        inj-unguarded-VRel .fst = inj-unguarded-PP

        -- Quasi-left-representability of inj-unguarded:
        inj-unguarded-VRel .snd .fst = mkLeftRepV
          Σ-Unguarded-V DV' inj-unguarded emb'-unguarded δl UpR δr UpL
          where
            rΣ : PBRel _ _ _
            rΣ = idPRel Σ-Unguarded

            δl : ⟨ PtbV Σ-Unguarded-V ⟩
            δl = PtbV Σ-Unguarded-V .snd .MonoidStr.ε

            δr : ⟨ PtbD ⟩
            δr = PtbD .snd .MonoidStr.ε

            UpR : PBSq rΣ inj-unguarded {!Id!} emb'-unguarded
            UpR (s , ds) (s' , es) (s≡s' , ds⊑es) = {!!}
            
            UpL : PBSq inj-unguarded rD' emb'-unguarded Id
            UpL = SqV-functionalRel emb'-unguarded Id rD'

        -- Quasi-right-representability of F(inj-unguarded)
        inj-unguarded-VRel .snd .snd = {!!}



        inj-guarded-VRel : ValRel {!!} DV' {!!}
        inj-guarded-VRel = {!!}
