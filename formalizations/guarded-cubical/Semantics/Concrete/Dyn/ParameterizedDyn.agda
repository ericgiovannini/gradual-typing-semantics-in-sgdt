{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}


open import Common.Later

module Semantics.Concrete.Dyn.ParameterizedDyn (k : Clock) where

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
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Constructions renaming (ℕ to NatP)
open import Semantics.Concrete.Predomain.Combinators hiding (U)
open import Semantics.Concrete.Predomain.Morphism hiding (_$_)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.FreeErrorDomain k


open import Semantics.Concrete.Perturbation.Semantic k
open import Semantics.Concrete.Types k as Ty hiding (Unit ; _×_)
open import Semantics.Concrete.Perturbation.Relation k as RelPP
open import Semantics.Concrete.Perturbation.QuasiRepresentation k
open import Semantics.Concrete.Relations k as Rel


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

open F-ob
open F-mor
open F-rel
open F-sq

open ExtAsEDMorphism

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


  DynTy→Sum : ∀ X → DynTy X → ((Σ[ s ∈ |S| ] (|P| s → DynTy X)) Sum.⊎ X)
  DynTy→Sum X (guarded x) = inr x
  DynTy→Sum X (unguarded s ds) = inl (s , ds)

  Sum→DynTy : ∀ X → ((Σ[ s ∈ |S| ] (|P| s → DynTy X)) Sum.⊎ X) → DynTy X
  Sum→DynTy X (inl (s , ds)) = unguarded s ds
  Sum→DynTy X (inr x) = guarded x

  retr : ∀ {X} → retract (DynTy→Sum X) (Sum→DynTy X)
  retr (guarded x) = refl
  retr (unguarded s ds) = refl

  sec : ∀ {X} → section (DynTy→Sum X) (Sum→DynTy X)
  sec (inl (s , ds)) = refl
  sec (inr x) = refl

  injective : ∀ {X} d d' → DynTy→Sum X d ≡ DynTy→Sum X d' → d ≡ d'
  injective d d' H = sym (retr d) ∙ (cong (Sum→DynTy _) H) ∙ retr d'


  -- isSet for DynTy
  
  module _ (X : Type ℓ) where

    Shape : Type ℓ
    Shape = X Sum.⊎ |S|
      
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

    tree-retr : retract Dyn→Tree Tree→Dyn
    tree-retr (guarded x) = refl
    tree-retr (unguarded s ds) =
      cong₂ unguarded refl (funExt (λ p → tree-retr (ds p)))

    isSetDynAsTree : isSet X → isSet DynAsTree
    isSetDynAsTree isSetX = isOfHLevelSuc-IW 1 (λ _ → isSetShape) tt
      where
        isSetShape : isSet Shape
        isSetShape = isSet⊎ isSetX isSetS

    isSetDynTy : isSet X → isSet (DynTy X)
    isSetDynTy isSetX =
      isSetRetract Dyn→Tree Tree→Dyn tree-retr (isSetDynAsTree isSetX)


  module _ (X : Predomain ℓ ℓ ℓ) where

   private
     |D| = DynTy ⟨ X ⟩
     module X = PredomainStr (X .snd)

     -- Sum = ((Σ[ s ∈ |S| ] (|P| s → |D|)) ⊎ ⟨ X ⟩)

     Pi : _ → _
     Pi s = |P| s → |D|

     Sigma : _
     Sigma = Σ[ s ∈ |S| ] Pi s

     Sum = Sigma Sum.⊎ ⟨ X ⟩


  
   -- Ordering relation + properties
   ----------------------------------
   {-# TERMINATING #-}
   -- Note that these are terminating because Π-ord only uses
   -- _⊑d_ at strictly smaller subterms.
   _⊑d_ : |D| → |D| → Type ℓ
   ⊑sigma : Sigma → Sigma → Type ℓ
   ⊑pi : ∀ s → Pi s → Pi s → Type ℓ
   _⊑sum_ : Sum → Sum → Type ℓ

   d ⊑d d' = (DynTy→Sum ⟨ X ⟩ d) ⊑sum (DynTy→Sum ⟨ X ⟩ d')
   ⊑pi s = Π-ord (|P| s) (λ _ → |D|) (λ _ → _⊑d_)
   ⊑sigma = Σ-ord S-set Pi ⊑pi
   _⊑sum_ = ⊎-ord ⊑sigma  X._≤_


   -- ⊑d→⊑sum : ∀ d d' → d ⊑d

   {-# TERMINATING #-}
   ⊑d-refl     : isRefl _⊑d_
   ⊑pi-refl    : ∀ s → isRefl (⊑pi s)
   ⊑sigma-refl : isRefl ⊑sigma
   ⊑sum-refl   : isRefl _⊑sum_

   ⊑d-refl d   = ⊑sum-refl (DynTy→Sum _ d)
   ⊑pi-refl s  = Π-ord-refl _ _ (λ _ → _⊑d_) (λ _ → ⊑d-refl)
   ⊑sigma-refl = Σ-ord-refl _ _ ⊑pi ⊑pi-refl
   ⊑sum-refl   = ⊎-ord-refl _ _ ⊑sigma-refl X.is-refl


   {-# TERMINATING #-}
   ⊑d-prop-valued     : isPropValued _⊑d_
   ⊑pi-prop-valued    : ∀ s → isPropValued (⊑pi s)
   ⊑sigma-prop-valued : isPropValued ⊑sigma
   ⊑sum-prop-valued   : isPropValued _⊑sum_

   ⊑d-prop-valued d d' = ⊑sum-prop-valued (DynTy→Sum ⟨ X ⟩ d) (DynTy→Sum ⟨ X ⟩ d') --⊑sum-prop (DynTy→Sum _ d)
   ⊑pi-prop-valued s   = Π-ord-prop-valued _ _ (λ _ → _⊑d_) (λ _ → ⊑d-prop-valued)
   ⊑sigma-prop-valued  = Σ-ord-prop-valued _ _ ⊑pi ⊑pi-prop-valued
   ⊑sum-prop-valued    = ⊎-ord-prop-valued _ _ ⊑sigma-prop-valued X.is-prop-valued


   {-# TERMINATING #-}
   ⊑d-antisym     : isAntisym _⊑d_
   ⊑pi-antisym    : ∀ s → isAntisym (⊑pi s)
   ⊑sigma-antisym : isAntisym ⊑sigma
   ⊑sum-antisym   : isAntisym _⊑sum_

   ⊑d-antisym d d' d⊑d' d'⊑d = injective d d' (⊑sum-antisym _ _ d⊑d' d'⊑d)
   ⊑pi-antisym s   = Π-ord-antisym _ _ (λ _ → _⊑d_) (λ _ → ⊑d-antisym)
   ⊑sigma-antisym  = Σ-ord-antisym _ _ ⊑pi ⊑pi-antisym
   ⊑sum-antisym    = ⊎-ord-antisym _ _ ⊑sigma-antisym X.is-antisym


   {-# TERMINATING #-}
   ⊑d-trans     : isTrans _⊑d_
   ⊑pi-trans    : ∀ s → isTrans (⊑pi s)
   ⊑sigma-trans : isTrans ⊑sigma
   ⊑sum-trans   : isTrans _⊑sum_

   ⊑d-trans d₁ d₂ d₃ d₁≤d₂ d₂≤d₃ = ⊑sum-trans _ _ _ d₁≤d₂ d₂≤d₃
   ⊑pi-trans s  = Π-ord-trans _ _ (λ _ → _⊑d_) (λ _ → ⊑d-trans)
   ⊑sigma-trans = Σ-ord-trans _ _ ⊑pi ⊑pi-trans
   ⊑sum-trans   = ⊎-ord-trans _ _ ⊑sigma-trans X.is-trans


   -- Bisimilarity relation + properties
   --------------------------------------
   
   {-# TERMINATING #-}
   _≈d_ : |D| → |D| → Type ℓ
   ≈sigma : Sigma → Sigma → Type ℓ
   ≈pi : ∀ s → Pi s → Pi s → Type ℓ
   _≈sum_ : Sum → Sum → Type ℓ

   d ≈d d' = (DynTy→Sum ⟨ X ⟩ d) ≈sum (DynTy→Sum ⟨ X ⟩ d')
   ≈pi s = Π-bisim (|P| s) (λ _ → |D|) (λ _ → _≈d_)
   ≈sigma = Σ-bisim S-set Pi ≈pi
   _≈sum_ = ⊎-bisim ≈sigma  X._≈_

   {-# TERMINATING #-}
   ≈d-refl     : isRefl _≈d_
   ≈pi-refl    : ∀ s → isRefl (≈pi s)
   ≈sigma-refl : isRefl ≈sigma
   ≈sum-refl   : isRefl _≈sum_

   ≈d-refl d   = ≈sum-refl (DynTy→Sum _ d)
   ≈pi-refl s  = Π-bisim-refl _ _ (λ _ → _≈d_) (λ _ → ≈d-refl)
   ≈sigma-refl = Σ-bisim-refl _ _ ≈pi ≈pi-refl
   ≈sum-refl   = ⊎-bisim-refl _ _ ≈sigma-refl X.is-refl-Bisim

   {-# TERMINATING #-}
   ≈d-prop-valued     : isPropValued _≈d_
   ≈pi-prop-valued    : ∀ s → isPropValued (≈pi s)
   ≈sigma-prop-valued : isPropValued ≈sigma
   ≈sum-prop-valued   : isPropValued _≈sum_

   ≈d-prop-valued d d' = ≈sum-prop-valued (DynTy→Sum ⟨ X ⟩ d) (DynTy→Sum ⟨ X ⟩ d')
   ≈pi-prop-valued s   = Π-bisim-prop-valued _ _ (λ _ → _≈d_) (λ _ → ≈d-prop-valued)
   ≈sigma-prop-valued  = Σ-bisim-prop-valued _ _ ≈pi ≈pi-prop-valued
   ≈sum-prop-valued    = ⊎-bisim-prop-valued _ _ ≈sigma-prop-valued X.is-prop-valued-Bisim

   {-# TERMINATING #-}
   ≈d-sym     : isSym _≈d_
   ≈pi-sym    : ∀ s → isSym (≈pi s)
   ≈sigma-sym : isSym ≈sigma
   ≈sum-sym   : isSym _≈sum_

   ≈d-sym d d' d≈d' = ≈sum-sym _ _ d≈d'
   ≈pi-sym s   = Π-bisim-sym _ _ (λ _ → _≈d_) (λ _ → ≈d-sym)
   ≈sigma-sym  = Σ-bisim-sym _ _ ≈pi ≈pi-sym
   ≈sum-sym    = ⊎-bisim-sym _ _ ≈sigma-sym X.is-sym

   --------------------------------
   -- Defining the predomain:
   --------------------------------
   DynPredom : Predomain ℓ ℓ ℓ
   DynPredom .fst = |D|
   DynPredom .snd = predomainstr (isSetDynTy ⟨ X ⟩ X.is-set)
      _⊑d_ (isorderingrelation ⊑d-prop-valued ⊑d-refl ⊑d-trans ⊑d-antisym)
      _≈d_ (isbisim ≈d-refl ≈d-sym ≈d-prop-valued)

   rDyn : PRel DynPredom DynPredom ℓ
   rDyn = idPRel DynPredom

   SigmaPredom : Predomain ℓ ℓ ℓ
   SigmaPredom = ΣP S-set (λ s → ΠP (|P| s) (λ _ → DynPredom))

   SumPredom : Predomain ℓ ℓ ℓ
   SumPredom = SigmaPredom ⊎p X

   -- Morphisms between DynP and SumP
   DynP→SumP : PMor DynPredom SumPredom
   DynP→SumP .PMor.f = DynTy→Sum ⟨ X ⟩
   DynP→SumP .PMor.isMon d⊑d' = d⊑d'
   DynP→SumP .PMor.pres≈ d≈d' = d≈d'

   SumP→DynP : PMor SumPredom DynPredom
   SumP→DynP .PMor.f = Sum→DynTy ⟨ X ⟩
   SumP→DynP .PMor.isMon {x = sum₁} {y = sum₂} sum₁≤sum₂ =
     transport (λ i → SumPredom .snd .PredomainStr._≤_ (sym (sec sum₁) i) (sym (sec sum₂) i)) sum₁≤sum₂
   SumP→DynP .PMor.pres≈ {x = sum₁} {y = sum₂} sum₁≈sum₂ =
     transport (λ i → SumPredom .snd .PredomainStr._≈_ (sym (sec sum₁) i) (sym (sec sum₂) i)) sum₁≈sum₂

   -- Predomain isomorphism between DynP and SumP
   Iso-DynP-SumP : PredomIso DynPredom SumPredom
   Iso-DynP-SumP .PredomIso.fun = DynP→SumP
   Iso-DynP-SumP .PredomIso.inv = SumP→DynP
   Iso-DynP-SumP .PredomIso.invRight = sec
   Iso-DynP-SumP .PredomIso.invLeft = retr

   Iso-SumP-DynP : PredomIso SumPredom DynPredom
   Iso-SumP-DynP = PredomIso-Inv Iso-DynP-SumP

   -- Embeddings
   emb-Sigma : PMor SigmaPredom DynPredom
   emb-Sigma = SumP→DynP ∘p σ1

   emb-X : PMor X DynPredom
   emb-X = SumP→DynP ∘p σ2

   -- Predomain relations
   inj-SigmaP : PRel SigmaPredom DynPredom ℓ
   inj-SigmaP = functionalRel emb-Sigma Id rDyn

   inj-XP : PRel X DynPredom ℓ
   inj-XP = functionalRel emb-X Id rDyn

   -- Projections
   proj-SigmaP : ErrorDomMor (F-ob DynPredom) (F-ob SigmaPredom)
   proj-SigmaP = Ext ((Case' η-mor (K _ ℧)) ∘p DynP→SumP)

   proj-XP : ErrorDomMor (F-ob DynPredom) (F-ob X)
   proj-XP = Ext ((Case' (K _ ℧) η-mor) ∘p DynP→SumP)

  module _ (C : ▹ (Predomain ℓ ℓ ℓ) → Predomain ℓ ℓ ℓ) where

    DP : Predomain ℓ ℓ ℓ
    DP = fix (λ D~ → DynPredom (C D~))

    DP' : Predomain ℓ ℓ ℓ
    DP' = DynPredom (C (next DP))

    -- Unfolding
    unfold-DP : DP ≡ DP'
    unfold-DP = fix-eq (λ D~ → DynPredom (C D~))

    DP→DP' : PMor DP DP'
    DP→DP' = mTransport unfold-DP

    DP'→DP : PMor DP' DP
    DP'→DP = mTransport (sym unfold-DP)

    unfold-fold :  DP'→DP ∘p DP→DP' ≡ Id
    unfold-fold = eqPMor _ _ (funExt (λ d → transport⁻Transport (λ i → ⟨ unfold-DP i ⟩) d ))

    fold-unfold :  DP→DP' ∘p DP'→DP ≡ Id
    fold-unfold = eqPMor _ _ (funExt λ d → transportTransport⁻ (λ i → ⟨ unfold-DP i ⟩) d)

    DP'≅DP : PredomIso DP' DP
    DP'≅DP .PredomIso.fun = DP'→DP
    DP'≅DP .PredomIso.inv = DP→DP'
    DP'≅DP .PredomIso.invRight = funExt⁻ (cong PMor.f unfold-fold)
    DP'≅DP .PredomIso.invLeft = funExt⁻ (cong PMor.f fold-unfold)

    EndoDP→EndoDP' : MonoidHom (Endo DP) (Endo DP')
    EndoDP→EndoDP' = PredomIso→EndoHom (PredomIso-Inv DP'≅DP)

    EndoDP'→EndoDP : MonoidHom (Endo DP') (Endo DP)
    EndoDP'→EndoDP = PredomIso→EndoHom DP'≅DP

    -- Identity relation on Dyn
    rD' : PRel DP' DP' ℓ
    rD' = idPRel DP'

    _⊑D'_ = rD' .PRel.R
    _≈D'_ = _≈d_ (C (next DP))


   -- Perturbations for Dyn
   --------------------------
   
   -- P_D ≅ (⊕ᵢ [s ∈ S] ⊕ᵢ [p ∈ P s] P_D) ⊕ P_X

   -- where P_X = (⊕ᵢ Sgen (FM 1)) ⊕ (⊕ᵢ (Sco P_D)) ⊕ (⊕ᵢ (Sop P_D^op))

    module _ (Sgen Sco Sop : Type ℓ-zero) where

      covariant : Type ℓ-zero
      covariant = ((Σ[ s ∈ |S| ] |P| s)) Sum.⊎ Sco

      -- Free monoid on one generator
      FreeMonOn1 : Monoid ℓ-zero
      FreeMonOn1 = Free.FM Unit ⊥ ⊥

      PtbD : Monoid ℓ-zero
      PtbD = Free.FM Sgen covariant Sop

      -- Submonoid of perturbations corresponding to (Σ S. Π P s . D)
      PtbSigma : Monoid ℓ-zero
      PtbSigma = ⊕ᵢ |S| (λ s → ⊕ᵢ (|P| s) (λ _ → PtbD))

      -- Equivalently, we could have defined this using a single ⊕ᵢ over the sigma type:
      -- PtbSigma' : Monoid ℓ-zero
      -- PtbSigma' = ⊕ᵢ (Σ[ s ∈ |S| ] |P| s) (λ _ → PtbD)

      -- Submonoid of perturbations corresponding to X
      PtbX : Monoid ℓ-zero
      PtbX = (⊕ᵢ Sgen (λ _ → FreeMonOn1))
        FP.⊕ (⊕ᵢ Sco  (λ _ → PtbD))
        FP.⊕ (⊕ᵢ Sop  (λ _ → PtbD ^op))
        -- We could have equivalently defined this instead using one ⊕ᵢ over the
        -- coproduct of Sgen, Sco, and Sop

      inj-gen : MonoidHom (⊕ᵢ Sgen (λ _ → FreeMonOn1)) PtbX
      inj-gen = i₁

      inj-co : MonoidHom (⊕ᵢ Sco (λ _ → PtbD)) PtbX
      inj-co = i₂ ∘hom i₁

      inj-op : MonoidHom (⊕ᵢ Sop (λ _ → PtbD ^op)) PtbX
      inj-op = i₂ ∘hom i₂


      PtbSum : Monoid ℓ-zero
      PtbSum = PtbSigma FP.⊕ PtbX

      -- Given s : S and p : P s, we can embed a perturbation on Dyn to a perturbation in the indexed coproduct
      inj-ptb-sigma : ∀ s p → MonoidHom PtbD PtbSigma
      inj-ptb-sigma s p = (Indexed.σ |S| (λ s' → ⊕ᵢ (|P| s') (λ _ → PtbD)) s) ∘hom (Indexed.σ (|P| s) (λ _ → PtbD) p)
      -- Goal: MonoidHom PtbD PtbSigma
      --
      --         σ _ _ p                              σ _ _ s
      -- PtbD ------------> ⊕ᵢ (|P| s) (λ _ → PtbD) ----------->  ⊕ᵢ |S| (λ s' → ⊕ᵢ (|P| s') (λ _ → PtbD))

      -- Going from a perturbation of Dyn to either a perturbation of
      -- the sigma or a perturbation of X. We define this by cases on
      -- the perturbation of Dyn.
      PtbD→PtbSum : MonoidHom PtbD PtbSum
      PtbD→PtbSum = Free.cases _ _ _ _
        (λ s-gen → i₂ .fst (inj-gen .fst (σ _ _ s-gen .fst (Free.gen _ _ _ tt))))
        (λ { (inl (s , p)) → i₁ ∘hom (inj-ptb-sigma s p)
           ; (inr s-co) →    i₂ ∘hom inj-co ∘hom (σ _ _ s-co)})
        (λ s-op → i₂ ∘hom inj-op ∘hom (σ _ _ s-op))

      -- Homomorphism from PtbD to PtbSigma
      PtbD→PtbSigma : MonoidHom PtbD PtbSigma
      PtbD→PtbSigma = (FP.rec (idMon _) ε-hom) ∘hom PtbD→PtbSum

      PtbD→PtbX : MonoidHom PtbD PtbX
      PtbD→PtbX = (FP.rec ε-hom (idMon _)) ∘hom PtbD→PtbSum

      -- Homomorphism from PtbSigma to PtbD
      PtbSigma→PtbD : MonoidHom PtbSigma PtbD
      PtbSigma→PtbD = Indexed.rec |S| (λ s → ⊕ᵢ (|P| s) (λ _ → PtbD)) PtbD
        (λ s → Indexed.rec (|P| s) (λ _ → PtbD) PtbD (λ p → Free.coHom _ _ _ (inl (s , p))))

      PtbX→PtbD : MonoidHom PtbX PtbD
      PtbX→PtbD = FP.rec
        (Indexed.rec Sgen (λ _ → FreeMonOn1) PtbD (λ s-gen → Free.rec ⊤ ⊥ ⊥ PtbD (λ _ → Free.gen _ _ _ s-gen) ⊥.rec ⊥.rec))
        (FP.rec
          (Indexed.rec Sco (λ _ → PtbD) PtbD (λ s-co → Free.coHom _ _ _ (inr s-co)))
          (Indexed.rec Sop (λ _ → PtbD ^op) PtbD (λ s-op → Free.opHom _ _ _ s-op)))

      PtbSum→PtbD : MonoidHom PtbSum PtbD
      PtbSum→PtbD = FP.rec PtbSigma→PtbD PtbX→PtbD


      opaque
        unfolding Indexed.rec Indexed.elim

        monoid-inverse-1 : PtbSum→PtbD ∘hom PtbD→PtbSum ≡ idMon PtbD
        monoid-inverse-1 = Free.cases-ind _ _ _
           (λ s-gen → refl)
           (λ { (inl (s , p)) → eqMonoidHom _ _ refl
              ; (inr s-co) → eqMonoidHom _ _ refl})
           λ s-op → eqMonoidHom _ _ refl

        monoid-inverse-2 : PtbD→PtbSum ∘hom PtbSum→PtbD ≡ idMon PtbSum
        monoid-inverse-2 = FP.ind
          -- PtbSigma
          (Indexed.ind |S| (λ s → ⊕ᵢ (|P| s) (λ _ → PtbD)) (λ s → Indexed.ind (|P| s) (λ _ → PtbD) (λ p → eqMonoidHom _ _ refl)))

          -- PtbX
          (FP.ind (Indexed.ind Sgen (λ _ → FreeMonOn1) (λ s-gen → Free.cases-ind ⊤ ⊥ ⊥ (λ _ → refl) (λ bot → ⊥.rec bot) (λ bot → ⊥.rec bot)))
            (FP.ind (Indexed.ind Sco (λ _ → PtbD)     (λ s-co → eqMonoidHom _ _ refl))
                    (Indexed.ind Sop (λ _ → PtbD ^op) (λ s-op → eqMonoidHom _ _ refl))))


      -- Interpretation of the perturbations as endomorphisms
      ---------------------------------------------------------
      module _
        (igen : Sgen → ⟨ Endo (C (next DP)) ⟩)
        (ico  : Sco →  MonoidHom  (Endo DP)      (Endo (C (next DP))))
        (iop  : Sop →  MonoidHom ((Endo DP) ^op) (Endo (C (next DP))))
        where

        SigmaP       = SigmaPredom   (C (next DP))
        SumP         = SumPredom     (C (next DP))
        Iso-SumP-DP' = Iso-SumP-DynP (C (next DP))

        {-# TERMINATING #-}
        iDyn' : MonoidHom PtbD (Endo DP')
        iDyn : MonoidHom PtbD (Endo DP)
        iSigma : MonoidHom PtbSigma (Endo SigmaP)
        iX : MonoidHom PtbX (Endo (C (next DP)))
        iSum : MonoidHom PtbSum (Endo SumP)

        iX = FP.rec (Indexed.rec _ _ _ (λ s-gen → Free.rec _ _ _ _ (λ _ → igen s-gen) ⊥.rec ⊥.rec))
             (FP.rec (Indexed.rec _ _ (Endo (C (next DP))) (λ s-co → (ico s-co) ∘hom iDyn))
                     (Indexed.rec _ _ (Endo (C (next DP))) (λ s-op → (iop s-op) ∘hom (iDyn ^opHom))))

        iSigma = Indexed.rec _ _ (Endo SigmaP)
          (λ s → (Σ-SemPtb S-set dec-eq-S s) ∘hom
            (Indexed.rec _ _ (Endo (ΠP (|P| s) (λ _ → DP')))
              (λ p → (Π-SemPtb (|P| s) (dec-eq-P s) p) ∘hom iDyn')))

        iDyn' = (PredomIso→EndoHom Iso-SumP-DP')
                 ∘hom iSum
                 ∘hom PtbD→PtbSum

        iSum = (FP.rec
                 (⊎A-SemPtb ∘hom iSigma)
                 (A⊎-SemPtb ∘hom iX))

        iDyn = EndoDP'→EndoDP ∘hom iDyn'


        module Definitions where

          DynV : ValType ℓ ℓ ℓ ℓ-zero
          DynV = mkValType DP PtbD iDyn

          DynV' : ValType ℓ ℓ ℓ ℓ-zero
          DynV' = mkValType DP' PtbD iDyn'

          SigmaV : ValType ℓ ℓ ℓ ℓ-zero
          SigmaV = mkValType SigmaP PtbSigma iSigma
          -- SigmaV = ΣV S λ s → ΠV (P s) (λ _ → DynV')

          XV : ValType ℓ ℓ ℓ ℓ-zero
          XV = mkValType (C (next DP)) PtbX iX

          SumV : ValType ℓ ℓ ℓ ℓ-zero
          SumV = mkValType SumP PtbSum iSum
          -- SumV = SigmaV Types.⊎ XV
   

          DynV'≅DynV : StrongIsoV DynV' DynV
          DynV'≅DynV = mkStrongIsoV DP'≅DP idMonoidIso eq
            where
              eq : iDyn ∘hom (idMon PtbD) ≡ PredomIso→EndoHom DP'≅DP ∘hom iDyn'
              eq = ∘hom-IdR iDyn

          VRel-DynV'-DynV : ValRel DynV' DynV ℓ
          VRel-DynV'-DynV = ValTyIso→ValRel DynV'≅DynV             

          VRel-DynV-DynV' : ValRel DynV DynV' ℓ
          VRel-DynV-DynV' = ValTyIso→ValRel (StrongIsoV-Inv DynV'≅DynV)


          -- Now we construct the ValType relations corresponding to the injections
          -- for Sigma and X.

          -- First we show that there is a relation between the sum type SigmaV ⊎ XV
          -- and DynV'
          -- We do so by constructing an isomorphism of value types:
          VRel-SumV-DynV' : ValRel SumV DynV' ℓ
          VRel-SumV-DynV' = ValTyIso→ValRel isom
            where
              monIso : MonoidIso PtbSum PtbD
              monIso = monoidiso PtbSum→PtbD PtbD→PtbSum
                (funExt⁻ (cong fst monoid-inverse-1))
                (funExt⁻ (cong fst monoid-inverse-2))

              eq : iDyn' ∘hom PtbSum→PtbD ≡ (PredomIso→EndoHom Iso-SumP-DP') ∘hom iSum
              eq = ((PredomIso→EndoHom Iso-SumP-DP') ∘hom (iSum ∘hom PtbD→PtbSum)) ∘hom PtbSum→PtbD
                   ≡⟨ ∘hom-Assoc _ _ _ ⟩
                     (PredomIso→EndoHom Iso-SumP-DP') ∘hom ((iSum ∘hom PtbD→PtbSum) ∘hom PtbSum→PtbD)
                   ≡⟨ cong₂ _∘hom_ refl (∘hom-Assoc _ _ _) ⟩
                   (PredomIso→EndoHom Iso-SumP-DP') ∘hom (iSum ∘hom (PtbD→PtbSum ∘hom PtbSum→PtbD))
                   ≡⟨ cong₂ _∘hom_ refl (cong₂ _∘hom_ refl monoid-inverse-2) ⟩
                   _
                   ≡⟨ cong₂ _∘hom_ refl (∘hom-IdR _) ⟩ _ ∎

              isom : StrongIsoV SumV DynV'
              isom = mkStrongIsoV Iso-SumP-DP' monIso eq


          -- Now we can define the desired injection relations SigmaV --|-- DynV
          -- and XV --|-- DynV by composing the above relation with the relations
          -- induced by inl and inr, respectively, and finally composing with the
          -- relation between DynV' and DynV.
          --
          --                      inl                   VRel-SumV-DynV'    VRel-DynV'-DynV
          -- E.g. we have SigmaV --|-- (SigmaV ⊎ XV = SumV) --|-- DynV'  --------|-------- DynV
          --
          inj-SigmaV : ValRel SigmaV DynV ℓ
          inj-SigmaV = Rel.⊙V (Rel.⊙V Rel.⊎-inl VRel-SumV-DynV') VRel-DynV'-DynV

          inj-XV : ValRel XV DynV ℓ
          inj-XV = Rel.⊙V (Rel.⊙V Rel.⊎-inr VRel-SumV-DynV') VRel-DynV'-DynV


