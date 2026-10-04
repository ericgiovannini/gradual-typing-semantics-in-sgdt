{-

  Denotational semantics of type precision as quasi-representable
  predomain relations with a push-pull structure.
  
-}
{-# OPTIONS --rewriting --lossy-unification --allow-unsolved-metas #-}
open import Common.Later
module Syntax.FineGrained.Denotation.TypePrecision (k : Clock) where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Foundations.Structure
open import Cubical.Data.List

open import Syntax.Types
open import Syntax.FineGrained.Denotation.Types k
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Relations k
open import Semantics.Concrete.Dyn.DynInstantiated k

-- Type precision derivations are interpreted as value relations:
-- reflexivity and transitivity as the identity and composition of
-- relations, the arrow rule by the functorial action of U(_ ⟶ F _) on
-- relations, and the two injections into the dynamic type by the
-- relations injNat and injArr. The latter relates ▹ U(D ⟶ F D) to D, so
-- it is precomposed with the relation Next between U(D ⟶ F D) and
-- ▹ U(D ⟶ F D).
⟦_⟧ty⊑ : ∀ {S T} → S ⊑ T → ValRel ⟦ S ⟧ty ⟦ T ⟧ty ℓ-zero
⟦ refl-⊑ ⟧ty⊑ = IdV _
⟦ trans-⊑ c c₁ ⟧ty⊑ = ⊙V ⟦ c ⟧ty⊑ ⟦ c₁ ⟧ty⊑
⟦ c ⇀ d ⟧ty⊑ = U (⟦ c ⟧ty⊑ ⟶ F ⟦ d ⟧ty⊑)
⟦ inj-nat ⟧ty⊑ = injNat
⟦ inj-arr ⟧ty⊑ = ⊙V (Next ⟦ dyn ⇀ dyn ⟧ty) injArr

⟦_⟧ctx⊑ : ∀ {Γ Δ} → Γ ⊑ctx Δ → ValRel ⟦ Γ ⟧ctx ⟦ Δ ⟧ctx ℓ-zero
⟦ [] ⟧ctx⊑ = IdV _
⟦ c ∷ C ⟧ctx⊑ = ⟦ C ⟧ctx⊑ × ⟦ c ⟧ty⊑

-- Equal derivations denote relations represented by the same
-- embedding. The unit and associativity laws hold because the
-- embedding of a composite is the composite of the embeddings, and
-- the ⇀-refl law because the embedding of U (Id ⟶ F Id) is the
-- identity (U⟶F-Id-emb).
--
-- The remaining law ⇀-trans does not hold in this strong form: the
-- projection representing F (c ⊙ c') (CompositionLemmaF) is the
-- composite of the two projections conjugated by perturbations, so
-- the embedding of (c ⊙ c') ⇀ (d ⊙ d') differs from that of
-- (c ⇀ d) ⊙ (c' ⇀ d') by perturbations. The two relations are
-- quasi-order-equivalent (Lemma D.18 in the paper), which is the
-- notion ValRel≈ would have to be weakened to.
⟦_⟧ty⊑-≈ : ∀ {S T} {c d : S ⊑ T} → c ≈ d → ValRel≈ ⟦ c ⟧ty⊑ ⟦ d ⟧ty⊑
⟦ sym≈ p ⟧ty⊑-≈ = sym ⟦ p ⟧ty⊑-≈
⟦ refl-trans ⟧ty⊑-≈ = eqPMor _ _ refl
⟦ trans-refl ⟧ty⊑-≈ = eqPMor _ _ refl
⟦ assoc ⟧ty⊑-≈ = eqPMor _ _ refl
⟦ ⇀-refl ⟧ty⊑-≈ = U⟶F-Id-emb
⟦ ⇀-trans ⟧ty⊑-≈ = {!!}
