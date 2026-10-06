{-

  Denotational semantics of type precision as quasi-representable
  predomain relations with a push-pull structure.
  
-}
{-# OPTIONS --rewriting --lossy-unification #-}
open import Common.Later
module Syntax.FineGrained.Denotation.TypePrecision (k : Clock) where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Foundations.Structure
open import Cubical.Data.List

open import Syntax.Types
open import Syntax.FineGrained.Denotation.Types k
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Relations k as Rel hiding (_×_)
open import Semantics.Concrete.Perturbation.QuasiRepresentation.QuasiEquivalence k
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
⟦ c × d ⟧ty⊑ = ⟦ c ⟧ty⊑ Rel.× ⟦ d ⟧ty⊑
⟦ inj-nat ⟧ty⊑ = injNat
⟦ inj-arr ⟧ty⊑ = ⊙V (Next ⟦ dyn ⇀ dyn ⟧ty) injArr
⟦ inj-times ⟧ty⊑ = injTimes

⟦_⟧ctx⊑ : ∀ {Γ Δ} → Γ ⊑ctx Δ → ValRel ⟦ Γ ⟧ctx ⟦ Δ ⟧ctx ℓ-zero
⟦ [] ⟧ctx⊑ = IdV _
⟦ c ∷ C ⟧ctx⊑ = ⟦ C ⟧ctx⊑ Rel.× ⟦ c ⟧ty⊑

-- Equal derivations denote quasi-order-equivalent relations. The unit
-- and associativity laws hold because the two relations are
-- represented by the same embedding (the embedding of a composite is
-- the composite of the embeddings), as does ⇀-refl, where the
-- embedding of U (Id ⟶ F Id) is the identity (U⟶F-Id-emb). The
-- ⇀-trans law is Lemma D.18 of the paper (U⟶F-comp-equiv). The two
-- product laws hold because the embedding of a product relation is the
-- product of the embeddings (×-Id-emb, ×-comp-equiv).
⟦_⟧ty⊑-≈ : ∀ {S T} {c d : S ⊑ T} → c ≈ d → ValRel≈ ⟦ c ⟧ty⊑ ⟦ d ⟧ty⊑
⟦ sym≈ p ⟧ty⊑-≈ = quasiEquivV-sym ⟦ p ⟧ty⊑-≈
⟦ refl-trans {c = c} ⟧ty⊑-≈ =
  eqEmbV→quasiEquivV _ _ (⟦ trans-⊑ refl-⊑ c ⟧ty⊑ .snd .fst) (⟦ c ⟧ty⊑ .snd .fst) (eqPMor _ _ refl)
⟦ trans-refl {c = c} ⟧ty⊑-≈ =
  eqEmbV→quasiEquivV _ _ (⟦ trans-⊑ c refl-⊑ ⟧ty⊑ .snd .fst) (⟦ c ⟧ty⊑ .snd .fst) (eqPMor _ _ refl)
⟦ assoc {c = c} {d = d} {d' = d'} ⟧ty⊑-≈ =
  eqEmbV→quasiEquivV _ _
    (⟦ trans-⊑ c (trans-⊑ d d') ⟧ty⊑ .snd .fst) (⟦ trans-⊑ (trans-⊑ c d) d' ⟧ty⊑ .snd .fst)
    (eqPMor _ _ refl)
⟦ ⇀-refl ⟧ty⊑-≈ = U⟶F-Id-emb
⟦ ⇀-trans {c = c} {d = d} {c' = c'} {d' = d'} ⟧ty⊑-≈ =
  U⟶F-comp-equiv ⟦ c ⟧ty⊑ ⟦ c' ⟧ty⊑ ⟦ d ⟧ty⊑ ⟦ d' ⟧ty⊑
⟦ ×-refl ⟧ty⊑-≈ = ×-Id-emb
⟦ ×-trans {c = c} {d = d} {c' = c'} {d' = d'} ⟧ty⊑-≈ =
  ×-comp-equiv ⟦ c ⟧ty⊑ ⟦ c' ⟧ty⊑ ⟦ d ⟧ty⊑ ⟦ d' ⟧ty⊑
