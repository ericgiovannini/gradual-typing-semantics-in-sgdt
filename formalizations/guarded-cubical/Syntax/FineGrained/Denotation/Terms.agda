{-
  Denotational semantics of gradual types as error predomains
-}
{-# OPTIONS --rewriting --allow-unsolved-metas --lossy-unification #-}
open import Common.Later
module Syntax.FineGrained.Denotation.Terms (k : Clock) where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Foundations.Structure
open import Cubical.Data.List

open import Semantics.Concrete.Predomain.Constructions
open import Semantics.Concrete.Predomain.Morphism renaming (Comp to Compose)
open import Semantics.Concrete.Types k

open import Syntax.Types
open import Syntax.FineGrained.Terms
open import Syntax.FineGrained.Denotation.Types k

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T R' S' T' : Ty
   b b' c c' d d' : S ⊑ S'

⟦_⟧C : Comp Γ S → ObliqueMor ⟦ Γ ⟧ctx (F ⟦ S ⟧ty)
⟦_⟧C = {!!}

-- ⟦_⟧S : Subst Δ Γ → ValTypeMor ⟦ Δ ⟧ctx ⟦ Γ ⟧ctx
-- ⟦_⟧V : Val Γ S → ValTypeMor ⟦ Γ ⟧ctx ⟦ S ⟧ty
-- -- TODO: consider alternatives
-- ⟦_⟧C : Comp Γ S → ValTypeMor ⟦ Γ ⟧ctx (U (F ⟦ S ⟧ty))
-- -- TODO: consider alternatives such as S × Γ → UF T
-- ⟦_⟧E : EvCtx Γ S T → CompTypeMor (F ⟦ S ⟧ty) (⟦ Γ ⟧ctx ⟶ F ⟦ T ⟧ty)

-- ⟦ ids ⟧S = Id
-- ⟦ γ ∘s δ ⟧S = ⟦ γ ⟧S ∘p ⟦ δ ⟧S
-- ⟦ ∘IdL {γ = γ} i ⟧S = CompPD-IdL ⟦ γ ⟧S i
-- ⟦ ∘IdR {γ = γ} i ⟧S = CompPD-IdR ⟦ γ ⟧S i
-- ⟦ ∘Assoc {γ = γ}{δ = δ}{θ = θ} i ⟧S = CompPD-Assoc ⟦ θ ⟧S ⟦ δ ⟧S ⟦ γ ⟧S i
-- ⟦ !s ⟧S = {!!}
-- ⟦ []η i ⟧S = {!!}
-- ⟦ γ ,s V ⟧S = ×-intro ⟦ γ ⟧S ⟦ V ⟧V
-- ⟦ wk ⟧S = π1
-- ⟦ wkβ {δ = δ}{V = V} i ⟧S =
--   eqPBMor ((Compose (×-intro ⟦ δ ⟧S ⟦ V ⟧V) π1)) ⟦ δ ⟧S refl i
-- ⟦ ,sη i ⟧S = {!!}

-- ⟦ V [ x ]v ⟧V = {!!}
-- ⟦ substId i ⟧V = {!!}
-- ⟦ substAssoc i ⟧V = {!!}
-- ⟦ var ⟧V = {!!}
-- ⟦ varβ i ⟧V = {!!}
-- ⟦ zro ⟧V = {!!}
-- ⟦ suc ⟧V = {!!}
-- ⟦ lda M ⟧V = {!!}
-- ⟦ fun-η i ⟧V = {!!}
-- ⟦ injectN ⟧V = {!!}
-- ⟦ injectArr ⟧V = {!!}
-- ⟦ up S⊑T ⟧V = {!!}

-- ⟦ E [ M ]∙ ⟧C = {!!}
-- ⟦ plugId i ⟧C = {!!}
-- ⟦ plugAssoc i ⟧C = {!!}
-- ⟦ M [ γ ]c ⟧C = {!!}
-- ⟦ substId i ⟧C = {!!}
-- ⟦ substAssoc i ⟧C = {!!}
-- ⟦ substPlugDist i ⟧C = {!!}
-- ⟦ err ⟧C = {!!}
-- ⟦ strictness i ⟧C = {!!}
-- ⟦ ret ⟧C = {!!}
-- ⟦ ret-β i ⟧C = {!!}
-- ⟦ app ⟧C = {!!}
-- ⟦ fun-β i ⟧C = {!!}
-- ⟦ matchNat Mz Ms ⟧C = {!!}
-- ⟦ matchNatβz Mz Ms i ⟧C = {!!}
-- ⟦ matchNatβs Mz Ms i ⟧C = {!!}
-- ⟦ matchNatη i ⟧C = {!!}
-- ⟦ matchDyn Mn Mf ⟧C = {!!}
-- ⟦ matchDynβn Mn Mf V i ⟧C = {!!}
-- ⟦ matchDynβf Mn Mf V i ⟧C = {!!}
-- ⟦ matchDynSubst Mn Mf γ i ⟧C = {!!}

-- ⟦ ∙E ⟧E = {!!}
-- ⟦ E ∘E E' ⟧E = {!!}
-- ⟦ ∘IdL i ⟧E = {!!}
-- ⟦ ∘IdR i ⟧E = {!!}
-- ⟦ ∘Assoc i ⟧E = {!!}
-- ⟦ E [ γ ]e ⟧E = {!!}
-- ⟦ substId i ⟧E = {!!}
-- ⟦ substAssoc i ⟧E = {!!}
-- ⟦ ∙substDist i ⟧E = {!!}
-- ⟦ ∘substDist i ⟧E = {!!}
-- ⟦ bind ⟨x⟩M ⟧E = {!!}
-- ⟦ ret-η i ⟧E = {!!}
-- ⟦ dn S⊑T ⟧E = {!!}
