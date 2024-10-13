{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

module Results where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport -- pathToIso
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Relation.Binary
open import Cubical.Data.Nat hiding (_^_ ; _+_)
open import Cubical.Data.List
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)

open import Common.Later
open import Common.ClockProperties
open import Semantics.GlobalLift
open import Semantics.Concrete.Predomain.Error
open import Semantics.Concrete.Predomain.Morphism hiding (Comp)

open import Semantics.Concrete.GuardedLift using (mapL ; unfold-mapL)
open import Semantics.Concrete.GuardedLiftError hiding (mapL)
open import Semantics.Concrete.LockStepErrorOrdering
open import Semantics.Concrete.WeakBisimilarity

open import Semantics.BigStepFunction
open import Semantics.CombinedAdequacy
open import Semantics.AdequacyLiftNat

open import Syntax.Types
open import Syntax.FineGrained.Terms
open import Syntax.FineGrained.Order
open import Syntax.FineGrained.Denotation.Terms
open import Syntax.FineGrained.Denotation.TermPrecision


private
  variable
    ℓ ℓ' ℓR : Level
    ℓ≈X ℓ≈Y ℓ⊑ : Level

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T R' S' T' : Ty
   B B' C C' D D' : Γ ⊑ctx Γ'
   b b' c c' d d' : S ⊑ S'
   E E' E'' : EvCtx Γ S T

-- open PartialFunctions {X = ℕ ⊎ ⊤}
open PartialFunctions
open PMor


-- The big-step term semantics, valued in elements of type *global* L℧ ℕ
bigStepTm' : Comp [] nat → L℧^gl ℕ
bigStepTm' M = λ k → ⟦_⟧C k M .f _

-- Composing the above semantics with the function that maps global lift ℕ
-- to Partial elements of type (ℕ + 1)
bigStepTm : Comp [] nat → Fun
bigStepTm M = ⟦ (λ k → mapL k ErrorX→X⊎⊤ (bigStepTm' M k)) ⟧

Graduality : ∀ {M M'} → Comp⊑ [] (refl-⊑ {nat}) M M'
  → bigStepTm M ≾ bigStepTm M'
Graduality {M = M}{M' = M'} M⊑M' =
  {!!}
  -- nat-adequate (bigStepTm' M) N N' (bigStepTm' M')
  --   (λ k → sq k .snd .fst tt tt refl )
  --   (λ k → sq k .snd .snd .snd .snd tt tt refl)
  --   λ k → sq k .snd .snd .snd .fst tt tt refl
  where
  sq = λ (k : Clock) → ⟦_⟧C⊑ k M⊑M'
  N : L℧^gl ℕ
  N k = sq k .fst .f _
  N' : L℧^gl ℕ
  N' k = sq k .snd .snd .fst .f _
