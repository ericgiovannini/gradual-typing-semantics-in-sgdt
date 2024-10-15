{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}

module Results where

{- This module defines the key results from the paper. -}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (_^_ ; _+_)
open import Cubical.Data.List
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)

open import Common.Later
open import Semantics.Adequacy.GlobalLift
open import Semantics.Concrete.Predomain.Error
open import Semantics.Concrete.Predomain.Morphism hiding (Comp)

open import Semantics.Concrete.GuardedLift using (mapL ; unfold-mapL)
open import Semantics.Concrete.GuardedLiftError hiding (mapL)
open import Semantics.Concrete.LockStepErrorOrdering
open import Semantics.Concrete.WeakBisimilarity

open import Semantics.Adequacy.BigStepFunction
open import Semantics.Adequacy.CombinedAdequacy
open import Semantics.Adequacy.AdequacyLiftNat
open import Semantics.Adequacy.Partial

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

open PMor


----------------------------
-- Big-step term semantics
----------------------------

-- First is the big-step term semantics (Section 3.5).  This is a
-- partial function from closed terms of type nat to N + 1 (where the
-- "+ 1" represents error)
--
-- In Agda, we represent a partial function from X to Y as a total
-- function from X into the type of *partial elements* of type Y (see
-- Semantics.Adequacy.Partial for the definition).


-- First we define a semantic function valued in elements of type
-- *global* L℧ ℕ:
bigStepTm' : Comp [] nat → L℧^gl ℕ
bigStepTm' M = λ k → ⟦_⟧C k M .f _

-- We obtain the desired big-step term semantics by composing the
-- above function with the function ⟦ · ⟧partial, which maps L^gl X to
-- partial elements of type X:
bigStepTm : Comp [] nat → Part (ℕ ⊎ ⊤) ℓ-zero
bigStepTm M = ⟦ (λ k → mapL k ErrorX→X⊎⊤ (bigStepTm' M k)) ⟧partial


-----------------------------------------------------------------------

---------------
-- Graduality
---------------

-- Now we prove the final graduality result: If two closed terms M and
-- M' of type nat are related syntactically, then their big-step
-- denotations as partial elements of type (ℕ + 1) are related in the
-- ordering on partial elements.
--
-- This corresponds to Sections 5.3 and 5.4 in the paper.

Graduality : ∀ {M M'} → Comp⊑ [] (refl-⊑ {nat}) M M'
  → bigStepTm M ≤part bigStepTm M'
Graduality {M = M}{M' = M'} M⊑M' =
  nat-adequate (bigStepTm' M) N N' (bigStepTm' M')
    (λ k → sq k .snd .fst tt tt refl )
    (λ k → sq k .snd .snd .snd .snd tt tt refl)
    λ k → sq k .snd .snd .snd .fst tt tt refl
  where
  sq = λ (k : Clock) → ⟦_⟧C⊑ k M⊑M'
  N : L℧^gl ℕ
  N k = sq k .fst .f _
  N' : L℧^gl ℕ
  N' k = sq k .snd .snd .fst .f _


-----------------------------------------------------------------------

------------------------------------------------------------
-- No-go theorem for relations on the free error domain L℧:
------------------------------------------------------------

-- The proof of the no-go theorem (Theorem 4.1 in the paper) is given
-- in the below file.
-- 
-- While this is not directly used anywhere in the construction of our
-- model, it serves as an explanation as to why the denotations of
-- types need to be equipped with two separate relations (an error
-- ordering and a bisimilarity relation).
--
-- Please see the file below for the statement and proof; the import
-- here ensures that it is type-checked whenever this Results file is
-- checked.

open import Semantics.GuardedResults.NoGoTheorem
