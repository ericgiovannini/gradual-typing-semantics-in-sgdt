{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}



open import Common.Later

module Semantics.Concrete.DoublePoset.DblDyn (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport

open import Cubical.Relation.Binary
open import Cubical.Data.Nat renaming (ℕ to Nat)
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma

open import Common.LaterProperties
open import Semantics.Lift k
-- open import Semantics.Concrete.LiftPreorder k

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Convenience
open import Semantics.Concrete.DoublePoset.Constructions
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.MonotoneCombinators
open import Semantics.Concrete.DoublePoset.DPMorProofs

open import Semantics.Concrete.DoublePoset.LockStepErrorBisim k

open BinaryRelation
open LiftDoublePoset
open ClockedCombinators k

private
  variable
    ℓ ℓ' ℓX ℓX' : Level

  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


DynP' : (D : ▹ DoublePoset ℓ-zero ℓ-zero ℓ-zero) -> DoublePoset ℓ-zero ℓ-zero ℓ-zero
DynP' D = ℕ ⊎p (DP▸ k (λ t → D t ==> 𝕃 (D t)))

DynP : DoublePoset ℓ-zero ℓ-zero ℓ-zero
DynP = fix DynP'

unfold-DynP : DynP ≡ DynP' (next DynP)
unfold-DynP = fix-eq DynP'

unfold-⟨DynP⟩ : ⟨ DynP ⟩ ≡ ⟨ DynP' (next DynP) ⟩
unfold-⟨DynP⟩ = λ i → ⟨ unfold-DynP i ⟩

DynP-Sum : DynP ≡ ℕ ⊎p ((DP▸' k) (DynP ==> 𝕃 DynP))
DynP-Sum = unfold-DynP

⟨DynP⟩-Sum : ⟨ DynP ⟩ ≡ Nat ⊎ (▹ (⟨ DynP ==> 𝕃 DynP ⟩))
⟨DynP⟩-Sum i = ⟨ DynP-Sum i ⟩
