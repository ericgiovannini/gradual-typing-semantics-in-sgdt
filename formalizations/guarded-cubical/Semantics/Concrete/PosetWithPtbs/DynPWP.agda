{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.PosetWithPtbs.DynPWP (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Relation.Binary
open import Cubical.Data.Nat renaming (ℕ to Nat)
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Common.LaterProperties
--open import Common.Preorder.Base
--open import Common.Preorder.Monotone
--open import Common.Preorder.Constructions
open import Semantics.Lift k
-- open import Semantics.Concrete.LiftPreorder k

open import Cubical.Relation.Binary.Poset
open import Common.Poset.Convenience
open import Common.Poset.Constructions
open import Common.Poset.Monotone
open import Semantics.MonotoneCombinators
open import Semantics.Concrete.PosetWithPtbs.Base k
open import Semantics.Concrete.PosetWithPtbs.Constructions k

open import Semantics.LockStepErrorOrdering k

open BinaryRelation
open LiftPoset
open ClockedCombinators k
open PosetWithPtb


private
  variable
    ℓ ℓ' : Level

  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A




module _ {ℓ : Level} where

  DynPWP' : (▹ PosetWithPtb ℓ ℓ ℓ) -> PosetWithPtb ℓ ℓ ℓ
  DynPWP' D~ = NatPWP ⊎PWP (PWP▸ (λ t -> (D~ t) ==>L (D~ t)))

  DynPWP : PosetWithPtb ℓ ℓ ℓ
  DynPWP = fix DynPWP'

  unfold-DynPWP : DynPWP ≡ DynPWP' (next DynPWP)
  unfold-DynPWP = fix-eq DynPWP'

  -- This is slow
  DynPWP-Sum : DynPWP' (next DynPWP) ≡ NatPWP ⊎PWP (PWP▹ (DynPWP ==>L DynPWP))
  DynPWP-Sum = DynPWP' (next DynPWP)
      ≡⟨ refl ⟩
    NatPWP ⊎PWP (PWP▸ λ t -> (next DynPWP t) ==>L (next DynPWP t))
      ≡⟨ refl ⟩
    NatPWP ⊎PWP (PWP▸ λ t -> (DynPWP) ==>L (DynPWP))
      ≡⟨ refl ⟩
    (NatPWP ⊎PWP (PWP▸ (next ((DynPWP) ==>L (DynPWP)))))
      -- ≡⟨ (λ i -> NatPWP ⊎PWP (PWP▸-next {!DynPWP!} i)) ⟩
      ≡⟨ refl ⟩
    NatPWP ⊎PWP (PWP▹ (DynPWP ==>L DynPWP)) ∎


  DynP : Poset ℓ ℓ
  DynP = DynPWP .P

  DynP' : Poset ℓ ℓ
  DynP' = DynPWP' (next DynPWP) .P

  unfold-DynP : DynP ≡ DynP'
  unfold-DynP i = (fix-eq DynPWP' i) .P

  unfold-⟨DynP⟩ : ⟨ DynP ⟩ ≡ ⟨ DynP' ⟩
  unfold-⟨DynP⟩ i = ⟨ unfold-DynP i ⟩

  DynP-Sum : DynP' ≡ ℕ ⊎p ((▸'' k) (DynP ==> 𝕃 DynP))
  DynP-Sum = {!DynP!}

  {-
  unfold-⟨DynP⟩ : ⟨ DynP ⟩ ≡ ⟨ DynP' (next DynP) ⟩
  unfold-⟨DynP⟩ = λ i → ⟨ unfold-DynP i ⟩

  DynP-Sum : DynP ≡ ℕ ⊎p ((▸'' k) (DynP ==> 𝕃 DynP))
  DynP-Sum = unfold-DynP



  InjNat : ⟨ ℕ ==> DynP ⟩
  InjNat = mCompU (mTransport (sym DynP-Sum)) σ1

  InjArr : ⟨ (DynP ==> 𝕃 DynP) ==> DynP ⟩
  InjArr = mCompU (mTransport (sym DynP-Sum)) (mCompU σ2 Next)

  ProjNat : ⟨ DynP ==> 𝕃 ℕ ⟩
  ProjNat = mCompU (Case' mRet (K _ ℧)) (mTransport DynP-Sum)

  ProjArr : ⟨ DynP ==> 𝕃 (DynP ==> 𝕃 DynP) ⟩
  ProjArr = {!!}
  -}
