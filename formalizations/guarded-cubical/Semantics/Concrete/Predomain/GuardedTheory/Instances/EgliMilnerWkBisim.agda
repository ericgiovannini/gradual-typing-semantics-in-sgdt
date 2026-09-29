{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.Predomain.GuardedTheory.Instances.EgliMilnerWkBisim (k : Clock) where

open import Cubical.Foundations.Prelude hiding (Σ)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.HITs.PropositionalTruncation
  renaming (elim to PTElim ; rec to PTRec)

open import Cubical.Data.List as L hiding ([_])
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Sigma hiding (Σ)
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Bool

open import Cubical.Relation.Nullary

open import Common.LaterProperties
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Constructions
  renaming (module Clocked to PredomainClocked)
  hiding (ℕ)
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Combinators

open import Semantics.Concrete.Predomain.GuardedTheory.Instances.FreeGuardedJoinSLErrorV2 k
open import Semantics.Concrete.Predomain.GuardedTheory.Instances.EgliMilner k


private
  variable
    ℓ  ℓ≤  ℓ≈  : Level
    ℓ' ℓ'≤ ℓ'≈ : Level
    ℓA ℓ≤A ℓ≈A ℓA' ℓ≤A' ℓ≈A' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ : Level
    ℓA₃ ℓ≤A₃ ℓ≈A₃ ℓA₄ ℓ≤A₄ ℓ≈A₄ : Level

    ℓR : Level

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

module _ (X : Predomain ℓ ℓ≤ ℓ≈) where

  private
    module X = PredomainStr (X .snd)
    module W = WkBisim X

  open EgliMilnerOrder X



  -- Weak bisimilarity of branches
  _≈ᵇ_ : Br ⟨ X ⟩ → Br ⟨ X ⟩ → Type _
  b ≈ᵇ c = ⟦ b ⟧ᵇ W.≈ ⟦ c ⟧ᵇ


  -- A pair of weakly bisimilar branches
  record BrPair : Type (ℓ-max ℓ ℓ≈) where
    constructor pair
    field
      left  : Br ⟨ X ⟩
      right : Br ⟨ X ⟩
      rel   : left ≈ᵇ right


  -- Projections from a list of paired branches
  lefts : List BrPair → List (Br ⟨ X ⟩)
  lefts []       = []
  lefts (p ∷ ps) = BrPair.left p ∷ lefts ps

  rights : List BrPair → List (Br ⟨ X ⟩)
  rights []       = []
  rights (p ∷ ps) = BrPair.right p ∷ rights ps


  -- A coupling between computations A and B is a finite list of
  -- paired branches whose left projection joins to A and whose right
  -- projection joins to B.
  record JoinCoupling (A B : |P| ⟨ X ⟩) : Type (ℓ-max ℓ ℓ≈) where
    constructor coupling
    field
      pairs   : List BrPair
      leftEq  : joinBr (lefts pairs) ≡ A
      rightEq : joinBr (rights pairs) ≡ B



  ≤EM-antisym→≈ :
      (∀ x y → x X.≤ y → x ≡ y)
    → ∀ {A B} → A ≤EM B → B ≤EM A → A W.≈ B
  ≤EM-antisym→≈ disc {A = A} {B = B} A≤B B≤A =
    rec≤EM (W.isProp≈ _ _)
      (λ dA dB leq → rec≤EM (W.isProp≈ _ _) (λ dB' dA' leq' → go dA dB dA' dB' leq leq') B≤A)
    A≤B
    where
      go : (dA : Decomp A) → (dB : Decomp B) → (dA' : Decomp A) → (dB' : Decomp B)
        → CoverLE _≤EM▹_ (dA .fst)  (dB .fst)
        → CoverLE _≤EM▹_ (dB' .fst) (dA' .fst)
        → A W.≈ B
      go (as , ea) (bs , eb) (as' , ea') (bs' , eb') as≤bs bs'≤as' = {!as≤bs!}
