{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.DynTypGen.World (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Preorder

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Preorder

open import Semantics.DynTypGen.Impred.Set

open BinaryRelation

private
  variable
    ℓ ℓ' : Level
    A : hSet ℓ-zero

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


{-
  Definition of semantic Worlds and their ordering relation.

  Note: In order for the ordering to be a preorder (prop-valued),
  we require that the objects indexing our worlds are *hSets*.

-}


⟨World⟩ : hSet ℓ-zero → Type ℓ-zero
⟨World⟩ A = List ⟨ A ⟩

isSetWorld : ∀ A → isSet (⟨World⟩ A)
isSetWorld (A , isSetA) = isOfHLevelList 0 isSetA


-- Prefix ordering on worlds:

_≤world_ : ⟨World⟩ A → ⟨World⟩ A → Type ℓ-zero
[] ≤world ys = ⊤
(x ∷ xs) ≤world [] = ⊥
(x ∷ xs) ≤world (y ∷ ys) = (x ≡ y) × (xs ≤world ys)


-- Properties of the prefix ordering:

≤world-prop : isPropValued (_≤world_ {A = A})
≤world-prop [] w₂ p q = refl
≤world-prop {A} (x ∷ xs) (y ∷ ys) = isProp× (A .snd x y) (≤world-prop xs ys)
  -- ≡-× (A .snd x y (p .fst) (q .fst))
  --     (≤world-prop xs ys (p .snd) (q .snd))

≤world-refl : ∀ (w : ⟨World⟩ A) → w ≤world w
≤world-refl [] = tt
≤world-refl (x ∷ xs) = refl , ≤world-refl xs

≤world-trans : ∀ (w₁ w₂ w₃ : ⟨World⟩ A)
  → w₁ ≤world w₂
  → w₂ ≤world w₃
  → w₁ ≤world w₃
≤world-trans w₁ w₂ w₃ = {!!}


-- Definition of Worlds as a Preorder

World : hSet ℓ-zero → Preorder ℓ-zero ℓ-zero
World A .fst = ⟨World⟩ A
World A .snd = preorderstr
  _≤world_
  (ispreorder (isSetWorld A) ≤world-prop ≤world-refl ≤world-trans)


-- Given an hSet A, returns the type of functors from
-- the preorder of worlds on A (viewed as a category)
-- into the category induced by impredicative set.
𝓕 : hSet ℓ-zero → hSet ℓ-zero
𝓕 A .fst = Functor (PreorderCategory (World A)) ISET
𝓕 A .snd = isSetFunctor {!!}

𝓣 : hSet ℓ-zero
𝓣 = fix (λ A~ → 𝓕 {!!})

