{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --guardedness #-}

module Semantics.DelayErrorOrdering  where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Relation.Binary

open import Semantics.Delay
open import Common.Preorder.Base
open import Common.Preorder.Monotone


private
  variable
    ℓ ℓ' : Level

 

-- Lifting the relation on a preorder X to the relation on Delay' (X + 1)
module Ord (X : Preorder ℓ ℓ')  where
  open BinaryRelation
  open Alternative (⟨ X ⟩ ⊎ ⊤)

  -- Lifting the relation on X to an "error" relation on X ⊎ ⊤
  R-result : (⟨ X ⟩ ⊎ ⊤) -> (⟨ X ⟩ ⊎ ⊤) -> Type ℓ'
  R-result (inl x) (inl y) = rel X x y
  R-result (inl x) (inr tt) = ⊥* -- can't have a value be less than error
  R-result (inr tt) y? = ⊤* -- error is the bottom element

  R-result-refl : isRefl R-result
  R-result-refl (inl x) = reflexive X x
  R-result-refl (inr x) = _

  R-result-trans : (x? y? z? : ⟨ X ⟩ ⊎ ⊤) -> R-result x? y? -> R-result y? z? -> R-result x? z?
  R-result-trans (inr tt) y? z? x?≤y? y?≤z? = tt*
  R-result-trans (inl x) (inl y) (inl z) x≤y y≤z = transitive X _ _ _ x≤y y≤z
  -- Agda can tell that the other cases are impossible!


  _⊑'_ : PreDelay' -> PreDelay' -> Type (ℓ-max ℓ ℓ')
  d ⊑' d' =
    -- If d terminates with a value x, then d' terminates with a related value y.
    ((x : ⟨ X ⟩) -> terminatesWith d (inl x) ->
      Σ[ y ∈ ⟨ X ⟩ ] (terminatesWith d' (inl y) × (rel X x y))) ×

    -- If d' terminates with a result y?, then d terminates
    -- with a related result x?.
    ((y? : ⟨ X ⟩ ⊎ ⊤) -> terminatesWith d' y? ->
    Σ[ x? ∈ ⟨ X ⟩ ⊎ ⊤ ] (terminatesWith d x? × R-result x? y?))
     
  ⊑'-refl : (d : PreDelay') -> d ⊑' d
  fst (⊑'-refl d) x d↓x = x , (d↓x , (reflexive X _))
  snd (⊑'-refl d) y? d↓y? = y? , (d↓y? , R-result-refl y?)

  ⊑'-trans : (d1 d2 d3 : PreDelay') -> d1 ⊑' d2 -> d2 ⊑' d3 -> d1 ⊑' d3
  ⊑'-trans d1 d2 d3 (d1≤d2-1 , d1≤d2-2) (d2≤d3-1 , d2≤d3-2) =
    pt1 , pt2
      where
        pt1 : (x1 : ⟨ X ⟩) →
                terminatesWith d1 (inl x1) →
                Σ-syntax ⟨ X ⟩ (λ y → terminatesWith d3 (inl y) × rel X x1 y)
        pt1 x1 d1↓x1 with d1≤d2-1 x1 d1↓x1
        ... | x2 , d2↓x2 , x1≤x2
          with d2≤d3-1 x2 d2↓x2
        ... | x3 , d3↓x3 , x2≤x3 =
          x3 , d3↓x3 , transitive X _ _ _ x1≤x2 x2≤x3

        pt2 : (z? : ⟨ X ⟩ ⊎ ⊤) →
                terminatesWith d3 z? →
                Σ-syntax (⟨ X ⟩ ⊎ ⊤) (λ x? → terminatesWith d1 x? × R-result x? z?)
        pt2 z? d3↓z? with d2≤d3-2 z? d3↓z?
        ... | (y? , d2↓y? , y?≤z?)
          with d1≤d2-2 y? d2↓y?
        ... | (x? , d1↓x? , x?≤y?) = x? , d1↓x? , (R-result-trans x? y? z? x?≤y? y?≤z?)


  -- Now define the ordering on the original Delay type
  _⊑_ : Delay (⟨ X ⟩ ⊎ ⊤) -> Delay (⟨ X ⟩ ⊎ ⊤) -> Type (ℓ-max ℓ ℓ')
  d1 ⊑ d2 = fromDelay d1 ⊑' fromDelay d2
