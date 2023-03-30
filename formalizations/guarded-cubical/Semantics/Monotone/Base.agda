{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


module Semantics.Monotone.Base where

open import Cubical.Relation.Binary.Poset
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure

open import Semantics.Predomains

private
  variable
    ℓ : Level

-- Monotone functions from X to Y
record MonFun (X Y : Predomain) : Set where
  module X = PosetStr (X .snd)
  module Y = PosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    f : (X .fst) → (Y .fst)
    isMon : ∀ {x y} → x ≤X y → f x ≤Y f y

-- Use reflection to show that this is a sigma type
-- Look for proof in standard library to show that
-- Sigma type with a proof that RHS is a prop, then equality of a pair
-- follows from equality of the LHS's
-- Specialize to the case of monotone functions and fill in the proof
-- later



-- Monotone relations between predomains X and Y
-- (antitone in X, monotone in Y).
record MonRel {ℓ' : Level} (X Y : Predomain) : Type (ℓ-suc ℓ') where
  module X = PosetStr (X .snd)
  module Y = PosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    R : ⟨ X ⟩ -> ⟨ Y ⟩ -> Type ℓ'
    isAntitone : ∀ {x x' y} -> R x y -> x' ≤X x -> R x' y
    isMonotone : ∀ {x y y'} -> R x y -> y ≤Y y' -> R x y'

predomain-monrel : (X : Predomain) -> MonRel X X
predomain-monrel X = record {
  R = rel X ;
  isAntitone = λ {x} {x'} {y} x≤y x'≤x → transitive X x' x y x'≤x x≤y ;
  isMonotone = λ {x} {y} {y'} x≤y y≤y' -> transitive X x y y' x≤y y≤y' }


compRel : {X Y Z : Type} ->
  (R1 : Y -> Z -> Type ℓ) ->
  (R2 : X -> Y -> Type ℓ) ->
  (X -> Z -> Type ℓ)
compRel {ℓ} {X} {Y} {Z} R1 R2 x z = Σ[ y ∈ Y ] R2 x y × R1 y z

CompMonRel : {X Y Z : Predomain} ->
  MonRel {ℓ} Y Z ->
  MonRel {ℓ} X Y ->
  MonRel {ℓ} X Z
CompMonRel {ℓ} {X} {Y} {Z} R1 R2 = record {
  R = compRel (MonRel.R R1) (MonRel.R R2) ;
  isAntitone = antitone ;
  isMonotone = {!!} }
    where
      antitone : {x x' : ⟨ X ⟩} {z : ⟨ Z ⟩} ->
        compRel (MonRel.R R1) (MonRel.R R2) x z ->
        rel X x' x ->
        compRel (MonRel.R R1) (MonRel.R R2) x' z 
      antitone (y , xR2y , yR1z) x'≤x = y , (MonRel.isAntitone R2 xR2y x'≤x) , yR1z

      monotone : {x : ⟨ X ⟩} {z z' : ⟨ Z ⟩} ->
        compRel (MonRel.R R1) (MonRel.R R2) x z ->
        rel Z z z' ->
        compRel (MonRel.R R1) (MonRel.R R2) x z'
      monotone (y , xR2y , yR1z) z≤z' = y , xR2y , (MonRel.isMonotone R1 yR1z z≤z')
