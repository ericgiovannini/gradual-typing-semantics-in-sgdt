{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --guardedness #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Adequacy.Coinductive.DelayErrorOrdering  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.Relation.Binary

open import Semantics.Adequacy.Coinductive.Delay
open import Common.Preorder.Base
open import Common.Preorder.Monotone
open import Cubical.Relation.Binary.Order.Poset


private
  variable
    ℓ ℓ' : Level



-- Use propositional truncation (elimProp)

-- Lifting a Preorder X to a Preorder structure on (⟨ X ⟩ ⊎ ⊤)
module ResultPoset (X : Poset ℓ ℓ') where
  open BinaryRelation

  module X = PosetStr (X .snd)

   -- Lifting the relation on X to an "error" relation on X ⊎ ⊤
  R-result : (⟨ X ⟩ ⊎ ⊤) -> (⟨ X ⟩ ⊎ ⊤) -> Type ℓ'
  R-result (inl x) (inl y) =  x X.≤ y
  R-result (inl x) (inr tt) = ⊥* -- can't have a value be less than error
  R-result (inr tt) y? = ⊤* -- error is the bottom element

  R-result-refl : isRefl R-result
  R-result-refl (inl x) = X.is-refl x
  R-result-refl (inr x) = _

  R-result-trans : (x? y? z? : ⟨ X ⟩ ⊎ ⊤) -> R-result x? y? -> R-result y? z? -> R-result x? z?
  R-result-trans (inr tt) y? z? x?≤y? y?≤z? = tt*
  R-result-trans (inl x) (inl y) (inl z) x≤y y≤z = X.is-trans _ _ _ x≤y y≤z
  -- Agda can tell that the other cases are impossible!

  R-result-antisym : (x? y? : ⟨ X ⟩ ⊎ ⊤) -> R-result x? y? -> R-result y? x? -> x? ≡ y?
  R-result-antisym (inl x) (inl y) H1 H2 = cong inl {!!}
  R-result-antisym (inr x) y? H1 H2 = {!!}

  R-result-propValued : isPropValued R-result
  R-result-propValued (inl x) (inl y)  = X.is-prop-valued x y
  R-result-propValued (inr tt) y? = isPropUnit*

  -- Note that this is not the same as the usual preorder construction on sum types,
  -- because there inr is related only to inr, whereas here error is related to everything.
  ResultP : Poset ℓ ℓ'
  ResultP = (⟨ X ⟩ ⊎ ⊤) , posetstr {!!} {!!}


{-preorderstr R-result
    (ispreorder (isSet⊎ (IsPreorder.is-set X.isPreorder) isSetUnit)
      R-result-propValued R-result-refl R-result-trans)
-}
 

-- Lifting the relation on a preorder X to the relation on Delay' (X + 1)
module Ord (X : Poset ℓ ℓ')  where
  open BinaryRelation
  open Alternative (⟨ X ⟩ ⊎ ⊤) -- Definition of Delay as a function
  open ResultPoset X           -- Error ordering on results
  -- private module X = PosetStr (X .snd)


  _⊑'_ : PreDelay' -> PreDelay' -> Type (ℓ-max ℓ ℓ')
  d ⊑' d' = ∥
    -- If d terminates with a value x, then d' terminates with a related value y.
    ((x : ⟨ X ⟩) -> terminatesWith d (inl x) ->
      Σ[ y ∈ ⟨ X ⟩ ] (terminatesWith d' (inl y) × (x X.≤ y))) ×

    -- If d' terminates with a result y?, then d terminates
    -- with a related result x?.
    ((y? : ⟨ X ⟩ ⊎ ⊤) -> terminatesWith d' y? ->
    Σ[ x? ∈ ⟨ X ⟩ ⊎ ⊤ ] (terminatesWith d x? × R-result x? y?)) ∥₁

  -- Prop valued
  ⊑'-prop : (d d' : PreDelay') -> isProp (d ⊑' d')
  ⊑'-prop d d' = isPropPropTrunc
  

  -- Reflexivity
  ⊑'-refl : (d : PreDelay') -> d ⊑' d
  ⊑'-refl d = ∣ aux ∣₁
    where
      aux : _ × _
      aux .fst x d↓x = x , (d↓x , (X.is-refl _))
      aux .snd y? d↓y? = y? , (d↓y? , R-result-refl y?)
      
{-
  fst (⊑'-refl d) x d↓x = x , (d↓x , (reflexive X _))
  snd (⊑'-refl d) y? d↓y? = y? , (d↓y? , R-result-refl y?)
-}

  -- Transitivity
  ⊑'-trans : (d1 d2 d3 : PreDelay') -> d1 ⊑' d2 -> d2 ⊑' d3 -> d1 ⊑' d3
  ⊑'-trans d1 d2 d3 H1 H2 = rec2 isPropPropTrunc aux H1 H2 where
    aux : _
    aux (d1≤d2-1 , d1≤d2-2) (d2≤d3-1 , d2≤d3-2) = ∣ pt1 , pt2 ∣₁
      where
        pt1 : (x1 : ⟨ X ⟩) →
                terminatesWith d1 (inl x1) →
                Σ-syntax ⟨ X ⟩ (λ y → terminatesWith d3 (inl y) × x1 X.≤ y)
        pt1 x1 d1↓x1 with d1≤d2-1 x1 d1↓x1
        ... | x2 , d2↓x2 , x1≤x2
          with d2≤d3-1 x2 d2↓x2
        ... | x3 , d3↓x3 , x2≤x3 =
          x3 , d3↓x3 , X.is-trans _ _ _ x1≤x2 x2≤x3

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

  -- NTS: reflexive, transitive, prop-valued
  -- This should follow becasue we have that Delay is a retract of
  -- Delay'.
  -- See pulledbackRel in Cubical.Relation.Binary.Properties



{-
 -- Defining Delay as a Poset constructor, i.e., DelayP : Poset -> Poset
Delay℧P : Poset ℓ ℓ' -> Poset ℓ (ℓ-max ℓ ℓ')
Delay℧P X = (Delay (⟨ X ⟩ ⊎ ⊤)) , ?
  where
    open Ord X
    module X = PosetStr (X .snd)
-}
