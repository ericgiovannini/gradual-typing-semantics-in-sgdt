{-# OPTIONS --safe --cubical #-}

module Common.Poset.Convenience where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Binary.Base

open BinaryRelation

private
  variable
    ℓ ℓ' : Level
    ℓX ℓ'X ℓY ℓ'Y : Level


-- Some convenience functions

rel : (X : Poset ℓ ℓ') -> (⟨ X ⟩ -> ⟨ X ⟩ -> Type ℓ')
rel X = PosetStr._≤_ (X .snd)

reflexive : (X : Poset ℓ ℓ') -> (x : ⟨ X ⟩) -> (rel X x x)
reflexive X x = IsPoset.is-refl (PosetStr.isPoset (str X)) x

transitive : (X : Poset ℓ ℓ') -> (x y z : ⟨ X ⟩) ->
  rel X x y -> rel X y z -> rel X x z
transitive X x y z x≤y y≤z =
  IsPoset.is-trans (PosetStr.isPoset (str X)) x y z x≤y y≤z

antisym : (d : Poset ℓ ℓ') -> (x y : ⟨ d ⟩) ->
  rel d x y -> rel d y x -> x ≡ y
antisym d x y x≤y y≤x = IsPoset.is-antisym (PosetStr.isPoset (str d)) x y x≤y y≤x

isSet-poset : (X : Poset ℓ ℓ') -> isSet ⟨ X ⟩
isSet-poset X = IsPoset.is-set (PosetStr.isPoset (str X))

isPropValued-poset : (X : Poset ℓ ℓ') ->
  isPropValued (PosetStr._≤_ (str X))
isPropValued-poset X = IsPoset.is-prop-valued
  (PosetStr.isPoset (str X))


