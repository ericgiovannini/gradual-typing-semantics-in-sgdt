{-# OPTIONS --safe #-}
module Cubical.HigherCategories.PreorderEnriched.PreorderEnriched where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Relation.Binary.Base

private
  variable
    ℓ ℓ' ℓ'' ℓc ℓc' ℓc'' ℓd ℓd' ℓd'' : Level

open BinaryRelation
open Category

record PreorderEnrichedCategory ℓ ℓ' ℓ'' : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓ''))) where
  field
    cat : Category ℓ ℓ'
    _≤_ : ∀ {x y} → cat [ x , y ] → cat [ x , y ] → Type ℓ''
    isProp≤ : ∀ x y (f g : cat [ x , y ]) → isProp (f ≤ g)
    isReflexive : ∀ {x y} → isRefl (_≤_ {x}{y})
    isTransitive : ∀ {x y} → isTrans (_≤_ {x}{y})

    isMonotone⋆ : ∀ {x y z} {f f' : cat [ x , y ]}{g g' : cat [ y , z ]}
                → f ≤ f' → g ≤ g'
                → (f ⋆⟨ cat ⟩ g) ≤ (f' ⋆⟨ cat ⟩ g')

open PreorderEnrichedCategory

record PreorderEnrichedFunctor (C : PreorderEnrichedCategory ℓc ℓc' ℓc'') (D : PreorderEnrichedCategory ℓd ℓd' ℓd'') : Type (ℓ-suc (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓc'') (ℓ-max (ℓ-max ℓd ℓd') ℓd''))) where
  field
    functor : Functor (C .cat) (D .cat)
    isMonotoneF : ∀ {x y} (f f' : C .cat [ x , y ]) → C ._≤_ f f' → D ._≤_ (functor ⟪ f ⟫) (functor ⟪ f' ⟫)
