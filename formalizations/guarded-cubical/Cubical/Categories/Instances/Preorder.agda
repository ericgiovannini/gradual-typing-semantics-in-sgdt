{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Preorder where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Proset

open import Cubical.Categories.Category

open Category

private
  variable
    ℓ ℓ' : Level

module _ (P : Proset ℓ ℓ') where

  open ProsetStr (snd P)

  PreorderCategory : Category ℓ ℓ'
  ob PreorderCategory           = fst P
  Hom[_,_] PreorderCategory     = _≲_
  id PreorderCategory           = is-refl _
  _⋆_ PreorderCategory          = is-trans _ _ _
  ⋆IdL PreorderCategory _       = is-prop-valued _ _ _ _
  ⋆IdR PreorderCategory _       = is-prop-valued _ _ _ _
  ⋆Assoc PreorderCategory _ _ _ = is-prop-valued _ _ _ _
  isSetHom PreorderCategory     = isProp→isSet (is-prop-valued _ _)

