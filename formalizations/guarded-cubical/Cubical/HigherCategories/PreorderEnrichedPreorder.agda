{-# OPTIONS --safe #-}

module Cubical.HigherCategories.PreorderEnrichedPreorder where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Relation.Binary.Base
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Foundations.HLevels
open import Cubical.Reflection.Base hiding (_$_)
open import Cubical.Reflection.RecordEquiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Common.Monotone


open import Common.Preorder
open import Cubical.HigherCategories.PreorderEnriched.PreorderEnriched


open BinaryRelation


private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓc ℓc' ℓc'' ℓd ℓd' ℓd'' : Level

open Category
open PreorderEnrichedCategory


  -- Category of Preorders
PreorderCat : {ℓ ℓ' : Level} -> Category
    (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
    (ℓ-max ℓ ℓ')
PreorderCat {ℓ} {ℓ'} = record
    { ob = Preorder ℓ ℓ'
    ; Hom[_,_] = λ X Y -> MonFun X Y
    ; id = MonId
    ; _⋆_ = MonComp
    ; ⋆IdL = λ {X} {Y} f -> EqMon f f refl
    ; ⋆IdR = λ {X} {Y} f -> EqMon f f refl
    ; ⋆Assoc = λ {X} {Y} {Z} {W} f g h -> EqMon _ _ refl
    ; isSetHom = MonFunIsSet }
    

  -- Category of Preorders enriched over itself
PEPCat : {ℓ ℓ' : Level} -> (A B : Preorder ℓ ℓ') -> PreorderEnrichedCategory
    (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
    (ℓ-max ℓ ℓ')
    (ℓ-max ℓ ℓ')
PEPCat {ℓ} {ℓ'} A B = record {
    cat = PreorderCat {ℓ} {ℓ'}
   ; _≤_ = λ {X} {Y} -> _≤mon_
   ; isProp≤ = λ X Y f g -> ≤mon-prop f g
   ; isReflexive =  ≤mon-refl
   ; isTransitive = ≤mon-trans
   ; isMonotone⋆ = λ {X} {Y} {Z} {f} {f'} {g} {g'} f≤f' g≤g' ->
     λ x → ≤mon→≤mon-het g g' g≤g' (MonFun.f f x) (MonFun.f f' x) (f≤f' x) }

-- For isMonotone⋆
-- NTS:    (MonFun.f g  (MonFun.f f  x)) ≤Z
--         (MonFun.f g' (MonFun.f f' x))

-- Have: g≤g' : (y : Y .fst) →
--              (MonFun.f g y) ≤Z (MonFun.f g' y)

-- In the goal, the argument to g is distinct from the argument to g',
-- so we proceed by using the lemma stating that the usual definition
-- of ordering on monotone functions implies the version where the functions
-- are passed distinct arguments.
