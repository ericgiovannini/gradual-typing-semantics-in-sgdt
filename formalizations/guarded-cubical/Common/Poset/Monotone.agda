 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

-- TODO: This could be generalized to handle monotone functions on
-- both preorders and posets.

module Common.Poset.Monotone where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Binary.Base
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma

-- open import Common.Preorder.Base
open import Cubical.Relation.Binary.Order.Poset
open import Common.Poset.Convenience


open BinaryRelation


private
  variable
    ℓ ℓ' : Level
    ℓX ℓ'X ℓY ℓ'Y : Level


module _ where

  -- Because of a bug with Cubical Agda's reflection, we need to declare
  -- a separate version of MonFun where the arguments to the isMon
  -- constructor are explicit.
  -- See https://github.com/agda/cubical/issues/995.
  module _ {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} where

    private

      module X = PosetStr (X .snd)
      module Y = PosetStr (Y .snd)
      _≤X_ = X._≤_
      _≤Y_ = Y._≤_

    monotone' : (⟨ X ⟩ -> ⟨ Y ⟩) -> Type (ℓ-max (ℓ-max ℓX ℓ'X) ℓ'Y)
    monotone' f = (x y : ⟨ X ⟩) -> x ≤X y → f x ≤Y f y       

    monotone : (⟨ X ⟩ -> ⟨ Y ⟩) -> Type (ℓ-max (ℓ-max ℓX ℓ'X) ℓ'Y)
    monotone f = {x y : ⟨ X ⟩} -> x ≤X y → f x ≤Y f y   

  -- Monotone functions from X to Y
  -- This definition works with Cubical Agda's reflection.
  record MonFun' (X : Poset ℓX ℓ'X) (Y : Poset ℓY ℓ'Y) :
    Type ((ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y))) where
    field
      f : (X .fst) → (Y .fst)
      isMon : monotone' {X = X} {Y = Y} f

  -- This is the definition we want, where the first two arguments to isMon
  -- are implicit.
  record MonFun (X : Poset ℓX ℓ'X) (Y : Poset ℓY ℓ'Y) :
    Type (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) where
    field
      f : (X .fst) → (Y .fst)
      isMon : monotone {X = X} {Y = Y} f

  open MonFun


  isoMonFunMonFun' : {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} -> Iso (MonFun X Y) (MonFun' X Y) 
  isoMonFunMonFun' = iso
    (λ g → record { f = MonFun.f g ; isMon = λ x y x≤y → isMon g x≤y })
    (λ g → record { f = MonFun'.f g ; isMon = λ {x} {y} x≤y -> MonFun'.isMon g x y x≤y })
    (λ g → refl)
    (λ g → refl)

  
  isPropIsMon : {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} -> (f : MonFun X Y) ->
    isProp (monotone {X = X} {Y = Y} (MonFun.f f))
  isPropIsMon {X = X} {Y = Y} f =
    isPropImplicitΠ2 (λ x y ->
      isPropΠ (λ x≤y -> isPropValued-poset Y (MonFun.f f x) (MonFun.f f y)))

  isPropIsMon' : {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} -> (f : ⟨ X ⟩ -> ⟨ Y ⟩) ->
    isProp (monotone' {X = X} {Y = Y} f)
  isPropIsMon' {X = X} {Y = Y} f =
    isPropΠ3 (λ x y x≤y -> isPropValued-poset Y (f x) (f y))


 -- Equivalence between MonFun' record and a sigma type   
  unquoteDecl MonFun'IsoΣ = declareRecordIsoΣ MonFun'IsoΣ (quote (MonFun'))


  -- Equality of monotone functions is implied by equality of the
  -- underlying functions.
  eqMon' : {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} -> (f g : MonFun' X Y) ->
    MonFun'.f f ≡ MonFun'.f g -> f ≡ g
  eqMon' {X = X} {Y = Y} f g p = isoFunInjective MonFun'IsoΣ f g
    (Σ≡Prop (λ h → isPropΠ3 (λ y z q → isPropValued-poset Y (h y) (h z))) p)

  eqMon : {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} -> (f g : MonFun X Y) ->
    MonFun.f f ≡ MonFun.f g -> f ≡ g
  eqMon {X} {Y} f g p = isoFunInjective isoMonFunMonFun' f g (eqMon' _ _ p)


  -- isSet for monotone functions
  MonFunIsSet : {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} -> isSet (MonFun X Y)
  MonFunIsSet {X = X} {Y = Y} = let composedIso = (compIso isoMonFunMonFun' MonFun'IsoΣ) in
    isSetRetract
      (Iso.fun composedIso) (Iso.inv composedIso) (Iso.leftInv composedIso)
      (isSetΣSndProp
        (isSet→ (isSet-poset Y))
        (isPropIsMon' {X = X} {Y = Y}))



 -- Ordering on monotone functions
  module _ {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y}  where

    _≤mon_ :
      MonFun X Y → MonFun X Y → Type (ℓ-max ℓX ℓ'Y)
    _≤mon_ f g = ∀ x -> rel Y (MonFun.f f x) (MonFun.f g x)

    ≤mon-prop : isPropValued _≤mon_
    ≤mon-prop f g =
      isPropΠ (λ x -> isPropValued-poset Y (MonFun.f f x) (MonFun.f g x))

    ≤mon-refl : isRefl _≤mon_
    ≤mon-refl = λ f x → reflexive Y (MonFun.f f x)

    ≤mon-trans : isTrans _≤mon_
    ≤mon-trans = λ f g h f≤g g≤h x →
      transitive Y (MonFun.f f x) (MonFun.f g x) (MonFun.f h x)
        (f≤g x) (g≤h x)

    ≤mon-antisym : isAntisym _≤mon_
    ≤mon-antisym f g f≤g g≤f =
      eqMon f g (funExt (λ x -> antisym Y (MonFun.f f x) (MonFun.f g x) (f≤g x) (g≤f x)))

    -- Alternate definition of ordering on monotone functions, where we allow for the
    -- arguments to be distinct
    _≤mon-het_ : MonFun X Y -> MonFun X Y -> Type (ℓ-max (ℓ-max ℓX ℓ'X) ℓ'Y)
    _≤mon-het_ f f' = ∀ x x' -> rel X x x' -> rel Y (MonFun.f f x) (MonFun.f f' x')

    ≤mon→≤mon-het : (f f' : MonFun X Y) -> f ≤mon f' -> f ≤mon-het f'
    ≤mon→≤mon-het f f' f≤f' = λ x x' x≤x' →
      MonFun.f f x    ≤⟨ MonFun.isMon f x≤x' ⟩
      MonFun.f f x'   ≤⟨ f≤f' x' ⟩
      MonFun.f f' x'  ◾
      where
        open PosetReasoning Y



 -- Predomain of monotone functions between two predomains
  IntHom : Poset ℓX ℓ'X -> Poset ℓY ℓ'Y ->
    Poset (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) ℓY) ℓ'Y) (ℓ-max ℓX ℓ'Y)
  IntHom X Y =
    MonFun X Y ,
    (posetstr
      (_≤mon_)
      (isposet MonFunIsSet ≤mon-prop ≤mon-refl ≤mon-trans ≤mon-antisym))

    -- Notation
  _==>_ : Poset ℓX ℓ'X -> Poset ℓY ℓ'Y ->
    Poset (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) ℓY) ℓ'Y) (ℓ-max ℓX ℓ'Y) -- (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  X ==> Y = IntHom X Y

  infixr 20 _==>_



  -- Some basic combinators/utility functions on monotone functions

  MonId : {X : Poset ℓ ℓ'} -> MonFun X X
  MonId = record { f = λ x -> x ; isMon = λ x≤y → x≤y }

  _$_ : {X Y : Poset ℓ ℓ'} -> MonFun X Y -> ⟨ X ⟩ -> ⟨ Y ⟩
  f $ x = MonFun.f f x

  MonComp : {X Y Z : Poset ℓ ℓ'} ->
    MonFun X Y -> MonFun Y Z -> MonFun X Z
  MonComp f g = record {
    f = λ x -> g $ (f $ x) ;
    isMon = λ {x1} {x2} x1≤x2 → isMon g (isMon f x1≤x2) }

