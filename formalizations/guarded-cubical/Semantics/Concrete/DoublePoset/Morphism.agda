 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

-- TODO: This could be generalized to handle monotone functions on
-- both preorders and posets.

module Semantics.Concrete.DoublePoset.Morphism where

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

open import Common.Common
-- open import Common.Preorder.Base
open import Cubical.Relation.Binary.Order.Poset
open import Common.Poset.Convenience

open import Semantics.Concrete.DoublePoset.Base

open BinaryRelation


private
  variable
    ℓ ℓ' : Level
    ℓX ℓ'X ℓ''X : Level
    ℓY ℓ'Y ℓ''Y : Level
    ℓZ ℓ'Z ℓ''Z : Level

    X : DoublePoset ℓX ℓ'X ℓ''X
    Y : DoublePoset ℓY ℓ'Y ℓ''Y
    Z : DoublePoset ℓZ ℓ'Z ℓ''Z


module _ where

  -- Because of a bug with Cubical Agda's reflection, we need to declare
  -- a separate version of MonFun where the arguments to the isMon
  -- constructor are explicit.
  -- See https://github.com/agda/cubical/issues/995.
  module _ {X : DoublePoset ℓX ℓ'X ℓ''X} {Y : DoublePoset ℓY ℓ'Y ℓ''Y} where

    private

      module X = DblPosetStr (X .snd)
      module Y = DblPosetStr (Y .snd)
      _≤X_ = X._≤_
      _≤Y_ = Y._≤_
      _≈X_ = X._≈_
      _≈Y_ = Y._≈_

    monotone' : (⟨ X ⟩ -> ⟨ Y ⟩) -> Type (ℓ-max (ℓ-max ℓX ℓ'X) ℓ'Y)
    monotone' f = (x y : ⟨ X ⟩) -> x ≤X y → f x ≤Y f y       

    monotone : (⟨ X ⟩ -> ⟨ Y ⟩) -> Type (ℓ-max (ℓ-max ℓX ℓ'X) ℓ'Y)
    monotone f = {x y : ⟨ X ⟩} -> x ≤X y → f x ≤Y f y

    preserve≈' : (⟨ X ⟩ -> ⟨ Y ⟩) -> Type (ℓ-max (ℓ-max ℓX ℓ''X) ℓ''Y)
    preserve≈' f = (x y : ⟨ X ⟩) -> x ≈X y → f x ≈Y f y

    preserve≈ : (⟨ X ⟩ -> ⟨ Y ⟩) -> Type (ℓ-max (ℓ-max ℓX ℓ''X) ℓ''Y)
    preserve≈ f = {x y : ⟨ X ⟩} -> x ≈X y → f x ≈Y f y




  -- Monotone functions from X to Y
  -- This definition works with Cubical Agda's reflection.
  record DPMor' (X : DoublePoset ℓX ℓ'X ℓ''X) (Y : DoublePoset ℓY ℓ'Y ℓ''Y) :
    Type ((ℓ-max (ℓ-max ℓX (ℓ-max ℓ'X ℓ''X)) (ℓ-max ℓY (ℓ-max ℓ'Y ℓ''Y)))) where
    field
      f : (X .fst) → (Y .fst)
      isMon : monotone' {X = X} {Y = Y} f
      pres≈ : preserve≈' {X = X} {Y = Y} f


  -- This is the definition we want, where the first two arguments to isMon
  -- are implicit.
  record DPMor (X : DoublePoset ℓX ℓ'X ℓ''X) (Y : DoublePoset ℓY ℓ'Y ℓ''Y) :
    Type ((ℓ-max (ℓ-max ℓX (ℓ-max ℓ'X ℓ''X)) (ℓ-max ℓY (ℓ-max ℓ'Y ℓ''Y)))) where
    field
      f : (X .fst) → (Y .fst)
      isMon : monotone {X = X} {Y = Y} f
      pres≈ : preserve≈ {X = X} {Y = Y} f

  open DPMor


  isoDPMorDPMor' : {X : DoublePoset ℓX ℓ'X ℓ''X} {Y : DoublePoset ℓY ℓ'Y ℓ''Y} ->
    Iso (DPMor X Y) (DPMor' X Y) 
  isoDPMorDPMor' = iso
    (λ g → record { f = DPMor.f g ; isMon = λ x y x≤y → isMon g x≤y ;
                    pres≈ = λ x y x≈y -> pres≈ g x≈y})
    (λ g → record { f = DPMor'.f g ; isMon = λ {x} {y} x≤y -> DPMor'.isMon g x y x≤y ;
                    pres≈ = λ {x} {y} x≈y -> DPMor'.pres≈ g x y x≈y })
    (λ g → refl)
    (λ g → refl)


  
  isPropIsMonotone : (f : DPMor X Y) ->
    isProp (monotone {X = X} {Y = Y} (DPMor.f f))
  isPropIsMonotone {X = X} {Y = Y} f =
    isPropImplicitΠ2 (λ x y ->
      isPropΠ (λ x≤y -> DblPosetStr.is-prop-valued (Y .snd) (DPMor.f f x) (DPMor.f f y)))

  isPropIsMonotone' : (f : ⟨ X ⟩ -> ⟨ Y ⟩) ->
    isProp (monotone' {X = X} {Y = Y} f)
  isPropIsMonotone' {X = X} {Y = Y} f =
    isPropΠ3 (λ x y x≤y -> DblPosetStr.is-prop-valued (Y .snd) (f x) (f y))

  isPropPres≈' : (f : ⟨ X ⟩ -> ⟨ Y ⟩) ->
    isProp (preserve≈' {X = X} {Y = Y} f)
  isPropPres≈' {X = X} {Y = Y} f =
    isPropΠ3 (λ x y x≤y -> DblPosetStr.is-prop-valued-PER (Y .snd) (f x) (f y))


 -- Equivalence between MonFun' record and a sigma type   
  unquoteDecl DPMor'IsoΣ = declareRecordIsoΣ DPMor'IsoΣ (quote (DPMor'))


  -- Equality of monotone functions is implied by equality of the
  -- underlying functions.
  eqDPMor' :  (f g : DPMor' X Y) ->
    DPMor'.f f ≡ DPMor'.f g -> f ≡ g
  eqDPMor' {X = X} {Y = Y} f g p =
    isoFunInjective DPMor'IsoΣ f g
      (Σ≡Prop (λ h -> isProp× (isPropIsMonotone' {X = X} {Y = Y} h)
                              (isPropPres≈' {X = X} {Y = Y} h))
               p)

  eqDPMor : (f g : DPMor X Y) ->
    DPMor.f f ≡ DPMor.f g -> f ≡ g
  eqDPMor {X} {Y} f g p = isoFunInjective isoDPMorDPMor' f g (eqDPMor' _ _ p)



  -- isSet for DP morphisms
  DPMorIsSet : isSet (DPMor X Y)
  DPMorIsSet {X = X} {Y = Y} = let composedIso = (compIso isoDPMorDPMor' DPMor'IsoΣ) in
    isSetRetract
      (Iso.fun composedIso) (Iso.inv composedIso) (Iso.leftInv composedIso)
      (isSetΣSndProp
        (isSet→ (DblPosetStr.is-set (Y .snd)))
        (λ h -> isProp×
                  (isPropIsMonotone' {X = X} {Y = Y} h)
                   (isPropPres≈' {X = X} {Y = Y} h)))



  -- Ordering on DP morphisms
  module _ {X : DoublePoset ℓX ℓ'X ℓ''X} {Y : DoublePoset ℓY ℓ'Y ℓ''Y} where

    private
      module X = DblPosetStr (X .snd)
      module Y = DblPosetStr (Y .snd)
      module YPoset = PosetStr (DoublePoset→Poset Y .snd)

    _≤mon_ :
      DPMor X Y → DPMor X Y → Type (ℓ-max ℓX ℓ'Y)
    _≤mon_ f g = ∀ x -> DPMor.f f x Y.≤ DPMor.f g x

    ≤mon-prop : isPropValued _≤mon_
    ≤mon-prop f g =
      isPropΠ (λ x -> Y.is-prop-valued (DPMor.f f x) (DPMor.f g x))

    ≤mon-refl : isRefl _≤mon_
    ≤mon-refl = λ f x → Y.is-refl (DPMor.f f x)

    ≤mon-trans : isTrans _≤mon_
    ≤mon-trans = λ f g h f≤g g≤h x →
      Y.is-trans (DPMor.f f x) (DPMor.f g x) (DPMor.f h x)
        (f≤g x) (g≤h x)

    ≤mon-antisym : isAntisym _≤mon_
    ≤mon-antisym f g f≤g g≤f =
      eqDPMor f g (funExt (λ x -> Y.is-antisym (DPMor.f f x) (DPMor.f g x) (f≤g x) (g≤f x)))


    -- Alternate definition of ordering on monotone functions, where we allow for the
    -- arguments to be distinct
    _≤mon-het_ : DPMor X Y -> DPMor X Y -> Type (ℓ-max (ℓ-max ℓX ℓ'X) ℓ'Y)
    _≤mon-het_ f f' = ∀ x x' -> x X.≤ x' -> (DPMor.f f x) Y.≤ (DPMor.f f' x')

    ≤mon→≤mon-het : (f f' : DPMor X Y) -> f ≤mon f' -> f ≤mon-het f'
    ≤mon→≤mon-het f f' f≤f' = λ x x' x≤x' →
      DPMor.f f x    ≤⟨ DPMor.isMon f x≤x' ⟩
      DPMor.f f x'   ≤⟨ f≤f' x' ⟩
      DPMor.f f' x'  ◾
      where
        open PosetReasoning (DoublePoset→Poset Y)

    TwoCell→≤mon : (f g : DPMor X Y) ->
      TwoCell (X._≤_) (Y._≤_) (DPMor.f f) (DPMor.f g) ->
      f ≤mon g
    TwoCell→≤mon f g f≤g = λ x → f≤g x x (X.is-refl x)

    -- Bisimilarity relation on DP morphisms
    _≈mon_ :
      DPMor X Y -> DPMor X Y -> Type (ℓ-max (ℓ-max ℓX ℓ''X) ℓ''Y)
    _≈mon_ f g = ∀ x x' -> x X.≈ x' -> DPMor.f f x Y.≈ DPMor.f g x'

    ≈mon-prop : isPropValued _≈mon_
    ≈mon-prop f g = isPropΠ3 (λ x x' x≈x' -> Y.is-prop-valued-PER (DPMor.f f x) (DPMor.f g x'))

    ≈mon-refl : isRefl _≈mon_
    ≈mon-refl f x x' x≈x' = pres≈ f x≈x'

    ≈mon-sym : isSym _≈mon_
    ≈mon-sym f g f≈g x x' x≈x' =
      DblPosetStr.is-sym (Y .snd) (DPMor.f f x') (DPMor.f g x)
        (f≈g x' x (DblPosetStr.is-sym (X .snd) x x' x≈x'))
     -- NTS:
     --   g x ≈Y f x'
     --
     -- Since ≈Y is symmetric, STS
     --   f x' ≈Y g x
     --
     -- Then since f≈g, STS x' ≈X x which holds by assumption since ≈X is symmetric




 -- Double poset of DP morphisms between two double posets
  IntHom : DoublePoset ℓX ℓ'X ℓ''X -> DoublePoset ℓY ℓ'Y ℓ''Y ->
    DoublePoset (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) ℓ''X) ℓY) ℓ'Y) ℓ''Y) (ℓ-max ℓX ℓ'Y) (ℓ-max (ℓ-max ℓX ℓ''X) ℓ''Y)
  IntHom X Y =
    DPMor X Y ,
    dblposetstr
      DPMorIsSet
      _≤mon_
      (isorderingrelation ≤mon-prop ≤mon-refl ≤mon-trans ≤mon-antisym)
      _≈mon_
      (isper ≈mon-refl ≈mon-sym ≈mon-prop)

    -- Notation
  _==>_ : DoublePoset ℓX ℓ'X ℓ''X -> DoublePoset ℓY ℓ'Y ℓ''Y ->
    DoublePoset (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) ℓ''X) ℓY) ℓ'Y) ℓ''Y) (ℓ-max ℓX ℓ'Y) (ℓ-max (ℓ-max ℓX ℓ''X) ℓ''Y)
  X ==> Y = IntHom X Y

  infixr 20 _==>_



  -- Some basic combinators/utility functions on double poset morphisms

  MonId : {X : DoublePoset ℓX ℓ'X ℓ''X} -> DPMor X X
  MonId = record { f = λ x -> x ; isMon = λ x≤y → x≤y ; pres≈ = λ x≈y -> x≈y }

  _$_ : DPMor X Y -> ⟨ X ⟩ -> ⟨ Y ⟩
  f $ x = DPMor.f f x

  MonComp :
    DPMor X Y -> DPMor Y Z -> DPMor X Z
  MonComp f g = record {
    f = λ x -> g $ (f $ x) ;
    isMon = λ {x1} {x2} x1≤x2 → isMon g (isMon f x1≤x2) ;
    pres≈ = λ x≈x' -> pres≈ g (pres≈ f x≈x')}



