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
    ℓW ℓ'W ℓ''W : Level

    X : PosetBisim ℓX ℓ'X ℓ''X
    Y : PosetBisim ℓY ℓ'Y ℓ''Y
    Z : PosetBisim ℓZ ℓ'Z ℓ''Z
    W : PosetBisim ℓW ℓ'W ℓ''W


module _ where

  -- Because of a bug with Cubical Agda's reflection, we need to declare
  -- a separate version of MonFun where the arguments to the isMon
  -- constructor are explicit.
  -- See https://github.com/agda/cubical/issues/995.
  module _ {X : PosetBisim ℓX ℓ'X ℓ''X} {Y : PosetBisim ℓY ℓ'Y ℓ''Y} where

    private

      module X = PosetBisimStr (X .snd)
      module Y = PosetBisimStr (Y .snd)
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


    preserve≡preserve' : preserve≈' ≡ preserve≈
    preserve≡preserve' = {!!}


  -- Monotone functions from X to Y
  -- This definition works with Cubical Agda's reflection.
  record PBMor' (X : PosetBisim ℓX ℓ'X ℓ''X) (Y : PosetBisim ℓY ℓ'Y ℓ''Y) :
    Type ((ℓ-max (ℓ-max ℓX (ℓ-max ℓ'X ℓ''X)) (ℓ-max ℓY (ℓ-max ℓ'Y ℓ''Y)))) where
    field
      f : (X .fst) → (Y .fst)
      isMon : monotone' {X = X} {Y = Y} f
      pres≈ : preserve≈' {X = X} {Y = Y} f


  -- This is the definition we want, where the first two arguments to isMon
  -- are implicit.
  record PBMor (X : PosetBisim ℓX ℓ'X ℓ''X) (Y : PosetBisim ℓY ℓ'Y ℓ''Y) :
    Type ((ℓ-max (ℓ-max ℓX (ℓ-max ℓ'X ℓ''X)) (ℓ-max ℓY (ℓ-max ℓ'Y ℓ''Y)))) where
    field
      f : (X .fst) → (Y .fst)
      isMon : monotone {X = X} {Y = Y} f
      pres≈ : preserve≈ {X = X} {Y = Y} f

  open PBMor


  isoPBMorPBMor' : {X : PosetBisim ℓX ℓ'X ℓ''X} {Y : PosetBisim ℓY ℓ'Y ℓ''Y} ->
    Iso (PBMor X Y) (PBMor' X Y) 
  isoPBMorPBMor' = iso
    (λ g → record { f = PBMor.f g ; isMon = λ x y x≤y → isMon g x≤y ;
                    pres≈ = λ x y x≈y -> pres≈ g x≈y})
    (λ g → record { f = PBMor'.f g ; isMon = λ {x} {y} x≤y -> PBMor'.isMon g x y x≤y ;
                    pres≈ = λ {x} {y} x≈y -> PBMor'.pres≈ g x y x≈y })
    (λ g → refl)
    (λ g → refl)


  
  isPropIsMonotone : (f : PBMor X Y) ->
    isProp (monotone {X = X} {Y = Y} (PBMor.f f))
  isPropIsMonotone {X = X} {Y = Y} f =
    isPropImplicitΠ2 (λ x y ->
      isPropΠ (λ x≤y -> PosetBisimStr.is-prop-valued (Y .snd) (PBMor.f f x) (PBMor.f f y)))

  isPropIsMonotone' : (f : ⟨ X ⟩ -> ⟨ Y ⟩) ->
    isProp (monotone' {X = X} {Y = Y} f)
  isPropIsMonotone' {X = X} {Y = Y} f =
    isPropΠ3 (λ x y x≤y -> PosetBisimStr.is-prop-valued (Y .snd) (f x) (f y))

  isPropPres≈' : (f : ⟨ X ⟩ -> ⟨ Y ⟩) ->
    isProp (preserve≈' {X = X} {Y = Y} f)
  isPropPres≈' {X = X} {Y = Y} f =
    isPropΠ3 (λ x y x≤y -> PosetBisimStr.is-prop-valued-Bisim (Y .snd) (f x) (f y))


 -- Equivalence between MonFun' record and a sigma type   
  unquoteDecl PBMor'IsoΣ = declareRecordIsoΣ PBMor'IsoΣ (quote (PBMor'))



  -- Equality of monotone functions is implied by equality of the
  -- underlying functions.
  eqPBMor' :  (f g : PBMor' X Y) ->
    PBMor'.f f ≡ PBMor'.f g -> f ≡ g
  eqPBMor' {X = X} {Y = Y} f g p =
    isoFunInjective PBMor'IsoΣ f g
      (Σ≡Prop (λ h -> isProp× (isPropIsMonotone' {X = X} {Y = Y} h)
                              (isPropPres≈' {X = X} {Y = Y} h))
               p)

  eqPBMor : (f g : PBMor X Y) ->
    PBMor.f f ≡ PBMor.f g -> f ≡ g
  eqPBMor {X} {Y} f g p = isoFunInjective isoPBMorPBMor' f g (eqPBMor' _ _ p)



{-
  eqPBMor' : (f g : PBMor' X Y) ->
    (p : PBMor'.f f ≡ PBMor'.f g) ->
    PathP (λ i → preserve≈' {X = X} {Y = Y} (p i)) (PBMor'.pres≈ f) (PBMor'.pres≈ g) ->
    f ≡ g
  eqPBMor' {X = X} {Y = Y} f g eq1 eq2 =
    isoFunInjective PBMor'IsoΣ f g
     (ΣPathP (eq1 ,
       ΣPathP
         ((isProp→PathP (λ i → isPropIsMonotone' {X = X} {Y = Y} (eq1 i)) _ _)
         , eq2)))


  eqPBMor : (f g : PBMor X Y) ->
    (p : PBMor.f f ≡ PBMor.f g) ->
    PathP (λ i → preserve≈ {X = X} {Y = Y} (p i)) (PBMor.pres≈ f) (PBMor.pres≈ g) ->
    f ≡ g
  eqPBMor {X = X} {Y = Y} f g eq1 eq2 =
    isoFunInjective isoPBMorPBMor' f g (eqPBMor' _ _ eq1 {!eq2!})
-}

  -- isSet for PB morphisms
  PBMorIsSet : isSet (PBMor X Y)
  PBMorIsSet {X = X} {Y = Y} = let composedIso = (compIso isoPBMorPBMor' PBMor'IsoΣ) in
    isSetRetract
      (Iso.fun composedIso) (Iso.inv composedIso) (Iso.leftInv composedIso)
      -- (isSetΣ
      --   (isSet→ (PosetBisimStr.is-set (Y .snd)))
      --   (λ f → isSet×
      --            (isProp→isSet (isPropIsMonotone' {X = X} {Y = Y} f))
      --            (isSetΠ3 (λ x y x≈y → PosetBisimStr.is-set-valued (Y .snd) (f x) (f y)))))
      (isSetΣSndProp
        (isSet→ (PosetBisimStr.is-set (Y .snd)))
        (λ h -> isProp×
                  (isPropIsMonotone' {X = X} {Y = Y} h)
                   (isPropPres≈' {X = X} {Y = Y} h)))




  -- Ordering on PB morphisms
  module _ {X : PosetBisim ℓX ℓ'X ℓ''X} {Y : PosetBisim ℓY ℓ'Y ℓ''Y} where

    private
      module X = PosetBisimStr (X .snd)
      module Y = PosetBisimStr (Y .snd)
      module YPoset = PosetStr (PosetBisim→Poset Y .snd)

    _≤mon_ :
      PBMor X Y → PBMor X Y → Type (ℓ-max ℓX ℓ'Y)
    _≤mon_ f g = ∀ x -> PBMor.f f x Y.≤ PBMor.f g x

    ≤mon-prop : isPropValued _≤mon_
    ≤mon-prop f g =
      isPropΠ (λ x -> Y.is-prop-valued (PBMor.f f x) (PBMor.f g x))

    ≤mon-refl : isRefl _≤mon_
    ≤mon-refl = λ f x → Y.is-refl (PBMor.f f x)

    ≤mon-trans : isTrans _≤mon_
    ≤mon-trans = λ f g h f≤g g≤h x →
      Y.is-trans (PBMor.f f x) (PBMor.f g x) (PBMor.f h x)
        (f≤g x) (g≤h x)

    ≤mon-antisym : isAntisym _≤mon_
    ≤mon-antisym f g f≤g g≤f = eqPBMor f g {!!}
      where
        eq1 : _
        eq1 = (funExt (λ x -> Y.is-antisym (PBMor.f f x) (PBMor.f g x) (f≤g x) (g≤f x)))
      -- eqPBMor f g (funExt (λ x -> Y.is-antisym (PBMor.f f x) (PBMor.f g x) (f≤g x) (g≤f x)))


    -- Alternate definition of ordering on morphisms where we allow for the
    -- arguments to be distinct
    _≤mon-het_ : PBMor X Y -> PBMor X Y -> Type (ℓ-max (ℓ-max ℓX ℓ'X) ℓ'Y)
    _≤mon-het_ f f' = ∀ x x' -> x X.≤ x' -> (PBMor.f f x) Y.≤ (PBMor.f f' x')

    ≤mon→≤mon-het : (f f' : PBMor X Y) -> f ≤mon f' -> f ≤mon-het f'
    ≤mon→≤mon-het f f' f≤f' = λ x x' x≤x' →
      PBMor.f f x    ≤⟨ PBMor.isMon f x≤x' ⟩
      PBMor.f f x'   ≤⟨ f≤f' x' ⟩
      PBMor.f f' x'  ◾
      where
        open PosetReasoning (PosetBisim→Poset Y)

    TwoCell→≤mon : (f g : PBMor X Y) ->
      TwoCell (X._≤_) (Y._≤_) (PBMor.f f) (PBMor.f g) ->
      f ≤mon g
    TwoCell→≤mon f g f≤g = λ x → f≤g x x (X.is-refl x)



    -- Bisimilarity relation on PB morphisms
    _≈mon_ :
      PBMor X Y -> PBMor X Y -> Type (ℓ-max (ℓ-max ℓX ℓ''X) ℓ''Y)
    _≈mon_ f g = ∀ x x' -> x X.≈ x' -> PBMor.f f x Y.≈ PBMor.f g x'

    ≈mon-prop : isPropValued _≈mon_
    ≈mon-prop f g = isPropΠ3 (λ x x' x≈x' -> Y.is-prop-valued-Bisim (PBMor.f f x) (PBMor.f g x'))

    ≈mon-refl : isRefl _≈mon_
    ≈mon-refl f x x' x≈x' = pres≈ f x≈x'

    ≈mon-sym : isSym _≈mon_
    ≈mon-sym f g f≈g x x' x≈x' =
      PosetBisimStr.is-sym (Y .snd) (PBMor.f f x') (PBMor.f g x)
        (f≈g x' x (PosetBisimStr.is-sym (X .snd) x x' x≈x'))
     -- NTS:
     --   g x ≈Y f x'
     --
     -- Since ≈Y is symmetric, STS
     --   f x' ≈Y g x
     --
     -- Then since f≈g, STS x' ≈X x which holds by assumption since ≈X is symmetric




 -- PB of PB morphisms between two PB's
  IntHom : PosetBisim ℓX ℓ'X ℓ''X -> PosetBisim ℓY ℓ'Y ℓ''Y ->
    PosetBisim (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) ℓ''X) ℓY) ℓ'Y) ℓ''Y) (ℓ-max ℓX ℓ'Y) (ℓ-max (ℓ-max ℓX ℓ''X) ℓ''Y)
  IntHom X Y =
    PBMor X Y ,
    posetbisimstr
      PBMorIsSet
      _≤mon_
      (isorderingrelation ≤mon-prop ≤mon-refl ≤mon-trans ≤mon-antisym)
      _≈mon_
      (isbisim ≈mon-refl ≈mon-sym ≈mon-prop)

    -- Notation
  _==>_ : PosetBisim ℓX ℓ'X ℓ''X -> PosetBisim ℓY ℓ'Y ℓ''Y ->
    PosetBisim (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) ℓ''X) ℓY) ℓ'Y) ℓ''Y) (ℓ-max ℓX ℓ'Y) (ℓ-max (ℓ-max ℓX ℓ''X) ℓ''Y)
  X ==> Y = IntHom X Y

  infixr 20 _==>_



  -- Some basic combinators/utility functions on morphisms of posets with bisimilarity

  Id : {X : PosetBisim ℓX ℓ'X ℓ''X} -> PBMor X X
  Id = record { f = λ x -> x ; isMon = λ x≤y → x≤y ; pres≈ = λ x≈y -> x≈y }

  _$_ : PBMor X Y -> ⟨ X ⟩ -> ⟨ Y ⟩
  f $ x = PBMor.f f x

  Comp :
    PBMor X Y -> PBMor Y Z -> PBMor X Z
  Comp f g = record {
    f = λ x -> g $ (f $ x) ;
    isMon = λ {x1} {x2} x1≤x2 → isMon g (isMon f x1≤x2) ;
    pres≈ = λ x≈x' -> pres≈ g (pres≈ f x≈x')}

  _∘p_ : PBMor Y Z → PBMor X Y → PBMor X Z
  g ∘p f = Comp f g
  infixl 20 _∘p_ -- TODO is this a good level?

{-
  IdL : (f : PBMor X Y) → Comp Id f ≡ f
  IdL f = eqPBMor (Comp Id f) f refl refl

  Assoc : (f : PBMor X Y) (g : PBMor Y Z) (h : PBMor Z W) →
    Comp (Comp f g) h ≡ Comp f (Comp g h)
  Assoc f g h = eqPBMor _ _ refl refl
-}



