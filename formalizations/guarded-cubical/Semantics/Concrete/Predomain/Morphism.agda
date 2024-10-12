 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

-- TODO: This could be generalized to handle monotone functions on
-- both preorders and posets.

module Semantics.Concrete.Predomain.Morphism where

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

open import Semantics.Concrete.Predomain.Base

open BinaryRelation


private
  variable
    ℓ ℓ' : Level
    ℓX ℓ'X ℓ''X : Level
    ℓY ℓ'Y ℓ''Y : Level
    ℓZ ℓ'Z ℓ''Z : Level
    ℓW ℓ'W ℓ''W : Level

    ℓA ℓ≤A ℓ≈A : Level
    ℓA' ℓ≤A' ℓ≈A' : Level

    ℓ≤X ℓ≈X : Level
    ℓ≤Y ℓ≈Y : Level
    ℓ≤Z ℓ≈Z : Level

    X : Predomain ℓX ℓ'X ℓ''X
    Y : Predomain ℓY ℓ'Y ℓ''Y
    Z : Predomain ℓZ ℓ'Z ℓ''Z
    W : Predomain ℓW ℓ'W ℓ''W


module _ where

  -- Because of a bug with Cubical Agda's reflection, we need to declare
  -- a separate version of MonFun where the arguments to the isMon
  -- constructor are explicit.
  -- See https://github.com/agda/cubical/issues/995.
  module _ {X : Predomain ℓX ℓ'X ℓ''X} {Y : Predomain ℓY ℓ'Y ℓ''Y} where

    private

      module X = PredomainStr (X .snd)
      module Y = PredomainStr (Y .snd)
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
  record PMor' (X : Predomain ℓX ℓ'X ℓ''X) (Y : Predomain ℓY ℓ'Y ℓ''Y) :
    Type ((ℓ-max (ℓ-max ℓX (ℓ-max ℓ'X ℓ''X)) (ℓ-max ℓY (ℓ-max ℓ'Y ℓ''Y)))) where
    field
      f : (X .fst) → (Y .fst)
      isMon : monotone' {X = X} {Y = Y} f
      pres≈ : preserve≈' {X = X} {Y = Y} f


  -- This is the definition we want, where the first two arguments to isMon
  -- are implicit.
  record PMor (X : Predomain ℓX ℓ'X ℓ''X) (Y : Predomain ℓY ℓ'Y ℓ''Y) :
    Type ((ℓ-max (ℓ-max ℓX (ℓ-max ℓ'X ℓ''X)) (ℓ-max ℓY (ℓ-max ℓ'Y ℓ''Y)))) where
    field
      f : (X .fst) → (Y .fst)
      isMon : monotone {X = X} {Y = Y} f
      pres≈ : preserve≈ {X = X} {Y = Y} f

  open PMor


  isoPMorPMor' : {X : Predomain ℓX ℓ'X ℓ''X} {Y : Predomain ℓY ℓ'Y ℓ''Y} ->
    Iso (PMor X Y) (PMor' X Y) 
  isoPMorPMor' = iso
    (λ g → record { f = PMor.f g ; isMon = λ x y x≤y → isMon g x≤y ;
                    pres≈ = λ x y x≈y -> pres≈ g x≈y})
    (λ g → record { f = PMor'.f g ; isMon = λ {x} {y} x≤y -> PMor'.isMon g x y x≤y ;
                    pres≈ = λ {x} {y} x≈y -> PMor'.pres≈ g x y x≈y })
    (λ g → refl)
    (λ g → refl)


  
  isPropIsMonotone : (f : PMor X Y) ->
    isProp (monotone {X = X} {Y = Y} (PMor.f f))
  isPropIsMonotone {X = X} {Y = Y} f =
    isPropImplicitΠ2 (λ x y ->
      isPropΠ (λ x≤y -> PredomainStr.is-prop-valued (Y .snd) (PMor.f f x) (PMor.f f y)))

  isPropIsMonotone' : (f : ⟨ X ⟩ -> ⟨ Y ⟩) ->
    isProp (monotone' {X = X} {Y = Y} f)
  isPropIsMonotone' {X = X} {Y = Y} f =
    isPropΠ3 (λ x y x≤y -> PredomainStr.is-prop-valued (Y .snd) (f x) (f y))

  isPropPres≈' : (f : ⟨ X ⟩ -> ⟨ Y ⟩) ->
    isProp (preserve≈' {X = X} {Y = Y} f)
  isPropPres≈' {X = X} {Y = Y} f =
    isPropΠ3 (λ x y x≤y -> PredomainStr.is-prop-valued-Bisim (Y .snd) (f x) (f y))


 -- Equivalence between MonFun' record and a sigma type   
  unquoteDecl PMor'IsoΣ = declareRecordIsoΣ PMor'IsoΣ (quote (PMor'))



  -- Equality of monotone functions is implied by equality of the
  -- underlying functions.
  eqPMor' :  (f g : PMor' X Y) ->
    PMor'.f f ≡ PMor'.f g -> f ≡ g
  eqPMor' {X = X} {Y = Y} f g p =
    isoFunInjective PMor'IsoΣ f g
      (Σ≡Prop (λ h -> isProp× (isPropIsMonotone' {X = X} {Y = Y} h)
                              (isPropPres≈' {X = X} {Y = Y} h))
               p)

  eqPMor : (f g : PMor X Y) ->
    PMor.f f ≡ PMor.f g -> f ≡ g
  eqPMor {X} {Y} f g p = isoFunInjective isoPMorPMor' f g (eqPMor' _ _ p)



{-
  eqPMor' : (f g : PMor' X Y) ->
    (p : PMor'.f f ≡ PMor'.f g) ->
    PathP (λ i → preserve≈' {X = X} {Y = Y} (p i)) (PMor'.pres≈ f) (PMor'.pres≈ g) ->
    f ≡ g
  eqPMor' {X = X} {Y = Y} f g eq1 eq2 =
    isoFunInjective PMor'IsoΣ f g
     (ΣPathP (eq1 ,
       ΣPathP
         ((isProp→PathP (λ i → isPropIsMonotone' {X = X} {Y = Y} (eq1 i)) _ _)
         , eq2)))


  eqPMor : (f g : PMor X Y) ->
    (p : PMor.f f ≡ PMor.f g) ->
    PathP (λ i → preserve≈ {X = X} {Y = Y} (p i)) (PMor.pres≈ f) (PMor.pres≈ g) ->
    f ≡ g
  eqPMor {X = X} {Y = Y} f g eq1 eq2 =
    isoFunInjective isoPMorPMor' f g (eqPMor' _ _ eq1 {!eq2!})
-}

  -- isSet for PB morphisms
  PMorIsSet : isSet (PMor X Y)
  PMorIsSet {X = X} {Y = Y} = let composedIso = (compIso isoPMorPMor' PMor'IsoΣ) in
    isSetRetract
      (Iso.fun composedIso) (Iso.inv composedIso) (Iso.leftInv composedIso)
      -- (isSetΣ
      --   (isSet→ (PredomainStr.is-set (Y .snd)))
      --   (λ f → isSet×
      --            (isProp→isSet (isPropIsMonotone' {X = X} {Y = Y} f))
      --            (isSetΠ3 (λ x y x≈y → PredomainStr.is-set-valued (Y .snd) (f x) (f y)))))
      (isSetΣSndProp
        (isSet→ (PredomainStr.is-set (Y .snd)))
        (λ h -> isProp×
                  (isPropIsMonotone' {X = X} {Y = Y} h)
                   (isPropPres≈' {X = X} {Y = Y} h)))




  -- Ordering on PB morphisms
  module _ {X : Predomain ℓX ℓ'X ℓ''X} {Y : Predomain ℓY ℓ'Y ℓ''Y} where

    private
      module X = PredomainStr (X .snd)
      module Y = PredomainStr (Y .snd)
      module YPoset = PosetStr (Predomain→Poset Y .snd)

    _≤mon_ :
      PMor X Y → PMor X Y → Type (ℓ-max ℓX ℓ'Y)
    _≤mon_ f g = ∀ x -> PMor.f f x Y.≤ PMor.f g x

    ≤mon-prop : isPropValued _≤mon_
    ≤mon-prop f g =
      isPropΠ (λ x -> Y.is-prop-valued (PMor.f f x) (PMor.f g x))

    ≤mon-refl : isRefl _≤mon_
    ≤mon-refl = λ f x → Y.is-refl (PMor.f f x)

    ≤mon-trans : isTrans _≤mon_
    ≤mon-trans = λ f g h f≤g g≤h x →
      Y.is-trans (PMor.f f x) (PMor.f g x) (PMor.f h x)
        (f≤g x) (g≤h x)

    ≤mon-antisym : isAntisym _≤mon_
    ≤mon-antisym f g f≤g g≤f = eqPMor f g {!!}
      where
        eq1 : _
        eq1 = (funExt (λ x -> Y.is-antisym (PMor.f f x) (PMor.f g x) (f≤g x) (g≤f x)))
      -- eqPMor f g (funExt (λ x -> Y.is-antisym (PMor.f f x) (PMor.f g x) (f≤g x) (g≤f x)))


    -- Alternate definition of ordering on morphisms where we allow for the
    -- arguments to be distinct
    _≤mon-het_ : PMor X Y -> PMor X Y -> Type (ℓ-max (ℓ-max ℓX ℓ'X) ℓ'Y)
    _≤mon-het_ f f' = ∀ x x' -> x X.≤ x' -> (PMor.f f x) Y.≤ (PMor.f f' x')

    ≤mon→≤mon-het : (f f' : PMor X Y) -> f ≤mon f' -> f ≤mon-het f'
    ≤mon→≤mon-het f f' f≤f' = λ x x' x≤x' →
      PMor.f f x    ≤⟨ PMor.isMon f x≤x' ⟩
      PMor.f f x'   ≤⟨ f≤f' x' ⟩
      PMor.f f' x'  ◾
      where
        open PosetReasoning (Predomain→Poset Y)

    TwoCell→≤mon : (f g : PMor X Y) ->
      TwoCell (X._≤_) (Y._≤_) (PMor.f f) (PMor.f g) ->
      f ≤mon g
    TwoCell→≤mon f g f≤g = λ x → f≤g x x (X.is-refl x)



    -- Bisimilarity relation on PB morphisms
    _≈mon_ :
      PMor X Y -> PMor X Y -> Type (ℓ-max (ℓ-max ℓX ℓ''X) ℓ''Y)
    _≈mon_ f g = ∀ x x' -> x X.≈ x' -> PMor.f f x Y.≈ PMor.f g x'

    ≈mon-prop : isPropValued _≈mon_
    ≈mon-prop f g = isPropΠ3 (λ x x' x≈x' -> Y.is-prop-valued-Bisim (PMor.f f x) (PMor.f g x'))

    ≈mon-refl : isRefl _≈mon_
    ≈mon-refl f x x' x≈x' = pres≈ f x≈x'

    ≈mon-sym : isSym _≈mon_
    ≈mon-sym f g f≈g x x' x≈x' =
      PredomainStr.is-sym (Y .snd) (PMor.f f x') (PMor.f g x)
        (f≈g x' x (PredomainStr.is-sym (X .snd) x x' x≈x'))
     -- NTS:
     --   g x ≈Y f x'
     --
     -- Since ≈Y is symmetric, STS
     --   f x' ≈Y g x
     --
     -- Then since f≈g, STS x' ≈X x which holds by assumption since ≈X is symmetric



 -- PB of PB morphisms between two PB's
  IntHom : Predomain ℓX ℓ'X ℓ''X -> Predomain ℓY ℓ'Y ℓ''Y ->
    Predomain (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) ℓ''X) ℓY) ℓ'Y) ℓ''Y) (ℓ-max ℓX ℓ'Y) (ℓ-max (ℓ-max ℓX ℓ''X) ℓ''Y)
  IntHom X Y =
    PMor X Y ,
    predomainstr
      PMorIsSet
      _≤mon_
      (isorderingrelation ≤mon-prop ≤mon-refl ≤mon-trans ≤mon-antisym)
      _≈mon_
      (isbisim ≈mon-refl ≈mon-sym ≈mon-prop)

    -- Notation
  _==>_ : Predomain ℓX ℓ'X ℓ''X -> Predomain ℓY ℓ'Y ℓ''Y ->
    Predomain (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) ℓ''X) ℓY) ℓ'Y) ℓ''Y) (ℓ-max ℓX ℓ'Y) (ℓ-max (ℓ-max ℓX ℓ''X) ℓ''Y)
  X ==> Y = IntHom X Y

  infixr 20 _==>_



  -- Some basic combinators/utility functions on morphisms of posets with bisimilarity

  Id : {X : Predomain ℓX ℓ'X ℓ''X} -> PMor X X
  Id = record { f = λ x -> x ; isMon = λ x≤y → x≤y ; pres≈ = λ x≈y -> x≈y }

  _$_ : PMor X Y -> ⟨ X ⟩ -> ⟨ Y ⟩
  f $ x = PMor.f f x

  Comp :
    PMor X Y -> PMor Y Z -> PMor X Z
  Comp f g = record {
    f = λ x -> g $ (f $ x) ;
    isMon = λ {x1} {x2} x1≤x2 → isMon g (isMon f x1≤x2) ;
    pres≈ = λ x≈x' -> pres≈ g (pres≈ f x≈x')}

  _∘p_ : PMor Y Z → PMor X Y → PMor X Z
  g ∘p f = Comp f g
  infixl 20 _∘p_ -- TODO is this a good level?


  ≈mon-comp : {X : Predomain ℓX ℓ≤X ℓ≈X} {Y : Predomain ℓY ℓ≤Y ℓ≈Y} {Z : Predomain ℓZ ℓ≤Z ℓ≈Z}
    {f g : PMor X Y} {f' g' : PMor Y Z} → f ≈mon g → f' ≈mon g' → (f' ∘p f) ≈mon (g' ∘p g)
  ≈mon-comp f≈g f'≈g' x₁ x₂ x₁≈x₂ = f'≈g' _ _ (f≈g x₁ x₂ x₁≈x₂)



  -- Identity and associativity of composition:

  CompPD-IdL : (f : PMor X Y) → Id ∘p f ≡ f
  CompPD-IdL g = eqPMor _ _ refl

  CompPD-IdR : (f : PMor X Y) → f ∘p Id ≡ f
  CompPD-IdR g = eqPMor _ _ refl

  CompPD-Assoc : (f : PMor X Y) (g : PMor Y Z) (h : PMor Z W) →
    Comp (Comp f g) h ≡ Comp f (Comp g h)
  CompPD-Assoc f g h = eqPMor _ _ refl



-- Isomorphism of predomains

record PredomIso (A : Predomain ℓA ℓ≤A ℓ≈A) (A' : Predomain ℓA' ℓ≤A' ℓ≈A') :
  Type (ℓ-max (ℓ-max (ℓ-max ℓA ℓ≤A) ℓ≈A) (ℓ-max (ℓ-max ℓA' ℓ≤A') ℓ≈A')) where
  open PMor
  field
    fun : PMor A A'
    inv : PMor A' A
    invRight : section (fun .f) (inv .f)
    invLeft  : retract (fun .f) (inv .f)

module _ {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  (isom : PredomIso A A') where

  open PredomIso

  private
    module isom = PredomIso isom

  PredomIso-Inv : PredomIso A' A
  PredomIso-Inv .fun = isom.inv
  PredomIso-Inv .inv = isom.fun
  PredomIso-Inv .invRight = isom.invLeft
  PredomIso-Inv .invLeft = isom.invRight


