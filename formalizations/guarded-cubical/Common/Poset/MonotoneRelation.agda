{-# OPTIONS --guarded --rewriting #-}


-- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Common.Poset.MonotoneRelation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.Univalence

open import Common.Common
open import Common.Poset.Convenience
open import Common.Poset.Constructions
open import Common.Poset.Monotone hiding (monotone)

open BinaryRelation


private
  variable
    ℓX ℓ'X ℓY ℓ'Y ℓZ ℓ'Z : Level
    ℓX' ℓ'X' ℓY' ℓ'Y' ℓZ' ℓ'Z' : Level
    ℓ ℓ' ℓR ℓR' : Level
    ℓo : Level

    X : Poset ℓX ℓ'X
    Y : Poset ℓY ℓ'Y


{-
record IsMonRel' {X Y : Poset ℓ ℓ'} (R : ⟨ X ⟩ -> ⟨ Y ⟩ -> Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor ismonrel

  module X = PosetStr (X .snd)
  module Y = PosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_

  field
    isPropValued : (x : ⟨ X ⟩) -> (y : ⟨ Y ⟩) -> isProp (R x y)
    isAntitone : ∀ x' x y  -> x' ≤X x -> R x y -> R x' y
    isMonotone : ∀ x  y y' -> R x y -> y ≤Y y' -> R x y'

unquoteDecl IsMonRel'IsoΣ = declareRecordIsoΣ IsMonRel'IsoΣ (quote (IsMonRel'))
-}



-- Monotone relations between posets X and Y
-- (antitone in X, monotone in Y).
--
-- TODO allow X and Y to have different levels
-- record MonRel (X Y : Poset ℓ ℓ') (ℓR : Level) :
--   Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓR)) where
record MonRel (X : Poset ℓX ℓ'X) (Y : Poset ℓY ℓ'Y) (ℓR : Level) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) (ℓ-suc ℓR)) where
  module X = PosetStr (X .snd)
  module Y = PosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    R : ⟨ X ⟩ -> ⟨ Y ⟩ -> Type ℓR
    is-prop-valued : (x : ⟨ X ⟩) -> (y : ⟨ Y ⟩) -> isProp (R x y)
    is-antitone : ∀ {x' x y} -> x' ≤X x -> R x y -> R x' y
    is-monotone : ∀ {x y y'} -> R x y -> y ≤Y y' -> R x y'

open MonRel hiding (module X ; module Y ; _≤X_ ; _≤Y_)

record MonRel' (X : Poset ℓX ℓ'X) (Y : Poset ℓY ℓ'Y) (ℓR : Level) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) (ℓ-suc ℓR)) where
  module X = PosetStr (X .snd)
  module Y = PosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    R : ⟨ X ⟩ -> ⟨ Y ⟩ -> hProp ℓR
    is-antitone : ∀ x' x y -> x' ≤X x -> ⟨ R x y ⟩ -> ⟨ R x' y ⟩
    is-monotone : ∀ x y y' -> ⟨ R x y ⟩ -> y ≤Y y' -> ⟨ R x y' ⟩

-- Iso between MonRel and MonRel'
MonRel≅MonRel' : ∀ {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} ->
  Iso (MonRel X Y ℓR) (MonRel' X Y ℓR)
MonRel≅MonRel' = iso
  (λ S -> record {
    R = λ x y -> S .MonRel.R x y , S .MonRel.is-prop-valued x y ;
    is-antitone = λ x' x y x'≤x xSy → S .MonRel.is-antitone x'≤x xSy ;
    is-monotone = λ x y y' xSy y≤y' → S .MonRel.is-monotone xSy y≤y' })

  (λ S → record {
    R = λ x y -> fst (S .MonRel'.R x y) ;
    is-prop-valued = λ x y -> snd (S .MonRel'.R x y) ;
    is-antitone = λ {x'} {x} {y} x'≤x xSy →
      S .MonRel'.is-antitone x' x y x'≤x xSy ;
    is-monotone = λ {x} {y} {y'} xSy y≤y' ->
      S .MonRel'.is-monotone x y y' xSy y≤y' })

  (λ b → refl)

  (λ a → refl)


-- Equivalence between MonRel' record and a sigma type   
unquoteDecl MonRel'IsoΣ = declareRecordIsoΣ MonRel'IsoΣ (quote (MonRel'))


-- MonRel' is a Set
isSetMonRel' : {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} -> isSet (MonRel' X Y ℓR)
isSetMonRel' = isSetRetract
  (Iso.fun MonRel'IsoΣ) (Iso.inv MonRel'IsoΣ)
  (Iso.leftInv MonRel'IsoΣ)
    (isSetΣSndProp
      (isSetΠ2 (λ _ _ -> isSetHProp))
      (λ R -> isProp× (isPropΠ5 (λ _ _ _ _ _ -> snd (R _ _)))
                      (isPropΠ5 (λ _ _ _ _ _ -> snd (R _ _)))))


-- MonRel is a Set
isSetMonRel : {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} -> isSet (MonRel X Y ℓR)
isSetMonRel = {!!}

-- Equality of monotone relations follows from equality
-- of their underlying relation
eqMonRel : {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} -> (R S : MonRel X Y ℓR) ->
  MonRel.R R ≡ MonRel.R S -> R ≡ S
eqMonRel = {!!}


module MonReasoning {ℓR : Level} {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} where
  module X = PosetStr (X .snd)
  module Y = PosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  
  
  -- _Anti⟨_⟩_: R x y -> x'≤X x -> R x' y
  [_]_Anti⟨_⟩_ : (S : MonRel X Y ℓR) ->
    (x' : ⟨ X ⟩) -> {x : ⟨ X ⟩} -> {y : ⟨ Y ⟩} ->
    x' ≤X x -> (S .MonRel.R) x y -> (S .MonRel.R) x' y
  [ S ] x' Anti⟨ x'≤x ⟩ x≤y = S .MonRel.is-antitone x'≤x x≤y


  [_]_Mon⟨_⟩_ : (S : MonRel X Y ℓR) ->
    (x : ⟨ X ⟩) -> {y y' : ⟨ Y ⟩} ->
    (S .MonRel.R) x y -> y ≤Y y' -> (S .MonRel.R x y')
  [ S ] x Mon⟨ x≤y ⟩ y≤y' = S .MonRel.is-monotone x≤y y≤y'


-- A sort of "identity" monotone relation.
-- Although it's not necessarily equal to the equality relation on
-- the underlying set of X, it *is* a unit for left and right
-- composition with an arbitrary monotone relation, as we will
-- show below.
poset-monrel : {ℓo : Level} -> (X : Poset ℓ ℓ') -> MonRel X X (ℓ-max ℓ' ℓo)
poset-monrel {ℓ' = ℓ'} {ℓo = ℓo} X = record {
  R = λ x x' -> Lift {i = ℓ'} {j = ℓo} (rel X x x') ;
  is-prop-valued = λ x x' -> isOfHLevelLift 1 (isPropValued-poset X x x') ;
  is-antitone = λ {x'} {x} {y}  x'≤x x≤y -> lift (transitive X x' x y x'≤x (lower x≤y)) ;
  is-monotone = λ {x}  {y} {y'} x≤y y≤y' -> lift (transitive X x y y' (lower x≤y) y≤y') }


-- Composing with functions on either side
functionalRel : {X' : Poset ℓX' ℓ'X'} {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} {Y' : Poset ℓY' ℓ'Y'} ->
  (f : MonFun X' X) ->
  (g : MonFun Y' Y) ->
  (R : MonRel X Y ℓR) ->
  MonRel X' Y' ℓR
functionalRel f g R = record {
  R = λ x' y' -> MonRel.R R (MonFun.f f x') (MonFun.f g y') ;
  is-prop-valued = λ x' y' -> MonRel.is-prop-valued R (MonFun.f f x') (MonFun.f g y') ;
  is-antitone = λ {x'1} {x'2} {y}   x'1≤x'2 H → MonRel.is-antitone R (MonFun.isMon f x'1≤x'2) H ;
  is-monotone = λ {x'}  {y'1} {y'2} H y'1≤y'2 → MonRel.is-monotone R H (MonFun.isMon g y'1≤y'2) }
  

-- Composing monotone relations
-- Note that becasue of the quantification over elements of Y,
-- the universe level of the resulting relation involves an
-- ℓ-max with ℓ (i.e. the level of the elements in Y)
CompMonRel : -- {ℓX ℓ'X ℓY ℓ'Y ℓZ ℓ'Z : Level} {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} {Z : Poset ℓZ ℓ'Z} ->
  {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} {Z : Poset ℓZ ℓ'Z} ->
  MonRel X Y ℓR ->
  MonRel Y Z ℓR ->
  MonRel X Z (ℓ-max ℓY ℓR)
CompMonRel {ℓ''} {X = X} {Y = Y} {Z = Z} R1 R2 = record {
  R = λ x z -> ∥ compRel (MonRel.R R1) (MonRel.R R2) x z ∥₁ ;
  is-prop-valued = λ x z -> isPropPropTrunc ;
  is-antitone = λ x'≤x H -> elim (λ _ -> isPropPropTrunc) (λ p -> ∣ antitone x'≤x p ∣₁) H ;
  is-monotone = λ H y≤y' -> {!!} }
    where
      antitone : {x' x : ⟨ X ⟩} {z : ⟨ Z ⟩} ->
        rel X x' x ->
        compRel (MonRel.R R1) (MonRel.R R2) x z ->
        compRel (MonRel.R R1) (MonRel.R R2) x' z 
      antitone x'≤x (y , xR1y , yR2z) = y , (MonRel.is-antitone R1 x'≤x xR1y) , yR2z

      monotone : {x : ⟨ X ⟩} {z z' : ⟨ Z ⟩} ->
        compRel (MonRel.R R1) (MonRel.R R2) x z ->
        rel Z z z' ->
        compRel (MonRel.R R1) (MonRel.R R2) x z'
      monotone (y , xR1y , yR2z) z≤z' = y , xR1y , (MonRel.is-monotone R2 yR2z z≤z')


-- Lifting a monotone relation to a higher universe level
LiftR : {ℓR' : Level} {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} (R : MonRel X Y ℓR) ->
  MonRel X Y (ℓ-max ℓR ℓR')
LiftR {ℓR' = ℓR'} R = record {
  R = λ x y -> Lift {j = ℓR'} (R .MonRel.R x y) ;
  is-prop-valued = λ x y -> isOfHLevelLift 1 (R .MonRel.is-prop-valued x y) ;
  is-antitone = λ x'≤x xRy -> lift (R .MonRel.is-antitone x'≤x (lower xRy)) ;
  is-monotone = λ xRy y≤y' -> lift (R .MonRel.is-monotone (lower xRy) y≤y') }



-- Composing a monotone relation R with the underlying relation of
-- a poset yields R.
CompUnitLeft-Lift : {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} -> (R : MonRel X Y ℓR) ->
  CompMonRel (poset-monrel {ℓo = ℓR} X) (LiftR {ℓR' = ℓ'X} R) ≡
  LiftR {ℓR' = ℓ-max ℓX ℓ'X} R
CompUnitLeft-Lift {X = X} R = eqMonRel _ _
  (funExt (λ x ->
    funExt (λ y ->
      hPropExt isPropPropTrunc (MonRel.is-prop-valued (LiftR R) x y)
        (λ H -> elim (λ _ -> MonRel.is-prop-valued (LiftR R) x y)
                (λ { (x' , x≤x' , x'Ry) ->
                  lift (MonRel.is-antitone R (lower x≤x') (lower x'Ry))
                  -- or : MonRel.is-antitone (LiftR R) (lower x≤x') (lift (lower x'Ry))
                  }) H)
        (λ xRy -> ∣ x , (lift (reflexive X x) , lift (lower xRy)) ∣₁))))


CompUnitLeft : {X Y : Poset ℓ ℓ} -> (R : MonRel X Y ℓ) ->
  CompMonRel (poset-monrel {ℓo = ℓ} X) R ≡ R
CompUnitLeft {X = X} R = eqMonRel _ _
  (funExt λ x ->
    funExt (λ y ->
      hPropExt isPropPropTrunc (R .MonRel.is-prop-valued x y)
        (λ H ->
          elim
            (λ _ -> R .MonRel.is-prop-valued x y)
            (λ { (x' , x≤x' , x'Ry) ->
                R .MonRel.is-antitone (lower x≤x') x'Ry})
            H)

        (λ xRy -> ∣ x , lift (reflexive X x) , xRy ∣₁)))

CompUnitRight : {X Y : Poset ℓ ℓ} -> (R : MonRel X Y ℓ) ->
  CompMonRel {!!} {!!} ≡ {!!}
CompUnitRight = {!!}

-- Composition of monotone relations is associative
CompAssoc : {!!}
CompAssoc = {!!}



-- Product of monotone relations
_×monrel_ : {X : Poset ℓX ℓ'X} {X' : Poset ℓX' ℓ'X'}
            {Y : Poset ℓY ℓ'Y} {Y' : Poset ℓY' ℓ'Y'} ->
  MonRel X X' ℓR ->
  MonRel Y Y' ℓR' ->
  MonRel (X ×p Y) (X' ×p Y') (ℓ-max ℓR ℓR')
(R ×monrel S) .R (x , y) (x' , y') = R.R x x' × S.R y y'
  where module R = MonRel R
        module S = MonRel S
(R ×monrel S) .is-prop-valued (x , y) (x' , y') =
  isProp× (R.is-prop-valued x x') (S.is-prop-valued y y')
  where module R = MonRel R
        module S = MonRel S
(R ×monrel S) .is-antitone {x' = x'1 , y'1} {x = x'2 , y'2} {y = x , y}
  (x'1≤x'2 , y'1≤y'2) (x'2Rx , y'2Sy) =
  (R.is-antitone x'1≤x'2 x'2Rx) , (S.is-antitone y'1≤y'2 y'2Sy)
  where module R = MonRel R
        module S = MonRel S
(R ×monrel S) .is-monotone {x = x , y} {y = x'1 , y'1} {y' = x'2 , y'2}
  (xRx'1 , ySy'1) (x'1≤x'2 , y'1≤y'2) =
  (R.is-monotone xRx'1 x'1≤x'2) , S.is-monotone ySy'1 y'1≤y'2
  where module R = MonRel R
        module S = MonRel S


--
-- Monotone relation between function spaces
--
_==>monrel_ : {ℓR : Level} {Ai Ao Bi Bo : Poset ℓ ℓ'} ->
  MonRel Ai Bi ℓR ->
  MonRel Ao Bo ℓR ->
  MonRel (Ai ==> Ao) (Bi ==> Bo) (ℓ-max ℓ ℓR)
R ==>monrel S = record {
  R = λ f g ->
    TwoCell (MonRel.R R) (MonRel.R S) (MonFun.f f) (MonFun.f g)  ;
  is-prop-valued = λ f g -> isPropTwoCell (S .MonRel.is-prop-valued) ;
  is-antitone = λ {f1} {f2} {g} f1≤f2 f1≤g  a b aRb →
    S .MonRel.is-antitone (f1≤f2 a) (f1≤g a b aRb) ;
  is-monotone = λ {f} {g1} {g2} f≤g1 g1≤g2 a b aRb →
    S .MonRel.is-monotone (f≤g1 a b aRb) (g1≤g2 b) }
