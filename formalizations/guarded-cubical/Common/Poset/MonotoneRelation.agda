 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Common.Poset.MonotoneRelation where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Poset
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Common.Common
open import Common.Poset.Convenience
open import Common.Poset.Monotone hiding (monotone)


private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓo : Level


-- Monotone relations between posets X and Y
-- (antitone in X, monotone in Y).
record MonRel (X Y : Poset ℓ ℓ') {ℓ'' : Level} : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) where
  module X = PosetStr (X .snd)
  module Y = PosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    R : ⟨ X ⟩ -> ⟨ Y ⟩ -> Type ℓ''
    isAntitone : ∀ {x x' y} -> R x y -> x' ≤X x -> R x' y
    isMonotone : ∀ {x y y'} -> R x y -> y ≤Y y' -> R x y'


module MonReasoning {ℓ'' : Level} {X Y : Poset ℓ ℓ'} where
  --open MonRel
  module X = PosetStr (X .snd)
  module Y = PosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  
  
  -- _Anti⟨_⟩_: R x y -> x'≤X x -> R x' y
  [_]_Anti⟨_⟩_ : (S : MonRel X Y {ℓ''}) ->
    (x' : ⟨ X ⟩) -> {x : ⟨ X ⟩} -> {y : ⟨ Y ⟩} ->
    x' ≤X x -> (S .MonRel.R) x y -> (S .MonRel.R) x' y
  [ S ] x' Anti⟨ x'≤x ⟩ x≤y = S .MonRel.isAntitone x≤y x'≤x


  [_]_Mon⟨_⟩_ : (S : MonRel X Y {ℓ''}) ->
    (x : ⟨ X ⟩) -> {y y' : ⟨ Y ⟩} ->
    (S .MonRel.R) x y -> y ≤Y y' -> (S .MonRel.R x y')
  [ S ] x Mon⟨ x≤y ⟩ y≤y' = S .MonRel.isMonotone x≤y y≤y'

poset-monrel : {ℓo : Level} -> (X : Poset ℓ ℓ') -> MonRel X X {ℓ-max ℓo ℓ'}
poset-monrel {ℓ' = ℓ'} {ℓo = ℓo} X = record {
  R = λ x1 x2 -> Lift {i = ℓ'} {j = ℓo} (rel X x1 x2) ;
  isAntitone = λ {x} {x'} {y} x≤y x'≤x → lift (transitive X x' x y x'≤x (lower x≤y)) ;
  isMonotone = λ {x} {y} {y'} x≤y y≤y' -> lift (transitive X x y y' (lower x≤y) y≤y') }


-- Composing with functions on either side
functionalRel : {X' X Y Y' : Poset ℓ ℓ'} ->
  (f : MonFun X' X) ->
  (g : MonFun Y' Y) ->
  (R : MonRel X Y {ℓ''}) ->
  MonRel X' Y'
functionalRel f g R = record {
  R = λ x' y' -> MonRel.R R (MonFun.f f x') (MonFun.f g y') ;
  isAntitone = λ {x'2} {x'1} {y} H x'1≤x'2 → MonRel.isAntitone R H (MonFun.isMon f x'1≤x'2) ;
  isMonotone = λ {x'} {y'1} {y'2} H y'1≤y'2 → MonRel.isMonotone R H (MonFun.isMon g y'1≤y'2) }
  

compRel : {ℓ ℓ' : Level} -> {X Y Z : Type ℓ} ->
  (R1 : X -> Y -> Type ℓ') ->
  (R2 : Y -> Z -> Type ℓ') ->
  (X -> Z -> Type (ℓ-max ℓ ℓ'))
compRel {ℓ} {ℓ'} {X} {Y} {Z} R1 R2 x z = Σ[ y ∈ Y ] R1 x y × R2 y z

CompMonRel : -- {ℓX ℓ'X ℓY ℓ'Y ℓZ ℓ'Z : Level} {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} {Z : Poset ℓZ ℓ'Z} ->
  {X Y Z : Poset ℓ ℓ'} ->
  MonRel X Y {ℓ''} ->
  MonRel Y Z {ℓ''} ->
  MonRel X Z {ℓ-max ℓ ℓ''}
CompMonRel {ℓ''} {X = X} {Y = Y} {Z = Z} R1 R2 = record {
  R = compRel (MonRel.R R1) (MonRel.R R2) ;
  isAntitone = antitone ;
  isMonotone = monotone }
    where
      antitone : {x x' : ⟨ X ⟩} {z : ⟨ Z ⟩} ->
        compRel (MonRel.R R1) (MonRel.R R2) x z ->
        rel X x' x ->
        compRel (MonRel.R R1) (MonRel.R R2) x' z 
      antitone (y , xR1y , yR2z) x'≤x = y , (MonRel.isAntitone R1 xR1y x'≤x) , yR2z

      monotone : {x : ⟨ X ⟩} {z z' : ⟨ Z ⟩} ->
        compRel (MonRel.R R1) (MonRel.R R2) x z ->
        rel Z z z' ->
        compRel (MonRel.R R1) (MonRel.R R2) x z'
      monotone (y , xR1y , yR2z) z≤z' = y , xR1y , (MonRel.isMonotone R2 yR2z z≤z')


-- Monotone relations between function spaces
_==>monrel_ : {ℓ'' : Level} {Ai Ao Bi Bo : Poset ℓ ℓ'} ->
  MonRel Ai Bi {ℓ''} ->
  MonRel Ao Bo {ℓ''} ->
  MonRel (Ai ==> Ao) (Bi ==> Bo) {ℓ-max ℓ ℓ''}
R ==>monrel S = record {
  R = λ f g -> TwoCell (MonRel.R R) (MonRel.R S) (MonFun.f f) (MonFun.f g)  ;
  isAntitone = λ {f1} {f2} {g} f1≤g f2≤f1 a b aRb → MonRel.isAntitone S (f1≤g a b aRb) (f2≤f1 a) ;
  isMonotone = λ {f} {g1} {g2} f≤g1 g1≤g2 a b aRb → MonRel.isMonotone S (f≤g1 a b aRb) (g1≤g2 b) }
