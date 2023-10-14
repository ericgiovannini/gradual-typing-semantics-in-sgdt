{-# OPTIONS --guarded --rewriting #-}


-- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.DoublePoset.DPMorRelation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Binary
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (elim)
open import Cubical.Data.Empty hiding (elim)
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.Univalence

open import Common.Common
open import Common.LaterProperties
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Convenience
open import Semantics.Concrete.DoublePoset.Constructions
open import Semantics.Concrete.DoublePoset.Morphism
open import Common.Later

open BinaryRelation

private
  variable
    ℓX ℓ'X ℓ''X ℓY ℓ'Y ℓ''Y ℓZ ℓ'Z ℓ''Z ℓA ℓ'A ℓ''A ℓB ℓ'B ℓ''B : Level
    ℓX' ℓ'X' ℓY' ℓ'Y' ℓZ' ℓ'Z' ℓA' ℓ'A' ℓB' ℓ'B' : Level
    ℓ ℓ' ℓ'' ℓR ℓR' ℓR'' : Level
    ℓo : Level

    X : DoublePoset ℓX ℓ'X ℓ''X
    Y : DoublePoset ℓY ℓ'Y ℓ''Y


record DPMorRel (X : DoublePoset ℓX ℓ'X ℓ''X) (Y : DoublePoset ℓY ℓ'Y ℓ''Y) (ℓR : Level) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) (ℓ-suc ℓR)) where
  module X = DblPosetStr (X .snd)
  module Y = DblPosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    R : ⟨ X ⟩ -> ⟨ Y ⟩ -> Type ℓR
    is-prop-valued : (x : ⟨ X ⟩) -> (y : ⟨ Y ⟩) -> isProp (R x y)
    is-antitone : ∀ {x' x y} -> x' ≤X x -> R x y -> R x' y
    is-monotone : ∀ {x y y'} -> R x y -> y ≤Y y' -> R x y'

open DPMorRel hiding (module X ; module Y ; _≤X_ ; _≤Y_)

record DPMorRel' (X : DoublePoset ℓX ℓ'X ℓ''X) (Y : DoublePoset ℓY ℓ'Y ℓ''Y) (ℓR : Level) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) (ℓ-suc ℓR)) where
  module X = DblPosetStr (X .snd)
  module Y = DblPosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    R : ⟨ X ⟩ -> ⟨ Y ⟩ -> hProp ℓR
    is-antitone : ∀ x' x y -> x' ≤X x -> ⟨ R x y ⟩ -> ⟨ R x' y ⟩
    is-monotone : ∀ x y y' -> ⟨ R x y ⟩ -> y ≤Y y' -> ⟨ R x y' ⟩



dblposet-monrel : {ℓo : Level} -> (X : DoublePoset ℓ ℓ' ℓ'') -> DPMorRel X X (ℓ-max ℓ' ℓo)
dblposet-monrel {ℓ' = ℓ'} {ℓo = ℓo} X = record {
  R = λ x x' -> Lift {i = ℓ'} {j = ℓo} (rel-≤ X x x') ;
  is-prop-valued = λ x x' -> isOfHLevelLift 1 (prop-valued-≤ X x x') ;
  is-antitone = λ {x'} {x} {y}  x'≤x x≤y -> lift (transitive-≤ X x' x y x'≤x (lower x≤y)) ;
  is-monotone = λ {x}  {y} {y'} x≤y y≤y' -> lift (transitive-≤ X x y y' (lower x≤y) y≤y') }


_==>dpmonrel_ : {ℓR : Level} {Ai Ao Bi Bo : DoublePoset ℓ ℓ' ℓ''} ->
  DPMorRel Ai Bi ℓR ->
  DPMorRel Ao Bo ℓR ->
  DPMorRel (Ai ==> Ao) (Bi ==> Bo) (ℓ-max ℓ ℓR)
R ==>dpmonrel S = record {
  R = λ f g ->
    TwoCell (DPMorRel.R R) (DPMorRel.R S) (DPMor.f f) (DPMor.f g)  ;
  is-prop-valued = λ f g -> isPropTwoCell (S .DPMorRel.is-prop-valued) ;
  is-antitone = λ {f1} {f2} {g} f1≤f2 f1≤g  a b aRb →
    S .DPMorRel.is-antitone (f1≤f2 a) (f1≤g a b aRb) ;
  is-monotone = λ {f} {g1} {g2} f≤g1 g1≤g2 a b aRb →
    S .DPMorRel.is-monotone (f≤g1 a b aRb) (g1≤g2 b) }
