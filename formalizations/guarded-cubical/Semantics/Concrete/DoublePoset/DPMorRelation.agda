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
open import Cubical.HITs.PropositionalTruncation renaming (rec to PTrec)
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
    ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  : Level
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' : Level
    ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  : Level
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' : Level
    ℓcᵢ ℓcₒ : Level

    ℓA₁ ℓ≤A₁ ℓ≈A₁ : Level
    ℓA₂ ℓ≤A₂ ℓ≈A₂ : Level
    ℓA₃ ℓ≤A₃ ℓ≈A₃ : Level
    ℓc₁ ℓc₂ : Level

    X : PosetBisim ℓX ℓ'X ℓ''X
    Y : PosetBisim ℓY ℓ'Y ℓ''Y


record PBRel (X : PosetBisim ℓX ℓ'X ℓ''X) (Y : PosetBisim ℓY ℓ'Y ℓ''Y) (ℓR : Level) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) (ℓ-suc ℓR)) where
  module X = PosetBisimStr (X .snd)
  module Y = PosetBisimStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    R : ⟨ X ⟩ -> ⟨ Y ⟩ -> Type ℓR
    is-prop-valued : (x : ⟨ X ⟩) -> (y : ⟨ Y ⟩) -> isProp (R x y)
    is-antitone : ∀ {x' x y} -> x' ≤X x -> R x y -> R x' y
    is-monotone : ∀ {x y y'} -> R x y -> y ≤Y y' -> R x y'

open PBRel hiding (module X ; module Y ; _≤X_ ; _≤Y_)

record PBRel' (X : PosetBisim ℓX ℓ'X ℓ''X) (Y : PosetBisim ℓY ℓ'Y ℓ''Y) (ℓR : Level) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) (ℓ-suc ℓR)) where
  module X = PosetBisimStr (X .snd)
  module Y = PosetBisimStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    R : ⟨ X ⟩ -> ⟨ Y ⟩ -> hProp ℓR
    is-antitone : ∀ x' x y -> x' ≤X x -> ⟨ R x y ⟩ -> ⟨ R x' y ⟩
    is-monotone : ∀ x y y' -> ⟨ R x y ⟩ -> y ≤Y y' -> ⟨ R x y' ⟩


-- Identity relation
posetbisim-monrel : {ℓo : Level} -> (X : PosetBisim ℓ ℓ' ℓ'') -> PBRel X X (ℓ-max ℓ' ℓo)
posetbisim-monrel {ℓ' = ℓ'} {ℓo = ℓo} X = record {
  R = λ x x' -> Lift {i = ℓ'} {j = ℓo} (rel-≤ X x x') ;
  is-prop-valued = λ x x' -> isOfHLevelLift 1 (prop-valued-≤ X x x') ;
  is-antitone = λ {x'} {x} {y}  x'≤x x≤y -> lift (transitive-≤ X x' x y x'≤x (lower x≤y)) ;
  is-monotone = λ {x}  {y} {y'} x≤y y≤y' -> lift (transitive-≤ X x y y' (lower x≤y) y≤y') }


idRel : {ℓo : Level} -> (X : PosetBisim ℓ ℓ' ℓ'') -> PBRel X X (ℓ-max ℓ' ℓo)
idRel {ℓo = ℓo} = posetbisim-monrel {ℓo = ℓo}



-- Composition of relations

-- Composing monotone relations
-- Note that becasue of the quantification over elements of Y,
-- the universe level of the resulting relation involves an
-- ℓ-max with ℓA₂ (i.e. the level of the elements in A₂)
_⊙_ : 
  {A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₃ : PosetBisim ℓA₃ ℓ≤A₃ ℓ≈A₃} ->
  PBRel A₁ A₂ ℓc₁ ->
  PBRel A₂ A₃ ℓc₂ ->
  PBRel A₁ A₃ (ℓ-max ℓA₂ (ℓ-max ℓc₁ ℓc₂))
_⊙_ {A₁ = A₁} {A₂ = A₂} {A₃ = A₃} c₁ c₂ = record {
  R = λ x z -> ∥ compRel (PBRel.R c₁) (PBRel.R c₂) x z ∥₁ ;
  is-prop-valued = λ x z -> isPropPropTrunc ;
  is-antitone = λ x'≤x H -> elim (λ _ -> isPropPropTrunc) (λ p -> ∣ comp-antitone x'≤x p ∣₁) H ;
  is-monotone = λ H y≤y' -> PTrec isPropPropTrunc (λ p → ∣ comp-monotone p y≤y' ∣₁) H }
    where

      module A₁ = PosetBisimStr (A₁ .snd)
      module A₃ = PosetBisimStr (A₃ .snd)
      
      module c₁ = PBRel c₁
      module c₂ = PBRel c₂

      comp-antitone : {x' x : ⟨ A₁ ⟩} {z : ⟨ A₃ ⟩} ->
         x' A₁.≤ x ->
        compRel (PBRel.R c₁) (PBRel.R c₂) x z ->
        compRel (PBRel.R c₁) (PBRel.R c₂) x' z 
      comp-antitone x'≤x (y , xc₁y , yc₂z) = y , (PBRel.is-antitone c₁ x'≤x xc₁y) , yc₂z

      comp-monotone : {x : ⟨ A₁ ⟩} {z z' : ⟨ A₃ ⟩} ->
        compRel (PBRel.R c₁) (PBRel.R c₂) x z ->
        z A₃.≤ z' ->
        compRel (PBRel.R c₁) (PBRel.R c₂) x z'
      comp-monotone (y , xc₁y , yc₂z) z≤z' = y , xc₁y , (PBRel.is-monotone c₂ yc₂z z≤z')



-- Exponential of relations

_==>pbmonrel_ :
  {Aᵢ : PosetBisim ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aᵢ' : PosetBisim ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
  {Aₒ : PosetBisim ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} {Aₒ' : PosetBisim ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'} ->
  PBRel Aᵢ Aᵢ' ℓcᵢ ->
  PBRel Aₒ Aₒ' ℓcₒ ->
  PBRel (Aᵢ ==> Aₒ) (Aᵢ' ==> Aₒ') (ℓ-max (ℓ-max ℓAᵢ ℓAᵢ') (ℓ-max ℓcᵢ ℓcₒ))
cᵢ ==>pbmonrel cₒ = record {
  R = λ f g ->
    TwoCell (PBRel.R cᵢ) (PBRel.R cₒ) (PBMor.f f) (PBMor.f g)  ;
  is-prop-valued = λ f g -> isPropTwoCell (cₒ .PBRel.is-prop-valued) ;
  is-antitone = λ {f1} {f2} {g} f1≤f2 f1≤g  a b aRb →
    cₒ .PBRel.is-antitone (f1≤f2 a) (f1≤g a b aRb) ;
  is-monotone = λ {f} {g1} {g2} f≤g1 g1≤g2 a b aRb →
    cₒ .PBRel.is-monotone (f≤g1 a b aRb) (g1≤g2 b) }
