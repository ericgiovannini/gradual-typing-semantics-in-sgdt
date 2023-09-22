module Semantics.Concrete.DoublePoset.Convenience where

open import Semantics.Concrete.DoublePoset.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Relation.Binary.Base

open BinaryRelation

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓ'X ℓY ℓ'Y : Level

is-set-DblPoset : (X : DoublePoset ℓ ℓ' ℓ'') -> isSet ⟨ X ⟩
is-set-DblPoset X = DblPosetStr.is-set (X .snd)

rel-≤ : (X : DoublePoset ℓ ℓ' ℓ'') -> (⟨ X ⟩ -> ⟨ X ⟩ -> Type ℓ')
rel-≤ X = DblPosetStr._≤_ (X .snd)

prop-valued-≤ : (X : DoublePoset ℓ ℓ' ℓ'') -> isPropValued (DblPosetStr._≤_ (str X))
prop-valued-≤ X = IsOrderingRelation.is-prop-valued
  (DblPosetStr.isOrderingRelation (str X))

reflexive-≤ : (X : DoublePoset ℓ ℓ' ℓ'') -> (x : ⟨ X ⟩) -> (rel-≤ X x x)
reflexive-≤ X x = IsOrderingRelation.is-refl (DblPosetStr.isOrderingRelation (str X)) x

transitive-≤ : (X : DoublePoset ℓ ℓ' ℓ'') -> (x y z : ⟨ X ⟩) ->
  rel-≤ X x y -> rel-≤ X y z -> rel-≤ X x z
transitive-≤ X x y z x≤y y≤z =
  IsOrderingRelation.is-trans (DblPosetStr.isOrderingRelation (str X)) x y z x≤y y≤z

antisym-≤ : (X : DoublePoset ℓ ℓ' ℓ'') -> (x y : ⟨ X ⟩) ->
  rel-≤ X x y -> rel-≤ X y x -> x ≡ y
antisym-≤ X x y x≤y y≤x =
  IsOrderingRelation.is-antisym (DblPosetStr.isOrderingRelation (str X)) x y x≤y y≤x

rel-≈ : (X : DoublePoset ℓ ℓ' ℓ'') -> (⟨ X ⟩ -> ⟨ X ⟩ -> Type ℓ'')
rel-≈ X = DblPosetStr._≈_ (X .snd)

reflexive-≈ : (X : DoublePoset ℓ ℓ' ℓ'') -> (x : ⟨ X ⟩) -> (rel-≈ X x x)
reflexive-≈ X x = IsPER.is-refl (DblPosetStr.isPER (str X)) x

sym-≈ : (X : DoublePoset ℓ ℓ' ℓ'') -> (x y : ⟨ X ⟩) -> rel-≈ X x y -> rel-≈ X y x
sym-≈ X x y x≈y = IsPER.is-sym (DblPosetStr.isPER (str X)) x y x≈y

prop-valued-≈ : (X : DoublePoset ℓ ℓ' ℓ'') -> isPropValued (DblPosetStr._≈_ (str X))
prop-valued-≈ X = IsPER.is-prop-valued (DblPosetStr.isPER (str X))
