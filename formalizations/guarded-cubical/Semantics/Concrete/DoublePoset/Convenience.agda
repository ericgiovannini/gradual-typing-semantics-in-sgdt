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

is-set-PosetBisim : (X : PosetBisim ℓ ℓ' ℓ'') -> isSet ⟨ X ⟩
is-set-PosetBisim X = PosetBisimStr.is-set (X .snd)

rel-≤ : (X : PosetBisim ℓ ℓ' ℓ'') -> (⟨ X ⟩ -> ⟨ X ⟩ -> Type ℓ')
rel-≤ X = PosetBisimStr._≤_ (X .snd)

prop-valued-≤ : (X : PosetBisim ℓ ℓ' ℓ'') -> isPropValued (PosetBisimStr._≤_ (str X))
prop-valued-≤ X = IsOrderingRelation.is-prop-valued
  (PosetBisimStr.isOrderingRelation (str X))

reflexive-≤ : (X : PosetBisim ℓ ℓ' ℓ'') -> (x : ⟨ X ⟩) -> (rel-≤ X x x)
reflexive-≤ X x = IsOrderingRelation.is-refl (PosetBisimStr.isOrderingRelation (str X)) x

transitive-≤ : (X : PosetBisim ℓ ℓ' ℓ'') -> (x y z : ⟨ X ⟩) ->
  rel-≤ X x y -> rel-≤ X y z -> rel-≤ X x z
transitive-≤ X x y z x≤y y≤z =
  IsOrderingRelation.is-trans (PosetBisimStr.isOrderingRelation (str X)) x y z x≤y y≤z

antisym-≤ : (X : PosetBisim ℓ ℓ' ℓ'') -> (x y : ⟨ X ⟩) ->
  rel-≤ X x y -> rel-≤ X y x -> x ≡ y
antisym-≤ X x y x≤y y≤x =
  IsOrderingRelation.is-antisym (PosetBisimStr.isOrderingRelation (str X)) x y x≤y y≤x

rel-≈ : (X : PosetBisim ℓ ℓ' ℓ'') -> (⟨ X ⟩ -> ⟨ X ⟩ -> Type ℓ'')
rel-≈ X = PosetBisimStr._≈_ (X .snd)

reflexive-≈ : (X : PosetBisim ℓ ℓ' ℓ'') -> (x : ⟨ X ⟩) -> (rel-≈ X x x)
reflexive-≈ X x = IsBisim.is-refl (PosetBisimStr.isBisim (str X)) x

sym-≈ : (X : PosetBisim ℓ ℓ' ℓ'') -> (x y : ⟨ X ⟩) -> rel-≈ X x y -> rel-≈ X y x
sym-≈ X x y x≈y = IsBisim.is-sym (PosetBisimStr.isBisim (str X)) x y x≈y

prop-valued-≈ : (X : PosetBisim ℓ ℓ' ℓ'') -> isPropValued (PosetBisimStr._≈_ (str X))
prop-valued-≈ X = IsBisim.is-prop-valued (PosetBisimStr.isBisim (str X))
