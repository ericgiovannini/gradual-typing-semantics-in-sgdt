module Semantics.Concrete.Predomain.Convenience where

open import Semantics.Concrete.Predomain.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Relation.Binary.Base

open BinaryRelation

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓ'X ℓY ℓ'Y : Level

is-set-Predomain : (X : Predomain ℓ ℓ' ℓ'') -> isSet ⟨ X ⟩
is-set-Predomain X = PredomainStr.is-set (X .snd)

rel-≤ : (X : Predomain ℓ ℓ' ℓ'') -> (⟨ X ⟩ -> ⟨ X ⟩ -> Type ℓ')
rel-≤ X = PredomainStr._≤_ (X .snd)

prop-valued-≤ : (X : Predomain ℓ ℓ' ℓ'') -> isPropValued (PredomainStr._≤_ (str X))
prop-valued-≤ X = IsOrderingRelation.is-prop-valued
  (PredomainStr.isOrderingRelation (str X))

reflexive-≤ : (X : Predomain ℓ ℓ' ℓ'') -> (x : ⟨ X ⟩) -> (rel-≤ X x x)
reflexive-≤ X x = IsOrderingRelation.is-refl (PredomainStr.isOrderingRelation (str X)) x

transitive-≤ : (X : Predomain ℓ ℓ' ℓ'') -> (x y z : ⟨ X ⟩) ->
  rel-≤ X x y -> rel-≤ X y z -> rel-≤ X x z
transitive-≤ X x y z x≤y y≤z =
  IsOrderingRelation.is-trans (PredomainStr.isOrderingRelation (str X)) x y z x≤y y≤z

antisym-≤ : (X : Predomain ℓ ℓ' ℓ'') -> (x y : ⟨ X ⟩) ->
  rel-≤ X x y -> rel-≤ X y x -> x ≡ y
antisym-≤ X x y x≤y y≤x =
  IsOrderingRelation.is-antisym (PredomainStr.isOrderingRelation (str X)) x y x≤y y≤x

rel-≈ : (X : Predomain ℓ ℓ' ℓ'') -> (⟨ X ⟩ -> ⟨ X ⟩ -> Type ℓ'')
rel-≈ X = PredomainStr._≈_ (X .snd)

reflexive-≈ : (X : Predomain ℓ ℓ' ℓ'') -> (x : ⟨ X ⟩) -> (rel-≈ X x x)
reflexive-≈ X x = IsBisim.is-refl (PredomainStr.isBisim (str X)) x

sym-≈ : (X : Predomain ℓ ℓ' ℓ'') -> (x y : ⟨ X ⟩) -> rel-≈ X x y -> rel-≈ X y x
sym-≈ X x y x≈y = IsBisim.is-sym (PredomainStr.isBisim (str X)) x y x≈y

prop-valued-≈ : (X : Predomain ℓ ℓ' ℓ'') -> isPropValued (PredomainStr._≈_ (str X))
prop-valued-≈ X = IsBisim.is-prop-valued (PredomainStr.isBisim (str X))
