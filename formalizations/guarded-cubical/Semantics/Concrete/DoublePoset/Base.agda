module Semantics.Concrete.DoublePoset.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Base

open import Common.Common
open import Common.Poset.Convenience
open import Common.Poset.Monotone

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv


open BinaryRelation

private
  variable
    ℓ ℓ' ℓ'' : Level


record IsOrderingRelation {A : Type ℓ} (_≤_ : A -> A -> Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isorderingrelation
  
  field
    is-prop-valued : isPropValued _≤_
    is-refl : isRefl _≤_
    is-trans : isTrans _≤_
    is-antisym : isAntisym _≤_

unquoteDecl IsOrderingRelationIsoΣ = declareRecordIsoΣ IsOrderingRelationIsoΣ (quote IsOrderingRelation)

record IsPER {A : Type ℓ} (_≈_ : A -> A -> Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isper
  
  field
    is-refl : isRefl _≈_
    is-sym : isSym _≈_
    is-prop-valued : isPropValued _≈_
    -- Need to be prop-valued?


unquoteDecl IsPERIsoΣ = declareRecordIsoΣ IsPERIsoΣ (quote IsPER)


record DblPosetStr (ℓ' ℓ'' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ''))) where

  constructor dblposetstr

  field
    is-set : isSet A
    _≤_     : A → A → Type ℓ'
    isOrderingRelation : IsOrderingRelation _≤_
    _≈_ : A -> A -> Type ℓ''
    isPER : IsPER _≈_

  infixl 7 _≤_


  open IsPER isPER public renaming (is-refl to is-refl-PER ;
                                    is-prop-valued to is-prop-valued-PER )
  open IsOrderingRelation isOrderingRelation public

DoublePoset : ∀ ℓ ℓ' ℓ'' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ'')))
DoublePoset ℓ ℓ' ℓ'' = TypeWithStr ℓ (DblPosetStr ℓ' ℓ'')

open DblPosetStr


DoublePoset→Poset : DoublePoset ℓ ℓ' ℓ'' -> Poset ℓ ℓ'
DoublePoset→Poset X = ⟨ X ⟩ ,
  (posetstr (X .snd ._≤_)
    (isposet (X .snd .is-set)
             (X .snd .is-prop-valued)
             (X .snd .is-refl)
             (X .snd .is-trans)
             (X .snd .is-antisym)))





