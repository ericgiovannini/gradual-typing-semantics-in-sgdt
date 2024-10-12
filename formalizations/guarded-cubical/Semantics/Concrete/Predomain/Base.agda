module Semantics.Concrete.Predomain.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

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

record IsBisim {A : Type ℓ} (_≈_ : A -> A -> Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isbisim
  
  field
    is-refl : isRefl _≈_
    is-sym : isSym _≈_
    is-prop-valued : isPropValued _≈_
    -- Need to be prop-valued?
    -- is-set-valued : ∀ x y → isSet (x ≈ y)


unquoteDecl IsBisimIsoΣ = declareRecordIsoΣ IsBisimIsoΣ (quote IsBisim)

record PredomainStr (ℓ' ℓ'' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ''))) where

  constructor predomainstr

  field
    is-set : isSet A
    _≤_     : A → A → Type ℓ'
    isOrderingRelation : IsOrderingRelation _≤_
    _≈_ : A -> A -> Type ℓ''
    isBisim : IsBisim _≈_

  infixl 7 _≤_

  open IsBisim isBisim public renaming (is-refl to is-refl-Bisim
                                      ; is-prop-valued to is-prop-valued-Bisim )
  open IsOrderingRelation isOrderingRelation public


unquoteDecl PredomainIsoΣ = declareRecordIsoΣ PredomainIsoΣ (quote PredomainStr)


Predomain : ∀ ℓ ℓ' ℓ'' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ'')))
Predomain ℓ ℓ' ℓ'' = TypeWithStr ℓ (PredomainStr ℓ' ℓ'')

open PredomainStr


Predomain→Poset : Predomain ℓ ℓ' ℓ'' -> Poset ℓ ℓ'
Predomain→Poset X = ⟨ X ⟩ ,
  (posetstr (X .snd ._≤_)
    (isposet (X .snd .is-set)
             (X .snd .is-prop-valued)
             (X .snd .is-refl)
             (X .snd .is-trans)
             (X .snd .is-antisym)))




-- Bisimilarity extends to functions

_≈fun_ :
  {ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ ℓAₒ ℓ≤Aₒ ℓ≈Aₒ : Level}
  {Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ}
  (f g : ⟨ Aᵢ ⟩ → ⟨ Aₒ ⟩) → Type (ℓ-max (ℓ-max ℓAᵢ ℓ≈Aᵢ) ℓ≈Aₒ)
_≈fun_ {Aᵢ = Aᵢ} {Aₒ = Aₒ} f g = ∀ x x' -> x Aᵢ.≈ x' -> f x Aₒ.≈ g x'
  where
    module Aᵢ = PredomainStr (Aᵢ .snd)
    module Aₒ = PredomainStr (Aₒ .snd)

-- Closure under composition of bisimilarity
module _
  {ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓA₃ ℓ≤A₃ ℓ≈A₃ : Level}
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁}
  {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂}
  {A₃ : Predomain ℓA₃ ℓ≤A₃ ℓ≈A₃}
  (f₁ g₁ : ⟨ A₁ ⟩ → ⟨ A₂ ⟩)
  (f₂ g₂ : ⟨ A₂ ⟩ → ⟨ A₃ ⟩) where

  ≈comp : (_≈fun_ {Aᵢ = A₁} {Aₒ = A₂} f₁ g₁) →
          (_≈fun_ {Aᵢ = A₂} {Aₒ = A₃} f₂ g₂) →
           _≈fun_ {Aᵢ = A₁} {Aₒ = A₃} (f₂ ∘ f₁) (g₂ ∘ g₁)
  ≈comp f₁≈g₁ f₂≈g₂ x y x≈y = f₂≈g₂ (f₁ x) (g₁ y) (f₁≈g₁ x y x≈y)

