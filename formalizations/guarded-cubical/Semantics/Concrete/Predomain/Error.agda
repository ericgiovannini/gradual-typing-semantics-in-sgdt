{-# OPTIONS --rewriting --guarded #-}

open import Common.Later


module Semantics.Concrete.Predomain.Error where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Sum

open import Cubical.Relation.Binary

-- open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.Predomain.Base

open import Common.ClockProperties



private
  variable
    ℓ ℓ' ℓR : Level
    ℓX ℓY : Level
    X : Type ℓX
    Y : Type ℓY
    ℓ≈X : Level


open BinaryRelation


-- Error monad
data Error (X : Type ℓ) : Type ℓ where
  ok : X -> Error X
  error : Error X

Iso-Error : {X : Type ℓ} -> Iso (Error X) (X ⊎ ⊤)
Iso-Error {X = X} = iso to inv sec retr
  where
    to : Error X → X ⊎ ⊤
    to (ok x) = inl x
    to error = inr tt

    inv : X ⊎ ⊤ → Error X
    inv (inl x) = ok x
    inv (inr tt) = error

    sec : section to inv
    sec (inl x) = refl
    sec (inr tt) = refl

    retr : retract to inv
    retr (ok x) = refl
    retr error = refl


isSetError : (X : Type ℓ) → isSet X → isSet (Error X)
isSetError X isSetX =
  isSetRetract (Iso.fun Iso-Error) (Iso.inv Iso-Error) (Iso.leftInv Iso-Error) (isSet⊎ isSetX isSetUnit)


extError : (X → Error Y) → (Error X → Error Y)
extError f (ok x) = f x
extError f error = error


-- Defining bisimilarity on Error X given bisimilarity on X

≈ErrorX : {X : Type ℓ} (R : X → X → Type ℓR) → Error X → Error X → Type ℓR
≈ErrorX R (ok x) (ok y) = R x y
≈ErrorX R error error = ⊤*
≈ErrorX R _ _ = ⊥*


ErrorX→X⊎⊤ : {X : Type ℓ} → Error X → X ⊎ ⊤
ErrorX→X⊎⊤ (ok x) = inl x
ErrorX→X⊎⊤ error = inr tt

X⊎⊤→ErrorX : {X : Type ℓ} → X ⊎ ⊤ → Error X
X⊎⊤→ErrorX (inl x) = ok x
X⊎⊤→ErrorX (inr tt) = error


module _ (X : Type ℓ) (_≈X_ : X → X → Type ℓ≈X) where

  Sum≈ : (X ⊎ ⊤) → (X ⊎ ⊤) → Type ℓ≈X
  Sum≈ (inl x) (inl x') = x ≈X x'
  Sum≈ (inr tt) (inr tt) = ⊤*
  Sum≈ _ _ = ⊥*

  module _ (H : ∀ x x' → clock-irrel (x ≈X x')) where

    Sum≈-clk-irrel : ∀ x? x'? → clock-irrel (Sum≈ x? x'?)
    Sum≈-clk-irrel (inl x) (inl x') = H x x'
    Sum≈-clk-irrel (inl x) (inr tt) = ⊥*-clock-irrel
    Sum≈-clk-irrel (inr tt) (inl x') = ⊥*-clock-irrel
    Sum≈-clk-irrel (inr tt) (inr tt) = Unit*-clock-irrel

  module _ (H : isPropValued _≈X_) where

    Sum≈-prop-valued : isPropValued Sum≈
    Sum≈-prop-valued (inl x) (inl y) p q = H x y p q
    Sum≈-prop-valued (inr tt) (inr tt) p q = refl

  module _ (H : isSym _≈X_) where

    Sum≈-sym : isSym Sum≈
    Sum≈-sym (inl x) (inl y) p = H x y p
    Sum≈-sym (inr tt) (inr tt) p = tt*


≈Error→≈⊎ : {X : Type ℓ} (R : X → X → Type ℓR) →
  (x? y? : Error X) → (≈ErrorX R x? y?) → Sum≈ X R (ErrorX→X⊎⊤ x?) (ErrorX→X⊎⊤ y?)
≈Error→≈⊎ R (ok x) (ok y) H = H
≈Error→≈⊎ R error error H = tt*


IsBisimErrorX : {X : Type ℓ} (R : X → X → Type ℓR) →
  IsBisim R → IsBisim (≈ErrorX R)
IsBisimErrorX R isBisimR =
  isbisim reflexive symmetric prop
    where
      reflexive : isRefl (≈ErrorX R)
      reflexive (ok x) = isBisimR .IsBisim.is-refl x
      reflexive error = tt*

      symmetric : isSym (≈ErrorX R)
      symmetric (ok x) (ok y) Rxy = isBisimR .IsBisim.is-sym x y Rxy
      symmetric error error tt* = tt*

      prop : isPropValued (≈ErrorX R)
      prop (ok x) (ok y) p q = isBisimR .IsBisim.is-prop-valued x y p q
      prop error error p q = refl
