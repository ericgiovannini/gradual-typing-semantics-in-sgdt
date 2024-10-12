{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Common
open import Common.Later

module Semantics.Concrete.GuardedLiftError (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma

open import Common.Common
open import Common.LaterProperties

open import Semantics.Concrete.Predomain.Error

open import Semantics.Concrete.GuardedLift k renaming (η to ηL) public

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ
    ℓX ℓY : Level
    X : Type ℓX
    Y : Type ℓY
private
  ▹_ : Set ℓ → Set ℓ
  ▹_ A = ▹_,_ k A


-- The guarded Lift + Error monad



-- Commutativity of the lift monad with the error monad

ErrorLift→LiftError' : ▹ (Error (L X) → L (Error X)) → Error (L X) → L (Error X)
ErrorLift→LiftError' IH (ok (ηL x)) = ηL (ok x)
ErrorLift→LiftError' IH (ok (θ lx~)) = θ (λ t → IH t (ok (lx~ t)))
ErrorLift→LiftError' IH error = ηL error



-- Lift + Error as a combination of L and Error
L℧ : (X : Type ℓ) -> Type ℓ
L℧ X = L (Error X)

pattern ℧ = ηL error
pattern η x = ηL (ok x)


isSetL℧ : (X : Type ℓ) → isSet X → isSet (L℧ X)
isSetL℧ X isSetX = isSetL (isSetError X isSetX)


module Monad where

  -- Monadic ext
  ext' : (X → L℧ Y) →
    ▹ (L℧ X → L℧ Y) → (L℧ X → L℧ Y)
  ext' f _ (η x) = f x
  ext' f _ ℧ = ℧
  ext' f rec (θ lx~) = θ (λ t → rec t (lx~ t))

  ext : (X → L℧ Y) → (L℧ X → L℧ Y)
  ext f = fix (ext' f)


  unfold-ext : ∀ (f : X → L℧ Y) → ext f ≡ ext' f (next (ext f))
  unfold-ext f = fix-eq (ext' f)

  -- Properties
  module _ (f : X → L℧ Y) where

    ext-η : (x : X) → ext f (η x) ≡ f x
    ext-η x = funExt⁻ (unfold-ext f) (η x)

    ext-℧ : ext f ℧ ≡ ℧
    ext-℧ = funExt⁻ (unfold-ext f) ℧

    ext-θ : (lx~ : ▹ L℧ X) → ext f (θ lx~) ≡ θ (ext f <$> lx~)
    ext-θ lx~ = funExt⁻ (unfold-ext f) (θ lx~)
