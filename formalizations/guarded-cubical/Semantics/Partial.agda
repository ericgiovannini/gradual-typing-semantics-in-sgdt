{-# OPTIONS --rewriting #-}

module Semantics.Partial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)

-- open import Semantics.Concrete.DoublePoset.Error
open import Semantics.Concrete.Predomain.Error


private
  variable
    ℓ ℓ' ℓR : Level
    ℓ'' ℓ''' : Level


-- Partial elements:

module _ (X : Type ℓ) where
  
  Part : (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
  Part ℓ' = Σ[ P ∈ hProp ( ℓ') ] (⟨ P ⟩ → X)

  injPart : {ℓ' : Level} → X → Part ℓ'
  injPart x = (⊤* , isPropUnit*) , (λ _ -> x)

module _ {X : Type ℓ} where

  defined : Part X ℓ'' → Type ℓ''
  defined (P , P→X) = ⟨ P ⟩

  isPropDefined : (x : Part X ℓ'') → isProp (defined x)
  isPropDefined (P , P→X) p₁ p₂ = P .snd p₁ p₂

  result : (x : Part X ℓ'') → defined x → X
  result (P , P→X) p = P→X p

module ErrorOrdPartial {X : Type ℓ} {Y : Type ℓ'}
  (_R_ : (X → Y → Type ℓR)) where

---------------------------------------
   -- Error ordering on partial elements
   ---------------------------------------

   -- The error ordering on partial elements ≤part is defined as the
   -- following conjunction:
   --
   -- 1. If the LHS is defined, as witnessed by a : ⟨ P ⟩, then either:
   --   i.  The LHS is an error
   --   ii. The LHS is a value x, and the RHS is a value y such that x is related to y
   --
   --   AND
   --
   -- 2. If the RHS is defined, i.e. a result y?, then the LHS is also
   -- a result x? such that x? is related to y?.

  private
    isleft : {A : Type ℓ} {B : Type ℓ'} → A ⊎ B → Type ℓ-zero
    isleft = Sum.rec (λ _ → ⊤) (λ _ → ⊥)

  _⊑result_ = Rel→ResultRel _R_

  _≤part_ : Part (X ⊎ ⊤) ℓ'' → Part (Y ⊎ ⊤) ℓ''' → Type _
  _≤part_ px py =
    ((a : defined px) →
      Sum.rec
        (λ x → Σ[ b ∈ defined py ] (inl x ⊑result (result py b)))
        (λ _ → ⊤*)
        (result px a))
   ×  ((b : defined py) → Σ[ a ∈ defined px ] ((result px a) ⊑result (result py b)))
      
