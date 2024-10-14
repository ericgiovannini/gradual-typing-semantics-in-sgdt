module Semantics.Adequacy.Partial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)


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


module ErrorOrdPartial {X : Type ℓ} {Y : Type ℓ'}
  (_R_ : (X ⊎ ⊤) → (Y ⊎ ⊤) → Type ℓR) where

   ---------------------------------------
   -- Error ordering on partial elements
   ---------------------------------------

   -- The error ordering on partial elements ≤part is defined as the
   -- following conjunction:
   --
   -- 1. If the LHS is defined, as witnessed by a : ⟨ P ⟩, then either:
   --   i.  The LHS is an error
   --   ii. The LHS is a result x? and the RHS is a result y?
   --       and x? is related to y?.
   -- 
   --   (Note that these are not mutually exclusive, i.e. if the LHS
   --   errors and the RHS is a result y? then either case i or ii
   --   applies.)
   --
   --   AND
   --
   -- 2. If the RHS is defined, i.e. a result y?, then the LHS is also
   -- a result x? such that x? is related to y?.
  _≤part_ : Part (X ⊎ ⊤) ℓ'' → Part (Y ⊎ ⊤) ℓ''' → Type _
  _≤part_ (P , P→X⊎⊤) (Q , Q→X⊎⊤) =
      (∀ (a : ⟨ P ⟩) → ((P→X⊎⊤ a) ≡ inr tt) ⊎
                       (Σ[ b ∈ ⟨ Q ⟩ ] (P→X⊎⊤ a) R (Q→X⊎⊤ b)))
    × (∀ (b : ⟨ Q ⟩) → Σ[ a ∈ ⟨ P ⟩ ] (P→X⊎⊤ a) R (Q→X⊎⊤ b))
