{-# OPTIONS --guarded --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS --overlapping-instances --instance-search-depth 5 #-}
-- Without this, instance search fails, as there is always the option
-- to use the instance for composition.

module Semantics.Concrete.Predomain.InstanceTest where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)

open import Cubical.Relation.Binary
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma


open import Common.Common

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Convenience
open import Semantics.Concrete.Predomain.Constructions renaming (ℕ to NatP)
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Constructions
open import Semantics.Concrete.Predomain.Combinators

private
  variable
    ℓ ℓ'             : Level
    ℓA  ℓ≤A  ℓ≈A     : Level
    ℓA' ℓ≤A' ℓ≈A'    : Level
    ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ    : Level
    ℓAₒ ℓ≤Aₒ ℓ≈Aₒ    : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁    : Level
    ℓA₂ ℓ≤A₂ ℓ≈A₂    : Level
    ℓA₃ ℓ≤A₃ ℓ≈A₃    : Level
    ℓA₁' ℓ≤A₁' ℓ≈A₁'    : Level
    ℓA₂' ℓ≤A₂' ℓ≈A₂'    : Level
    ℓA₃' ℓ≤A₃' ℓ≈A₃'    : Level

    ℓc : Level



record IsMorphism (Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ) (Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ) (f : ⟨ Aᵢ ⟩ → ⟨ Aₒ ⟩) :
  Type (ℓ-max (ℓ-max ℓAᵢ (ℓ-max ℓ≤Aᵢ ℓ≈Aᵢ)) (ℓ-max ℓAₒ (ℓ-max ℓ≤Aₒ ℓ≈Aₒ))) where
  field
    isMon : monotone {X = Aᵢ} {Y = Aₒ} f
    pres≈ : preserve≈ {X = Aᵢ} {Y = Aₒ} f

open IsMorphism {{...}} public

instance
  IsMorphismId : {A : Predomain ℓA ℓ≤A ℓ≈A} → IsMorphism A A (λ x → x)
  IsMorphismId .IsMorphism.isMon x≤y = x≤y
  IsMorphismId .IsMorphism.pres≈ x≈y = x≈y

instance
  IsMorphismComp : {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₃ : Predomain ℓA₃ ℓ≤A₃ ℓ≈A₃}
    → {f : ⟨ A₁ ⟩ → ⟨ A₂ ⟩} {g : ⟨ A₂ ⟩ → ⟨ A₃ ⟩}
    → {{IsMorphism A₁ A₂ f}}
    → {{IsMorphism A₂ A₃ g}}
    → IsMorphism A₁ A₃ (g ∘ f)

  IsMorphismComp {f = f} {g = g} ⦃ isMor-f ⦄ ⦃ isMor-g ⦄
    .IsMorphism.isMon {x = x} {y = y} x≤y =
    isMor-g .isMon (isMor-f .isMon x≤y)
    -- isMon {f = g} (isMon {f = f} x≤y)
  IsMorphismComp {f = f} {g = g} ⦃ isMor-f ⦄ ⦃ isMor-g ⦄
    .IsMorphism.pres≈ {x = x} {y = y} x≈y =
    isMor-g .pres≈ (isMor-f .pres≈ x≈y)
  {-# OVERLAPPABLE IsMorphismComp #-}
  -- Allows this instance to be discarded in favor of a strictly more specific instance
  -- see https://agda.readthedocs.io/en/v2.7.0/language/instance-arguments.html#overlap-and-backtracking


-- instance
--   IsMorphismApp : {Aᵢ : Predomain ℓA₁ ℓ≤Aᵢ ℓ≈Aᵢ} {Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ}


ex1 : ∀ {A : Predomain ℓA ℓ≤A ℓ≈A}
  → monotone {X = A} {Y = A} (λ x → x)
ex1 {A = A} = isMon {Aᵢ = A} {Aₒ = A}



instance
  IsMorphismPi1 : {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂}
    → IsMorphism (A₁ ×dp A₂) A₁ fst
  IsMorphismPi1 .IsMorphism.isMon {x = (x₁ , y₁)} {y = (x₂ , y₂)} (p , q) = p
  IsMorphismPi1 .IsMorphism.pres≈ {x = (x₁ , y₁)} {y = (x₂ , y₂)} (p , q) = p


ex2 : ∀ {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂}
  → monotone {X = A₁ ×dp A₂} {Y = A₁} fst
ex2 {A₁ = A₁} {A₂ = A₂} = isMon {Aᵢ = A₁ ×dp A₂} {Aₒ = A₁} {{IsMorphismPi1 {A₂ = A₂}}}

-- We need to explicitly speficy the instance, because Agda cannot infer the implicit argument A₂


{-
instance
  IsMorphismProd : {A : Predomain ℓA ℓ≤A ℓ≈A} {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂}
    → {f : ⟨ A ⟩ → ⟨ A₁ ⟩} {g : ⟨ A ⟩ → ⟨ A₂ ⟩}
    → {{IsMorphism A A₁ f}}
    → {{IsMorphism A A₂ g}}
    → IsMorphism A (A₁ ×dp A₂) (λ x → (f x , g x))
  IsMorphismProd = {!!}
-}


  


