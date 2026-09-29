{-# OPTIONS --guarded --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --backtracking-instance-search #-}


module Semantics.Concrete.Predomain.InstanceTest2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)

open import Cubical.Relation.Binary
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty


open import Common.Common

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Convenience
open import Semantics.Concrete.Predomain.Constructions renaming (ℕ to NatP)
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Constructions
open import Semantics.Concrete.Predomain.Combinators

open import Cubical.Relation.Binary.Base

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
    ℓR ℓRᵢ ℓRₒ ℓR₁ ℓR₂ ℓR₃ : Level
    ℓAᵢ' ℓAₒ' : Level


module _
  {A₁ : Type ℓA₁} {A₁' : Type ℓA₁'}
  {A₂ : Type ℓA₂} {A₂' : Type ℓA₂'}
  (R₁ : Rel A₁ A₁' ℓR₁) (R₂ : Rel A₂ A₂' ℓR₂) where

  _×rel_ : Rel (A₁ × A₂) (A₁' × A₂') (ℓ-max ℓR₁ ℓR₂)
  _×rel_ (x₁ , x₂) (y₁ , y₂) = (R₁ x₁ y₁) × (R₂ x₂ y₂)
  

  _⊎rel_ : Rel (A₁ ⊎ A₂) (A₁' ⊎ A₂') (ℓ-max ℓR₁ ℓR₂)
  inl x₁ ⊎rel inl y₁ = Lift {j = ℓR₂} (R₁ x₁ y₁)
  inr x₂ ⊎rel inr y₂ = Lift {j = ℓR₁} (R₂ x₂ y₂)
  _ ⊎rel _ = ⊥*




module _
  {Aᵢ  : Type ℓAᵢ}
  {Aᵢ' : Type ℓAᵢ'}
  {Aₒ  : Type ℓAₒ}
  {Aₒ' : Type ℓAₒ'}
  (Rᵢ  : Rel Aᵢ Aᵢ' ℓRᵢ)
  (Rₒ  : Rel Aₒ Aₒ' ℓRₒ)
  (f   : Aᵢ  → Aₒ)
  (g   : Aᵢ' → Aₒ')
  where

    2Cell-Type : Type (ℓ-max (ℓ-max (ℓ-max ℓAᵢ ℓAᵢ') ℓRᵢ) ℓRₒ)
    2Cell-Type = ∀ (x : Aᵢ) (y : Aᵢ')
          → Rᵢ x y
          → Rₒ (f x) (g y)
  
    record 2Cell
      : Type (ℓ-max (ℓ-max (ℓ-max ℓAᵢ ℓAᵢ') ℓRᵢ) ℓRₒ) where
      
      constructor mk2Cell
      field
        is2Cell : 2Cell-Type


-- open 2Cell
open 2Cell {{...}} public



module _ {A : Type ℓ} {A' : Type ℓ'} {R : Rel A A' ℓR} where

  instance
    2CellId : 2Cell R R (λ x → x) (λ x → x)
    2CellId .is2Cell x y Rxy = Rxy
    {-# OVERLAPPABLE 2CellId #-}


module _
    {A₁  : Type ℓA₁ }
    {A₁' : Type ℓA₁'}
    {A₂  : Type ℓA₂ }
    {A₂' : Type ℓA₂'}
    {A₃  : Type ℓA₃ }
    {A₃' : Type ℓA₃'}
    {R₁  : Rel A₁ A₁' ℓR₁}
    {R₂  : Rel A₂ A₂' ℓR₂}
    {R₃  : Rel A₃ A₃' ℓR₃}
    {f₁  : A₁  → A₂ }
    {g₁  : A₁' → A₂'}
    {f₂  : A₂  → A₃ }
    {g₂  : A₂' → A₃'}
    {{α : 2Cell R₁ R₂ f₁ g₁}}
    {{β : 2Cell R₂ R₃ f₂ g₂}}
    where

  instance
    Comp2CellV : 2Cell R₁ R₃ (f₂ ∘ f₁) (g₂ ∘ g₁)
    Comp2CellV .is2Cell x y xRy =
      β .is2Cell (f₁ x) (g₁ y) (α .is2Cell x y xRy)
    {-# OVERLAPPABLE Comp2CellV #-}
    -- Allows this instance to be discarded in favor of a strictly more specific instance
    -- see https://agda.readthedocs.io/en/v2.7.0/language/instance-arguments.html#overlap-and-backtracking



module _
  {A₁ : Type ℓA₁} {A₁' : Type ℓA₁'}
  {A₂ : Type ℓA₂} {A₂' : Type ℓA₂'}
  {R₁ : Rel A₁ A₁' ℓR₁} {R₂ : Rel A₂ A₂' ℓR₂}
  where
    instance
      2CellFst : 2Cell (R₁ ×rel R₂) R₁ fst fst
      2CellFst .is2Cell (x₁ , x₂) (y₁ , y₂) (x₁Ry₁ , x₂Ry₂) = x₁Ry₁

      2CellSnd : 2Cell (R₁ ×rel R₂) R₂ snd snd
      2CellSnd .is2Cell (x₁ , x₂) (y₁ , y₂) (x₁Ry₁ , x₂Ry₂) = x₂Ry₂



{-
These instances will not be in scope, as they have explicit arguments.

From https://agda.readthedocs.io/en/stable/language/instance-arguments.html:

    Instances with explicit arguments are also accepted but will not
    be considered as instances because the value of the explicit arguments
    cannot be derived automatically.

-}
module _
  {A₁ : Type ℓA₁} {A₁' : Type ℓA₁'}
  {A₂ : Type ℓA₂} {A₂' : Type ℓA₂'}
  (R₁ : Rel A₁ A₁' ℓR₁) (R₂ : Rel A₂ A₂' ℓR₂)
  where
    instance
      2CellFstBad : 2Cell (R₁ ×rel R₂) R₁ fst fst
      2CellFstBad .is2Cell (x₁ , x₂) (y₁ , y₂) (x₁Ry₁ , x₂Ry₂) = x₁Ry₁

      2CellSndBad : 2Cell (R₁ ×rel R₂) R₂ snd snd
      2CellSndBad .is2Cell (x₁ , x₂) (y₁ , y₂) (x₁Ry₁ , x₂Ry₂) = x₂Ry₂



module Test 
  {A₁ : Type ℓA₁} {A₁' : Type ℓA₁'}
  {A₂ : Type ℓA₂} {A₂' : Type ℓA₂'}
  (R₁ : Rel A₁ A₁' ℓR₁) (R₂ : Rel A₂ A₂' ℓR₂)
  where

  2CellTest : 2Cell-Type (R₁ ×rel R₂) R₁ fst fst
  2CellTest = is2Cell -- Agda can find the correct instance (i.e. 2CellFst)


module Test2
  {A₁ : Type ℓA₁} {A₁' : Type ℓA₁'}
  {A₂ : Type ℓA₂} {A₂' : Type ℓA₂'}
  {A₃ : Type ℓA₃} {A₃' : Type ℓA₃'}
  (R₁ : Rel A₁ A₁' ℓR₁) (R₂ : Rel A₂ A₂' ℓR₂) (R₃ : Rel A₃ A₃' ℓR₃)
  where

  2CellTest : 2Cell-Type ((R₁ ×rel R₂) ×rel R₃) R₁ (fst ∘ fst) (fst ∘ fst)
  2CellTest = is2Cell -- {{r = Comp2CellV {α = 2CellFst} {β = 2CellFst}}}



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


  


