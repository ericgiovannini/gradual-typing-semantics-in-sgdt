{-# OPTIONS --guarded --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.Predomain.SquareCombinators where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)

open import Cubical.Relation.Binary
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (elim)
open import Cubical.Data.Empty hiding (elim)
open import Cubical.Data.Nat
open import Cubical.HITs.PropositionalTruncation renaming (map to PTmap ; rec to PTrec)


open import Common.Common

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Convenience
open import Semantics.Concrete.Predomain.Constructions renaming (ℕ to NatP)
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Combinators
open import Semantics.Concrete.Predomain.SquareOpaque

private
  variable
    ℓ ℓ'             : Level
    ℓA  ℓ≤A  ℓ≈A     : Level
    ℓA' ℓ≤A' ℓ≈A'    : Level
    ℓc : Level
    
  variable
    ℓAᵢ   ℓ≤Aᵢ   ℓ≈Aᵢ   : Level
    ℓAᵢ'  ℓ≤Aᵢ'  ℓ≈Aᵢ'  : Level
    ℓAᵢ'' ℓ≤Aᵢ'' ℓ≈Aᵢ'' : Level
    ℓAₒ   ℓ≤Aₒ   ℓ≈Aₒ   : Level
    ℓAₒ'  ℓ≤Aₒ'  ℓ≈Aₒ'  : Level
    ℓAₒ'' ℓ≤Aₒ'' ℓ≈Aₒ'' : Level
    ℓcᵢ ℓcₒ ℓcᵢ' ℓcₒ'   : Level

  variable
    ℓA₁   ℓ≤A₁   ℓ≈A₁   : Level
    ℓA₁'  ℓ≤A₁'  ℓ≈A₁'  : Level
    ℓA₂   ℓ≤A₂   ℓ≈A₂   : Level
    ℓA₂'  ℓ≤A₂'  ℓ≈A₂'  : Level
    ℓA₃   ℓ≤A₃   ℓ≈A₃   : Level
    ℓA₃'  ℓ≤A₃'  ℓ≈A₃'  : Level
   
    ℓc₁ ℓc₂ ℓc₃  : Level

  variable
    ℓAᵢ₁  ℓ≤Aᵢ₁  ℓ≈Aᵢ₁  : Level
    ℓAᵢ₁' ℓ≤Aᵢ₁' ℓ≈Aᵢ₁' : Level
    ℓAₒ₁  ℓ≤Aₒ₁  ℓ≈Aₒ₁  : Level
    ℓAₒ₁' ℓ≤Aₒ₁' ℓ≈Aₒ₁' : Level
    ℓcᵢ₁ ℓcₒ₁           : Level
  
    --
    ℓAᵢ₂  ℓ≤Aᵢ₂  ℓ≈Aᵢ₂  : Level
    ℓAᵢ₂' ℓ≤Aᵢ₂' ℓ≈Aᵢ₂' : Level
    ℓAₒ₂  ℓ≤Aₒ₂  ℓ≈Aₒ₂  : Level
    ℓAₒ₂' ℓ≤Aₒ₂' ℓ≈Aₒ₂' : Level
    ℓcᵢ₂ ℓcₒ₂           : Level

    ℓAᵢ₃ ℓ≤Aᵢ₃ ℓ≈Aᵢ₃ : Level
    ℓAₒ₃ ℓ≤Aₒ₃ ℓ≈Aₒ₃ : Level

    ℓΓ ℓ≤Γ ℓ≈Γ ℓΓ' ℓ≤Γ' ℓ≈Γ' : Level
    ℓcΓ : Level

  variable
    A   : Predomain ℓA   ℓ≤A   ℓ≈A
    A'  : Predomain ℓA'  ℓ≤A'  ℓ≈A'

    A₁  : Predomain ℓA₁  ℓ≤A₁  ℓ≈A₁
    A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁'
    A₂  : Predomain ℓA₂  ℓ≤A₂  ℓ≈A₂
    A₂' : Predomain ℓA₂' ℓ≤A₂' ℓ≈A₂'
    A₃  : Predomain ℓA₃  ℓ≤A₃  ℓ≈A₃
    A₃' : Predomain ℓA₃' ℓ≤A₃' ℓ≈A₃'

    Aᵢ  : Predomain ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ
    Aₒ  : Predomain ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ
    Aᵢ' : Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'
    Aₒ' : Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'
    Γ   : Predomain ℓΓ   ℓ≤Γ   ℓ≈Γ
    Γ'  : Predomain ℓΓ'  ℓ≤Γ'  ℓ≈Γ'

    cΓ : PRel Γ Γ' ℓcΓ
    cᵢ : PRel Aᵢ Aᵢ' ℓcᵢ
    cₒ : PRel Aₒ Aₒ' ℓcₒ

    c₁ : PRel A₁ A₁' ℓc₁
    c₂ : PRel A₂ A₂' ℓc₂
    c₃ : PRel A₃ A₃' ℓc₃




-- π1 : (A ×dp B) ==> A
Sq-π1 : {c₁ : PRel A₁ A₁' ℓc₁} {c₂ : PRel A₂ A₂' ℓc₂}
  → PSq (c₁ ×pbmonrel c₂) c₁ (π1 {A = A₁} {B = A₂}) (π1 {A = A₁'} {B = A₂'})
Sq-π1 {A₁ = A₁} {A₁' = A₁'} {A₂ = A₂} {A₂' = A₂'} {c₁ = c₁} {c₂ = c₂} =
  mkPSq (c₁ ×pbmonrel c₂) c₁ (π1 {A = A₁} {B = A₂}) (π1 {A = A₁'} {B = A₂'})
    (λ {(x , y) (z , w) (p , q) → p})

-- π2 : (A ×dp B) ==> B
Sq-π2 : {c₁ : PRel A₁ A₁' ℓc₁} {c₂ : PRel A₂ A₂' ℓc₂}
  → PSq (c₁ ×pbmonrel c₂) c₂ (π2 {A = A₁} {B = A₂}) (π2 {A = A₁'} {B = A₂'})
Sq-π2 {A₁ = A₁} {A₁' = A₁'} {A₂ = A₂} {A₂' = A₂'} {c₁ = c₁} {c₂ = c₂} =
  mkPSq (c₁ ×pbmonrel c₂) c₂ (π2 {A = A₁} {B = A₂}) (π2 {A = A₁'} {B = A₂'})
    (λ {(x , y) (z , w) (p , q) → q})


opaque
  unfolding PSq

  -- (f : ⟨ A ==> B ⟩) -> (g : ⟨ A ==> C ⟩ ) -> ⟨ A ==> B ×dp C ⟩
  Sq-ProdIntro : {c : PRel A A' ℓc} {c₁ : PRel A₁ A₁' ℓc₁} {c₂ : PRel A₂ A₂' ℓc₂}
    → {f₁ : PMor A A₁} {g₁ : PMor A' A₁'} {f₂ : PMor A A₂} {g₂ : PMor A' A₂'}
    → PSq c c₁ f₁ g₁
    → PSq c c₂ f₂ g₂
    → PSq c (c₁ ×pbmonrel c₂) (PairFun f₁ f₂) (PairFun g₁ g₂)
  Sq-ProdIntro α β x y x≤y = (α x y x≤y) , (β x y x≤y)

  -- SwapPair : ⟨ (A₁ ×dp A₂) ==> (A₂ ×dp A₁) ⟩
  Sq-SwapPair : {c₁ : PRel A₁ A₁' ℓc₁} {c₂ : PRel A₂ A₂' ℓc₂}
    → PSq (c₁ ×pbmonrel c₂) (c₂ ×pbmonrel c₁)
          (SwapPair {A = A₁} {B = A₂}) (SwapPair {A = A₁'} {B = A₂'})
  Sq-SwapPair (x₁ , x₂) (y₁ , y₂) (p , q) = q , p

  -- With1st : ⟨ Γ ==> Aₒ ⟩ -> ⟨ Γ ×dp Aᵢ ==> Aₒ ⟩
  Sq-With1st : {cΓ : PRel Γ Γ' ℓcΓ} {cᵢ : PRel Aᵢ Aᵢ' ℓcᵢ} {cₒ : PRel Aₒ Aₒ' ℓcₒ} 
    → {f : PMor Γ Aₒ} {g : PMor Γ' Aₒ'}
    → PSq cΓ cₒ f g
    → PSq (cΓ ×pbmonrel cᵢ) cₒ (With1st {A = Aᵢ} f) (With1st {A = Aᵢ'} g)
  Sq-With1st α (γ , x) (γ' , y) (γ≤γ' , x≤y) = α γ γ' γ≤γ'


  -- With2nd : ⟨ Aᵢ ==> Aₒ ⟩ -> ⟨ Γ ×dp Aᵢ ==> Aₒ ⟩
  Sq-With2nd : {cΓ : PRel Γ Γ' ℓcΓ} {cᵢ : PRel Aᵢ Aᵢ' ℓcᵢ} {cₒ : PRel Aₒ Aₒ' ℓcₒ}
    → {f : PMor Aᵢ Aₒ} {g : PMor Aᵢ' Aₒ'}
    → PSq cᵢ cₒ f g
    → PSq (cΓ ×pbmonrel cᵢ) cₒ (With2nd {Γ = Γ} f) (With2nd {Γ = Γ'} g)
  Sq-With2nd α (γ , x) (γ' , y) (γ≤γ' , x≤y) = α x y x≤y


  -- Curry :  ⟨ (Γ ×dp Aᵢ) ==> Aₒ ⟩ -> ⟨ Γ ==> Aᵢ ==> Aₒ ⟩
  Sq-Curry : {cΓ : PRel Γ Γ' ℓcΓ} {cᵢ : PRel Aᵢ Aᵢ' ℓcᵢ} {cₒ : PRel Aₒ Aₒ' ℓcₒ}
    → {f : PMor (Γ ×dp Aᵢ) Aₒ} {g : PMor (Γ' ×dp Aᵢ') Aₒ'}
    → PSq (cΓ ×pbmonrel cᵢ) cₒ f g
    → PSq cΓ (cᵢ ==>pbmonrel cₒ) (Curry {Γ = Γ} {A = Aᵢ} f) (Curry {Γ = Γ'} {A = Aᵢ'} g)
  Sq-Curry α γ γ' γ≤γ' x y x≤y = α (γ , x) (γ' , y) (γ≤γ' , x≤y)

  -- Uncurry : ⟨ Γ ==> Aᵢ ==> Aₒ ⟩ -> ⟨ (Γ ×dp Aᵢ) ==> Aₒ ⟩
  Sq-Uncurry : {cΓ : PRel Γ Γ' ℓcΓ} {cᵢ : PRel Aᵢ Aᵢ' ℓcᵢ} {cₒ : PRel Aₒ Aₒ' ℓcₒ}
    → {f : PMor Γ (Aᵢ ==> Aₒ)} {g : PMor Γ' (Aᵢ' ==> Aₒ')}
    → PSq cΓ (cᵢ ==>pbmonrel cₒ) f g
    → PSq (cΓ ×pbmonrel cᵢ) cₒ (Uncurry f) (Uncurry g)
  Sq-Uncurry α (γ , x) (γ' , y) (γ≤γ' , x≤y) = α γ γ' γ≤γ' x y x≤y

  -- App : ⟨ ((A ==> B) ×dp A) ==> B ⟩


  -- _∘p'_ : ⟨ (Γ ×dp A₂ ==> A₃) ⟩ -> ⟨ (Γ ×dp A₁ ==> A₂) ⟩ -> ⟨ (Γ ×dp A₁ ==> A₃) ⟩
  Sq-CompStrong :
      {cΓ : PRel Γ Γ' ℓcΓ}   {c₁ : PRel A₁ A₁' ℓc₁}
    → {c₂ : PRel A₂ A₂' ℓc₂} {c₃ : PRel A₃ A₃' ℓc₃}
    → {f₁ : PMor (Γ ×dp A₁) A₂} {g₁ : PMor (Γ' ×dp A₁') A₂'}
    → {f₂ : PMor (Γ ×dp A₂) A₃} {g₂ : PMor (Γ' ×dp A₂') A₃'}
    → PSq (cΓ ×pbmonrel c₁) c₂ f₁ g₁
    → PSq (cΓ ×pbmonrel c₂) c₃ f₂ g₂
    → PSq (cΓ ×pbmonrel c₁) c₃
       (_∘p'_ {Γ = Γ}  {B = A₂}  {C = A₃}  {A = A₁}  f₂ f₁)
       (_∘p'_ {Γ = Γ'} {B = A₂'} {C = A₃'} {A = A₁'} g₂ g₁)
  Sq-CompStrong α β = {!!}

