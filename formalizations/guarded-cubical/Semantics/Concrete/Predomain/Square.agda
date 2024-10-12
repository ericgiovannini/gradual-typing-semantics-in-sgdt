{-# OPTIONS --guarded --rewriting #-}


-- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.Predomain.Square where

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

open BinaryRelation

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

  variable
    ℓα ℓβ ℓα₁ ℓα₂ : Level

    -- Aᵢ  : PosetBisim ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ
    -- Aᵢ' : PosetBisim ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'
    -- Aₒ  : PosetBisim ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  
    -- Aₒ' : PosetBisim ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'


PSq :
  {Aᵢ  : Predomain ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ}
  {Aᵢ' : Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
  {Aₒ  : Predomain ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ} 
  {Aₒ' : Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'} →
  (cᵢ  : PRel Aᵢ Aᵢ' ℓcᵢ) →
  (cₒ  : PRel Aₒ Aₒ' ℓcₒ) →
  (f   : PMor Aᵢ  Aₒ) →
  (g   : PMor Aᵢ' Aₒ') →
  Type (ℓ-max (ℓ-max ℓAᵢ ℓAᵢ') (ℓ-max ℓcᵢ ℓcₒ))
PSq cᵢ cₒ f g = TwoCell (cᵢ .PRel.R) (cₒ .PRel.R) (f .PMor.f) (g .PMor.f)


--          cᵢ
--     Aᵢ o---* Aᵢ'
--     |         |
--   f |         | g 
--     v         v
--     Aₒ o---* Aₒ'
--          cₒ


isPropPSq :
  {Aᵢ  : Predomain ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ}
  {Aᵢ' : Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
  {Aₒ  : Predomain ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ} 
  {Aₒ' : Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'} →
  (cᵢ  : PRel Aᵢ Aᵢ' ℓcᵢ) →
  (cₒ  : PRel Aₒ Aₒ' ℓcₒ) →
  (f   : PMor Aᵢ  Aₒ) →
  (g   : PMor Aᵢ' Aₒ') →
  isProp (PSq cᵢ cₒ f g)
isPropPSq cᵢ cₒ f g = isPropTwoCell (cₒ .PRel.is-prop-valued)


-- "Horizontal" identity squares.

-- The existence of these squares relies on the fact that f is
-- *montone*.

Predom-IdSqH : -- {ℓo : Level} →
  {Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ}
  {Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} →
  (f : PMor Aᵢ Aₒ) →
  PSq (idPRel Aᵢ) (idPRel Aₒ) f f
Predom-IdSqH f x₁ x₂ x₁≤x₂ =
  (f .PMor.isMon x₁≤x₂)

-- "Vertical" identity squares.

Predom-IdSqV : -- {ℓo : Level} →
  {A : Predomain ℓA ℓ≤A ℓ≈A}
  {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  (c : PRel A A' ℓc) →
  PSq c c Id Id
Predom-IdSqV c x y xRy = xRy
  


-- Vertical composition of squares

--           c₁
--      A₁ o---* A₁'
--      |         |
--   f₁ |    α₁   | g₁
--      v         v                                 c₁
--      A₂ o---* A₂'                           A₁ o---* A₁'
--           c₂                                |         |
--                        =====>      f₂ ∘ f₁  | α₂ ∘ α₁ |  g₂ ∘ g₁
--           c₂                                v         v
--      A₂ o---* A₂'                           A₃ o---* A₃' 
--      |         |                                 c₃
--   f₂ |    α₂   | g₂
--      v         v
--      A₃ o---* A₃'
--           c₃


CompSqV :
  {A₁  : Predomain ℓA₁  ℓ≤A₁  ℓ≈A₁ }
  {A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁'}
  {A₂  : Predomain ℓA₂  ℓ≤A₂  ℓ≈A₂ }
  {A₂' : Predomain ℓA₂' ℓ≤A₂' ℓ≈A₂'}
  {A₃  : Predomain ℓA₃  ℓ≤A₃  ℓ≈A₃ }
  {A₃' : Predomain ℓA₃' ℓ≤A₃' ℓ≈A₃'}
  {c₁  : PRel A₁ A₁' ℓc₁}
  {c₂  : PRel A₂ A₂' ℓc₂}
  {c₃  : PRel A₃ A₃' ℓc₃}
  {f₁  : PMor A₁  A₂ }
  {g₁  : PMor A₁' A₂'}
  {f₂  : PMor A₂  A₃ }
  {g₂  : PMor A₂' A₃'} →
  PSq c₁ c₂ f₁ g₁ →
  PSq c₂ c₃ f₂ g₂ →
  PSq c₁ c₃ (f₂ ∘p f₁) (g₂ ∘p g₁)
CompSqV α₁ α₂ x y xRy = α₂ _ _ (α₁ _ _ xRy)

_∘psqv_ = CompSqV
infixl 20 _∘psqv_


-- Iterated vertical composition
CompSqV-iterate :
  {A₁  : Predomain ℓA₁  ℓ≤A₁  ℓ≈A₁ }
  {A₂  : Predomain ℓA₂  ℓ≤A₂  ℓ≈A₂ }
  (c : PRel A₁ A₂ ℓc) →
  (f : PMor A₁ A₁) →
  (g : PMor A₂ A₂) →
  (PSq c c f g) →
  (n : ℕ) → PSq c c (f ^m n) (g ^m n)
CompSqV-iterate c f g α zero = Predom-IdSqV c
CompSqV-iterate c f g α (suc n) =
  CompSqV {c₁ = c} {c₂ = c} {c₃ = c}
          {f₁ = f ^m n} {g₁ = g ^m n} {f₂ = f} {g₂ = g}
          (CompSqV-iterate c f g α n) α
{-
CompSqV-iterate-idL :
  {A₁  : Predomain ℓA₁  ℓ≤A₁  ℓ≈A₁ }
  {A₂  : Predomain ℓA₂  ℓ≤A₂  ℓ≈A₂ }
  (c : PRel A₁ A₂ ℓc) →
  (g : PMor A₂ A₂) →
  (PSq c c Id g) →
  (n : ℕ) → PSq c c Id (g ^m n)
CompSqV-iterate-idL = {!!}


-- TwoCell-iterated R f g α zero = λ _ _ → id
-- TwoCell-iterated R f g α (suc n) = λ x₁ x₂ Rx₁x₂ →
--   α ((f ^ n) x₁)
--     ((g ^ n) x₂)
--     (TwoCell-iterated R f g α n x₁ x₂ Rx₁x₂)
-}

-- Horizontal composition of squares

--          cᵢ₁                    cᵢ₂
--     Aᵢ₁ o---* Aᵢ₂          Aᵢ₂ o---* Aᵢ₃
--     |         |            |         |
--   f |    α    | g        g |    β    | h
--     v         v            v         v   
--     Aₒ₁ o---* Aₒ₂          Aₒ₂ o---* Aₒ₃
--          cₒ₁                    cₒ₂     
--
--                   
--                    ||
--                    VV
--
--                cᵢ₁ ⊙ cᵢ₂        
--            Aᵢ₁ o-------* Aᵢ₂  
--            |             |   
--          f |    α ⊙ β    | h
--            v             v
--            Aₒ₁ o-------* Aₒ₂
--                cₒ₁ ⊙ cₒ₂

CompSqH :
  {Aᵢ₁ : Predomain ℓAᵢ₁ ℓ≤Aᵢ₁ ℓ≈Aᵢ₁}
  {Aᵢ₂ : Predomain ℓAᵢ₂ ℓ≤Aᵢ₂ ℓ≈Aᵢ₂}
  {Aᵢ₃ : Predomain ℓAᵢ₃ ℓ≤Aᵢ₃ ℓ≈Aᵢ₃}
  {Aₒ₁ : Predomain ℓAₒ₁ ℓ≤Aₒ₁ ℓ≈Aₒ₁}
  {Aₒ₂ : Predomain ℓAₒ₂ ℓ≤Aₒ₂ ℓ≈Aₒ₂}
  {Aₒ₃ : Predomain ℓAₒ₃ ℓ≤Aₒ₃ ℓ≈Aₒ₃}
  {cᵢ₁ : PRel Aᵢ₁ Aᵢ₂ ℓcᵢ₁}
  {cᵢ₂ : PRel Aᵢ₂ Aᵢ₃ ℓcᵢ₂}
  {cₒ₁ : PRel Aₒ₁ Aₒ₂ ℓcₒ₁}
  {cₒ₂ : PRel Aₒ₂ Aₒ₃ ℓcₒ₂}
  {f : PMor Aᵢ₁ Aₒ₁}
  {g : PMor Aᵢ₂ Aₒ₂}
  {h : PMor Aᵢ₃ Aₒ₃} →
  PSq cᵢ₁ cₒ₁  f g →
  PSq cᵢ₂ cₒ₂ g h →
  PSq (cᵢ₁ ⊙ cᵢ₂) (cₒ₁ ⊙ cₒ₂) f h
CompSqH {g = g} α β x z xcᵢ₁cᵢ₂z =
  PTmap
    (λ (y , xcᵢ₁y , ycᵢ₂z) →
      (g $ y)
      , α _ _ xcᵢ₁y  -- NTS (f x) cₒ₁ (g y)
      , β _ _ ycᵢ₂z) -- NTS (g y) cₒ₂ (h z)
    xcᵢ₁cᵢ₂z

_∘psqh_ = CompSqH
infixl 20 _∘psqh_



-- Action of the exponential ==> on squares

module _
  {Aᵢ₁  : Predomain ℓAᵢ₁  ℓ≤Aᵢ₁  ℓ≈Aᵢ₁}
  {Aᵢ₁' : Predomain ℓAᵢ₁' ℓ≤Aᵢ₁' ℓ≈Aᵢ₁'}
  {Aₒ₁  : Predomain ℓAₒ₁  ℓ≤Aₒ₁  ℓ≈Aₒ₁} 
  {Aₒ₁' : Predomain ℓAₒ₁' ℓ≤Aₒ₁' ℓ≈Aₒ₁'}
  {Aᵢ₂  : Predomain ℓAᵢ₂  ℓ≤Aᵢ₂  ℓ≈Aᵢ₂}
  {Aᵢ₂' : Predomain ℓAᵢ₂' ℓ≤Aᵢ₂' ℓ≈Aᵢ₂'}
  {Aₒ₂  : Predomain ℓAₒ₂  ℓ≤Aₒ₂  ℓ≈Aₒ₂} 
  {Aₒ₂' : Predomain ℓAₒ₂' ℓ≤Aₒ₂' ℓ≈Aₒ₂'}
  {cᵢ₁  : PRel Aᵢ₁ Aᵢ₁' ℓcᵢ₁}
  {cₒ₁  : PRel Aₒ₁ Aₒ₁' ℓcₒ₁}
  {f₁   : PMor Aₒ₁  Aᵢ₁}   -- Notice the flip in direction!
  {g₁   : PMor Aₒ₁' Aᵢ₁'}  -- Notice the flip in direction!
  {cᵢ₂  : PRel Aᵢ₂ Aᵢ₂' ℓcᵢ₂}
  {cₒ₂  : PRel Aₒ₂ Aₒ₂' ℓcₒ₂}
  {f₂   : PMor Aᵢ₂  Aₒ₂} 
  {g₂   : PMor Aᵢ₂' Aₒ₂'}

  where

--          cₒ₁                    cᵢ₂
--     Aₒ₁ o---* Aₒ₁'         Aᵢ₂ o---* Aᵢ₂'
--      |         |            |         |
--   f₁ |    α    | g₁      f₂ |    β    | g₂ 
--      v         v            v         v
--     Aᵢ₁ o---* Aᵢ₁'         Aₒ₂ o---* Aₒ₂'
--          cᵢ₁                    cₒ₂

  _==>psq_ : PSq cₒ₁ cᵢ₁ f₁ g₁ → PSq cᵢ₂ cₒ₂ f₂ g₂ →
    PSq (cᵢ₁ ==>pbmonrel cᵢ₂) (cₒ₁ ==>pbmonrel cₒ₂) (f₁ ~-> f₂) (g₁ ~-> g₂)
  α ==>psq β = λ q q' γ → λ x y xRy → β _ _ (γ _ _ (α _ _ xRy))

-- Given:
--          cᵢ₁            
--     Aᵢ₁ o---* Aᵢ₁'      
--      |         |        
--   q  |    γ    | q'     
--      v         v        
--     Aᵢ₂ o---* Aᵢ₂'      
--          cᵢ₂            
--
-- Need to build:
--
--                    cₒ₁            
--               Aₒ₁ o---* Aₒ₁'      
--                |         |        
--   f₂ ∘ q ∘ f₁  |         | g₂ ∘ q' ∘ g₁     
--                v         v        
--               Aₒ₂ o---* Aₒ₂'      
--                    cₒ₂   
--
-- This is just vertical pasting of squares!



-- Squares corresponding to the identity and associativity of
-- composition of predomain relations
---------------------------------------------------------------

sq-idA⊙c-c : {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain  ℓA' ℓ≤A' ℓ≈A'} (c : PRel A A' ℓc) →
  PSq (idPRel A ⊙ c) c Id Id
sq-idA⊙c-c {A = A} {A' = A'} c x y H =
  PTrec (c.is-prop-valued x y) (λ { (x' , x≤x' , x'Ry) → c.is-antitone x≤x' x'Ry }) H
  where module c = PRel c


sq-c⊙A'-c : {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain  ℓA' ℓ≤A' ℓ≈A'} (c : PRel A A' ℓc) →
  PSq (c ⊙ idPRel A') c Id Id
sq-c⊙A'-c {A = A} {A' = A'} c x y H =
  PTrec (c.is-prop-valued x y) (λ { (y' , xRy' , y'≤y) → c.is-monotone xRy' y'≤y }) H
  where module c = PRel c


sq-c-idA⊙c : {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain  ℓA' ℓ≤A' ℓ≈A'} (c : PRel A A' ℓc) →
    PSq c (idPRel A ⊙ c) Id Id
sq-c-idA⊙c {A = A} {A' = A'} c x y xRy = ∣ x , A.is-refl x , xRy ∣₁
  where module A = PredomainStr (A .snd)


sq-c-c⊙A' : {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain  ℓA' ℓ≤A' ℓ≈A'} (c : PRel A A' ℓc) →
    PSq c (c ⊙ idPRel A') Id Id
sq-c-c⊙A' {A = A} {A' = A'} c x y xRy = ∣ y , xRy , A'.is-refl y ∣₁
  where module A' = PredomainStr (A' .snd)


-- TODO associativity




-- lemma about squares between functional relations
SqV-functionalRel :
  {Aᵢ  : Predomain ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ}  {Aₒ  : Predomain  ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ}
  {Aᵢ' : Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'} {Aₒ' : Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'} →
  (f : PMor Aᵢ  Aₒ) →
  (g : PMor Aᵢ' Aₒ') →
  (c : PRel Aₒ Aₒ' ℓc) →
  PSq (functionalRel f g c) c f g
SqV-functionalRel f g c a a' fa-R-gb = fa-R-gb

-- SqV-functionalRel-bot :
--   {Aᵢ  : Predomain ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ}  {Aₒ  : Predomain  ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ}
--   {Aᵢ' : Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'} {Aₒ' : Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'} →
--   (f : PMor Aᵢ  Aᵢ) →
--   (g : PMor Aᵢ' Aᵢ') →
--   (c : PRel Aᵢ Aᵢ' ℓc) →
--   PSq c (functionalRel f g c) f g


-- Identity and associativity laws for composition of horizontal morphisms
--------------------------------------------------------------------------

PredomainRel-Comp-IdL : {A₁ : Predomain ℓ ℓ ℓ≈A₁} {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} →
  (c : PRel A₁ A₂ ℓ) → ((idPRel A₁) ⊙ c) ≡ c
PredomainRel-Comp-IdL c = eqPRel _ _ (funExt λ x → funExt λ y →
  hPropExt
    isPropPropTrunc (c.is-prop-valued x y)
    (λ H → sq-idA⊙c-c c x y H)
    (λ H → sq-c-idA⊙c c x y H))
  where module c = PRel c

PredomainRel-Comp-IdR : {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : Predomain ℓ ℓ ℓ≈A₂} →
  (c : PRel A₁ A₂ ℓ) → (c ⊙ (idPRel A₂)) ≡ c
PredomainRel-Comp-IdR c = eqPRel _ _ (funExt λ x → funExt λ y →
  hPropExt
    isPropPropTrunc (c.is-prop-valued x y)
    (λ H → sq-c⊙A'-c c x y H)
    (λ H → sq-c-c⊙A' c x y H))
  where module c = PRel c

-- TODO associativity





-- Action of × on squares
--------------------------

module _
  {Aᵢ₁ : Predomain ℓAᵢ₁ ℓ≤Aᵢ₁ ℓ≈Aᵢ₁} {Aᵢ₁' : Predomain ℓAᵢ₁' ℓ≤Aᵢ₁' ℓ≈Aᵢ₁'}
  {Aᵢ₂ : Predomain ℓAᵢ₂ ℓ≤Aᵢ₂ ℓ≈Aᵢ₂} {Aᵢ₂' : Predomain ℓAᵢ₂' ℓ≤Aᵢ₂' ℓ≈Aᵢ₂'}
  {Aₒ₁ : Predomain ℓAₒ₁ ℓ≤Aₒ₁ ℓ≈Aₒ₁} {Aₒ₁' : Predomain ℓAₒ₁' ℓ≤Aₒ₁' ℓ≈Aₒ₁'}
  {Aₒ₂ : Predomain ℓAₒ₂ ℓ≤Aₒ₂ ℓ≈Aₒ₂} {Aₒ₂' : Predomain ℓAₒ₂' ℓ≤Aₒ₂' ℓ≈Aₒ₂'}
  {cᵢ₁ : PRel Aᵢ₁ Aᵢ₁' ℓcᵢ₁}
  {cᵢ₂ : PRel Aᵢ₂ Aᵢ₂' ℓcᵢ₂}
  {cₒ₁ : PRel Aₒ₁ Aₒ₁' ℓcₒ₁}
  {cₒ₂ : PRel Aₒ₂ Aₒ₂' ℓcₒ₂}
  {f₁ : PMor Aᵢ₁ Aₒ₁}
  {g₁ : PMor Aᵢ₁' Aₒ₁'}
  {f₂ : PMor Aᵢ₂ Aₒ₂}
  {g₂ : PMor Aᵢ₂' Aₒ₂'}
  where

  _×-Sq_ :
    PSq cᵢ₁ cₒ₁ f₁ g₁ →
    PSq cᵢ₂ cₒ₂ f₂ g₂ →
    PSq (cᵢ₁ ×pbmonrel cᵢ₂) (cₒ₁ ×pbmonrel cₒ₂) (f₁ ×mor f₂) (g₁ ×mor g₂)
  (α₁ ×-Sq α₂) (aᵢ₁ , aᵢ₂) (aᵢ₁' , aᵢ₂') (R₁₂ , R₁₂') =
    (α₁ aᵢ₁ aᵢ₁' R₁₂) , (α₂ aᵢ₂ aᵢ₂' R₁₂')


-- Action of ⊎ on squares
--------------------------

module _
  {Aᵢ₁ : Predomain ℓAᵢ₁ ℓ≤Aᵢ₁ ℓ≈Aᵢ₁} {Aᵢ₁' : Predomain ℓAᵢ₁' ℓ≤Aᵢ₁' ℓ≈Aᵢ₁'}
  {Aᵢ₂ : Predomain ℓAᵢ₂ ℓ≤Aᵢ₂ ℓ≈Aᵢ₂} {Aᵢ₂' : Predomain ℓAᵢ₂' ℓ≤Aᵢ₂' ℓ≈Aᵢ₂'}
  {Aₒ₁ : Predomain ℓAₒ₁ ℓ≤Aₒ₁ ℓ≈Aₒ₁} {Aₒ₁' : Predomain ℓAₒ₁' ℓ≤Aₒ₁' ℓ≈Aₒ₁'}
  {Aₒ₂ : Predomain ℓAₒ₂ ℓ≤Aₒ₂ ℓ≈Aₒ₂} {Aₒ₂' : Predomain ℓAₒ₂' ℓ≤Aₒ₂' ℓ≈Aₒ₂'}
  {cᵢ₁ : PRel Aᵢ₁ Aᵢ₁' ℓcᵢ₁}
  {cᵢ₂ : PRel Aᵢ₂ Aᵢ₂' ℓcᵢ₂}
  {cₒ₁ : PRel Aₒ₁ Aₒ₁' ℓcₒ₁}
  {cₒ₂ : PRel Aₒ₂ Aₒ₂' ℓcₒ₂}
  {f₁ : PMor Aᵢ₁ Aₒ₁}
  {g₁ : PMor Aᵢ₁' Aₒ₁'}
  {f₂ : PMor Aᵢ₂ Aₒ₂}
  {g₂ : PMor Aᵢ₂' Aₒ₂'}
  where

  _⊎-Sq_ :
    PSq cᵢ₁ cₒ₁ f₁ g₁ →
    PSq cᵢ₂ cₒ₂ f₂ g₂ →
    PSq (cᵢ₁ ⊎-rel cᵢ₂) (cₒ₁ ⊎-rel cₒ₂) (f₁ ⊎-mor f₂) (g₁ ⊎-mor g₂)
  (α ⊎-Sq β) (inl xᵢ₁) (inl xᵢ₁') H = lift (α xᵢ₁ xᵢ₁' (lower H))
  (α ⊎-Sq β) (inr xᵢ₂) (inr xᵢ₂') H = lift (β xᵢ₂ xᵢ₂' (lower H))


-- Action of Π on squares
--------------------------

module _ (X : Type ℓ)
  (Aᵢ : X → Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ) (Aᵢ' : X → Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ')
  (Aₒ : X → Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ) (Aₒ' : X → Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ')
  (cᵢ : ∀ x → PRel (Aᵢ x) (Aᵢ' x) ℓcᵢ)
  (cₒ : ∀ x → PRel (Aₒ x) (Aₒ' x) ℓcₒ)
  (f : ∀ x → PMor (Aᵢ  x) (Aₒ  x))
  (g : ∀ x → PMor (Aᵢ' x) (Aₒ' x)) 
  where 

  Π-Sq :
    (∀ x → PSq (cᵢ x) (cₒ x) (f x) (g x)) →
    PSq (ΠR X Aᵢ Aᵢ' cᵢ) (ΠR X Aₒ Aₒ' cₒ) (Π-mor X _ _ f) (Π-mor X _ _ g)
  Π-Sq αs as as' asRas' x = αs x (as x) (as' x) (asRas' x)


-- Action of Σ on squares
--------------------------

module _ (X : hSet ℓ)
  (Aᵢ : ⟨ X ⟩ → Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ) (Aᵢ' : ⟨ X ⟩ → Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ')
  (Aₒ : ⟨ X ⟩ → Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ) (Aₒ' : ⟨ X ⟩ → Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ')
  (cᵢ : ∀ x → PRel (Aᵢ x) (Aᵢ' x) ℓcᵢ)
  (cₒ : ∀ x → PRel (Aₒ x) (Aₒ' x) ℓcₒ)
  (f : ∀ x → PMor (Aᵢ  x) (Aₒ  x))
  (g : ∀ x → PMor (Aᵢ' x) (Aₒ' x)) 
  where 

  Σ-Sq :
    (∀ x → PSq (cᵢ x) (cₒ x) (f x) (g x)) →
    PSq (ΣR X Aᵢ Aᵢ' cᵢ) (ΣR X Aₒ Aₒ' cₒ) (Σ-mor X _ _ f) (Σ-mor X _ _ g)
  Σ-Sq αs (x₁ , a₁) (x₂ , a₂) (x₁≡x₂ , a₁₂≤a₂) =
    x₁≡x₂ ,
    let sq = αs x₂ (subst (λ z → ⟨ Aᵢ z ⟩) x₁≡x₂ a₁) a₂ a₁₂≤a₂ in
    subst (λ z → cₒ x₂ .PRel.R z (g x₂ .PMor.f a₂)) lem sq

    where
    
      --        subst          f x₂
      -- Aᵢ x₁ -------> Aᵢ x₂ -------> Aₒ x₂
      --
      --
      --                  =
      --
      --         f x₁          subst
      -- Aᵢ x₁ -------> Aₒ x₁ -------> Aₒ x₂
      
      lem : f x₂ .PMor.f (subst (λ z → ⟨ Aᵢ z ⟩) x₁≡x₂ a₁) ≡
            subst (λ x → ⟨ Aₒ x ⟩) x₁≡x₂ (f x₁ .PMor.f a₁)
      lem = sym (fromPathP (λ i → f (x₁≡x₂ i) .PMor.f (subst-filler (λ x → ⟨ Aᵢ x ⟩) x₁≡x₂ a₁ i)))


-- Action of transport on squares
{-
open PRel

transport-square : {A₁ A₁' : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ A₂' : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} →
  {c : PRel A₁ A₂ ℓc} →
  {c' : PRel A₁' A₂' ℓc} →
  (eq₁ : A₁ ≡ A₁') →
  (eq₂ : A₂ ≡ A₂') →
  (PathP (λ i → PRel (eq₁ i) (eq₂ i) ℓc) c c') →
  PSq c c' (mTransport eq₁) (mTransport eq₂)
transport-square eq₁ eq₂ path x y xRy =
  transport
    (λ i → (path i) .R
      (transport-filler (λ j → ⟨ eq₁ j ⟩) x i)
      (transport-filler (λ j → ⟨ eq₂ j ⟩) y i))
    xRy


module _
  {Aᵢ₁ Aᵢ₁' : Predomain ℓAᵢ₁ ℓ≤Aᵢ₁ ℓ≈Aᵢ₁}
  {Aᵢ₂ Aᵢ₂' : Predomain ℓAᵢ₂ ℓ≤Aᵢ₂ ℓ≈Aᵢ₂}
  {Aₒ₁ Aₒ₁' : Predomain ℓAₒ₁ ℓ≤Aₒ₁ ℓ≈Aₒ₁}
  {Aₒ₂ Aₒ₂' : Predomain ℓAₒ₂ ℓ≤Aₒ₂ ℓ≈Aₒ₂}
  {cᵢ  : PRel Aᵢ₁  Aᵢ₂  ℓcᵢ}
  {cᵢ' : PRel Aᵢ₁' Aᵢ₂' ℓcᵢ}
  {cₒ  : PRel Aₒ₁  Aₒ₂  ℓcₒ}
  {cₒ' : PRel Aₒ₁' Aₒ₂' ℓcₒ}
  {f  : PMor Aᵢ₁  Aₒ₁}
  {f' : PMor Aᵢ₁' Aₒ₁'}
  {g  : PMor Aᵢ₂  Aₒ₂}
  {g' : PMor Aᵢ₂' Aₒ₂'}
  (eqᵢ₁ : Aᵢ₁ ≡ Aᵢ₁')
  (eqᵢ₂ : Aᵢ₂ ≡ Aᵢ₂')
  (eqₒ₁ : Aₒ₁ ≡ Aₒ₁')
  (eqₒ₂ : Aₒ₂ ≡ Aₒ₂')
  (cᵢ≡cᵢ' : PathP (λ i → PRel (eqᵢ₁ i) (eqᵢ₂ i) ℓcᵢ) cᵢ cᵢ')
  (cₒ≡cₒ' : PathP (λ i → PRel (eqₒ₁ i) (eqₒ₂ i) ℓcₒ) cₒ cₒ') where
  
  transport-sq : PSq cᵢ cₒ f g → PSq cᵢ' cₒ' {!!} {!!}
  transport-sq = {!!}

  --c  .R x y →
  --c' .R (transport (cong fst eq₁) x) (transport (cong fst eq₂) y)
-}
