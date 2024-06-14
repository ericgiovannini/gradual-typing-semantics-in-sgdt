{-# OPTIONS --guarded --rewriting #-}


-- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.DoublePoset.PBSquare where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)

open import Cubical.Relation.Binary
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (elim)
open import Cubical.Data.Empty hiding (elim)
open import Cubical.HITs.PropositionalTruncation renaming (map to PTmap)


open import Common.Common

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Convenience
open import Semantics.Concrete.DoublePoset.Constructions
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.DblPosetCombinators

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


PBSq :
  {Aᵢ  : PosetBisim ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ}
  {Aᵢ' : PosetBisim ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
  {Aₒ  : PosetBisim ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ} 
  {Aₒ' : PosetBisim ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'} →
  (cᵢ  : PBRel Aᵢ Aᵢ' ℓcᵢ) →
  (cₒ  : PBRel Aₒ Aₒ' ℓcₒ) →
  (f   : PBMor Aᵢ  Aₒ) →
  (g   : PBMor Aᵢ' Aₒ') →
  Type (ℓ-max (ℓ-max ℓAᵢ ℓAᵢ') (ℓ-max ℓcᵢ ℓcₒ))
PBSq cᵢ cₒ f g = TwoCell (cᵢ .PBRel.R) (cₒ .PBRel.R) (f .PBMor.f) (g .PBMor.f)


--          cᵢ
--     Aᵢ o---* Aᵢ'
--     |         |
--   f |         | g 
--     v         v
--     Aₒ o---* Aₒ'
--          cₒ





-- "Horizontal" identity squares.

-- The existence of these squares relies on the fact that f is
-- *montone*.

IdSqH : {ℓo : Level} →
  {Aᵢ : PosetBisim ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ}
  {Aₒ : PosetBisim ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} →
  (f : PBMor Aᵢ Aₒ) →
  PBSq (idRel {ℓo = ℓo} Aᵢ) (idRel {ℓo = ℓo} Aₒ) f f
IdSqH f x₁ x₂ x₁≤x₂ =
  lift (f .PBMor.isMon (lower x₁≤x₂))

-- "Vertical" identity squares.

IdSqV : {ℓo : Level} →
  {A : PosetBisim ℓA ℓ≤A ℓ≈A}
  {A' : PosetBisim ℓA' ℓ≤A' ℓ≈A'}
  (c : PBRel A A' ℓc) →
  PBSq c c Id Id
IdSqV c x y xRy = xRy
  


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


compSqV :
  {A₁  : PosetBisim ℓA₁  ℓ≤A₁  ℓ≈A₁ }
  {A₁' : PosetBisim ℓA₁' ℓ≤A₁' ℓ≈A₁'}
  {A₂  : PosetBisim ℓA₂  ℓ≤A₂  ℓ≈A₂ }
  {A₂' : PosetBisim ℓA₂' ℓ≤A₂' ℓ≈A₂'}
  {A₃  : PosetBisim ℓA₃  ℓ≤A₃  ℓ≈A₃ }
  {A₃' : PosetBisim ℓA₃' ℓ≤A₃' ℓ≈A₃'}
  {c₁  : PBRel A₁ A₁' ℓc₁}
  {c₂  : PBRel A₂ A₂' ℓc₂}
  {c₃  : PBRel A₃ A₃' ℓc₃}
  {f₁  : PBMor A₁  A₂ }
  {g₁  : PBMor A₁' A₂'}
  {f₂  : PBMor A₂  A₃ }
  {g₂  : PBMor A₂' A₃'} →
  PBSq c₁ c₂ f₁ g₁ →
  PBSq c₂ c₃ f₂ g₂ →
  PBSq c₁ c₃ (f₂ ∘p f₁) (g₂ ∘p g₁)
compSqV α₁ α₂ x y xRy = α₂ _ _ (α₁ _ _ xRy)



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

compSqH :
  {Aᵢ₁ : PosetBisim ℓAᵢ₁ ℓ≤Aᵢ₁ ℓ≈Aᵢ₁}
  {Aᵢ₂ : PosetBisim ℓAᵢ₂ ℓ≤Aᵢ₂ ℓ≈Aᵢ₂}
  {Aᵢ₃ : PosetBisim ℓAᵢ₃ ℓ≤Aᵢ₃ ℓ≈Aᵢ₃}
  {Aₒ₁ : PosetBisim ℓAₒ₁ ℓ≤Aₒ₁ ℓ≈Aₒ₁}
  {Aₒ₂ : PosetBisim ℓAₒ₂ ℓ≤Aₒ₂ ℓ≈Aₒ₂}
  {Aₒ₃ : PosetBisim ℓAₒ₃ ℓ≤Aₒ₃ ℓ≈Aₒ₃}
  {cᵢ₁ : PBRel Aᵢ₁ Aᵢ₂ ℓcᵢ₁}
  {cᵢ₂ : PBRel Aᵢ₂ Aᵢ₃ ℓcᵢ₂}
  {cₒ₁ : PBRel Aₒ₁ Aₒ₂ ℓcₒ₁}
  {cₒ₂ : PBRel Aₒ₂ Aₒ₃ ℓcₒ₂}
  {f : PBMor Aᵢ₁ Aₒ₁}
  {g : PBMor Aᵢ₂ Aₒ₂}
  {h : PBMor Aᵢ₃ Aₒ₃} →
  PBSq cᵢ₁ cₒ₁  f g →
  PBSq cᵢ₂ cₒ₂ g h →
  PBSq (cᵢ₁ ⊙ cᵢ₂) (cₒ₁ ⊙ cₒ₂) f h
compSqH {g = g} α β x z xcᵢ₁cᵢ₂z =
  PTmap
    (λ (y , xcᵢ₁y , ycᵢ₂z) →
      (g $ y)
      , α _ _ xcᵢ₁y  -- NTS (f x) cₒ₁ (g y)
      , β _ _ ycᵢ₂z) -- NTS (g y) cₒ₂ (h z)
    xcᵢ₁cᵢ₂z



-- Action of the functor F on squares




-- Action of the exponential ==> on squares

module _
  {Aᵢ₁  : PosetBisim ℓAᵢ₁  ℓ≤Aᵢ₁  ℓ≈Aᵢ₁}
  {Aᵢ₁' : PosetBisim ℓAᵢ₁' ℓ≤Aᵢ₁' ℓ≈Aᵢ₁'}
  {Aₒ₁  : PosetBisim ℓAₒ₁  ℓ≤Aₒ₁  ℓ≈Aₒ₁} 
  {Aₒ₁' : PosetBisim ℓAₒ₁' ℓ≤Aₒ₁' ℓ≈Aₒ₁'}
  {Aᵢ₂  : PosetBisim ℓAᵢ₂  ℓ≤Aᵢ₂  ℓ≈Aᵢ₂}
  {Aᵢ₂' : PosetBisim ℓAᵢ₂' ℓ≤Aᵢ₂' ℓ≈Aᵢ₂'}
  {Aₒ₂  : PosetBisim ℓAₒ₂  ℓ≤Aₒ₂  ℓ≈Aₒ₂} 
  {Aₒ₂' : PosetBisim ℓAₒ₂' ℓ≤Aₒ₂' ℓ≈Aₒ₂'}
  {cᵢ₁  : PBRel Aᵢ₁ Aᵢ₁' ℓcᵢ₁}
  {cₒ₁  : PBRel Aₒ₁ Aₒ₁' ℓcₒ₁}
  {f₁   : PBMor Aₒ₁  Aᵢ₁}   -- Notice the flip in direction!
  {g₁   : PBMor Aₒ₁' Aᵢ₁'}  -- Notice the flip in direction!
  {cᵢ₂  : PBRel Aᵢ₂ Aᵢ₂' ℓcᵢ₂}
  {cₒ₂  : PBRel Aₒ₂ Aₒ₂' ℓcₒ₂}
  {f₂   : PBMor Aᵢ₂  Aₒ₂} 
  {g₂   : PBMor Aᵢ₂' Aₒ₂'}

  where

--          cₒ₁                    cᵢ₂
--     Aₒ₁ o---* Aₒ₁'         Aᵢ₂ o---* Aᵢ₂'
--      |         |            |         |
--   f₁ |    α    | g₁      f₂ |    β    | g₂ 
--      v         v            v         v
--     Aᵢ₁ o---* Aᵢ₁'         Aₒ₂ o---* Aₒ₂'
--          cᵢ₁                    cₒ₂

  _==>psq_ : PBSq cₒ₁ cᵢ₁ f₁ g₁ → PBSq cᵢ₂ cₒ₂ f₂ g₂ →
    PBSq (cᵢ₁ ==>pbmonrel cᵢ₂) (cₒ₁ ==>pbmonrel cₒ₂) (f₁ ~-> f₂) (g₁ ~-> g₂)
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
