{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.Polymorphic (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.HLevels
import Cubical.Data.Sigma as Data
open import Cubical.Foundations.Structure
open import Cubical.Data.List

open import Semantics.Concrete.Predomain.Base


private
  variable
    ℓ : Level
    -- ℓh  ℓ≤  ℓ≈ ℓR  ℓsq : Level


-- Thin double categories enriched in the category of reflexive,
-- symmetric relations.


-- hhom[ x , y , ℓc ]

-- product category 𝒞 × Level
-- objects: C.ob × Level.ob
-- morphism between (x , ℓ) → (x' , ℓ')

--record ThinDoubleCat : Typeω where
record ThinDoubleCat (ℓob ℓv ℓh ℓsq ℓ≈ : Level)
  : Type (ℓ-suc (ℓ-max (ℓ-max (ℓ-max ℓob ℓv) ℓh) (ℓ-max ℓsq ℓ≈))) where

  field
    --ℓob ℓv ℓh ℓsq ℓ≈ : Level
    
    ob : Type ℓob

    vhom[_,_] : ob → ob → Type ℓv

    hhom[_,_] : ob → ob → Type ℓh

    sq : {xᵢ xₒ yᵢ yₒ : ob}
      → hhom[ xᵢ , yᵢ ] → hhom[ xₒ , yₒ ]
      → vhom[ xᵢ , xₒ ] → vhom[ yᵢ , yₒ ]
      → Type ℓsq

    -- vertical id, composition, and laws
    idV : (x : ob) → vhom[ x , x ]
    _⋆V_ : {x y z : ob} → vhom[ x , y ] → vhom[ y , z ] → vhom[ x , z ]


    idLV : {x y : ob} → (f : vhom[ x , y ]) → (idV x) ⋆V f ≡ f
    idRV : {x y : ob} → (f : vhom[ x , y ]) → f ⋆V (idV y) ≡ f
    assocV : {w x y z : ob} →
      (f : vhom[ w , x ]) (g : vhom[ x , y ]) (h : vhom[ y , z ])
      → (f ⋆V g) ⋆V h ≡ f ⋆V (g ⋆V h)
    

    -- horizontal id, composition and laws
    idH : (x : ob) → hhom[ x , x ]
    _⋆H_ : {x y z : ob} → hhom[ x , y ] → hhom[ y , z ] → hhom[ x , z ]


    -- the identity laws hold up to equality
    idLH : {x y : ob} → (c : hhom[ x , y ]) → (idH x) ⋆H c ≡ c
    idRH : {x y : ob} → (c : hhom[ x , y ]) → c ⋆H (idH y) ≡ c


    -- associativity holds up to equality
    assocH : {w x y z : ob} →
      (c₁ : hhom[ w , x ]) (c₂ : hhom[ x , y ]) (c₃ : hhom[ y , z ])
      → (c₁ ⋆H c₂) ⋆H c₃ ≡ c₁ ⋆H (c₂ ⋆H c₃)
      

    -- vertical and horizontal identity squares
    idSqV : {x y : ob} → (c : hhom[ x , y ])
      → sq c c (idV x) (idV y)
      
    idSqH : {xᵢ xₒ : ob} → (f : vhom[ xᵢ , xₒ ])
      → sq (idH xᵢ) (idH xₒ) f f


    -- horizontal and vertical composition of squares
    CompSqV :
      {A₁ A₁' A₂ A₂' A₃ A₃' : ob}
      {c₁  : hhom[ A₁ , A₁' ]}
      {c₂  : hhom[ A₂ , A₂' ]}
      {c₃  : hhom[ A₃ , A₃' ]}
      {f₁  : vhom[ A₁ , A₂ ]}
      {g₁  : vhom[ A₁' , A₂' ]}
      {f₂  : vhom[ A₂ , A₃ ]}
      {g₂  : vhom[ A₂' , A₃' ]} →
      sq c₁ c₂ f₁ g₁ →
      sq c₂ c₃ f₂ g₂ →
      sq c₁ c₃ (f₁ ⋆V f₂) (g₁ ⋆V g₂)


    CompSqH :
      {Aᵢ₁  Aᵢ₂  Aᵢ₃  Aₒ₁  Aₒ₂  Aₒ₃ : ob}
      {cᵢ₁ : hhom[ Aᵢ₁ , Aᵢ₂ ]}
      {cᵢ₂ : hhom[ Aᵢ₂ , Aᵢ₃ ]}
      {cₒ₁ : hhom[ Aₒ₁ , Aₒ₂ ]}
      {cₒ₂ : hhom[ Aₒ₂ , Aₒ₃ ]}
      {f : vhom[ Aᵢ₁ ,  Aₒ₁ ]}
      {g : vhom[ Aᵢ₂ , Aₒ₂ ]}
      {h : vhom[ Aᵢ₃ , Aₒ₃ ]} →
      sq cᵢ₁ cₒ₁ f g →
      sq cᵢ₂ cₒ₂ g h →
      sq (cᵢ₁ ⋆H cᵢ₂) (cₒ₁ ⋆H cₒ₂) f h


    -- vertical and horizontal morphisms form a Set
    isSetVMor : ∀ {x y : ob} → isSet (vhom[ x , y ])
    isSetHMor : ∀ {x y : ob} → isSet (hhom[ x , y ])


    -- thin condition (squares are Prop-valued)
    isPropSq : {xᵢ xₒ yᵢ yₒ : ob}
        {cᵢ : hhom[ xᵢ , yᵢ ]} {cₒ : hhom[ xₒ , yₒ ]}
      → (f : vhom[ xᵢ , xₒ ]) (g : vhom[ yᵢ , yₒ ])
      → isProp (sq cᵢ cₒ f g)


    -- TODO: horizontal morphisms are Prop-valued? Can't state this at
    -- this level.
    

    -- vertical enrichment in RefSymSet: the category defined as follows:
    --   - Objects are sets equipped with a reflexive, symmetric relation ≈
    --   - Morphisms are functions that preserve ≈
    
    _≈vhom_ : {xᵢ xₒ : ob} → vhom[ xᵢ , xₒ ] → vhom[ xᵢ , xₒ ] → Type ℓ≈

    isBisim≈ : {xᵢ xₒ : ob} → IsBisim (_≈vhom_ {xᵢ} {xₒ})

    comp≈ : {x y z : ob} (f f' : vhom[ x , y ]) (g g' : vhom[ y , z ])
      → f ≈vhom f' → g ≈vhom g' → (f ⋆V g) ≈vhom (f' ⋆V g')

    -- in general, for a category enriched over V, we have
    --   ∘ : Hom[x,y] ⊗ Hom[y,z] → Hom[x,z]  (morphism in V)
    --
    -- When V = RefSymSet, the above simplifies to the condition in
    -- the record.
