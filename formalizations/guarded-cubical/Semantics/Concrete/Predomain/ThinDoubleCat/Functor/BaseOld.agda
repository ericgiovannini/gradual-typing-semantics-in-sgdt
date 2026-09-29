{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Base (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.HLevels

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k

private
  variable
    ℓ : Level
    ℓob ℓv ℓh ℓsq ℓ≈ : Level
    ℓob' ℓv' ℓh' ℓsq' ℓ≈' : Level
open ThinDoubleCat

module _
  (C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈)
  (D : ThinDoubleCat ℓob' ℓv' ℓh' ℓsq' ℓ≈') where

  private
    module C = ThinDoubleCat C
    module D = ThinDoubleCat D

  record ThinDoubleFunctor
    : Type (ℓ-max
      (ℓ-max (ℓ-max (ℓ-max ℓob ℓob') (ℓ-max ℓv ℓv')) (ℓ-max ℓh ℓh'))
      (ℓ-max (ℓ-max ℓsq ℓsq') (ℓ-max ℓ≈ ℓ≈'))) where
    field
      F-ob : C.ob → D.ob

      F-homV : {x y : C.ob}
        → C.vhom[ x , y ] → D.vhom[ (F-ob x) , (F-ob y) ]

      F-idV : {x : C.ob} -- rename to F-homV-id?
        → F-homV (C.idV {x}) ≡ D.idV {F-ob x}

      F-seqV : {x₁ x₂ x₃ : C.ob} -- rename to F-homV-comp?
        → (f : C.vhom[ x₁ , x₂ ])
        → (g : C.vhom[ x₂ ,  x₃ ])
        → (F-homV (f C.⋆V g) ≡ (F-homV f) D.⋆V (F-homV g))

      F-homH : ∀ {x x' : C.ob}
        → C.hhom[ x ,  x' ] → D.hhom[ (F-ob x) , (F-ob x') ]

      F-idH : {x : C.ob} -- rename to F-homH-id?
        → F-homH (C.idH {x}) ≡ D.idH {F-ob x}

      F-seqH : {x₁ x₂ x₃ : C.ob} -- rename to F-homH-comp?
        → (c : C.hhom[ x₁ , x₂ ]) (c' : C.hhom[ x₂ , x₃ ])
        → D.sq (F-homH c D.⋆H F-homH c') (F-homH (c C.⋆H c'))
               (D.idV {F-ob x₁}) (D.idV {F-ob x₃})
      
      F-sq : ∀ {xᵢ yᵢ xₒ yₒ : C.ob}
        → {cᵢ : C.hhom[ xᵢ , yᵢ ]}
        → {cₒ : C.hhom[ xₒ , yₒ ]}
        → {f : C.vhom[ xᵢ , xₒ ]}
        → {g : C.vhom[ yᵢ , yₒ ]}
        → C.sq cᵢ cₒ f g
        → D.sq (F-homH cᵢ) (F-homH cₒ) (F-homV f) (F-homV g)

      -- The action on vertical morphisms preserves bisimilarity
      F-bisim : ∀ {x y : C.ob}
        → (f g : C.vhom[ x , y ])
        → f C.≈vhom g
        → (F-homV f) D.≈vhom (F-homV g)
        


 -- → hhom[ xᵢ , yᵢ ] → hhom[ xₒ , yₒ ]
 -- → vhom[ xᵢ , xₒ ] → vhom[ yᵢ , yₒ ]


module _
  {C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈}
  {D : ThinDoubleCat ℓob' ℓv' ℓh' ℓsq' ℓ≈'}
  where

  open ThinDoubleFunctor

  -- Helpful notation

  -- action on objects
  infix 30 _⟅_⟆
  _⟅_⟆ : (F : ThinDoubleFunctor C D)
       → C .ob
       → D .ob
  _⟅_⟆ = F-ob

  -- action on vertical morphisms
  infix 30 _⟪_⟫v -- same infix level as on objects since these will never be used in the same context
  _⟪_⟫v : (F : ThinDoubleFunctor C D)
       → ∀ {x y}
       → C [ x , y ]v
       → D [(F ⟅ x ⟆) , (F ⟅ y ⟆)]v
  _⟪_⟫v = F-homV

  -- action on horizontal morphisms
  infix 30 _⟪_⟫h -- same infix level as on objects since these will never be used in the same context
  _⟪_⟫h : (F : ThinDoubleFunctor C D)
       → ∀ {x y}
       → C [ x , y ]h
       → D [(F ⟅ x ⟆) , (F ⟅ y ⟆)]h
  _⟪_⟫h = F-homH


  -- action on squares
  infix 30 _⟪_⟫sq -- same infix level as on objects since these will never be used in the same context
  _⟪_⟫sq : (F : ThinDoubleFunctor C D)
     → {xᵢ yᵢ xₒ yₒ : C .ob}
       {cᵢ : C [ xᵢ , yᵢ ]h}
       {cₒ : C [ xₒ , yₒ ]h}
       {f : C [ xᵢ , xₒ ]v}
       {g : C [ yᵢ , yₒ ]v}
       → C [ cᵢ , cₒ , f , g ]sq
       → D [ (F ⟪ cᵢ ⟫h) , (F ⟪ cₒ ⟫h) , (F ⟪ f ⟫v) , (F ⟪ g ⟫v) ]sq
  _⟪_⟫sq = F-sq
