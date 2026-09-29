{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.RightAdjointTo (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Base k

private
  variable
    ℓ : Level
    ℓobC ℓvC ℓhC ℓsqC ℓ≈C : Level
    ℓobD ℓvD ℓhD ℓsqD ℓ≈D : Level

module _
  {C : ThinDoubleCat ℓobC ℓvC ℓhC ℓsqC ℓ≈C}
  {D : ThinDoubleCat ℓobD ℓvD ℓhD ℓsqD ℓ≈D}
  where

  private
    module C = ThinDoubleCat C
    module D = ThinDoubleCat D


  record RightAdjointTo (F : ThinDoubleFunctor C D)
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓobC ℓvC) ℓhC) ℓsqC) ℓ≈C) ℓobD) ℓvD) ℓhD) ℓsqD) ℓ≈D)
    where
    
    private
      module F = ThinDoubleFunctor F
      F-ob = F .ThinDoubleFunctor.F-ob
      F-homH = F .ThinDoubleFunctor.F-homH

    field
      -- action on objects and horizontal morphisms
      G-ob : D.ob → C.ob
      G-homH : ∀ {d d' : D.ob}
        → D [ d ,  d' ]h → C [ (G-ob d) , (G-ob d') ]h

      -- universal arrow
      ε-ob : (d : D.ob) → D [ F-ob (G-ob d) , d ]v

      -- universal square
      ε-homH : ∀ {d d' : D.ob} (s : D.hhom[ d , d' ]) →
        D [ F-homH (G-homH s) , s , (ε-ob d) , (ε-ob d') ]sq

    sharp : (c : C.ob) (d : D.ob)
      → C [ c , G-ob d ]v
      → D [ F-ob c , d ]v
    sharp c d h = (ε-ob d) D.∘V (F ⟪ h ⟫v)


    field

      -- preservation of bisimilarity by `sharp`
      sharp-pres≈ : ∀ {c d} → (h h' : C [ c , G-ob d ]v)
        → h C.≈vhom h'
        → (sharp c d h) D.≈vhom (sharp c d h)

      sharp-pres≈inv : ∀ {c d} → (h h' : C [ c , G-ob d ]v)
        → (sharp c d h) D.≈vhom (sharp c d h)
        → h C.≈vhom h'
        
      -- universality of ε-ob (existence and uniqueness)
      univ : (c : C.ob) (d : D.ob) → isEquiv (sharp c d)

    -- existence part of universality
    flat : (c : C.ob) (d : D.ob)
      → D [ F-ob c , d ]v
      → C [ c , G-ob d ]v
    flat c d f = invIsEq (univ c d) f

    sharpSq : {c c' : C.ob} {d d' : D.ob}
      → (r : C [ c , c' ]h) (s : D [ d , d' ]h)
      → (g  : C [ c  , G-ob d  ]v)
      → (g' : C [ c' , G-ob d' ]v)
      → C [ r , G-homH s , g , g' ]sq
      → D [ F-homH r , s , (sharp _ _ g) , (sharp _ _ g') ]sq
    sharpSq r s g g' sq = (F ⟪ sq ⟫sq) D.⋆SqV (ε-homH s)


    -- Note: the uniqueness part of universality for ε-homH is
    -- automatic because the squares are Prop-valued
    field
      univ-sq : {c c' : C.ob} {d d' : D.ob}
        → (r : C [ c , c' ]h) (s : D [ d , d' ]h)
        → (f  : D [ F-ob c  , d  ]v)
        → (f' : D [ F-ob c' , d' ]v)
        → D [ F-homH r , s , f , f' ]sq
        → C [ r , G-homH s , flat _ _ f , flat _ _ f' ]sq



  -- TODO: deriving naturality of ε
  -- TODO: deriving G on morphisms and functoriality of G
  -- TODO: deriving the unit η and the triangle identities
