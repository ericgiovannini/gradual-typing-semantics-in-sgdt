{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.LeftAdjointTo (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Base k

open import Semantics.Concrete.Predomain.ThinDoubleCat.Adjoint k

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

  
  record LeftAdjointTo (G : ThinDoubleFunctor D C)
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓobC ℓvC) ℓhC) ℓsqC) ℓ≈C) ℓobD) ℓvD) ℓhD) ℓsqD) ℓ≈D)
    where
    
    private
      module G = ThinDoubleFunctor G
      G-ob = G .ThinDoubleFunctor.F-ob
      G-homH = G .ThinDoubleFunctor.F-homH

    field
      -- action on objects and horizontal morphisms
      F-ob : C.ob → D.ob
      F-homH : ∀ {c c' : C.ob}
        → C [ c ,  c' ]h → D [ (F-ob c) , (F-ob c') ]h

      -- universal arrow
      η-ob : (c : C.ob) → C [ c , G-ob (F-ob c) ]v

      -- universal square
      η-homH : ∀ {c c' : C.ob} (r : C.hhom[ c , c' ]) →
        C [ r , G-homH (F-homH r) , (η-ob c) , (η-ob c') ]sq

    flat : (c : C.ob) (d : D.ob)
      → D [ F-ob c , d ]v
      → C [ c , G-ob d ]v
    flat c d h = (G ⟪ h ⟫v) C.∘V (η-ob c)

    field

      -- preservation of bisimilarity by `flat`
      flat-pres≈ : ∀ {c d} → (h h' : D [ F-ob c , d ]v)
        → h D.≈vhom h'
        → (flat c d h) C.≈vhom (flat c d h)

      flat-pres≈inv : ∀ {c d} → (h h' : D [ F-ob c , d ]v)
        → (flat c d h) C.≈vhom (flat c d h)
        → h D.≈vhom h'

      -- universality of η-ob (existence and uniqueness)
      univ : (c : C.ob) (d : D.ob) → isEquiv (flat c d)

    -- existence part of universality
    sharp : (c : C.ob) (d : D.ob)
      → C [ c , G-ob d ]v
      → D [ F-ob c , d ]v
    sharp c d f = invIsEq (univ c d) f --invEquiv {!univ c d!} .fst {!!}

    sharp-pres≈ : ∀ {c d} → (f f' : C [ c , G-ob d ]v)
      → f C.≈vhom f'
      → (sharp c d f) D.≈vhom (sharp c d f')
    sharp-pres≈ f f' f≈f' = {!!}


    flatSq : {c c' : C.ob} {d d' : D.ob}
      → (r : C [ c , c' ]h) (s : D [ d , d' ]h)
      → (g  : D [ F-ob c  , d  ]v)
      → (g' : D [ F-ob c' , d' ]v)
      → D [ F-homH r , s , g , g' ]sq
      → C [ r , G-homH s , (flat _ _ g) , (flat _ _ g') ]sq
    flatSq r s g g' sq = (η-homH r) C.⋆SqV (G ⟪ sq ⟫sq)

    -- Note: the uniqueness part of universality for η-homH is
    -- automatic because the squares are Prop-valued
    field
      univ-sq : {c c' : C.ob} {d d' : D.ob}
        → (r : C [ c , c' ]h) (s : D [ d , d' ]h)
        → (f  : C [ c  , G-ob d  ]v)
        → (f' : C [ c' , G-ob d' ]v)
        → C [ r , G-homH s , f , f' ]sq
        → D [ F-homH r , s , sharp _ _ f , sharp _ _ f' ]sq

    univ-sq' : {c c' : C.ob} {d d' : D.ob}
      → (r : C [ c , c' ]h) (s : D [ d , d' ]h)
      → (g  : D [ F-ob c  , d  ]v)
      → (g' : D [ F-ob c' , d' ]v)
      → C [ r , G-homH s , (flat _ _ g) , (flat _ _ g') ]sq
      → D [ F-homH r , s , g , g' ]sq
    univ-sq' r s g g' sq = subst2
      (λ q q' → D [ F-homH r , s , q , q' ]sq)
      (retIsEq (univ _ _) g)
      (retIsEq (univ _ _) g')
      (univ-sq r s (flat _ _ g) (flat _ _ g') sq)


  -- TODO: deriving naturality of η
  -- TODO: deriving F on morphisms and functoriality of F
  -- TODO: deriving the counit ε and the triangle identities


  module _ {G : ThinDoubleFunctor D C} (adj : LeftAdjointTo G) where

    open ThinDoubleFunctor
    open UnitCounit
    open TriangleIdentities
    open _⊣_

    private
      module G = ThinDoubleFunctor G
      module adj = LeftAdjointTo adj

    toFunctor : ThinDoubleFunctor C D
    toFunctor .F-ob = adj.F-ob
    toFunctor .F-homV {x = x} {y = y} f =
      adj.sharp x (adj.F-ob y) (f C.⋆V adj.η-ob y) -- C.vhom[ x , G.F-ob (adj.F-ob y) ]
    toFunctor .F-idV = {!!}
    toFunctor .F-seqV = {!!}
    toFunctor .F-homH = adj.F-homH
    toFunctor .F-idH = {!!}
    toFunctor .F-seqH = {!!}
    toFunctor .F-sq = {!!}
    toFunctor .F-bisim = {!!}

    toAdjunction : toFunctor ⊣ G
    toAdjunction = {!!}
