{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.NatTrans.Base (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.HLevels

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Isomorphism k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Base k

--open import Cubical.Categories.NaturalTransformation.Base

private
  variable
    ℓ : Level
    ℓob ℓv ℓh ℓsq ℓ≈ : Level
    ℓob' ℓv' ℓh' ℓsq' ℓ≈' : Level
    l : Laxity

open ThinDoubleCat
open FunctorWithLaxity

module _
  {C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈}
  {D : ThinDoubleCat ℓob' ℓv' ℓh' ℓsq' ℓ≈'}
  (F G : FunctorWithLaxity l C D)
  where

  private
    module C = ThinDoubleCat C
    module D = ThinDoubleCat D
    module F = FunctorWithLaxity F
    module G = FunctorWithLaxity G

  record ThinDoubleNatTrans :
    Type (ℓ-max (ℓ-max (ℓ-max ℓob (ℓ-max ℓv ℓv')) ℓh) ℓsq') where
    
    field

      -- Objects map to vertical morphisms
      N-ob : ∀ (x : C.ob) → D.vhom[ F.F-ob x , G.F-ob x ]

      -- Naturality with respect to vertical morphisms
      N-nat : ∀ {xᵢ xₒ : C.ob} → (f : C.vhom[ xᵢ , xₒ ])
        → ((F.F-homV f) D.⋆V (N-ob xₒ)) ≡ ((N-ob xᵢ) D.⋆V (G.F-homV f))

      -- Horizontal morphisms map to squares
      N-rel : ∀ {x x' : C.ob} (c : C.hhom[ x , x' ]) →
        D.sq (F.F-homH c) (G.F-homH c) (N-ob x) (N-ob x')

      -- Note: naturality with respect to *squares* is automatic
      -- because squares are Prop-valued.


module _
  {C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈}
  {D : ThinDoubleCat ℓob' ℓv' ℓh' ℓsq' ℓ≈'}
  where

  open ThinDoubleNatTrans

  infix 10 _⇒_
  _⇒_ : FunctorWithLaxity l C D
      → FunctorWithLaxity l C D
      → Type (ℓ-max (ℓ-max (ℓ-max ℓob (ℓ-max ℓv ℓv')) ℓh) ℓsq')
  _⇒_ = ThinDoubleNatTrans


  -- component of a natural transformation
  infix 30 _⟦_⟧
  _⟦_⟧ : ∀ {F G : FunctorWithLaxity l C D} → F ⇒ G
    → (x : C .ob) → D [ F .F-ob x , G .F-ob x ]v
  _⟦_⟧ = N-ob



---- Natural isomorphisms ----

module _
  {C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈}
  {D : ThinDoubleCat ℓob' ℓv' ℓh' ℓsq' ℓ≈'}
  (F G : FunctorWithLaxity l C D)
  where

  private
    module C = ThinDoubleCat C
    module D = ThinDoubleCat D
    module F = FunctorWithLaxity F
    module G = FunctorWithLaxity G

  record NatIso
    : Type (ℓ-max (ℓ-max (ℓ-max ℓob (ℓ-max ℓv ℓv')) ℓh) ℓsq') where

    field
      trans : ThinDoubleNatTrans F G
    open ThinDoubleNatTrans trans

    field
      nIsoV : ∀ (x : C.ob)
        → isIsoV D (N-ob x)
      nIsoSq : ∀ {x x' : C.ob} (r : C.hhom[ x , x' ])
        → isIsoSq D (nIsoV x) (nIsoV x') (N-rel r)

    open isIsoV
