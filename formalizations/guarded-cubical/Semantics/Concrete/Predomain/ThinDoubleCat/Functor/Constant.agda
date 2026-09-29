{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Constant (k : Clock) where

open import Cubical.Foundations.Prelude

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Base k

private
  variable
    ℓ : Level
    ℓobC ℓvC ℓhC ℓsqC ℓ≈C : Level
    ℓobD ℓvD ℓhD ℓsqD ℓ≈D : Level
 
open ThinDoubleCat
open FunctorBase
open FunctorWithLaxity

module _
  {C : ThinDoubleCat ℓobC ℓvC ℓhC ℓsqC ℓ≈C}
  {D : ThinDoubleCat ℓobD ℓvD ℓhD ℓsqD ℓ≈D} where

  private
    module D = ThinDoubleCat D

  module _ (d : D.ob) where
    KBase : FunctorBase C D
    KBase .F-ob _ = d
    KBase .F-homV _ = D.idV
    KBase .F-idV = refl
    KBase .F-seqV _ _ = sym (D.idLV D.idV)
    KBase .F-homH _ = D.idH
    KBase .F-idH = refl
    KBase .F-sq _ = D.idSqV D.idH -- could define this as D.idSqH D.idV
    KBase .F-bisim _ _ _ = D.Bisim.is-refl d d D.idV
    

    K : {l : Laxity} → FunctorWithLaxity l C D
    K .base = KBase
    K {strict} .F-seqH r s = lift (D.idLH D.idH)
    K {lax} .F-seqH r s =
      lift (subst
        (λ r → D.sq r D.idH D.idV D.idV)
        (sym (D.idLH D.idH))
        (D.idSqV D.idH))
    K {oplax} .F-seqH r s =
      lift (subst
        (λ r → D.sq D.idH r D.idV D.idV)
        (sym (D.idLH D.idH))
        (D.idSqV D.idH))
