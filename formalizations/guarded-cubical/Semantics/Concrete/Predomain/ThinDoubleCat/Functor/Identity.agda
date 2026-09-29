{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Identity (k : Clock) where

open import Cubical.Foundations.Prelude

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Base k


private
  variable
    ℓ : Level
    ℓob ℓv ℓh ℓsq ℓ≈ : Level
 
open ThinDoubleCat
open FunctorBase
open FunctorWithLaxity
open Functor

module _ (C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈) where

  private
    module C = ThinDoubleCat C

  IdBase : FunctorBase C C
  IdBase .F-ob x = x
  IdBase .F-homV f = f
  IdBase .F-idV = refl
  IdBase .F-seqV f g = refl
  IdBase .F-homH r = r
  IdBase .F-idH = refl
  IdBase .F-sq sq = sq
  IdBase .F-bisim f g f≈g = f≈g

  IdF : {l : Laxity} → FunctorWithLaxity l C C
  IdF .base = IdBase
  IdF {strict} .F-seqH r r' = lift refl
  IdF {lax}    .F-seqH r r' = lift (C.idSqV (r C.⋆H r'))
  IdF {oplax}  .F-seqH r r' = lift (C.idSqV (r C.⋆H r'))

{-
  IdStr : FunctorWithLaxity strict C C
  IdStr .base = IdBase
  IdStr .F-seqH r r' = lift refl

  IdLax : FunctorWithLaxity lax C C
  IdLax .base = IdBase
  IdLax .F-seqH r r' = lift (C.idSqV (r C.⋆H r'))

  IdOpl : FunctorWithLaxity oplax C C
  IdOpl .base = IdBase
  IdOpl .F-seqH r r' = lift (C.idSqV (r C.⋆H r'))

  IdF : {l : Laxity} → FunctorWithLaxity l C C
  IdF {strict} = IdStr
  IdF {lax} = IdLax
  IdF {oplax} = IdOpl


Id-obj : ∀ {C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈} (l : Laxity) (x : C .ob)
  → IdF C {l} .base .F-ob x ≡ x
Id-obj strict x = refl
Id-obj lax x = refl
Id-obj oplax x = refl
-}



𝟙⟨_⟩ : ∀ (C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈) {l : Laxity} → FunctorWithLaxity l C C
𝟙⟨_⟩ = IdF




{-

  IdF : Functor C C
  IdF .laxity = strict
  IdF .F .base .F-ob x = x
  IdF .F .base .F-homV f = f
  IdF .F .base .F-idV = refl
  IdF .F .base .F-seqV f g = refl
  IdF .F .base .F-homH c = c
  IdF .F .base .F-idH = refl
  IdF .F .base .F-sq sq = sq
  IdF .F .base .F-bisim f g f≈g = f≈g
  IdF .F .F-seqH c c' = lift refl -- C.idSqV (c C.⋆H c')


𝟙⟨_⟩ : ∀ (C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈) → Functor C C
𝟙⟨_⟩ = IdF

-}
