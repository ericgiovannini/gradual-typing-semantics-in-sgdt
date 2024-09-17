{-# OPTIONS --safe #-}
module Cubical.Algebra.Monoid.Displayed.Instances.Reindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma as Sigma hiding (_×_)

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.Displayed as Disp
open import Cubical.Algebra.Monoid.Instances.CartesianProduct
open import Cubical.Algebra.Semigroup.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

module _ {M : Monoid ℓ}{N : Monoid ℓ'}(ϕ : MonoidHom M N)
  (Mᴰ : Monoidᴰ N ℓᴰ) where
  private
    module Mᴰ = Monoidᴰ Mᴰ
    module N = MonoidStr (N .snd)
    module M = MonoidStr (M .snd)
    module ϕ = IsMonoidHom (ϕ .snd)

  Reindex : Monoidᴰ M ℓᴰ
  Reindex .Monoidᴰ.eltᴰ x = Mᴰ.eltᴰ (ϕ .fst x)
  Reindex .Monoidᴰ.εᴰ = Mᴰ.reind (sym ϕ.presε) Mᴰ.εᴰ
  Reindex .Monoidᴰ._·ᴰ_ xᴰ yᴰ = Mᴰ.reind (sym (ϕ.pres· _ _)) (xᴰ Mᴰ.·ᴰ yᴰ)
  Reindex .Monoidᴰ.·IdLᴰ xᴰ = Mᴰ.rectify (
    symP (Mᴰ.reind-filler _ _)
    Mᴰ.∙ᴰ (symP (Mᴰ.reind-filler _ _) Mᴰ.·ᴰcong refl {x = xᴰ})
    Mᴰ.∙ᴰ Mᴰ.·IdLᴰ xᴰ)
  Reindex .Monoidᴰ.·IdRᴰ xᴰ = Mᴰ.rectify (
    symP (Mᴰ.reind-filler _ _)
    Mᴰ.∙ᴰ (refl {x = xᴰ} Mᴰ.·ᴰcong symP (Mᴰ.reind-filler _ _))
    Mᴰ.∙ᴰ Mᴰ.·IdRᴰ xᴰ)
  Reindex .Monoidᴰ.·Assocᴰ xᴰ yᴰ zᴰ = Mᴰ.rectify
    (symP (Mᴰ.reind-filler _ _)
    Mᴰ.∙ᴰ (refl {x = xᴰ} Mᴰ.·ᴰcong symP (Mᴰ.reind-filler _ _))
    Mᴰ.∙ᴰ Mᴰ.·Assocᴰ xᴰ yᴰ zᴰ
    Mᴰ.∙ᴰ (Mᴰ.reind-filler _ _ Mᴰ.·ᴰcong refl {x = zᴰ})
    Mᴰ.∙ᴰ Mᴰ.reind-filler _ _
    )
  Reindex .Monoidᴰ.isSetEltᴰ = Mᴰ.isSetEltᴰ

  π : MonoidHomᴰ ϕ Reindex Mᴰ
  π .fst = λ z → z
  π .snd .fst = symP (Mᴰ.reind-filler _ _)
  π .snd .snd xᴰ yᴰ = symP (Mᴰ.reind-filler _ _)


module _ {M : Monoid ℓ} {N : Monoid ℓ'} (ϕ : MonoidHom M N) (Nᴰ : Monoidᴰ N ℓᴰ) where

  Section→LocalSection : Section (Reindex ϕ Nᴰ) → LocalSection ϕ Nᴰ
  Section→LocalSection s =
    _gs⋆h_ {M = M} {N = N} {Mᴰ = Reindex ϕ Nᴰ} {Nᴰ = Nᴰ} s (π ϕ Nᴰ)


module _ {N : Monoid ℓ'} (ϕ : MonoidHom NatM N) (Nᴰ : Monoidᴰ N ℓᴰ) where

  elimNatLS : (e : Monoidᴰ.eltᴰ Nᴰ (ϕ .fst 1)) → LocalSection ϕ Nᴰ
  elimNatLS e = Section→LocalSection ϕ Nᴰ (elimNatSection (Reindex ϕ Nᴰ) e)

