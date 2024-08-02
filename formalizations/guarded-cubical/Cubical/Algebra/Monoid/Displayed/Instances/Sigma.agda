{-

  Sigma for Displayed Monoids.

  The most general would have the base monoid be a Sigma, but this is
  what we need for our development currently.

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Monoid.Displayed.Instances.Sigma where

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

module _ {M : Monoid ℓ}{N : Monoid ℓ'} (Mᴰ : Monoidᴰ (M × N) ℓᴰ) where
  private
    module Mᴰ = Monoidᴰ Mᴰ
    module N = MonoidStr (N .snd)
    module M = MonoidStr (M .snd)
  open Monoidᴰ
  Σl : Monoidᴰ M (ℓ-max ℓ' ℓᴰ)
  Σl .eltᴰ m = Σ[ n ∈ ⟨ N ⟩ ] Mᴰ.eltᴰ (m , n)
  Σl .εᴰ = N.ε , Mᴰ.εᴰ
  Σl ._·ᴰ_ (n , mᴰ) (n' , mᴰ') = (n N.· n') , (mᴰ Mᴰ.·ᴰ mᴰ')
  Σl .·IdRᴰ (n , mᴰ) = ΣPathP (N.·IdR n , Mᴰ.·IdRᴰ mᴰ)
  Σl .·IdLᴰ (n , mᴰ) = ΣPathP (N.·IdL n , Mᴰ.·IdLᴰ mᴰ)
  Σl .·Assocᴰ xᴰ yᴰ zᴰ = ΣPathP (N.·Assoc _ _ _ , Mᴰ.·Assocᴰ _ _ _)
  Σl .isSetEltᴰ = isSetΣ N.is-set (λ _ → Mᴰ.isSetEltᴰ)

  Σr : Monoidᴰ N (ℓ-max ℓ ℓᴰ)
  Σr .eltᴰ n = Σ[ m ∈ ⟨ M ⟩ ] Mᴰ.eltᴰ (m , n)
  Σr .εᴰ = M.ε , Mᴰ.εᴰ
  Σr ._·ᴰ_ (m , mᴰ) (m' , mᴰ') = (m M.· m') , (mᴰ Mᴰ.·ᴰ mᴰ')
  Σr .·IdRᴰ (m , mᴰ) = ΣPathP (M.·IdR m , Mᴰ.·IdRᴰ mᴰ)
  Σr .·IdLᴰ (m , mᴰ) = ΣPathP (M.·IdL m , Mᴰ.·IdLᴰ mᴰ)
  Σr .·Assocᴰ xᴰ yᴰ zᴰ = ΣPathP (M.·Assoc _ _ _ , Mᴰ.·Assocᴰ _ _ _)
  Σr .isSetEltᴰ = isSetΣ M.is-set (λ _ → Mᴰ.isSetEltᴰ)

module _ {M : Monoid ℓ}{N : Monoid ℓ'} {Mᴰ : Monoidᴰ (M × N) ℓᴰ} where
  private
    module Mᴰ = Monoidᴰ Mᴰ
    module N = MonoidStr (N .snd)
    module M = MonoidStr (M .snd)

    SigL = Σl {M = M}{N = N} Mᴰ
    SigR = Σr {M = M}{N = N} Mᴰ
  open Monoidᴰ

  fstL : VMonoidHomᴰ (Σl {M = M}{N = N} Mᴰ) (wkn M N)
  fstL .fst (n , mᴰ)= n
  fstL .snd .fst = refl
  fstL .snd .snd x y = refl

  fstL' : MonoidHom (Disp.Σ SigL) N
  fstL' = unWkn {N = N}{ϕ = fstHom}(recΣV {Mᴰ = SigL}{Nᴰ = wkn M N} fstL)

  sndL : LocalSection {M = Disp.Σ SigL}
         (corec (fstHom {Mᴰ = SigL}) fstL')
         Mᴰ
  sndL .fst (m , n , mᴰ) = mᴰ
  sndL .snd .fst = refl
  sndL .snd .snd x y = refl

  fstR : VMonoidHomᴰ SigR (wkn N M)
  fstR .fst (m , mᴰ) = m
  fstR .snd .fst = refl
  fstR .snd .snd x y = refl

  fstR' : MonoidHom (Disp.Σ SigR) M
  fstR' = (unWkn {N = M}{ϕ = fstHom} (recΣV {Mᴰ = SigR} {Nᴰ = wkn N M} fstR))

  sndR : LocalSection {M = Disp.Σ SigR}
         (corec fstR' (fstHom {Mᴰ = SigR}))
         Mᴰ
  sndR .fst (n , m , mᴰ) = mᴰ
  sndR .snd .fst = refl
  sndR .snd .snd x y = refl
