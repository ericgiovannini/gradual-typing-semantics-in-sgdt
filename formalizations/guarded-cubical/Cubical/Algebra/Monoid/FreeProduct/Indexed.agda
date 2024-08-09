{-# OPTIONS --safe #-}
module Cubical.Algebra.Monoid.FreeProduct.Indexed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid.Displayed

open import Cubical.Data.Empty as Empty hiding (elim; rec)

private variable
  ℓ ℓ' ℓ'' ℓ''' ℓᴰ : Level
open MonoidStr


module _ (X : Type ℓ) (M : X → Monoid ℓ') where
  data |⊕ᵢ| : Type (ℓ-max ℓ ℓ') where
    gen       : ∀ x (m : ⟨ M x ⟩) → |⊕ᵢ|
    εₑ         : |⊕ᵢ|
    _·ₑ_       : |⊕ᵢ| → |⊕ᵢ| → |⊕ᵢ|
    identityᵣₑ : ∀ x     → x ·ₑ εₑ ≡ x
    identityₗₑ : ∀ x     → εₑ ·ₑ x ≡ x
    assocₑ     : ∀ x y z → x ·ₑ (y ·ₑ z) ≡ (x ·ₑ y) ·ₑ z
    gen-ε : ∀ x → gen x (M x .snd .ε) ≡ εₑ
    gen-· : ∀ x m n → gen x (M x .snd ._·_ m n) ≡ (gen x m ·ₑ gen x n)
    trunc     : isSet |⊕ᵢ|

  ⊕ᵢ : Monoid _
  ⊕ᵢ = |⊕ᵢ| , (monoidstr εₑ _·ₑ_
    (ismonoid (issemigroup trunc assocₑ) identityᵣₑ identityₗₑ))

  σ : ∀ x → MonoidHom (M x) ⊕ᵢ
  σ x .fst = gen x
  σ x .snd .IsMonoidHom.presε = gen-ε x
  σ x .snd .IsMonoidHom.pres· = gen-· x

  module _
    (Mᴰ : Monoidᴰ ⊕ᵢ ℓᴰ)
    (σᴰ : ∀ x → LocalSection (σ x) Mᴰ)
    where
    private
      module Mᴰ = Monoidᴰ Mᴰ
    elim : Section Mᴰ
    elim .fst = f where
      f : ∀ x → Mᴰ.eltᴰ x
      f (gen x m) = σᴰ x .fst m
      f εₑ = Mᴰ.εᴰ
      f (x ·ₑ y) = f x Mᴰ.·ᴰ f y 
      f (identityᵣₑ x i) = Mᴰ.·IdRᴰ (f x) i
      f (identityₗₑ x i) = Mᴰ.·IdLᴰ (f x) i
      f (assocₑ x y z i) = Mᴰ.·Assocᴰ (f x) (f y) (f z) i
      f (gen-ε x i) = σᴰ x .snd .fst i
      f (gen-· x m n i) = σᴰ x .snd .snd m n i
      f (trunc x y p q i j) =
        isOfHLevel→isOfHLevelDep 2 (λ x → Mᴰ.isSetEltᴰ)
          (f x) (f y)
          (cong f p) (cong f q)
          (trunc x y p q) i j
    elim .snd .fst = refl
    elim .snd .snd x y = refl
  module _
    (N : Monoid ℓ')
    (⟦σ⟧ : ∀ x → MonoidHom (M x) N)
    where
    open IsMonoidHom
    rec : MonoidHom ⊕ᵢ N
    rec = unWkn {ϕ = idMon _} s where
      s : Section (wkn ⊕ᵢ N)
      s = elim (wkn ⊕ᵢ N)
        ( λ x → (⟦σ⟧ x .fst)
        , (⟦σ⟧ x .snd .presε
        ,  ⟦σ⟧ x .snd .pres·))
    
