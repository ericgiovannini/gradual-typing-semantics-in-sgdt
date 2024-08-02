{-# OPTIONS --safe #-}
module Cubical.Algebra.Monoid.Displayed where

open import Cubical.Foundations.Prelude hiding (Σ)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma hiding (Σ)

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup.Base

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' : Level

record Monoidᴰ (M : Monoid ℓ) ℓ' : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  open MonoidStr (M .snd)
  field
    eltᴰ : ⟨ M ⟩ → Type ℓ'
    εᴰ : eltᴰ ε
    _·ᴰ_ : ∀ {x y} → eltᴰ x → eltᴰ y → eltᴰ (x · y)
  _≡[_]_ : ∀ {x y} → eltᴰ x → x ≡ y → eltᴰ y → Type _
  xᴰ ≡[ p ] yᴰ = PathP (λ i → eltᴰ (p i)) xᴰ yᴰ
  field
    ·IdRᴰ : ∀ {x}(xᴰ : eltᴰ x) → (xᴰ ·ᴰ εᴰ) ≡[ ·IdR x ] xᴰ
    ·IdLᴰ : ∀ {x}(xᴰ : eltᴰ x) → (εᴰ ·ᴰ xᴰ) ≡[ ·IdL x ] xᴰ
    ·Assocᴰ  : ∀ {x y z}(xᴰ : eltᴰ x)(yᴰ : eltᴰ y)(zᴰ : eltᴰ z)
      → (xᴰ ·ᴰ (yᴰ ·ᴰ zᴰ)) ≡[ ·Assoc x y z ] ((xᴰ ·ᴰ yᴰ) ·ᴰ zᴰ)
    isSetEltᴰ : ∀ {x} → isSet (eltᴰ x)

record Submonoid (M : Monoid ℓ) ℓ' : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  open MonoidStr (M .snd)
  field
    eltᴰ : ⟨ M ⟩ → Type ℓ'
    εᴰ : eltᴰ ε
    _·ᴰ_ : ∀ {x y} → eltᴰ x → eltᴰ y → eltᴰ (x · y)
    isPropEltᴰ : ∀ {x} → isProp (eltᴰ x)

submonoid→Monoidᴰ : {M : Monoid ℓ}(Mᴰ : Submonoid M ℓᴰ) → Monoidᴰ M ℓᴰ
submonoid→Monoidᴰ Mᴰ .Monoidᴰ.eltᴰ = Submonoid.eltᴰ Mᴰ
submonoid→Monoidᴰ Mᴰ .Monoidᴰ.εᴰ = Submonoid.εᴰ Mᴰ
submonoid→Monoidᴰ Mᴰ .Monoidᴰ._·ᴰ_ = Submonoid._·ᴰ_ Mᴰ
submonoid→Monoidᴰ Mᴰ .Monoidᴰ.·IdRᴰ _ =
  isProp→PathP (λ i → Submonoid.isPropEltᴰ Mᴰ) _ _
submonoid→Monoidᴰ Mᴰ .Monoidᴰ.·IdLᴰ _ =
  isProp→PathP (λ i → Submonoid.isPropEltᴰ Mᴰ) _ _
submonoid→Monoidᴰ Mᴰ .Monoidᴰ.·Assocᴰ _ _ _ =
  isProp→PathP (λ i → Submonoid.isPropEltᴰ Mᴰ) _ _
submonoid→Monoidᴰ Mᴰ .Monoidᴰ.isSetEltᴰ = isProp→isSet (Submonoid.isPropEltᴰ Mᴰ)

module _ {M : Monoid ℓ}(Mᴰ : Monoidᴰ M ℓᴰ) where
  private
    module Mᴰ = Monoidᴰ Mᴰ
    module M = MonoidStr (M .snd)
  Σ : Monoid (ℓ-max ℓ ℓᴰ)
  Σ .fst = Σ[ m ∈ ⟨ M ⟩ ] Mᴰ.eltᴰ m
  Σ .snd .MonoidStr.ε = M.ε , Mᴰ.εᴰ
  Σ .snd .MonoidStr._·_ (m , mᴰ) (m' , mᴰ') = (m M.· m') , (mᴰ Mᴰ.·ᴰ mᴰ')
  Σ .snd .MonoidStr.isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set =
    isSetΣ M.is-set (λ _ → Mᴰ.isSetEltᴰ)
  Σ .snd .MonoidStr.isMonoid .IsMonoid.isSemigroup .IsSemigroup.·Assoc _ _ _ =
    ΣPathP ((M.·Assoc _ _ _) , (Mᴰ.·Assocᴰ _ _ _))
  Σ .snd .MonoidStr.isMonoid .IsMonoid.·IdR _ =
    ΣPathP ((M.·IdR _) , (Mᴰ.·IdRᴰ _))
  Σ .snd .MonoidStr.isMonoid .IsMonoid.·IdL _ =
    ΣPathP ((M.·IdL _) , (Mᴰ.·IdLᴰ _))

LocalSection : {M : Monoid ℓ} {N : Monoid ℓ'}
  (ϕ : MonoidHom M N)
  (Nᴰ : Monoidᴰ N ℓᴰ)
  → Type (ℓ-max ℓ ℓᴰ)
LocalSection {M = M} {N = N} ϕ Nᴰ =
  Σ[ f ∈ (∀ (x : ⟨ M ⟩) → eltᴰ (ϕ .fst x)) ]
  (f ε ≡[ presε ] εᴰ) ×
  (∀ x y → f (x · y) ≡[ pres· x y ] (f x ·ᴰ f y))
  where
    open Monoidᴰ Nᴰ
    open IsMonoidHom (ϕ .snd)
    open MonoidStr (M .snd)

-- _s∘h_ :
--   {M : Monoid ℓ}{N : Monoid ℓ'}
--   {P : Monoid ℓ''}{Pᴰ : Monoidᴰ P ℓᴰ}
--   {ϕ : MonoidHom N P}
--   (ϕᴰ : LocalSection ϕ Pᴰ)
--   (ψ : MonoidHom M N)
--   → LocalSection (ϕ ∘hom ψ) Pᴰ
-- (ϕᴰ s∘h ψ) .fst x = ϕᴰ .fst (ψ .fst x)
-- (ϕᴰ s∘h ψ) .snd .fst = {!!}
-- (ϕᴰ s∘h ψ) .snd .snd = {!!}

Section : {M : Monoid ℓ} (Mᴰ : Monoidᴰ M ℓ') → Type (ℓ-max ℓ ℓ')
Section {M = M} Mᴰ = LocalSection (idMon M) Mᴰ


module _ {M : Monoid ℓ}{Mᴰ : Monoidᴰ M ℓᴰ} where
  fstHom : MonoidHom (Σ Mᴰ) M
  fstHom .fst = fst
  fstHom .snd .IsMonoidHom.presε = refl
  fstHom .snd .IsMonoidHom.pres· _ _ = refl

  sndHom : LocalSection fstHom Mᴰ
  sndHom .fst = snd
  sndHom .snd .fst = refl
  sndHom .snd .snd x y = refl

  corecΣ : {N : Monoid ℓ'}
    → (ϕ : MonoidHom N M)
    → LocalSection ϕ Mᴰ
    → MonoidHom N (Σ Mᴰ)
  corecΣ ϕ ϕᴰ .fst x = ϕ .fst x , ϕᴰ .fst x
  corecΣ ϕ ϕᴰ .snd .IsMonoidHom.presε =
    ΣPathP ((ϕ .snd .IsMonoidHom.presε) , (ϕᴰ .snd .fst))
  corecΣ ϕ ϕᴰ .snd .IsMonoidHom.pres· x y =
    ΣPathP ((ϕ .snd .IsMonoidHom.pres· x y) , (ϕᴰ .snd .snd x y))

MonoidHomᴰ : {M : Monoid ℓ}{N : Monoid ℓ'}
  (ϕ : MonoidHom M N)
  → Monoidᴰ M ℓᴰ
  → Monoidᴰ N ℓᴰ' → Type (ℓ-max (ℓ-max ℓ ℓᴰ) ℓᴰ')
MonoidHomᴰ {M = M}{N} ϕ Mᴰ Nᴰ =
  LocalSection (ϕ ∘hom fstHom {Mᴰ = Mᴰ}) Nᴰ

VMonoidHomᴰ : {M : Monoid ℓ}
  → Monoidᴰ M ℓᴰ
  → Monoidᴰ M ℓᴰ' → Type (ℓ-max (ℓ-max ℓ ℓᴰ) ℓᴰ')
VMonoidHomᴰ Mᴰ Nᴰ = MonoidHomᴰ (idMon _) Mᴰ Nᴰ

open MonoidStr
wkn : (M : Monoid ℓ) (N : Monoid ℓ') → Monoidᴰ M ℓ'
wkn M N .Monoidᴰ.eltᴰ x = ⟨ N ⟩
wkn M N .Monoidᴰ.εᴰ = N .snd .ε
wkn M N .Monoidᴰ._·ᴰ_ = N .snd ._·_
wkn M N .Monoidᴰ.·IdRᴰ = N .snd .·IdR
wkn M N .Monoidᴰ.·IdLᴰ = N .snd .·IdL
wkn M N .Monoidᴰ.·Assocᴰ = N .snd .·Assoc
wkn M N .Monoidᴰ.isSetEltᴰ = is-set (N .snd)

module _ {M : Monoid ℓ}{N : Monoid ℓ'}{P : Monoid ℓ''} where
  unWkn : {ϕ : MonoidHom P M}
    → LocalSection ϕ (wkn M N)
    → MonoidHom P N
  unWkn ψ .fst = ψ .fst
  unWkn ψ .snd .IsMonoidHom.presε = ψ .snd .fst
  unWkn ψ .snd .IsMonoidHom.pres· = ψ .snd .snd

open Monoidᴰ
_^opᴰ : ∀ {M : Monoid ℓ} → Monoidᴰ M ℓᴰ → Monoidᴰ (M ^op) ℓᴰ
(Mᴰ ^opᴰ) .Monoidᴰ.eltᴰ = Mᴰ .eltᴰ
(Mᴰ ^opᴰ) .Monoidᴰ.εᴰ = Mᴰ .εᴰ
(Mᴰ ^opᴰ) .Monoidᴰ._·ᴰ_ xᴰ yᴰ = Mᴰ ._·ᴰ_ yᴰ xᴰ
(Mᴰ ^opᴰ) .Monoidᴰ.·IdRᴰ = Mᴰ .·IdLᴰ
(Mᴰ ^opᴰ) .Monoidᴰ.·IdLᴰ = Mᴰ .·IdRᴰ
(Mᴰ ^opᴰ) .·Assocᴰ xᴰ yᴰ zᴰ = symP (Mᴰ .·Assocᴰ _ _ _)
(Mᴰ ^opᴰ) .Monoidᴰ.isSetEltᴰ = Mᴰ .isSetEltᴰ
