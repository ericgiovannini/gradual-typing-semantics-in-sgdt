{-# OPTIONS --safe #-}
module Cubical.Algebra.Monoid.Displayed where

open import Cubical.Foundations.Prelude hiding (Σ)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma hiding (Σ)
import Cubical.Data.Equality as Eq
open import Cubical.Data.Nat hiding (_·_)

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓᴰ ℓᴰ' : Level
    ℓM ℓN ℓP ℓMᴰ ℓNᴰ ℓPᴰ : Level

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

  reind : ∀ {x y} (p : x ≡ y) → eltᴰ x → eltᴰ y
  reind = subst eltᴰ

  reind-filler : ∀ {x y}(p : x ≡ y)
    → (xᴰ : eltᴰ x)
    → xᴰ ≡[ p ] reind p xᴰ
  reind-filler = subst-filler eltᴰ

  rectify :
    ∀ {x y} {xᴰ yᴰ}
    → {p q : x ≡ y}
    → xᴰ ≡[ p ] yᴰ → xᴰ ≡[ q ] yᴰ
  rectify {xᴰ = xᴰ}{yᴰ = yᴰ} = subst (xᴰ ≡[_] yᴰ)
    (is-set _ _ _ _)
  infixr 30 _∙ᴰ_
  _∙ᴰ_ :
    ∀ {x y z} {xᴰ yᴰ zᴰ}
    → {p : x ≡ y}{q : y ≡ z}
    → xᴰ ≡[ p ] yᴰ → yᴰ ≡[ q ] zᴰ
    → xᴰ ≡[ p ∙ q ] zᴰ
  _∙ᴰ_ {xᴰ = xᴰ}{zᴰ = zᴰ}{p}{q} pᴰ qᴰ =
    subst (λ p → PathP (λ i → p i) xᴰ zᴰ)
      (sym (congFunct eltᴰ p q))
      (compPathP pᴰ qᴰ)
  _·ᴰcong_ :
    ∀ {w x y z}
      {wᴰ xᴰ yᴰ zᴰ}
      {p : w ≡ x}
      {q : y ≡ z}
    → wᴰ ≡[ p ] xᴰ → yᴰ ≡[ q ] zᴰ
    → (wᴰ ·ᴰ yᴰ) ≡[ cong₂ _·_ p q ] (xᴰ ·ᴰ zᴰ)
  pᴰ ·ᴰcong qᴰ = congP₂ (λ _ → _·ᴰ_) pᴰ qᴰ

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
open Monoidᴰ
-- rectifySection : {M : Monoid ℓ} {N : Monoid ℓ'}
--   {Nᴰ : Monoidᴰ N ℓᴰ}
--   {ϕ ϕ' : MonoidHom M N}
--   → ϕ .fst Eq.≡ ϕ' .fst
--   → LocalSection ϕ Nᴰ
--   → LocalSection ϕ' Nᴰ
-- rectifySection {Nᴰ = Nᴰ} Eq.refl f .fst x =
-- rectifySection Eq.refl f .snd = {!!}

Section : {M : Monoid ℓ} (Mᴰ : Monoidᴰ M ℓ') → Type (ℓ-max ℓ ℓ')
Section {M = M} Mᴰ = LocalSection (idMon M) Mᴰ

MonoidHomᴰ : {M : Monoid ℓ}{N : Monoid ℓ'}
  (ϕ : MonoidHom M N)
  → Monoidᴰ M ℓᴰ
  → Monoidᴰ N ℓᴰ' → Type (ℓ-max (ℓ-max ℓ ℓᴰ) ℓᴰ')
MonoidHomᴰ {M = M}{N} ϕ Mᴰ Nᴰ =
  Σ[ ϕᴰ ∈ (∀ {x} → (Mᴰ.eltᴰ x) → Nᴰ.eltᴰ (ϕ .fst x)) ]
  (ϕᴰ Mᴰ.εᴰ Nᴰ.≡[ ϕ .snd .presε ] Nᴰ.εᴰ) ×
  (∀ {x}{y} xᴰ yᴰ
    → ϕᴰ (xᴰ Mᴰ.·ᴰ yᴰ) Nᴰ.≡[ ϕ .snd .pres· x y ] (ϕᴰ xᴰ Nᴰ.·ᴰ ϕᴰ yᴰ) )
  where
    module Mᴰ = Monoidᴰ Mᴰ
    module Nᴰ = Monoidᴰ Nᴰ
    open IsMonoidHom


module _
  {M : Monoid ℓM} {N : Monoid ℓN} {P : Monoid ℓP}
  {Mᴰ : Monoidᴰ M ℓMᴰ} {Nᴰ : Monoidᴰ N ℓNᴰ} {Pᴰ : Monoidᴰ P ℓPᴰ}
  {ψ : MonoidHom M N} {ϕ : MonoidHom N P} where

  module Pᴰ = Monoidᴰ Pᴰ

  _∘MonoidHomᴰ_ :
   MonoidHomᴰ ϕ Nᴰ Pᴰ → MonoidHomᴰ ψ Mᴰ Nᴰ → MonoidHomᴰ (ϕ ∘hom ψ) Mᴰ Pᴰ
  (ϕᴰ ∘MonoidHomᴰ ψᴰ) .fst xᴰ = ϕᴰ .fst (ψᴰ .fst xᴰ)
  (ϕᴰ ∘MonoidHomᴰ ψᴰ) .snd .fst =
    (congP (λ i → ϕᴰ .fst) (ψᴰ .snd .fst)) Pᴰ.∙ᴰ (ϕᴰ .snd .fst)
  (ϕᴰ ∘MonoidHomᴰ ψᴰ) .snd .snd xᴰ yᴰ =
    (congP (λ i → ϕᴰ .fst) (ψᴰ .snd .snd xᴰ yᴰ)) Pᴰ.∙ᴰ (ϕᴰ .snd .snd _ _)

VMonoidHomᴰ : {M : Monoid ℓ}
  → Monoidᴰ M ℓᴰ
  → Monoidᴰ M ℓᴰ' → Type (ℓ-max (ℓ-max ℓ ℓᴰ) ℓᴰ')
VMonoidHomᴰ Mᴰ Nᴰ = MonoidHomᴰ (idMon _) Mᴰ Nᴰ

module _   {M : Monoid ℓ}{N : Monoid ℓ'}
  {Mᴰ : Monoidᴰ M ℓᴰ}{Nᴰ : Monoidᴰ N ℓᴰ'}
  {ϕ : MonoidHom M N}
  where
  private
    module Nᴰ = Monoidᴰ Nᴰ
  _gs⋆h_ : (s : Section Mᴰ) (ϕᴰ : MonoidHomᴰ ϕ Mᴰ Nᴰ) → LocalSection ϕ Nᴰ
  (s gs⋆h ϕᴰ) .fst x = ϕᴰ .fst (s .fst x)
  (s gs⋆h ϕᴰ) .snd .fst =
    Nᴰ.rectify (cong (ϕᴰ .fst) (s .snd .fst) Nᴰ.∙ᴰ ϕᴰ .snd .fst)
  (s gs⋆h ϕᴰ) .snd .snd x y =
    Nᴰ.rectify (cong (ϕᴰ .fst) (s .snd .snd x y) Nᴰ.∙ᴰ ϕᴰ .snd .snd _ _)
{- Σ -}
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

module _ {M : Monoid ℓ}{Mᴰ : Monoidᴰ M ℓᴰ}{N : Monoid ℓ'}{Nᴰ : Monoidᴰ N ℓᴰ'}
  where
  private
    module Nᴰ = Monoidᴰ Nᴰ
  recΣ :
    ∀ (ϕ : MonoidHom M N)
    → (ϕᴰ : MonoidHomᴰ ϕ Mᴰ Nᴰ)
    → LocalSection {M = Σ Mᴰ} (ϕ ∘hom fstHom) Nᴰ
  recΣ ϕ ϕᴰ .fst (m , mᴰ) = ϕᴰ .fst {m} mᴰ
  recΣ ϕ ϕᴰ .snd .fst =
    Nᴰ.rectify (ϕᴰ .snd .fst)
  recΣ ϕ ϕᴰ .snd .snd x y =
    Nᴰ.rectify (ϕᴰ .snd .snd (x .snd) (y .snd))
module _ {M : Monoid ℓ}{Mᴰ : Monoidᴰ M ℓᴰ}{Nᴰ : Monoidᴰ M ℓᴰ'} where
  private
    module Nᴰ = Monoidᴰ Nᴰ

  recΣV :
    (ϕᴰ : VMonoidHomᴰ Mᴰ Nᴰ)
    → LocalSection {M = Σ Mᴰ} fstHom Nᴰ
  recΣV ϕᴰ .fst (m , mᴰ) = ϕᴰ .fst {m} mᴰ
  recΣV ϕᴰ .snd .fst = ϕᴰ .snd .fst
  recΣV ϕᴰ .snd .snd x y = ϕᴰ .snd .snd (x .snd) (y .snd)

{- weakening -}
open MonoidStr
wkn : (M : Monoid ℓ) (N : Monoid ℓ') → Monoidᴰ M ℓ'
wkn M N .Monoidᴰ.eltᴰ x = ⟨ N ⟩
wkn M N .Monoidᴰ.εᴰ = N .snd .ε
wkn M N .Monoidᴰ._·ᴰ_ = N .snd ._·_
wkn M N .Monoidᴰ.·IdRᴰ = N .snd .·IdR
wkn M N .Monoidᴰ.·IdLᴰ = N .snd .·IdL
wkn M N .Monoidᴰ.·Assocᴰ = N .snd .·Assoc
wkn M N .Monoidᴰ.isSetEltᴰ = is-set (N .snd)

open IsMonoidHom
wknHom :
  {M : Monoid ℓ}{M' : Monoid ℓ'}
  {N : Monoid ℓ''}{N' : Monoid ℓ'''}
  (ϕ : MonoidHom M N)
  (ψ : MonoidHom M' N')
  → MonoidHomᴰ ϕ (wkn M M') (wkn N N')
wknHom ϕ ψ .fst = ψ .fst
wknHom ϕ ψ .snd .fst = ψ .snd .presε
wknHom ϕ ψ .snd .snd = ψ .snd .pres·

module _ {M : Monoid ℓ}{N : Monoid ℓ'}{P : Monoid ℓ''} where
  unWkn : {ϕ : MonoidHom P M}
    → LocalSection ϕ (wkn M N)
    → MonoidHom P N
  unWkn ψ .fst = ψ .fst
  unWkn ψ .snd .IsMonoidHom.presε = ψ .snd .fst
  unWkn ψ .snd .IsMonoidHom.pres· = ψ .snd .snd

IdHomᴰ : (M : Monoid ℓ) →
  MonoidHomᴰ {M = M} {N = M} (idMon M) (wkn M M) (wkn M M)
IdHomᴰ M = wknHom (idMon M) (idMon M)

open Monoidᴰ
_^opᴰ : ∀ {M : Monoid ℓ} → Monoidᴰ M ℓᴰ → Monoidᴰ (M ^op) ℓᴰ
(Mᴰ ^opᴰ) .Monoidᴰ.eltᴰ = Mᴰ .eltᴰ
(Mᴰ ^opᴰ) .Monoidᴰ.εᴰ = Mᴰ .εᴰ
(Mᴰ ^opᴰ) .Monoidᴰ._·ᴰ_ xᴰ yᴰ = Mᴰ ._·ᴰ_ yᴰ xᴰ
(Mᴰ ^opᴰ) .Monoidᴰ.·IdRᴰ = Mᴰ .·IdLᴰ
(Mᴰ ^opᴰ) .Monoidᴰ.·IdLᴰ = Mᴰ .·IdRᴰ
(Mᴰ ^opᴰ) .·Assocᴰ xᴰ yᴰ zᴰ = symP (Mᴰ .·Assocᴰ _ _ _)
(Mᴰ ^opᴰ) .Monoidᴰ.isSetEltᴰ = Mᴰ .isSetEltᴰ


mkSectionSubmonoid : ∀ {M : Monoid ℓ}{N : Monoid ℓ'}{P : Monoidᴰ N ℓᴰ}
  {ϕ : MonoidHom M N}
  → (∀ y → isProp (P .eltᴰ y))
  → (∀ x → P .eltᴰ (ϕ .fst x))
  → LocalSection ϕ P
mkSectionSubmonoid isPropEltᴰ f .fst = f
mkSectionSubmonoid isPropEltᴰ f .snd .fst =
  isProp→PathP (λ i → isPropEltᴰ _) _ _
mkSectionSubmonoid isPropEltᴰ f .snd .snd x y =
  isProp→PathP (λ i → isPropEltᴰ _) _ _


-- Universal property of Nat monoid



  

module _  (Nᴰ : Monoidᴰ NatM ℓᴰ) where

  private
    module Nᴰ = Monoidᴰ Nᴰ

    h : Nᴰ.eltᴰ 1 → (n : ℕ) → Nᴰ.eltᴰ n
    h e zero = Nᴰ.εᴰ 
    h e (suc n) = e Nᴰ.·ᴰ h e n

  elimNatSection : Nᴰ.eltᴰ 1 → Section Nᴰ
  elimNatSection e .fst = h e
  elimNatSection e .snd .fst = refl
  elimNatSection e .snd .snd = pf
    where
      pf : ∀ n m → h e (n + m) ≡ (h e n Nᴰ.·ᴰ h e m)
      pf zero m = sym (Nᴰ.·IdLᴰ _)
      pf (suc n) m =
        (cong₂ Nᴰ._·ᴰ_ refl (pf n m)) ∙
        (Nᴰ.·Assocᴰ e (h e n) (h e m))
       

{-
module _ {N : Monoid ℓ'} (ϕ : MonoidHom NatM N) (Nᴰ : Monoidᴰ N ℓᴰ) where

  private
    module Nᴰ = Monoidᴰ Nᴰ
    module ϕ = IsMonoidHom (ϕ .snd)

  module _ (e : Nᴰ.eltᴰ (ϕ .fst 1)) where
    private
      h : (n : ℕ) → Nᴰ.eltᴰ (ϕ .fst n)
      h zero = reind Nᴰ (sym ϕ.presε) Nᴰ.εᴰ
      h (suc n) = reind Nᴰ (sym (ϕ.pres· 1 n)) (e Nᴰ.·ᴰ h n)

      h-id : h zero  Nᴰ.≡[ ϕ.presε ]  Nᴰ.εᴰ
      h-id = symP (reind-filler Nᴰ _ Nᴰ.εᴰ)

      h-comp : ∀ n m →
        h (n + m) Nᴰ.≡[ ϕ.pres· n m ] (h n Nᴰ.·ᴰ h m)
      h-comp zero m = {!!}
      h-comp (suc n) m = {!!}
    
    elimNatLS :  LocalSection ϕ Nᴰ
    elimNatLS .fst = h
    elimNatLS .snd .fst = h-id
    elimNatLS .snd .snd = h-comp

    -- foo : LocalSection ϕ Nᴰ
    -- foo = elimNatSection {!reindex!} {!!} gs⋆h {!!}
-}
