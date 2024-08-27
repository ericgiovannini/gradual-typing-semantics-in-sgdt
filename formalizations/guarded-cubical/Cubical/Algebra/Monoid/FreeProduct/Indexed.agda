-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Cubical.Algebra.Monoid.FreeProduct.Indexed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Reindex

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

  -- module _
  --   (Mᴰ : Monoidᴰ ⊕ᵢ ℓᴰ)
  --   (σᴰ : ∀ x → LocalSection (σ x) Mᴰ)
  --   (isProp

  module _ {ℓ : Level} (N : Monoid ℓ) where
    private
      module N = MonoidStr (N .snd)
      open Monoidᴰ

    MonPath : Monoidᴰ (N ×M N) ℓ
    MonPath = submonoid→Monoidᴰ sub
      where
        open Submonoid
        sub : Submonoid (N ×M N) ℓ
        sub .eltᴰ (x , y) = x ≡ y
        sub .εᴰ = refl
        sub ._·ᴰ_ p q = cong₂ N._·_ p q
        sub .isPropEltᴰ = N.is-set _ _
    
    -- Eq : Monoidᴰ (N ×M N) ℓ
    -- Eq .eltᴰ (x , y) = x ≡ y
    -- Eq .εᴰ = refl
    -- Eq ._·ᴰ_ {x = (x₁ , y₁)} {y = (x₂ , y₂)} p q = cong₂ N._·_ p q
    -- Eq .·IdRᴰ {x = (x , y)} xᴰ = isProp→PathP (λ i → N.is-set _ _) _ _
    -- Eq .·IdLᴰ xᴰ = isProp→PathP (λ i → N.is-set _ _) _ _
    -- Eq .·Assocᴰ xᴰ yᴰ zᴰ = isProp→PathP (λ i → N.is-set _ _) _ _
    -- Eq .isSetEltᴰ = isProp→isSet (N.is-set _ _)

  -- Given a homomorphism f : M → N and a displayed monoid Nᴰ over N
  -- the "pullback" Mᴰ of N along f is displayed over M.
  
  -- module _ {ℓ ℓ' ℓᴰ : Level} {M : Monoid ℓ} {N : Monoid ℓ'}
  --   (f : MonoidHom M N)
  --   (Nᴰ : Monoidᴰ N ℓᴰ) where

  --   open Monoidᴰ
  --   private
  --     module M = MonoidStr (M .snd)
  --     module Nᴰ = Monoidᴰ Nᴰ
  --     module f = IsMonoidHom (f .snd)

  --   pullback : Monoidᴰ M ℓᴰ
  --   pullback .eltᴰ x = Nᴰ.eltᴰ (f .fst x)
  --   pullback .εᴰ = reind Nᴰ (sym f.presε) Nᴰ.εᴰ
  --   pullback ._·ᴰ_ {x = x} {y = y} n n' = reind Nᴰ (sym (f.pres· x y)) (Nᴰ._·ᴰ_ n n')
  --   pullback .·IdRᴰ {x = x} xᴰ = let foo =
  --     symP (reind-filler Nᴰ (λ i → f .fst (M.·IdR x i)) (reind Nᴰ (sym (f.pres· x M.ε)) {!!})) in {!!}
  --   pullback .·IdLᴰ xᴰ = {!!}
  --   pullback .·Assocᴰ = {!!}
  --   pullback .isSetEltᴰ = Nᴰ.isSetEltᴰ

  module _ {ℓ ℓ' : Level} {M : Monoid ℓ} {N : Monoid ℓ'}
    (f g : MonoidHom M N) where

    private
      module N = MonoidStr (N .snd)
      module f = IsMonoidHom (f .snd)
      module g = IsMonoidHom (g .snd)
      open Monoidᴰ

    Eq : Monoidᴰ M ℓ'
    Eq = Reindex (×M-intro f g) (MonPath N)

  module _
    (N : Monoid ℓ'')
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

  rec-is-uniq : {N : Monoid ℓ''} {⟦σ⟧ : ∀ x → MonoidHom (M x) N} {ψ : MonoidHom ⊕ᵢ N}
   → (∀ x → (⟦σ⟧ x) ≡ ψ ∘hom (σ x))
   → rec N ⟦σ⟧ ≡ ψ
  rec-is-uniq {N = N} {⟦σ⟧ = ⟦σ⟧} {ψ = ψ} eq =
    eqMonoidHom _ _ (funExt (λ m → h .fst m))
    where
      ⊕ᴰ : Monoidᴰ ⊕ᵢ _
      ⊕ᴰ = Eq (rec N ⟦σ⟧) ψ

      h : Section ⊕ᴰ
      h = elim ⊕ᴰ (λ x →
          (λ m → funExt⁻ (cong fst (eq x)) m)
        , isProp→PathP (λ i → N .snd .is-set _ _) _ _
        , λ _ _ → isProp→PathP (λ i → N .snd .is-set _ _) _ _)
    
  module _
    {P : Monoid ℓ''}
    {ϕ ψ : MonoidHom ⊕ᵢ P}
    where

    ind :
      (∀ x → ϕ ∘hom (σ x) ≡ ψ ∘hom (σ x))
      → ϕ ≡ ψ
    ind eq = sym (rec-is-uniq (λ x → refl)) ∙ rec-is-uniq eq


-- module _ (X : Type ℓ) (M : X → Monoid ℓ') where

--   data IndexedCoproduct : Type (ℓ-max ℓ ℓ') where
--     ⟦_⟧ : {x : X} → ⟨ M x ⟩ → IndexedCoproduct
--     ε         : IndexedCoproduct
--     _·_       : IndexedCoproduct → IndexedCoproduct → IndexedCoproduct

--     idₓ : ∀ {x : X} → ⟦ MonoidStr.ε (M x .snd) ⟧ ≡ ε
--     compₓ : ∀ {x : X} → ∀ mx mx' -> ⟦ MonoidStr._·_ (M x .snd) mx mx' ⟧ ≡ (⟦ mx ⟧ · ⟦ mx' ⟧)
    
--     identityᵣ : ∀ x     → x · ε ≡ x
--     identityₗ : ∀ x     → ε · x ≡ x
--     assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
--     trunc     : isSet IndexedCoproduct

--   ⊕ : Monoid (ℓ-max ℓ ℓ')
--   ⊕ = IndexedCoproduct , (monoidstr ε _·_ (ismonoid (issemigroup trunc assoc) identityᵣ identityₗ))

--   iₓ : (x : X) → MonoidHom (M x) ⊕
--   iₓ x .fst mx = ⟦ mx ⟧
--   iₓ x .snd .IsMonoidHom.presε = idₓ
--   iₓ x .snd .IsMonoidHom.pres· = compₓ

--   module _ (Mᴰ : Monoidᴰ ⊕ ℓᴰ) where
--     private
--       module Mᴰ = Monoidᴰ Mᴰ
--     module _
--       -- (hₓ : ∀ {x} (mx : ⟨ M x ⟩) → Mᴰ.eltᴰ ⟦ mx ⟧)
--       (hₓ : ∀ (x : X) → LocalSection (iₓ x) Mᴰ)      
  
--       where
--       elim : Section Mᴰ
--       elim .fst = f where
--         f : (x : ⟨ ⊕ ⟩) → Mᴰ.eltᴰ x
--         f ⟦ mx ⟧ = hₓ _ .fst mx
--         f ε = Mᴰ.εᴰ
--         f (x · y) = f x Mᴰ.·ᴰ f y
--         f (idₓ i) = hₓ _ .snd .fst i
--         f (compₓ mx mx' i) =  hₓ _ .snd .snd mx mx' i
--         f (identityᵣ x i) = Mᴰ.·IdRᴰ (f x) i
--         f (identityₗ x i) =  Mᴰ.·IdLᴰ (f x) i
--         f (assoc x y z i) = Mᴰ.·Assocᴰ (f x) (f y) (f z) i
--         f (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2 (λ x → Mᴰ.isSetEltᴰ)
--           (f x) (f y)
--           (cong f p) (cong f q)
--           (trunc x y p q)
--           i j
--       elim .snd .fst = refl
--       elim .snd .snd x y = refl

--   module _ (N : Monoid ℓ''')
--     (hX : (x : X) → MonoidHom (M x) N)
--     where
--     rec : MonoidHom ⊕ N
--     rec = unWkn {ϕ = idMon _} s where
--       s : Section (wkn ⊕ N)
--       s = elim (wkn ⊕ N) ls where
--         ls : (x : X) → LocalSection (iₓ x) (wkn ⊕ N)
--         ls x .fst mx = hX x .fst mx
--         ls x .snd .fst = hX x .snd .IsMonoidHom.presε
--         ls x .snd .snd mx mx' = hX x .snd .IsMonoidHom.pres· mx mx'
