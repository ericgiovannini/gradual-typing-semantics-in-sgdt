{-# OPTIONS --safe #-}

module Cubical.Algebra.Monoid.FreeMonoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Reindex
open import Cubical.Data.Empty as Empty hiding (elim; rec)

private variable
  ℓ ℓ' ℓ'' ℓ''' ℓᴰ ℓᴰ' : Level

module _  (A : Type ℓ) (B : Type ℓ') (C : Type ℓ'') where
  data FreeMonoid : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    ⟦_⟧       : A → FreeMonoid
    ⟦_⟧co     : B → FreeMonoid → FreeMonoid
    ⟦_⟧op     : C → FreeMonoid → FreeMonoid
    ε         : FreeMonoid
    _·_       : FreeMonoid → FreeMonoid → FreeMonoid
    identityᵣ : ∀ x     → x · ε ≡ x
    identityₗ : ∀ x     → ε · x ≡ x
    assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
    co-ε : ∀ b → ⟦ b ⟧co ε ≡ ε
    co-· : ∀ b x y → ⟦ b ⟧co (x · y) ≡ (⟦ b ⟧co x · ⟦ b ⟧co y)
    op-ε : ∀ b → ⟦ b ⟧op ε ≡ ε
    op-· : ∀ b x y → ⟦ b ⟧op (y · x) ≡ (⟦ b ⟧op x · ⟦ b ⟧op y)
    trunc     : isSet FreeMonoid

  FM : Monoid _
  FM = FreeMonoid , (monoidstr ε _·_ (ismonoid (issemigroup trunc assoc) identityᵣ identityₗ))

  gen : A → ⟨ FM ⟩
  gen x = ⟦ x ⟧

  coHom : B → MonoidHom FM FM
  coHom b .fst = ⟦ b ⟧co
  coHom b .snd .IsMonoidHom.presε = co-ε b
  coHom b .snd .IsMonoidHom.pres· = co-· b

  opHom : C → MonoidHom (FM ^op) FM
  opHom c .fst = ⟦ c ⟧op
  opHom c .snd .IsMonoidHom.presε = op-ε c
  opHom c .snd .IsMonoidHom.pres· = op-· c

  module _ (Mᴰ : Monoidᴰ FM ℓᴰ) where
    private
      module Mᴰ = Monoidᴰ Mᴰ
    module _
      (iA : ∀ a → Mᴰ.eltᴰ ⟦ a ⟧)
      (iB : ∀ b → MonoidHomᴰ (coHom b) Mᴰ Mᴰ)
      (iC : ∀ c → MonoidHomᴰ (opHom c) (Mᴰ ^opᴰ) Mᴰ)
      
      where
      elim : Section Mᴰ
      elim .fst = f where
        f : ∀ x → Mᴰ.eltᴰ x
        f ⟦ a ⟧ = iA a
        f (⟦ b ⟧co x) = iB b .fst (f x)
        f (co-ε b i) = iB b .snd .fst i
        f (co-· b x y i) = iB b .snd .snd (f x) (f y) i
        f (⟦ c ⟧op x) = iC c .fst (f x)
        f (op-ε c i) = iC c .snd .fst i
        f (op-· c x y i) = iC c .snd .snd (f x) (f y) i
        f ε = Mᴰ.εᴰ
        f (x · y) = f x Mᴰ.·ᴰ f y
        f (identityᵣ x i) = Mᴰ.·IdRᴰ (f x) i
        f (identityₗ x i) = Mᴰ.·IdLᴰ (f x) i
        f (assoc x y z i) = Mᴰ.·Assocᴰ (f x) (f y) (f z) i
        f (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2 (λ x → Mᴰ.isSetEltᴰ)
          (f x) (f y)
          (cong f p) (cong f q)
          (trunc x y p q)
          i j
      elim .snd .fst = refl
      elim .snd .snd x y = refl

  module _ (N : Monoid ℓ''')
    (iA : A → ⟨ N ⟩)
    (iB : B → MonoidHom N N)
    (iC : C → MonoidHom (N ^op) N)
    where
    rec : MonoidHom FM N
    rec = unWkn {ϕ = idMon _} s where
      s : Section (wkn FM N)
      s = elim (wkn FM N) iA
        (λ b → wknHom (coHom b) (iB b))
        λ c → wknHom (opHom c) (iC c)


  -- Case split (no recursion)
  module _
    (Mᴰ : Monoidᴰ FM ℓᴰ)
    -- (σᴰ : ∀ x → LocalSection (σ x) Mᴰ)
    where
    private
      module Mᴰ = Monoidᴰ Mᴰ
    module _
      (iA : ∀ a → Mᴰ.eltᴰ ⟦ a ⟧)
      (iB : ∀ b → LocalSection (coHom b) Mᴰ)
      (iC : ∀ c → LocalSection (opHom c) Mᴰ)
      where

      elimCases : Section Mᴰ
      elimCases .fst = f where
        f : ∀ x → Mᴰ.eltᴰ x
        f ⟦ a ⟧ = iA a
        f (⟦ b ⟧co x) = iB b .fst x
        f (⟦ c ⟧op x) = iC c .fst x
        f ε = Mᴰ.εᴰ
        f (x · y) = f x Mᴰ.·ᴰ f y
        f (identityᵣ x i) = Mᴰ.·IdRᴰ (f x) i
        f (identityₗ x i) = Mᴰ.·IdLᴰ (f x) i
        f (assoc x y z i) = Mᴰ.·Assocᴰ (f x) (f y) (f z) i
        f (co-ε b i) = iB b .snd .fst i
        f (co-· b x y i) = iB b .snd .snd x y i
        f (op-ε c i) = iC c .snd .fst i
        f (op-· c x y i) = iC c .snd .snd x y i
        f (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2 (λ x → Mᴰ.isSetEltᴰ)
          (f x) (f y)
          (cong f p) (cong f q)
          (trunc x y p q)
          i j
      elimCases .snd .fst = refl
      elimCases .snd .snd x y = refl



-- Here's a local elimination principle but only when we don't use the coHom/opHom
module _ (A : Type ℓ) where
  FMsimp : Monoid ℓ
  FMsimp = FM A ⊥ ⊥

  module _ {M : Monoid ℓ'}
      (Mᴰ : Monoidᴰ M ℓᴰ')
      (ϕ : MonoidHom FMsimp M) where
    private
      module Mᴰ = Monoidᴰ Mᴰ
    module _ (iA : ∀ a → Mᴰ.eltᴰ ( ϕ .fst (gen _ _ _ a))) where
      elimLocal : LocalSection ϕ Mᴰ
      elimLocal =
        _gs⋆h_
          {Mᴰ = Reindex {M = FMsimp}{N = M} ϕ Mᴰ}
          {Nᴰ = Mᴰ}
          {ϕ = ϕ}
          (elim A ⊥ ⊥ (Reindex ϕ Mᴰ) iA Empty.elim Empty.elim) (π ϕ Mᴰ)
