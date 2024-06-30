{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}



open import Common.Later

module Semantics.Concrete.DynPerturb (k : Clock) where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup

open import Cubical.Data.Nat hiding (_·_)

open import Semantics.Concrete.Dyn k
open import Semantics.Concrete.Predomains.PrePerturbations k


private variable
  ℓ : Level
  A : Type ℓ

private
  ▹_ : {ℓ : Level} → Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

-------------------------
-- Perturbations for Dyn
-------------------------

-- The monoid of perturbations for Dyn is defined as a
-- higher-inductive type.

-- Recall that Dyn ≅ ℕ + (Dyn × Dyn) + (Dyn ==> UF Dyn)
--                 ≅ ℕ + (Dyn × Dyn) + U (Dyn ⟶ F Dyn)
--                 
-- We define PtbD to be the least solution (i.e. initial algebra) in
-- the category of monoids to the equation
--
-- PtbD ≅ (PtbD ⊕ PtbD) ⊕ (ℕ ⊕ PtbD ^op ⊕ ℕ ⊕ PtbD)
--
data |PtbD| : Type where
  ε : |PtbD|
  _·_ : |PtbD| → |PtbD| → |PtbD|
  identityᵣ : ∀ x → x · ε ≡ x
  identityₗ  :  ∀ x → ε · x ≡ x
  assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
  trunc : isSet |PtbD|
 
  ⟦_⟧×-left    : |PtbD| → |PtbD|
  ⟦_⟧×-right   : |PtbD| → |PtbD|
  ⟦_⟧arr-left  : |PtbD| → |PtbD|
  ⟦_⟧arr-right : |PtbD| → |PtbD|
  ⟦_⟧arr-U    : |PtbD|
  ⟦_⟧arr-F    : |PtbD|

  id-×-left    : ⟦ ε ⟧×-left ≡ ε
  id-×-right   : ⟦ ε ⟧×-right ≡ ε
  id-arr-left  : ⟦ ε ⟧arr-left ≡ ε
  id-arr-right : ⟦ ε ⟧arr-right ≡ ε

  comp-×-left    : ∀ p p' → ⟦ p · p' ⟧×-left    ≡ (⟦ p ⟧×-left · ⟦ p' ⟧×-left)
  comp-×-right   : ∀ p p' → ⟦ p · p' ⟧×-right   ≡ (⟦ p ⟧×-right · ⟦ p' ⟧×-right)
  -- arr-left is contravariant
  comp-arr-left  : ∀ p p' → ⟦ p · p' ⟧arr-left  ≡ (⟦ p' ⟧arr-left · ⟦ p ⟧arr-left)
  comp-arr-right : ∀ p p' → ⟦ p · p' ⟧arr-right ≡ (⟦ p ⟧arr-right · ⟦ p' ⟧arr-right)

open MonoidStr
PtbD : Monoid ℓ-zero
PtbD .fst = |PtbD|
PtbD .snd .MonoidStr.ε = |PtbD|.ε
PtbD .snd .MonoidStr._·_ = |PtbD|._·_
PtbD .snd .isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set = trunc
PtbD .snd .isMonoid .IsMonoid.isSemigroup .IsSemigroup.·Assoc = assoc
PtbD .snd .isMonoid .IsMonoid.·IdR = identityᵣ
PtbD .snd .isMonoid .IsMonoid.·IdL = identityₗ

-- recursion principle: PtbD is the initial algebra of the above functor
module _
       {M : Monoid ℓ}
       (×-left : MonoidHom M M)
       (×-right : MonoidHom M M)
       (arr-left : MonoidHom (M ^op) M)
       (arr-right : MonoidHom M M)
       (arr-U : ⟨ M ⟩)
       (arr-F : ⟨ M ⟩)
       where
  private
    |M| = ⟨ M ⟩
    module M = MonoidStr (M .snd)
    open IsSemigroup
    open IsMonoidHom

    |rec| : |PtbD| → |M|
    |rec| |PtbD|.ε = M.ε
    |rec| (p |PtbD|.· q) = (|rec| p) M.· (|rec| q)
    |rec| (identityᵣ p i) = M.·IdR (|rec| p) i
    |rec| (identityₗ p i) = M.·IdL (|rec| p) i
    |rec| (assoc p q r i) = M.isSemigroup .·Assoc (|rec| p) (|rec| q) (|rec| r) i
    |rec| (trunc p q p≡q p≡q' i j) =
      M.isSemigroup .is-set (|rec| p) (|rec| q) (cong |rec| p≡q) (cong |rec| p≡q') i j
    |rec| ⟦ p ⟧×-left = ×-left .fst (|rec| p)
    |rec| (id-×-left i) = ×-left .snd .presε i
    |rec| (comp-×-left p q i) = ×-left .snd .pres· (|rec| p) (|rec| q) i
    |rec| ⟦ p ⟧×-right = ×-right .fst (|rec| p)
    |rec| (id-×-right i) = ×-right .snd .presε i
    |rec| (comp-×-right p q i) = ×-right .snd .pres· (|rec| p) (|rec| q) i
    |rec| ⟦ p ⟧arr-left = arr-left .fst (|rec| p)
    |rec| (id-arr-left i) = arr-left .snd .presε i
    |rec| (comp-arr-left p q i) = arr-left .snd .pres· (|rec| q) (|rec| p) i
    |rec| ⟦ p ⟧arr-right = arr-right .fst (|rec| p)
    |rec| (id-arr-right i) = arr-right .snd .presε i
    |rec| (comp-arr-right p q i) = arr-right .snd .pres· (|rec| p) (|rec| q) i
    |rec| ⟦_⟧arr-U = arr-U
    |rec| ⟦_⟧arr-F = arr-F
  rec : MonoidHom PtbD M
  rec .fst = |rec|
  rec .snd .presε = refl
  rec .snd .pres· x y = refl

open DynDef {ℓ-zero}
-- Monoid homomorphism into the endomorphisms on Dyn
ι-dyn : MonoidHom PtbD (Endo Dyn)
ι-dyn = rec
  -- ×-l
  {!!}
  -- ×-r
  {!!}
  -- arr-dom
  {!!}
  -- arr-cod
  {!!}
  -- U
  {!!}
  -- F
  {!!}


-- The push-pull property for the three relations inj-nat, inj-prod, and inj-arr



