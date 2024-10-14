{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
module Semantics.Concrete.Perturbation.Relation.Constructions.Sigma (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_)
open import Cubical.Relation.Nullary.Base


open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.FreeProduct.Indexed as Indexed
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Sigma

open import Cubical.Relation.Nullary

open import Common.Common
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions hiding (π1; π2)
open import Semantics.Concrete.Predomain.Relation as PRel hiding (ΣR)
open import Semantics.Concrete.Predomain.Square

open import Semantics.Concrete.Perturbation.Semantic k
open import Semantics.Concrete.Types k as Types hiding (U; F; _⟶_)
open import Semantics.Concrete.Perturbation.Relation.Base k

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓ≤' ℓ≈' ℓM' : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂ : Level
    ℓc ℓc' ℓd ℓd' : Level
    ℓX : Level

module _
  (X : DiscreteTy ℓX)
  {A₁ : ⟨ X ⟩ → ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁}
  {A₂ : ⟨ X ⟩ → ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂}
  (R⟨_⟩ : (x : ⟨ X ⟩) → VRelPP (A₁ x) (A₂ x) ℓc)
  where

  private
  
    X-as-set : hSet _
    X-as-set = ⟨ X ⟩ , Discrete→isSet (X .snd)

    |A₁| : ⟨ X ⟩ → Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁
    |A₁| = ValType→Predomain ∘ A₁
   
    |A₂| : ⟨ X ⟩ → Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂
    |A₂| = ValType→Predomain ∘ A₂

    |R| : _
    |R| = VRelPP→PredomainRel ∘ R⟨_⟩

    Σ-R : PRel (ΣP X-as-set |A₁|) (ΣP X-as-set |A₂|) (ℓ-max ℓX ℓc)
    Σ-R = PRel.ΣR X-as-set |A₁| |A₂| |R|
  

  opaque
    unfolding ⊕ᵢ σ Indexed.rec Indexed.elim
    ΣV-Sq : 
      ∀ x →
      (m₁ : ⟨ PtbV (A₁ x) ⟩) (m₂ : ⟨ PtbV (A₂ x) ⟩)
      (α : VRelPtbSq (A₁ x) (A₂ x) (VRelPP→PredomainRel R⟨ x ⟩) m₁ m₂) →
      VRelPtbSq
        (ΣV X A₁) (ΣV X A₂) Σ-R
        (σ _ _ _ .fst m₁) (σ _ _ _ .fst m₂)
    ΣV-Sq x m₁ m₂ α = sq
      where
        dec→sq : ∀ y → (d : Dec (x ≡ y)) →
               PSq (VRelPP→PredomainRel R⟨ y ⟩) (VRelPP→PredomainRel R⟨ y ⟩)
                    (PtbIfEqual x (interpV (A₁ x) .fst m₁) y d .fst)
                    (PtbIfEqual x (interpV (A₂ x) .fst m₂) y d .fst)
        dec→sq y (yes eq) =
          λ a₁ a₂ a₁Ra₂ → predomrel-transport
                     (λ i → ValType→Predomain (A₁ (eq i)))
                     (λ i → ValType→Predomain (A₂ (eq i)))
                     (λ i → VRelPP→PredomainRel R⟨ eq i ⟩)
                     _ _ (α _ _ (predomrel-transport
                       (sym (λ i → ValType→Predomain (A₁ (eq i))))
                       (sym (λ i → ValType→Predomain (A₂ (eq i))))
                       (symP (λ i → VRelPP→PredomainRel R⟨ eq i ⟩))
                       a₁ a₂ a₁Ra₂))
        dec→sq y (no neq) = Predom-IdSqV (VRelPP→PredomainRel R⟨ y ⟩)

        sq :  PSq Σ-R Σ-R                   
                   (Σ-mor X-as-set _ _ (λ y → PtbIfEqual x (interpV (A₁ x) .fst m₁) y (X .snd x y) .fst))
                   (Σ-mor X-as-set _ _ (λ y → PtbIfEqual x (interpV (A₂ x) .fst m₂) y (X .snd x y) .fst))
        sq = Σ-Sq X-as-set _ _ _ _ |R| |R| _ _ (λ y → dec→sq y (X .snd x y)) 
        

ΣR : (X : DiscreteTy ℓX) →
  (A₁ : ⟨ X ⟩ → ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁) →
  (A₂ : ⟨ X ⟩ → ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂) →
  (R⟨_⟩ : (x : ⟨ X ⟩) → VRelPP (A₁ x) (A₂ x) ℓc) →
  VRelPP (ΣV X A₁) (ΣV X A₂) (ℓ-max ℓX ℓc)

-- Predomain relation
ΣR X A₁ A₂ R⟨_⟩ = mkVRelPP _ _
  Sigma-rel Sigma-push Sigma-pull

  where

    X-as-set : hSet _
    X-as-set = ⟨ X ⟩ , Discrete→isSet (X .snd)

    Sigma-rel = (PRel.ΣR X-as-set (ValType→Predomain ∘ A₁) (ValType→Predomain ∘ A₂) (VRelPP→PredomainRel ∘ R⟨_⟩))

    Sigma-push : PushV (ΣV X A₁) (ΣV X A₂) Sigma-rel
    Sigma-push = Indexed.elim ⟨ X ⟩ (PtbV ∘ A₁) (Σl (VRelPtb (ΣV X A₁) (ΣV X A₂) Sigma-rel)) push-x
      where
        push-x : ∀ x → LocalSection ((σ ⟨ X ⟩ (PtbV ∘ A₁) x)) (Σl (VRelPtb (ΣV X A₁) (ΣV X A₂) _))
        push-x x = corecL {Mᴰ = VRelPtb (ΣV X A₁) (ΣV X A₂) Sigma-rel}
          ((σ _ _ x) ∘hom pushV R⟨ x ⟩)
          (corecVRelPtb (λ m → ΣV-Sq X R⟨_⟩ x m ((pushV R⟨ x ⟩) .fst m) (pushVSq R⟨ x ⟩ m)))

    Sigma-pull :  PullV (ΣV X A₁) (ΣV X A₂) Sigma-rel
    Sigma-pull = Indexed.elim ⟨ X ⟩ (PtbV ∘ A₂) (Σr (VRelPtb (ΣV X A₁) (ΣV X A₂) Sigma-rel)) pull-x
      where
        pull-x : ∀ x → LocalSection ((σ ⟨ X ⟩ (PtbV ∘ A₂) x)) (Σr (VRelPtb (ΣV X A₁) (ΣV X A₂) _))
        pull-x x = corecR {Mᴰ = VRelPtb (ΣV X A₁) (ΣV X A₂) Sigma-rel}
          ((σ _ _ x) ∘hom pullV R⟨ x ⟩)
          (corecVRelPtb (λ m → ΣV-Sq X R⟨_⟩ x ((pullV R⟨ x ⟩) .fst m) m (pullVSq R⟨ x ⟩ m)))
