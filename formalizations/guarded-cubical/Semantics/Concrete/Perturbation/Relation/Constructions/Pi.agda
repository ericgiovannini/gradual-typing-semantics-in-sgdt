{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
module Semantics.Concrete.Perturbation.Relation.Constructions.Pi (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_)
open import Cubical.Relation.Nullary.Base


open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Sigma
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.FreeProduct.Indexed as Indexed

open import Cubical.Relation.Nullary

open import Common.Common
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions hiding (π1; π2)
open import Semantics.Concrete.Predomain.Relation as PRel hiding (ΣR ; ΠR)
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

  opaque
    unfolding ⊕ᵢ σ Indexed.rec Indexed.elim
    ΠV-Sq : 
      ∀ x →
      (m₁ : ⟨ PtbV (A₁ x) ⟩) (m₂ : ⟨ PtbV (A₂ x) ⟩)
      (α : VRelPtbSq (A₁ x) (A₂ x) (VRelPP→PredomainRel R⟨ x ⟩) m₁ m₂) →
      VRelPtbSq
        (ΠV X A₁) (ΠV X A₂)
        (PRel.ΠR (X .fst) (ValType→Predomain ∘ A₁) (ValType→Predomain ∘ A₂) (VRelPP→PredomainRel ∘ R⟨_⟩))
        (σ _ _ _ .fst m₁) (σ _ _ _ .fst m₂)
    ΠV-Sq x m₁ m₂ α = sq
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

        sq :  PSq (PRel.ΠR ⟨ X ⟩ (ValType→Predomain ∘ A₁) (ValType→Predomain ∘ A₂) (VRelPP→PredomainRel ∘ R⟨_⟩))
                   (PRel.ΠR ⟨ X ⟩ (ValType→Predomain ∘ A₁) (ValType→Predomain ∘ A₂) (VRelPP→PredomainRel ∘ R⟨_⟩))
                   (Π-mor ⟨ X ⟩ _ _ (λ y → PtbIfEqual x (interpV (A₁ x) .fst m₁) y (X .snd x y) .fst))
                   (Π-mor ⟨ X ⟩ _ _ (λ y → PtbIfEqual x (interpV (A₂ x) .fst m₂) y (X .snd x y) .fst))
        sq = Π-Sq ⟨ X ⟩ _ _ _ _ _ _ _ _ (λ y → dec→sq y (X .snd x y)) 
        

{-
module _
  (X : DiscreteTy ℓX)
  {A₁ : ⟨ X ⟩ → ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁}
  {A₂ : ⟨ X ⟩ → ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂}
  (R⟨_⟩ : (x : ⟨ X ⟩) → VRelPP (A₁ x) (A₂ x) ℓc)
  (m₁ : ∀ y → ⟨ PtbV (A₁ y) ⟩) (m₂ : ∀ y → ⟨ PtbV (A₂ y) ⟩)
  where

  opaque
    unfolding ⊕ᵢ σ Indexed.rec Indexed.elim
    ΠV-Sq : (α : ∀ y → VRelPtbSq (A₁ y) (A₂ y) (VRelPP→PredomainRel R⟨ y ⟩) (m₁ y) (m₂ y)) →
      ∀ x →
      VRelPtbSq
        (ΠV X A₁) (ΠV X A₂)
        (PRel.ΠR (X .fst) (ValType→Predomain ∘ A₁) (ValType→Predomain ∘ A₂) (VRelPP→PredomainRel ∘ R⟨_⟩))
        (σ _ _ _ .fst (m₁ x)) (σ _ _ _ .fst (m₂ x))
    ΠV-Sq α x = sq
      where
        dec→sq : ∀ y → (d : Dec (x ≡ y)) →
               PSq (VRelPP→PredomainRel R⟨ y ⟩) (VRelPP→PredomainRel R⟨ y ⟩)
                    (PtbIfEqual x (interpV (A₁ x) .fst (m₁ x)) y d .fst)
                    (PtbIfEqual x (interpV (A₂ x) .fst (m₂ x)) y d .fst)
        dec→sq y (yes eq) =
          λ a₁ a₂ a₁Ra₂ → predomrel-transport
                     (λ i → ValType→Predomain (A₁ (eq i)))
                     (λ i → ValType→Predomain (A₂ (eq i)))
                     (λ i → VRelPP→PredomainRel R⟨ eq i ⟩)
                     _ _ (α x _ _ (predomrel-transport
                       (sym (λ i → ValType→Predomain (A₁ (eq i))))
                       (sym (λ i → ValType→Predomain (A₂ (eq i))))
                       (symP (λ i → VRelPP→PredomainRel R⟨ eq i ⟩))
                       a₁ a₂ a₁Ra₂))
        dec→sq y (no neq) = Predom-IdSqV (VRelPP→PredomainRel R⟨ y ⟩)

        sq :  PSq (PRel.ΠR ⟨ X ⟩ (ValType→Predomain ∘ A₁) (ValType→Predomain ∘ A₂) (VRelPP→PredomainRel ∘ R⟨_⟩))
                   (PRel.ΠR ⟨ X ⟩ (ValType→Predomain ∘ A₁) (ValType→Predomain ∘ A₂) (VRelPP→PredomainRel ∘ R⟨_⟩))
                   (Π-mor ⟨ X ⟩ _ _ (λ y → PtbIfEqual x (interpV (A₁ x) .fst (m₁ x)) y (X .snd x y) .fst))
                   (Π-mor ⟨ X ⟩ _ _ (λ y → PtbIfEqual x (interpV (A₂ x) .fst (m₂ x)) y (X .snd x y) .fst))
        sq = Π-Sq ⟨ X ⟩ _ _ _ _ _ _ _ _ (λ y → dec→sq y (X .snd x y)) 
        
-}




ΠR : (X : DiscreteTy ℓX) →
  (A₁ : ⟨ X ⟩ → ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁) →
  (A₂ : ⟨ X ⟩ → ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂) →
  (R⟨_⟩ : (x : ⟨ X ⟩) → VRelPP (A₁ x) (A₂ x) ℓc) →
  VRelPP (ΠV X A₁) (ΠV X A₂) (ℓ-max ℓX ℓc)

-- Predomain relation
ΠR X A₁ A₂ R⟨_⟩ = mkVRelPP _ _
  Pi-rel Pi-push Pi-pull

  where
    Pi-rel = (PRel.ΠR ⟨ X ⟩ (ValType→Predomain ∘ A₁) (ValType→Predomain ∘ A₂) (VRelPP→PredomainRel ∘ R⟨_⟩))

    Pi-push : PushV (ΠV X A₁) (ΠV X A₂) Pi-rel
    Pi-push = Indexed.elim ⟨ X ⟩ (λ y → PtbV (A₁ y)) (Σl (VRelPtb (ΠV X A₁) (ΠV X A₂) Pi-rel)) push-x -- suffices to provide a push for each x
      where
        push-x : ∀ (x : ⟨ X ⟩) → LocalSection (σ ⟨ X ⟩ (λ y → PtbV (A₁ y)) x) (Σl (VRelPtb (ΠV X A₁) (ΠV X A₂) _))
        push-x x = corecL {Mᴰ = VRelPtb (ΠV X A₁) (ΠV X A₂) Pi-rel}
          ((σ ⟨ X ⟩ (λ y → PtbV (A₂ y)) x) ∘hom pushV R⟨ x ⟩)
          -- (corecVRelPtb λ m₁ → ΠV-Sq ? ? ? ? ? ?)
          (corecVRelPtb λ m as bs as-R-bs y →
            ΠV-Sq X R⟨_⟩ x m ((pushV R⟨ x ⟩) .fst m) (pushVSq R⟨ x ⟩ m) as bs as-R-bs y)
            -- Interesting technical note: if in the argument to
            -- corecVRelPtb, we type λ m → ? and then try to refine
            -- `ΠV-Sq` inside the hole, Agda gets stuck.  Similarly if
            -- we type ΠV-Sq ? ? ? ? ? ? in the hole and try to give
            -- it, Agda also gets stuck. If we manually type
            -- ΠV-Sq ? ? ? ? ? ? and load the file, Agda also gets stuck.
            -- 
            -- The issue seems to be related to R⟨_⟩, since if we
            -- fill that in and leave the rest as ?'s the issue does not occur.

    Pi-pull : PullV (ΠV X A₁) (ΠV X A₂) Pi-rel

    Pi-pull = Indexed.elim ⟨ X ⟩ (λ y → PtbV (A₂ y)) (Σr (VRelPtb (ΠV X A₁) (ΠV X A₂) Pi-rel)) pull-x
      where
       pull-x : ∀ x → LocalSection (σ _ _ x) (Σr (VRelPtb (ΠV X A₁) (ΠV X A₂) _))
       pull-x x = corecR {Mᴰ = VRelPtb (ΠV X A₁) (ΠV X A₂) Pi-rel}
         ((σ ⟨ X ⟩ (λ y → PtbV (A₁ y)) x) ∘hom pullV R⟨ x ⟩)
         (corecVRelPtb (λ m → ΠV-Sq X R⟨_⟩ x ((pullV R⟨ x ⟩) .fst m) m (pullVSq R⟨ x ⟩ m)))

       pull : ∀ x → MonoidHom (PtbV (A₂ x)) (⊕ᵢ ⟨ X ⟩ (λ x → PtbV (A₁ x)))                               
       pull x = (σ _ _ x ∘hom pullV R⟨ x ⟩)

{-
       opaque
         pull-sq' : ∀ x (m' : ⟨ PtbV (A₂ x) ⟩) →
           VRelPtbSq
             (ΠV X A₁) (ΠV X A₂)
             (PRel.ΠR (X .fst) (ValType→Predomain ∘ A₁) (ValType→Predomain ∘ A₂) (VRelPP→PredomainRel ∘ R⟨_⟩))
             (pull x .fst m') (σ _ _ x .fst m')
         pull-sq' x m' = Π-Sq ⟨ X ⟩ _ _ _ _ _ _
           (λ y → PtbIfEqual x (interpV (A₁ x) .fst (pullV R⟨ x ⟩ .fst m')) y {!X .snd x y!} .fst)
           (λ y → PtbIfEqual x (interpV (A₂ x) .fst m') y {!!} .fst)
           {!!} 
           --   (λ y → dec→sq y (X .snd x y))
           where
             dec→sq : ∀ y → (d : Dec (x ≡ y)) →
               PSq (VRelPP→PredomainRel R⟨ y ⟩) (VRelPP→PredomainRel R⟨ y ⟩)
                    (PtbIfEqual x (interpV (A₁ x) .fst (pullV R⟨ x ⟩ .fst m')) y d .fst)
                    (PtbIfEqual x (interpV (A₂ x) .fst m') y d .fst)
             dec→sq y (yes eq) = sq
               where
                 sq : PSq (VRelPP→PredomainRel R⟨ y ⟩)
                           (VRelPP→PredomainRel R⟨ y ⟩)
                           (subst (λ z → ⟨ Endo _ ⟩) eq (interpV (A₁ x) .fst (pullV R⟨ x ⟩ .fst m')) .fst)
                           (subst (λ z → ⟨ Endo _ ⟩) eq (interpV (A₂ x) .fst m') .fst)
                 sq a₁ a₂ a₁Ra₂ =
                   predomrel-transport
                     (λ i → ValType→Predomain (A₁ (eq i)))
                     (λ i → ValType→Predomain (A₂ (eq i)))
                     (λ i → VRelPP→PredomainRel R⟨ eq i ⟩)
                     _ _ (pullVSq R⟨ x ⟩ m' _ _ (predomrel-transport
                       (sym (λ i → ValType→Predomain (A₁ (eq i))))
                       (sym (λ i → ValType→Predomain (A₂ (eq i))))
                       (symP (λ i → VRelPP→PredomainRel R⟨ eq i ⟩))
                       a₁ a₂ a₁Ra₂))
             dec→sq y (no neq) = Predom-IdSqV (VRelPP→PredomainRel R⟨ y ⟩)

-}
      

  


{-
-- Push
  ΠR X A₁ A₂ R⟨_⟩ .snd .fst = Indexed.elim _ _ _ push-x -- suffices to provide a push for each x
    where
      push-x : ∀ (x : ⟨ X ⟩) → LocalSection (σ _ _ x) (Σl (VRelPtb (ΠV X A₁) (ΠV X A₂) _))
      push-x x = corecL
        (σ _ _ x ∘hom pushV R⟨ x ⟩)
        (corecVRelPtb λ m as bs as-R-bs y → let foo = pushVSq R⟨ x ⟩ m in {!!})


-- Pull
Indexed.elim _ _ _ pull-x
  where

    pull : ∀ x → MonoidHom (PtbV (A₂ x)) (⊕ᵢ ⟨ X ⟩ (λ x → PtbV (A₁ x)))                               
    pull x = (σ _ _ x ∘hom pullV R⟨ x ⟩)

    pull-sq' : ∀ x (m' : ⟨ PtbV (A₂ x) ⟩) →
      VRelPtbSq
        (ΠV X A₁) (ΠV X A₂)
        (PRel.ΠR (X .fst) (ValType→Predomain ∘ A₁) (ValType→Predomain ∘ A₂) (VRelPP→PredomainRel ∘ R⟨_⟩))
        (pull x .fst m') (σ _ _ x .fst m')
    pull-sq' x m' = Π-Sq ⟨ X ⟩ _ _ _ _ _ _
      (λ y → PtbIfEqual x (interpV (A₁ x) .fst (pullV R⟨ x ⟩ .fst m')) y _ .fst)
      (λ y → PtbIfEqual x (interpV (A₂ x) .fst m') y _ .fst)
      (λ y → dec→sq y (X .snd x y))
      where
        dec→sq : ∀ y → (d : Dec (x ≡ y)) →
          PSq (VRelPP→PredomainRel R⟨ y ⟩) (VRelPP→PredomainRel R⟨ y ⟩)
               (PtbIfEqual x (interpV (A₁ x) .fst (pullV R⟨ x ⟩ .fst m')) y d .fst)
               (PtbIfEqual x (interpV (A₂ x) .fst m') y d .fst)
        dec→sq y (yes eq) = sq
          where
            sq : PSq (VRelPP→PredomainRel R⟨ y ⟩)
                      (VRelPP→PredomainRel R⟨ y ⟩)
                      (subst (λ z → ⟨ Endo _ ⟩) eq (interpV (A₁ x) .fst (pullV R⟨ x ⟩ .fst m')) .fst)
                      (subst (λ z → ⟨ Endo _ ⟩) eq (interpV (A₂ x) .fst m') .fst)
            sq a₁ a₂ a₁Ra₂ =
              predomrel-transport
                (λ i → ValType→Predomain (A₁ (eq i)))
                (λ i → ValType→Predomain (A₂ (eq i)))
                (λ i → VRelPP→PredomainRel R⟨ eq i ⟩)
                _ _ (pullVSq R⟨ x ⟩ m' _ _ (predomrel-transport
                  (sym (λ i → ValType→Predomain (A₁ (eq i))))
                  (sym (λ i → ValType→Predomain (A₂ (eq i))))
                  (symP (λ i → VRelPP→PredomainRel R⟨ eq i ⟩))
                  a₁ a₂ a₁Ra₂))
        dec→sq y (no neq) = Predom-IdSqV (R⟨ y ⟩ .fst)


    pull-x : ∀ x → LocalSection (σ _ _ x) (Σr (VRelPtb (ΠV X A₁) (ΠV X A₂) _))
    pull-x x = corecR (pull x) (corecVRelPtb (λ m' → pull-sq' x m'))
{-
    pull-x x = corecR (σ _ _ x ∘hom pullV R⟨ x ⟩)
      (corecVRelPtb {!!})
        where
          goal : ∀ (m : ⟨ PtbV (A₂ x)⟩) (as : (∀ y → ⟨ A₁ y ⟩)) (bs : (∀ y → ⟨ A₂ y ⟩))
                   (as-R-bs : ∀ y → R⟨ y ⟩ .fst .PRel.R (as y) (bs y))
                   (y : ⟨ X ⟩) →
                   {!!}
          goal m as bs as-R-bs y = {!!}

          goal' : ∀ (m' : ⟨ PtbV (A₂ x) ⟩) → VRelPtbSq
            (ΠV X A₁) (ΠV X A₂)
            (PRel.ΠR (X .fst) (ValType→Predomain ∘ A₁) (ValType→Predomain ∘ A₂) (VRelPP→PredomainRel ∘ R⟨_⟩))
            ((σ _ _ x ∘hom pullV R⟨ x ⟩) .fst m') (gen x m')
          goal' m' = {!m'!}

-}

-}
