{-# OPTIONS --cubical --rewriting --guarded #-}
open import Later

module GuardedCat (k : Clock) where


open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint

variable
  ℓ ℓ' : Level

▸c : ∀ (C : ▹ k , Category ℓ ℓ') → Category ℓ ℓ'
▸c C = record
         { ob = ▸ λ t → Category.ob (C t)
         ; Hom[_,_] = λ a b → ▸ (λ t → Category.Hom[_,_] (C t) (a t) (b t))
         ; id = λ t → Category.id (C t)
         ; _⋆_ = λ f g t → Category._⋆_ (C t) (f t) (g t)
         ; ⋆IdL = λ f i t → Category.⋆IdL (C t) (f t) i
         ; ⋆IdR = λ f i t → Category.⋆IdR (C t) (f t) i
         ; ⋆Assoc = λ f g h i t → Category.⋆Assoc (C t) (f t) (g t) (h t) i
         ; isSetHom = λ x y → λ p:x≡y q:x≡y i j t → Category.isSetHom (C t) (x t) (y t) (λ k → p:x≡y k t) ((λ k → q:x≡y k t)) i j
         }

next-c : ∀ (C : Category ℓ ℓ') → Functor C (▸c (next C))
next-c C = record
  { F-ob = λ x t → x
  ; F-hom = λ z t → z
  ; F-id = λ i t → C.id
  ; F-seq = λ f g i t → f ⋆ g
  }
  where module C = Category C
        open C

record GuardedCat : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  open NaturalBijection
  field
    C : Category ℓ ℓ'
    θ-UMP : isRightAdjoint (next-c C)

-- Conjecture: Every GuardedCat has an initial object ⊥ = fix θ₀
