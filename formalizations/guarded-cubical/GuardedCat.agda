{-# OPTIONS --cubical --rewriting --guarded #-}
open import Later

module GuardedCat (k : Clock) where


open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Constructions.BinProduct

open import Cubical.Categories.Instances.Sets

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


▹c : ∀ (C : Category ℓ ℓ') → Category ℓ ℓ'
▹c C = ▸c (next C)

▹F : ∀ {C D : Category ℓ ℓ'} → Functor C D → Functor (▹c C) (▹c D)
▹F F = record
  { F-ob = λ x t → F-ob (x t)
  ; F-hom = λ x t → F-hom (x t)
  ; F-id = λ i t → F-id i
  ; F-seq = λ f g i t → F-seq (f t) (g t) i
  }
  where module F = Functor F
        open F

next-c : ∀ (C : Category ℓ ℓ') → Functor C (▹c C)
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


PROF : (ℓ' : Level) → (C : Category ℓ ℓ') (D : Category ℓ ℓ') → Category (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
PROF ℓ' C D = FUNCTOR ((C ^op) × D) (SET ℓ')

Profunctor : (C : Category ℓ ℓ') (D : Category ℓ ℓ') → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Profunctor C D = Category.ob (PROF _ C D)

-- e : A → B
-- p : B → ▹ A

-- e a ~> b
-- iff (next a) ~> p b
-- defines e as a relative left adjoint
-- doesn't uniquely determine p

-- a▹ ~> p b
-- iff ▹ (λ t → e (a▹ t) ~> b)
-- iff (▹ e) a▹ ~> (next b)
-- defines p as a relative right adjoint
-- doesn't uniquely determine e

-- e seems more fundamental than p tbh...but which of these holds period?


-- e : A → B
-- p : B → Option (▹ A)

-- e a ~> b
-- iff some (next a) ~> p b
-- defines e as a relative left adjoint
-- doesn't uniquely determine p

-- a?▹ ~> p b
-- iff Option (▹ e) a▹ ~> (next b)
-- defines p as a relative right adjoint
-- doesn't uniquely determine e

-- ▹p : Profunctor C D → (Profunctor (▹ C) (▹ D))
