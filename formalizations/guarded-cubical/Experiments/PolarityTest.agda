{-# OPTIONS --polarity #-}

module Experiments.PolarityTest where

open import Agda.Builtin.Sigma

OrdSet : Set₁
OrdSet = Σ Set (λ X →
  Σ (X → X → Set) λ f → ∀ (x : X) → f x x)

⟨_⟩ : OrdSet → Set
⟨ A ⟩ = A .fst

OrdSet→≤ : (A : OrdSet) → (⟨ A ⟩ → ⟨ A ⟩ → Set)
OrdSet→≤ A = A .snd .fst

OrdSet→refl : (A : OrdSet) → (x : ⟨ A ⟩) → OrdSet→≤ A x x
OrdSet→refl A = A .snd .snd


module _ (F : @++ OrdSet → OrdSet) where

  -- We define the OrdSet Mu mutually with its underlying type
  Mu : OrdSet

  -- The underlying type of Mu (notice the reference to Mu as an OrdSet)
  data |Mu| : Set where
    inn : ⟨ F Mu ⟩ → |Mu|

  -- The ordering relation on Mu (again notice the reference to the OrdSet Mu)
  data _≤Mu_ : |Mu| → |Mu| → Set where
    ≤inn : ∀ (x y : F Mu .fst)
      → (F Mu) .snd .fst x y
      → (inn x) ≤Mu (inn y)

  _≤Mu'_ : |Mu| → |Mu| → Set
  inn x ≤Mu' inn y = F Mu .snd .fst x y

  -- The proof that the ordering relation is reflexive
  {-# TERMINATING #-}
  isRefl≤Mu : ∀ x → x ≤Mu x
  isRefl≤Mu (inn x) = ≤inn x x ((F Mu) .snd .snd x)

  isRefl≤Mu' : ∀ x → x ≤Mu' x
  isRefl≤Mu' (inn x) = F Mu .snd .snd x
 

  -- Definition of Mu as an OrdSet
  Mu .fst = |Mu|
  Mu .snd .fst = _≤Mu'_
  Mu .snd .snd = isRefl≤Mu'



{-
record OrdSet : Set₁ where
  field
    X : Set
    _≤_ : X → X → Set
    isRefl : ∀ x → x ≤ x

open OrdSet

⟨_⟩ : OrdSet → Set
⟨ A ⟩ = A .X


module _ (F : @++ OrdSet → OrdSet) where

  -- We define the OrdSet Mu mutually with its underlying type
  Mu : OrdSet

  -- The underlying type of Mu (notice the reference to Mu as an OrdSet)
  data |Mu| : Set where
    inn : ⟨ F Mu ⟩ → |Mu|

  -- The ordering relation on Mu (again notice the reference to the OrdSet Mu)
  data _≤Mu_ : |Mu| → |Mu| → Set where
    ≤inn : ∀ (x y : ⟨ F Mu ⟩)
      → (F Mu) ._≤_ x y
      → (inn x) ≤Mu (inn y)

  -- The proof that the ordering relation is reflexive
  {-# TERMINATING #-}
  isRefl≤Mu : ∀ x → x ≤Mu x
  isRefl≤Mu (inn x) = ≤inn x x (F Mu .isRefl x)
 

  -- Definition of Mu as an OrdSet
  Mu .X = |Mu|
  Mu ._≤_ = _≤Mu_
  Mu .isRefl = isRefl≤Mu
-}
