{-# OPTIONS --polarity #-}


module Cubical.Algebra.Structures.Experiments.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Function

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Fin
open import Cubical.Data.Sigma

open import Cubical.Algebra.Structures.Experiments.BaseAlt3

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓᴰ ℓᴰ' : Level
    ℓM ℓN ℓP ℓMᴰ ℓNᴰ ℓPᴰ : Level


module _ {ℓX ℓar : Level}
  (X : Type ℓX) (ar : X → Type ℓar)
  where

  open Struct X ar

  module _ {ℓE ℓq : Level}
    (E : Type ℓE)
    (q : E → Type ℓq)
    (lhs rhs : Expr E q)
    where

    open Eqns E q lhs rhs

    record Structureᴰ (M : Structure ℓ) ℓᴰ : Type {!!} where
      open StructureStr (M .snd)

      field
        -- A family indexed by elements of M
        eltᴰ : ⟨ M ⟩ → Type ℓᴰ

        -- Given x : X, an `ar x`-indexed collection `vars` of elements of M, and
        -- a family for each z ∈ ar x displayed over the element `vars z` ∈ M,
        -- we get a single element displayed over `op x vars`
        opᴰ : ∀ {x : X} {vars : ar x → ⟨ M ⟩}
          → (varsᴰ : (z : ar x) → eltᴰ (vars z))
          → eltᴰ (op x vars)

      _≡[_]_ : ∀ {x y} → eltᴰ x → x ≡ y → eltᴰ y → Type _
      xᴰ ≡[ p ] yᴰ = PathP (λ i → eltᴰ (p i)) xᴰ yᴰ

      field

        -- For each equation e of the structure M, we have a
        -- corresponding equation displayed over e.
        eqnᴰ : (e : E) {vars : q e → ⟨ M ⟩}
          → (varsᴰ : (z : q e) → eltᴰ (vars z))
          → (x : eltᴰ (lhs ⟨ M ⟩ op e vars))
          → (y : eltᴰ (rhs ⟨ M ⟩ op e vars))
          → {!!} ≡[ eqn e vars ] {!!}

        isSetEltᴰ : ∀ {x} → isSet (eltᴰ x)
    
