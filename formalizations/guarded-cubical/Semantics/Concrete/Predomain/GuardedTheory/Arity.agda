{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.Predomain.GuardedTheory.Arity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Nat

private
  variable
    ℓ ℓ' : Level


-- An arity is simply a list of natural numbers, where the natural
-- number at index d represents the number of variables at depth d.
Arity : Type
Arity = List ℕ


-- Number of variables at depth d (default is 0)
lookup : Arity → ℕ → ℕ
lookup [] _ = 0
lookup (n ∷ _) zero = n
lookup (n ∷ ns) (suc d) = lookup ns d


-- Shift (prepend a zero)
shift : Arity → Arity
shift Γ = 0 ∷ Γ


-- Product of arities (pointwise addition)
_⊕_ : Arity → Arity → Arity
[] ⊕ Δ = Δ
Γ ⊕ [] = Γ
(m ∷ ms) ⊕ (n ∷ ns) = (m + n) ∷ (ms ⊕ ns)

-- Unit arity (arity with one variable at depth d)
unitArity : ℕ → Arity
unitArity zero = 1 ∷ []
unitArity (suc d) = 0 ∷ unitArity d
