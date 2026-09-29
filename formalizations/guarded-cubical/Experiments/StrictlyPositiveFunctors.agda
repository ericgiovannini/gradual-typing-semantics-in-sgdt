{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}

module Experiments.StrictlyPositiveFunctors where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.List as List
open import Cubical.Data.Nat hiding (_^_ ; _+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Bool as Bool

private
  variable
    ℓ ℓ' ℓA ℓB : Level


data FDesc : Type (ℓ-suc ℓ-zero)  where
  -- _+_ : FDesc → FDesc → FDesc
  `1 : FDesc
  `rec : FDesc → FDesc
  `Σ : (A : Type) → (A → FDesc) → FDesc


-- "Coproduct" of descriptions
_`+_ : FDesc → FDesc → FDesc
A `+ B = `Σ Bool (Bool.elim A B)


-- Description of the product of types
_`×_ : Type → Type → FDesc
A `× B = `Σ A λ _ → `Σ B (λ _ → `1)


-- Interpreting an FDesc as an endofunctor on Type.
⟦_⟧ : FDesc → Type ℓ → Type ℓ
⟦ `1 ⟧ X = Unit*
⟦ `rec d ⟧ X = X × (⟦ d ⟧ X)
⟦ `Σ A f ⟧ X = Σ[ x ∈ A ] (⟦ f x ⟧ X)

fmap : (d : FDesc) → {A : Type ℓA} → {B : Type ℓB}
  → (A → B)
  → (⟦ d ⟧ A → ⟦ d ⟧ B)
fmap `1 fold* _ = tt*
fmap (`rec d) fold* (x , xs) = (fold* x) , (fmap d fold* xs)
fmap (`Σ A' f) fold* (x , xs) = x , (fmap (f x) fold* xs)


-- The least fixpoint of a functor associated arising from an FDesc
data Mu (d : FDesc) : Type where
  fold : ⟦ d ⟧ (Mu d) → Mu d


module _ (d : FDesc) where

  F : {ℓ : Level} → _ → _
  F {ℓ} = ⟦_⟧ {ℓ} d


recMu : {B : Type ℓB}
  → (d : FDesc)
  → (⟦ d ⟧ B → B)
  → (Mu d) → B
-- recMu d fold* (fold x) = fold* (fmap d (recMu d fold*) x)

recMu `1 g (fold x') = g tt*

recMu (`rec d) g (fold (x , y)) = g ((recMu (`rec d) g x) , fmap d (λ z → recMu (`rec d) fst z) y)
-- x :  Mu (`rec d)
-- y :  ⟦ d ⟧ (Mu (`rec d))

recMu (`Σ A f) g (fold (x , xs)) = {!!}

--------------------------------------

-- Example: nat

natD : FDesc
natD = `1 `+ (`rec `1)

nat : Type
nat = Mu natD

zro : nat
zro = fold (true , tt*)

succ : nat → nat
succ n = fold (false , (n , tt*))

