{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}

open import Common.Later
open import Common.Common

module Experiments.TreeAsContainer where

open import Agda.Primitive

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.List as List
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)

private
  variable
    ℓ ℓ' : Level

data TreeHole : Type where
  hole : TreeHole
  leaf : ℕ → TreeHole
  node : TreeHole → TreeHole → TreeHole

data Hole : TreeHole → Type where
  here  : Hole hole
  left  : ∀ l r → Hole l → Hole (node l r)
  right : ∀ l r → Hole r → Hole (node l r)

Tree : (X : Type ℓ) → Type ℓ
Tree X = Σ[ b ∈ TreeHole ] ((h : Hole b) → X)


module _ (X : Type ℓ) where

  pair : Tree X → Tree X → Tree X
  pair (h₁ , f₁) (h₂ , f₂) = treehole , fun
    where
      treehole : TreeHole
      treehole = node h₁ h₂
      
      fun : Hole treehole → X
      fun (left  .h₁ .h₂ p) = f₁ p
      fun (right .h₁ .h₂ q) = f₂ q
  
    

