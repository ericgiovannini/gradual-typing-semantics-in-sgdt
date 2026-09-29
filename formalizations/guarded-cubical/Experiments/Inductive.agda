{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}

open import Common.Later
open import Common.Common

module Experiments.Inductive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function

open import Cubical.Data.List as List
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)

private
  variable
    ℓ ℓ' : Level


module _ (k : Clock) where

  private
    ▹_ : Type ℓ -> Type ℓ
    ▹ A = ▹_,_ k A


  -- Fixpoint of an arbitrary functor F using guarded recursion
  μ : (F : Type ℓ → Type ℓ) → Type ℓ
  μ F = fix {k = k} (λ T~ → F (▸ T~))

  μ-eq : ∀ (F : Type ℓ → Type ℓ)
    → μ F ≡ F (▹ μ F)
  μ-eq F = fix-eq (λ T~ → F (▸ T~))

  module _ (F : Type ℓ → Type ℓ) where

    fold : F (▹ μ F) → μ F
    fold = transport⁻ (μ-eq F)

    unfold : μ F → F (▹ μ F)
    unfold = transport (μ-eq F)

    fold-unfold : ∀ x → fold (unfold x) ≡ x
    fold-unfold x = transport⁻Transport (μ-eq F) x

    unfold-fold : ∀ x → unfold (fold x) ≡ x
    unfold-fold x = transportTransport⁻ (μ-eq F) x

    μ-elim : {B : μ F → Type ℓ'}
      → {!!}
      → (x : μ F) → B x
    μ-elim = {!!}


  -- Definition of binary trees of natural numbers using guarded
  -- recursion
  TreeF : Type → Type
  TreeF X = ⊤ ⊎ (ℕ × X × X)

  Tree : Type
  Tree = μ TreeF

  Tree' : Type
  Tree' = TreeF (▹ Tree)

  _ : Tree ≡ Tree'
  _ = μ-eq TreeF

  Tree→Tree' : Tree → Tree'
  Tree→Tree' = unfold TreeF

  Tree'→Tree : Tree' → Tree
  Tree'→Tree = fold TreeF


  -- Constructors
  leaf : Tree
  leaf = fold TreeF (inl tt)

  node' : ℕ → ▹ Tree → ▹ Tree → Tree
  node' n x~ y~ = Tree'→Tree (inr (n , x~ , y~))
  -- fold TreeF (inr (n , x~ , y~))

  node : ℕ → Tree → Tree → Tree
  node n x y = node' n (next x) (next y)
  -- fold TreeF (inr (n , next x , next y))


  -- Elimination principle
  elimTree'' : {B : Tree → Type ℓ'}
    → (caseLeaf : B leaf)
    → (caseNode : ∀ n x~ y~
        → ▸ (λ t → B (x~ t))
        → ▸ (λ t → B (y~ t))
        → B (node' n x~ y~))
    → (x : Tree) → B x
  elimTree'' caseLeaf caseNode x = {!!}


  elimTree' : {B : Tree → Type ℓ'}
    → (caseLeaf : B leaf)
    → (caseNode : ∀ n x y
        → ▹ (B x)
        → ▹ (B y)
        → B (node n x y))
    → (x : Tree) → B x
  elimTree' caseLeaf caseNode x = {!!}


  elimTree : {B : Tree → Type ℓ'}
    → (caseLeaf : B leaf)
    → (caseNode : ∀ n x y → B x → B y → B (node n x y))
    → (x : Tree) → B x
  elimTree {B = B} caseLeaf caseNode x =
    elimTree' {B = B} caseLeaf (λ n x y Hx~ Hy~ → caseNode n x y {!!} {!!}) x
    where
      aux : ▹ ((x : Tree') → B (Tree'→Tree x))
             → (x : Tree') → B (Tree'→Tree x)
      aux rec (inl tt) = caseLeaf
      aux rec (inr (n , x~ , y~)) = {!caseNode n ? ? ? ?!}
    -- elimTree' {B = B} caseLeaf (λ n x~ y~ Hx~ Hy~ → {!!}) x
  
