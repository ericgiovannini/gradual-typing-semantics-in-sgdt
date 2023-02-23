{-# OPTIONS --cubical --rewriting --guarded #-}

open import Later

module Results (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_ ; _^_)
open import Cubical.Data.Nat.Order
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty.Base renaming (rec to exFalso)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary


open import StrongBisimulation k
open import Semantics k
open import SyntacticTermPrecision k
open import GradualSTLC
open import MonFuns k

private
  variable
    l : Level
    A B : Set l
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A




-- Results about the intensional theory


module 2Cell
  (A A' B B' : Predomain)
  (A▹A' : EP A A')
  (B▹B' : EP B B')
 where

  open 𝕃
  open EP

  _⊑A'_ : ⟨ A' ⟩ -> ⟨ A' ⟩ -> Type
  _⊑A'_ = rel A'

  _⊑B'_ : ⟨ 𝕃 B' ⟩ -> ⟨ 𝕃 B' ⟩ -> Type
  _⊑B'_ = rel (𝕃 B')

  _⊑c_ : ⟨ A ⟩ -> ⟨ A' ⟩ -> Type
  a ⊑c a' = (U (emb A▹A') a) ⊑A' a'

  _⊑d_ : ⟨ 𝕃 B ⟩ -> ⟨ 𝕃 B' ⟩ -> Type
  lb ⊑d lb' = (mapL (U (emb B▹B')) lb) ⊑B' lb'

  _⊑f_ : ⟨ A ==> 𝕃 B ⟩ -> ⟨ A' ==> 𝕃 B' ⟩ -> Type
  f ⊑f f' = fun-order-het A A' (𝕃 B) (𝕃 B') _⊑c_ _⊑d_ (MonFun.f f) (MonFun.f f')
  

module 2CellVertical
  (A A' A'' B B' B'' : Predomain)
  (A▹A' : EP A A')
  (A'▹A'' : EP A' A'')
  (B▹B' : EP B B')
  (B'▹B'' : EP B' B'')
  where




-- Results about the extensional theory

tick-extensionality : (X : Set) -> (lx~ : ▹ (L℧ X)) -> (ly : L℧ X) ->
  ▸ (λ t -> lx~ t ≡ ly) ->
  lx~ ≡ next ly
tick-extensionality X lx~ ly H = λ i t → H t i


tick-extensionality' : (X : Set) -> (lx~ : ▹ (L℧ X)) -> (ly : L℧ X) ->
  ((t : Tick k) -> lx~ t ≡ ly) -> -- is there an implicit ▸ here?
  lx~ ≡ next ly
tick-extensionality' X lx~ ly H = λ i t₁ → H t₁ i






η≢δ : (d : Predomain) -> (x : ⟨ d ⟩) -> (n : Nat) ->
  ¬ ((η x) ≡ (δ ^ n) ℧)
η≢δ d x zero contra = {!!}
η≢δ d x (suc n) = {!!}


open 𝕃 ℕ -- defines the lock-step relation


-- Bisimilarity is non-trivial at Nat type
≈-non-trivial : {!!}
≈-non-trivial = {!!}

-- Bisimilarity is not transitive at Nat type



-- Adequacy of lock-step relation
module AdequacyLockstep
  -- (lx ly : L℧ Nat)
  -- (lx≾ly : lx ≾ ly)
  where

  _≾'_ : L℧ Nat → L℧ Nat → Type
  _≾'_ = ord' (next _≾_)

  {-
  lx≾'ly : lx ≾' ly
  lx≾'ly = transport (λ i → unfold-ord i lx ly) lx≾ly
  -}

  eq-later-eq-now : (X : Set) -> (lx~ : ▹ (L℧ X)) -> (ly : L℧ X) ->
    ▸ (λ t -> lx~ t ≡ ly) ->
    θ lx~ ≡ θ (next ly)
  eq-later-eq-now = {!!}


  sigma-later : (X : Set) (A : X -> Tick k -> Type) ->
    ▸ (λ t -> Σ X λ x -> A x t) ->
    Σ (▹ X) λ x~ -> ▸ (λ t -> A (x~ t) t)
  sigma-later X A H = (λ t → fst (H t)) , (λ t → snd (H t))

  ≾->≾' : (lx ly : L℧ Nat) ->
    lx ≾ ly -> lx ≾' ly
  ≾->≾' lx ly lx≾ly = transport (λ i → unfold-ord i lx ly) lx≾ly

  adequate-err-baby :
    ▹ ((lx : L℧ Nat) ->
      (H-lx : lx ≾' δ ℧) ->
      (lx ≡ ℧) ⊎ (lx ≡ δ ℧)) ->
    (lx : L℧ Nat) ->
    (H-lx : lx ≾' δ ℧) ->
    (lx ≡ ℧) ⊎ (lx ≡ δ ℧)
  adequate-err-baby _ (η x) ()
  adequate-err-baby _ ℧ _ = inl refl
  adequate-err-baby IH (θ lx~) H-lx =
    inr (cong θ (tick-extensionality Nat lx~ ℧
      λ t → {!!}))


  data GuardedNat : Type where
    zro : GuardedNat
    suc : ▹ Nat -> GuardedNat

  _≤GN_ : GuardedNat -> Nat -> Type
  n~ ≤GN m = {!!}

{-
  adequate-err :
    ▹ ((m : Nat) ->
    (lx : L℧ Nat) ->
    (H-lx : lx ≾' (δ ^ m) ℧) ->
    (Σ (▹ Nat) λ n -> (n ≤GN m) × (lx ≡ (δ ^ n) ℧))) ->
    (m : Nat) ->
    (lx : L℧ Nat) ->
    (H-lx : lx ≾' (δ ^ m) ℧) ->
    (Σ (▹ Nat) λ n -> (n ≤ m) × ((lx ≡ (δ ^ n) ℧)))
  adequate-err _ zero (η x) ()
  adequate-err _ (suc m') (η x) ()
  adequate-err _ m ℧ H-lx = next (0 , {!!})
  adequate-err _ zero (θ lx~) ()
  adequate-err IH (suc m') (θ lx~) H-lx = {!!}
-}

  ≾'-δ : (lx ly : L℧ Nat) -> (lx ≾' ly) -> (lx ≾' (δ ly))
  ≾'-δ = {!!}


  adequate-err-2 : (m : Nat) -> Σ Nat λ n -> (n ≤ m) ×
    (▹ ((lx : L℧ Nat) ->
        (H-lx : lx ≾' (δ ^ m) ℧) ->
        (lx ≡ (δ ^ n) ℧)) ->
      (lx : L℧ Nat) ->
      (H-lx : lx ≾' (δ ^ m) ℧) ->
      ((lx ≡ (δ ^ n) ℧)))
  adequate-err-2 zero = zero , ≤-refl , thm-zero
    where
      thm-zero : ▹ ((lx : L℧ Nat) → lx ≾' (δ ^ zero) ℧ → lx ≡ (δ ^ zero) ℧) →
                    (lx : L℧ Nat) → lx ≾' (δ ^ zero) ℧ → lx ≡ (δ ^ zero) ℧
      thm-zero IH ℧ H-lx = refl
  adequate-err-2 (suc m') =
    (suc (fst (adequate-err-2 m'))) , ({!!} , {!!})
      where
        thm-suc-m' : {!!}
        thm-suc-m' IH ℧ H-lx = {!!}
        thm-suc-m' IH (θ lx~) H-lx =
          cong θ (tick-irrelevance Nat lx~ ((δ ^ fst (adequate-err-2 m')) ℧)
          λ t → {!!})


-- Given:  θ lx~ ≾' (δ ^ suc m') ℧
-- i.e.    θ lx~ ≾' θ (next (δ ^ m') ℧)
-- i.e.    ▸ (λ t -> (lx~ t) ≾ (δ ^ m') ℧)

-- By IH, we have
-- ▸ (λ t -> lx~ t ≡ (δ ^ n') ℧ for some n')

-- By tick extensionality, we have
-- lx~ ≡ next (δ ^ n') ℧, so
-- θ lx~ ≡ θ (next (δ ^ n') ℧) ≡ (δ ^ (suc n')) ℧


-- Adequacy of weak bisimilarity relation

open Bisimilarity ℕ

module AdequacyBisimilarity
  (lx ly : L℧ Nat)
  (lx≈ly : lx ≈ ly) where


-- Combined result: Adequacy of extensional ordering

open ExtRel ℕ

module AdequacyExt
  (lx ly : L℧ Nat)
  (lx⊴ly : lx ⊴ ly) where

  adequate-1 : (n : Nat) (x : Nat) ->
    (lx ≡ (δ ^ n) (η x)) ->
    Σ Nat λ m -> ly ≡ (δ ^ m) (η x)
  adequate-1 n x H-lx = {!!}

  adequate-2 : (m : Nat) ->
    (ly ≡ (δ ^ m) ℧) ->
    Σ Nat λ n -> lx ≡ (δ ^ n) ℧
  adequate-2 m H-ly = {!!}



  




{-
gradual_guarantee : (M : Tm · nat) (N : Tm · nat) ->
                    · |- M ⊑tm N # nat ->
                    ⟦ M ⟧ ≲ ⟦ N ⟧
-}
