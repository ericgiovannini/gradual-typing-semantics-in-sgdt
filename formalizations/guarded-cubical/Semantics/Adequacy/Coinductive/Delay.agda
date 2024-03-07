{-# OPTIONS --cubical --rewriting --guarded #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -W noUnsupportedIndexedMatch #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Later
open import Common.Common

module Semantics.Adequacy.Coinductive.Delay where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat -- renaming (ℕ to Nat) hiding (_·_ ; _^_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Path

import Cubical.Data.Equality as Eq

open import Cubical.Foundations.HLevels


private
  variable
    ℓ : Level
    X : Type ℓ


record Delay (Res : Type ℓ) : Type ℓ

data State (Res : Type ℓ) : Type ℓ where
  done : Res -> State Res
  running : Delay Res -> State Res

record Delay Res where
  coinductive
  field view : State Res

open Delay public


-- Turn a State into a Delay.
fromState : State X → Delay X
view (fromState s) = s

-- The delay that returns the given value of type X in one step.
doneD : X -> Delay X
doneD x = fromState (done x)


-- Given a Delay d, returns the Delay d' that takes runs for one step
-- and then behaves as d.
stepD : Delay X -> Delay X
stepD d = fromState (running d)


-- An alternative definition of the Delay type using functions from natural numbers
-- to X ⊎ Unit that are defined at most once.
module Alternative (X : Type ℓ) where

  -- Given a Delay d, return a function on nats that, when d ≡ running ^ n (done x),
  -- maps n to inl x and every other number to inr tt.
  fromDelay : Delay X → (ℕ → X ⊎ Unit)
  fromDelay d n with d .view
--      f d n       | done x  = inl x
  fromDelay d zero    | done x = inl x
  fromDelay d (suc n) | done x = inr tt
  fromDelay d zero    | running _ = inr tt
  fromDelay d (suc n) | running d' = fromDelay d' n

  -- Given a function f on nats, return a delay that runs for n0 steps and returns x,
  -- where n0 is the smallest nat such that f n0 = inl x.
  toDelay : (ℕ → X ⊎ Unit) → Delay X
  toDelay f .view with f zero
  ... | inl x  = done x
  ... | inr tt = running (toDelay λ n → f (suc n))

  retr : (d : Delay X) → toDelay (fromDelay d) ≡ d
  retr d i .view with d .view
  ... | done x  = done x
  ... | running d' = running (retr d' i)


  PreDelay' : Type ℓ
  PreDelay' = ℕ -> (X ⊎ Unit)

  Delay' : Type ℓ
  Delay' = Σ[ f ∈ PreDelay' ] fromDelay (toDelay f) ≡ f


  terminatesWith : PreDelay' -> X -> Type ℓ
  terminatesWith d x = Σ[ n ∈ ℕ ] d n ≡ inl x

  terminates : PreDelay' -> Type ℓ
  terminates d = Σ[ n ∈ ℕ ] Σ[ x ∈ X ] d n ≡ inl x

  -- We can characterize the functions f for which fromDelay (toDelay f) ≡ f
  -- These are the functions that are defined at most once, i.e.,
  -- if f n ≡ inl x and f m ≡ inl x', then n ≡ m
  -- This is needed for showing that terminatesWith is a Prop.
  
  fromDelay-def-atmost-once : (d : Delay X) (n m : ℕ) -> (x x' : X) ->
    fromDelay d n ≡ inl x -> fromDelay d m ≡ inl x' -> n ≡ m
  fromDelay-def-atmost-once d n m x x' eq1 eq2 with n | m | d .view
  ... | zero   | zero   | done x = refl
  ... | suc n' | suc m' | running d' =
    cong suc (fromDelay-def-atmost-once d' n' m' x x' eq1 eq2)

  -- Impossible cases
  ... | n      | suc m' | done x = ⊥.rec (inl≠inr _ _ (sym eq2))
  ... | suc n' | m      | done x = ⊥.rec (inl≠inr _ _ (sym eq1))
  
  ... | zero   | m    | running d' = ⊥.rec (inl≠inr _ _ (sym eq1))
  ... | n      | zero | running d' = ⊥.rec (inl≠inr _ _ (sym eq2))


  delay'-necessary : (f : Delay') -> (n m : ℕ) (x x' : X) ->
    (fst f n ≡ inl x) -> (fst f m ≡ inl x') -> (n ≡ m)
  delay'-necessary f n m x x' eq1 eq2 = fromDelay-def-atmost-once
    (toDelay (fst f)) n m x x'
    ((λ i -> snd f i n) ∙ eq1) ((λ i -> snd f i m) ∙ eq2)

  -- Can also formulate the converse implication (TODO)
  delay'-sufficient : (f : PreDelay') ->
    ((n m : ℕ) (x x' : X) ->
     (f n ≡ inl x) -> (f m ≡ inl x') -> (n ≡ m)) ->
    fromDelay (toDelay f) ≡ f
  delay'-sufficient f H = {!!}

  -- Given a delay d, convert it to a function f using fromDelay,
  -- satisfying the condition that fromDelay (toDelay f) ≡ f.
  -- This condition is trivially satisfied since we have
  -- fromDelay (toDelay (fromDelay d)) ≡ fromDelay d
  -- (using the retraction property).
  Delay→Fun : (d : Delay X) -> Delay'
  fst (Delay→Fun d) = fromDelay d
  snd (Delay→Fun d) = cong fromDelay (retr d)
    

  isProp-terminatesWith : (d : Delay') (x : X) -> isProp (terminatesWith (fst d) x)
  isProp-terminatesWith d x = {!!}

  -- "Constructors" for Delay' corresponding to done and running
  delayFunDone : (x : X) -> Delay'
  delayFunDone x = {!!}
    where
      delayFunDone' : (x : X) -> PreDelay'
      delayFunDone' x zero = inl x
      delayFunDone' x (suc n) = inr tt

  doneD-corresp : (x : X) -> fromDelay (doneD x) ≡ delayFunDone x .fst
  doneD-corresp x = funExt (λ { zero → refl ; (suc n) → refl})

  delayFunRunning : (d : PreDelay') -> PreDelay'
  delayFunRunning d = {!!}

  -- runningD-corresp : (d : Delay) -> fromDelay (runningD d)



isSetDelay : ∀ {ℓ : Level} -> {X : Type ℓ} → isSet X → isSet (Delay X)
isSetDelay {X = X} p =
  isSetRetract fromDelay toDelay retr (isSetΠ λ n → isSet⊎ p isSetUnit)
  where open Alternative X




