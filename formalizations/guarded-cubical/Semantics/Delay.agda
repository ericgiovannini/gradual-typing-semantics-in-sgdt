{-# OPTIONS --cubical --rewriting --guarded #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -W noUnsupportedIndexedMatch #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Later
open import Common.Common

module Semantics.Delay where

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
open import Cubical.Relation.Binary.Poset

import Cubical.Data.Equality as Eq

open import Semantics.Predomains hiding (ℕ)
open import Semantics.StrongBisimulation
open import Semantics.Lift

open import Results.IntensionalAdequacy

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


fromState : State X → Delay X
view (fromState s) = s

-- The delay that returns the given value of type X in one step.
doneD : X -> Delay X
doneD x = fromState (done x)


-- Given a delay d, returns the delay d' that takes runs for one step
-- and then behaves as d.
stepD : Delay X -> Delay X
stepD d = fromState (running d)


-- An alternative definition of the Delay type using functions from natural numbers
-- to X ⊎ Unit
module Alternative (X : Type ℓ) where

  -- Given a delay d, return a function on nats that, when d ≡ running ^ n (done x),
  -- maps n to x and every other number to undefined.
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


  -- Iso with global lift

  f' : (∀ k -> L k X) -> PreDelay'
  f' y n with y k0
  f' y zero    | η x = inl x
  f' y (suc n) | η x = inr tt
  f' y zero    | θ l~ = inr tt
  f' y (suc n) | θ l~ = f' y n

  f : (∀ k -> L k X) -> Delay'
  f y = (f' y) , {!!}

  g'' : (k : Clock) -> (▹ k , (Delay' -> L k X)) -> Delay' -> L k X
  g'' k rec h with fst h zero
  ... | inl x = η x
  ... | inr tt = θ (λ t → rec t ((λ n -> fst h (suc n)) , {!!}))

  g' : ∀ k -> Delay' -> L k X
  g' k = fix (g'' k)

  g : Delay' -> (∀ k -> L k X)
  g h k = g' k h

  sec' : (h : Delay') -> (k : Clock) ->
    (▹ k , (f (λ k' -> g'' k' (next (g' k')) h) ≡ h)) ->
           (f (λ k' -> g'' k' (next (g' k')) h) ≡ h)
  sec' h k IH with fst h zero in eq
  ... | inl x = Σ≡Prop {!!} aux
    where
      aux : f' (λ k' -> η x) ≡ h .fst
      aux = funExt λ { zero → sym (Eq.eqToPath eq) ; (suc n) → {!!}}
  ... | inr x = Σ≡Prop {!!} {!!}
  

  unfold-g' : {k : Clock} -> g' k ≡ g'' k (next (g' k))
  unfold-g' {k} = fix-eq (g'' k)

  sec : section f g
  sec = {!!}


isSetDelay : ∀ {ℓ : Level} -> {X : Type ℓ} → isSet X → isSet (Delay X)
isSetDelay {X = X} p = isSetRetract fromDelay toDelay retr (isSetΠ λ n → isSet⊎ p isSetUnit)
  where open Alternative X






data Result (X : Type) : Type where
  value : X -> Result X
  error : Result X

ResToSum : Result X -> X ⊎ Unit
ResToSum (value x) = inl x
ResToSum error = inr tt

SumToRes : X ⊎ Unit -> Result X
SumToRes (inl x) = value x
SumToRes (inr tt) = error

result-retr : (x : Result X) → SumToRes (ResToSum x) ≡ x
result-retr (value x) = refl
result-retr error = refl

isSetResult : isSet X -> isSet (Result X)
isSetResult H = isSetRetract ResToSum SumToRes result-retr (isSet⊎ H isSetUnit)

_^? : Type -> Type
X ^? = Result X


diag : (Res Run : Type) -> State X -> Type₀
diag Res Run (done x) = Res
diag Res Run (running m) = Run


result≠running : {X : Type} -> ∀ {x : X} {m : Delay X} {ℓ} {Whatever : Type ℓ} →
  done x ≡ running m → Whatever
result≠running eq = ⊥.rec (transport (cong (diag ⊤ ⊥) eq) tt)



-- used for showing that the result constructor is injective
pred' : X -> State X → X
pred' _ (done x) = x
pred' x (running m) = x

-- used for showing that the running constructor is injective
pred'' : State X -> Delay X
view (pred'' (done x)) = done x
pred'' (running m) = m

result-inj : {ℓ : Level} {X : Type ℓ} {x y : X} -> done x ≡ done y -> x ≡ y
result-inj {x = x} eq = cong′ (pred' x) eq




module IsSet (X : Type) (isSetX : isSet X)  where

  X? : Type
  X? = Result X

  ≡-stable  : {m m' : Delay X?} → Stable (m ≡ m')
  ≡'-stable : {s s' : State X?} → Stable (s ≡ s')

  view (≡-stable ¬¬p i) = ≡'-stable (λ ¬p → ¬¬p (λ p → ¬p (cong view p))) i
  
  ≡'-stable {done x}  {done y}  ¬¬p' =
    cong′ done {!!}
  ≡'-stable {running m} {running m'}  ¬¬p' =
    cong′ running (≡-stable (λ ¬p -> ¬¬p' (λ p -> ¬p (cong pred'' p))))
  ≡'-stable {done x}  {running m} ¬¬p' = ⊥.rec (¬¬p' (result≠running {X?}))
  ≡'-stable {running m} {done x}  ¬¬p' = ⊥.rec (¬¬p' (λ p → result≠running {X?} (sym p)))

  retrState : State X? -> X? ⊎ Delay X?
  retrState (done x) = inl x
  retrState (running d) = inr d

  secState : X? ⊎ Delay X? -> State X?
  secState (inl x) = done x
  secState (inr d) = running d
  



--  isSetState = isSetRetract retrState secState {!!} (isSet⊎ (isSetResult isSetX) isSetDelay)


-- Lock-step bisimilarity relation on Delays, but with no error ordering.
module StrongBisim (X : Type) where -- (H-irrel : clock-irrel ⟨ X ⟩) where


  -- Mutually define coinductive bisimilarity of delays
  -- along with the relation on states of a delay.
 

  -- Coinductive lock-step bisimilarity on delays
  record _≈_ (m m' : Delay X) : Type

  -- Bisimilarity on states
  _≈'_ : State X -> State X -> Type
  done x ≈' done x' = x ≡ x' -- rel X x x' × rel X x' x
  running m ≈' running m' = m ≈ m' -- using the coinductive bisimilarity on delays
  _ ≈' _ = ⊥

  data _≈''_ : State X -> State X -> Type where
    con : {s s' : State X} -> (s ≈' s') -> (s ≈'' s')


  record _≈_ m m' where
    coinductive
    field prove : view m ≈'' view m'


  open _≈_ public

  enc : {d d' : Delay X} -> d ≡ d' -> d ≈ d'
  enc' : {s s' : State X} -> s ≡ s' -> s ≈'' s'

  enc {d} {d'} eq .prove = enc' (cong view eq)
  enc' {done x} {done y} eq = con (result-inj eq)
  enc' {done x} {running d'} eq = result≠running eq
  enc' {running d} {done y} eq = result≠running (sym eq)
  enc' {running d} {running d'} eq = con (enc (cong pred'' eq))

  dec : {d d' : Delay X} -> d ≈ d' -> d ≡ d'
  dec' : {s s' : State X} -> s ≈'' s' -> s ≡ s'

  view (dec {d} {d'} eq i) = dec' (eq .prove) i
  dec' {done x} {done x₁} (con p) = cong done p
  dec' {done x} {running x₁} (con ())
  dec' {running x} {done x₁} (con ())
  dec' {running x} {running x₁} (con x₂) = cong running (dec x₂)

