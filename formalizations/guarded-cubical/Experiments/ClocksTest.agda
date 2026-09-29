{-# OPTIONS --cubical --rewriting --guarded #-}
{-# OPTIONS --guardedness #-}

open import Later

module ClocksTest where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

private
  variable
    l : Level
    A B : Set l

{-

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A


open Stream

repeat : {A : Set} (a : A) -> Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

-}





----------------------------------------
-- ########## Guarded Streams ##########


data GStream (k : Clock) : Type where
  Cons : ℕ -> ▹ k , (GStream k) -> (GStream k)

GSHead : {k : Clock} -> GStream k -> ℕ
GSHead (Cons n _) = n

GSTail : (k : Clock) -> GStream k -> ▹ k , GStream k
GSTail k (Cons _ xs') = xs'


mergef : {k : Clock} -> (ℕ -> ℕ -> ▹ k , (GStream k) -> GStream k) ->
  GStream k -> GStream k -> GStream k
mergef {k} f = fix mergef'
  where
    mergef' : ▹ k , (GStream _ → GStream _ → GStream _) ->
                    (GStream _ → GStream _ → GStream _)
    mergef' rec (Cons x xs') (Cons y ys') = f x y ((rec ⊛ xs') ⊛ ys')


-- Defining "completed streams" via clock quantification.

Stream : Type
Stream = ∀ (k : Clock) -> GStream k


-- Could also define this via the application of a clock constant k0
SHead : Stream -> ℕ
SHead s = transport clock-iso (λ k -> GSHead (s k))


STail : Stream -> Stream
STail s k = GSTail k (s k) (k ◇)

force' : (∀ k → (▹ k , A)) → (∀ (k : Clock) → A)
force' = λ x k -> (x k) (k ◇)


-- I can't seem to define STail using force directly.
-- Doing so seems to require clock irrelevance.


STail' : Stream -> Stream
STail' s k =
  {- force (λ k' t →
    transport
      (sym (λ i → clock-irrel GStream k k' i))
      (GSTail k' (s k') t)
  ) k -}

  -- Or:
  force (λ k' →
    transport
      (sym (λ i → ▸_ {k'} (λ t -> clock-irrel GStream k k' i)))
      (λ t → GSTail k' (s k') t)
  ) k

  -- The first argumemt to transport has type
  -- (▸ (λ t₁ → GStream k')) ≡ (▸ (λ t₁ → GStream k))
  -- i.e.
  -- ((t₁ : Tick k') → GStream k') ≡ ((t₁ : Tick k') → GStream k)

-- force (λ k' -> GSTail k (s k)) k


