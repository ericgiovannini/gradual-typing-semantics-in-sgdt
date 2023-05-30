{-# OPTIONS --cubical --rewriting --guarded #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -W noUnsupportedIndexedMatch #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Later
open import Common.Common

module Results.Delay where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_ ; _^_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Path
open import Cubical.Relation.Binary.Poset

import Cubical.Data.Equality as Eq

open import Semantics.Predomains
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
  done : Res -> State Res  -- should rename result to done
  running : Delay Res -> State Res
  -- squash : isSet (State Res)

record Delay Res where
  coinductive
  field view : State Res


open Delay public


delayUnit : State X → Delay X
view (delayUnit s) = s

-- The delay that returns the given value of type X in one step.
doneD : X -> Delay X
doneD x = delayUnit (done x)


-- Given a delay d, returns the delay d' that takes runs for one step
-- and then behaves as d.
stepD : Delay X -> Delay X
stepD d = delayUnit (running d)

_↓_#_ : Delay X -> X -> Nat -> Type
d ↓ x # n = {!!}


-- Given a delay d, return a function on nats n that,
-- when d ≡ running ^ n (done x), maps n to x and every other number to undefined
toFun : Delay X -> (Nat -> (X ⊎ Unit))
toFun d zero with view d
... | done x = inl x
... | running x = inr _
toFun d (suc n) with view d
... | done x = inr _
... | running d' = toFun d' n

-- Given a function f on nats, return a delay that runs for n0 steps and returns x,
-- where n0 is the smallest nat such that f n0 = inl x
fromFun : {X : Type ℓ} -> (Nat -> (X ⊎ Unit)) -> Delay X
fromFun {X = X} f .view with f 0
... | inl x = done x
... | inr _ = running (fromFun (f ∘ suc))

retrFun : (d : Delay X) -> fromFun (toFun d) ≡ d
retrFun d i .view with d .view in eq
... | done x = done x
... | running d' = running (goal _ eq i)
  where
    goal : ∀ s -> s Eq.≡ running d' -> fromFun (toFun (delayUnit s) ∘ suc) ≡ d'
    goal .(running d') Eq.refl = retrFun d'

   
isSetDelay : isSet X -> isSet (Delay X)
isSetDelay H = isSetRetract toFun fromFun retrFun (isSetΠ λ _ -> isSet⊎ H isSetUnit)


isSetDelay' : ∀ {ℓ : Level} -> {X : Type ℓ} → isSet X → isSet (Delay X)
isSetDelay' {X = X} p = isSetRetract f g h (isSetΠ λ n → isSet⊎ p isSetUnit)
    where
      -- f : Delay X → (Nat → X ⊎ Unit)
      -- f d zero with d .view
      -- ... | done x = inl x
      -- ... | running x = {!inr tt!}
      -- f d (suc n) with d .view
      -- ... | done x = inr tt
      -- ... | running d' = f d' n
      
      f : Delay X → (Nat → X ⊎ Unit)
      f d n with d .view
--      f d n       | done x  = inl x
      f d zero    | done x = inl x
      f d (suc n) | done x = inr tt
      f d zero    | running _ = inr tt
      f d (suc n) | running d' = f d' n

      g : (Nat → X ⊎ Unit) → Delay X
      g f .view with f zero
      ... | inl x  = done x
      ... | inr tt = running (g λ n → f (suc n))

      h : (d : Delay X) → g (f d) ≡ d
      h d i .view with d .view
      ... | done x  = done x
      ... | running d' = running (h d' i)



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




{-
module Isomorphism {X : Type} where

  -- to : L℧F X -> Delay (Result (□ X))
  -- to l = to' (Iso.fun L℧F-iso l)

  to' : (((□ X) ⊎ ⊤) ⊎ (L℧F X)) -> Delay (Result (□ X))
  view (to' (inl (inl x))) = done (value x)
  view (to' (inl (inr tt))) = done error
  view (to' (inr l')) = running (to' (inr l'))

  to : L℧F X -> Delay (Result (□ X))
  to l = to' (Iso.fun L℧F-iso l)

  fro' : (k : Clock) -> ▹ k ,
    (Delay (Result (□ X)) -> L℧ k X) ->
    (Delay (Result (□ X)) -> L℧ k X)
  fro' k rec m with (view m)
  ... | done (value x) = η (x k)
  ... | done error = ℧
  ... | running m' = θ (λ t -> rec t m')

  fro : Delay (Result (□ X)) -> L℧F X
  fro d k = fix (fro' k) d

  unfold-fro : (d : Delay (Result (□ X))) (k : Clock) ->
    fro d k ≡ fro' k (next (λ d -> fro d k)) d
  unfold-fro d k = let eq = fix-eq (fro' k) in
    λ i -> eq i d


  sec : section to fro
  sec d = {!!}


  retr' : (k : Clock) -> (l : L℧F X) -> ▹ k ,
    (fro' k (next (λ d -> fro d k)) (to' (Iso.fun L℧F-iso l)) ≡ l k) ->
    (fro' k (next (λ d -> fro d k)) (to' (Iso.fun L℧F-iso l)) ≡ l k)
  retr' k l IH with (Iso.fun L℧F-iso l) in eq
  ... | inl (inl x) = let eq' = L℧F-iso-η-inv l x {!!} in {!!}
  ... | inl (inr tt) = let eq' = {!L℧F-iso-inv-℧!} in {!!}
  ... | inr l' = {!!}

  retr : retract to fro
  retr l with (Iso.fun L℧F-iso l) in eq
  ... | inl (inl x) = {!!}
  ... | inl (inr tt) =
    {!!} ≡⟨ funExt (λ k -> unfold-fro (to' (inl (inr tt))) k) ⟩
    {!!} ≡⟨ {!!} ⟩ {!!}
    l ∎ 
  ... | inr l' = {!!} 



module Isomorphism2 {X : Type} where

  to' : (k : Clock) -> L℧ k X -> Delay (Result (□ X))
  view (to' k (η x)) = done (value (λ k -> x))
  view (to' k ℧) = done error
  view (to' k (θ x)) = running (to' k (x ◇))

  to : L℧F X -> Delay (Result (□ X))
  to l = to' k0 (l k0)

  

-- TODO should X have type Clock -> Type?
-- Then the correct iso would be
-- L℧F X ≅ Delay (∀ k -> X k)
module Isom {X : Type} (H-irrel : clock-irrel X) where

   X? = Result X

   ∀-to-delay : (L℧F X) -> Delay (Result X)
   view (∀-to-delay l) with (Iso.fun (L℧F-iso-irrel H-irrel) l)
   ... | inl (inl x) = done (value x)
   ... | inl (inr tt) = done error
   ... | inr l' = running (∀-to-delay l')


   delay-to-∀'' : (k : Clock) -> ▹ k , (Delay X? -> L℧ k X) -> (Delay X? -> L℧ k X)
   delay-to-∀'' k rec m with (view m)
   ... | done (value x) = η x
   ... | done error = ℧
   ... | running m' = θ (λ t → rec t m')

   delay-to-∀' : (k : Clock) -> (Delay X?) -> L℧ k X
   delay-to-∀' k = fix (delay-to-∀'' k)

   unfold-d2∀ : (k : Clock) -> delay-to-∀' k ≡ delay-to-∀'' k (next (delay-to-∀' k))
   unfold-d2∀ k = fix-eq (delay-to-∀'' k)

   delay-to-∀ : Delay X? -> L℧F X
   delay-to-∀ m k = fix (delay-to-∀'' k) m

   sec : section ∀-to-delay delay-to-∀
   sec b = {!!}

   retr : retract ∀-to-delay delay-to-∀
   retr l with (Iso.fun (L℧F-iso-irrel H-irrel) l)
   ... | inl (inl x) = clock-ext (λ k → {!!})
   ... | inl (inr _) = {!!}
   ... | inr x = {!!}


  -- Showing these are inverses requires a notion of equality for Delays,
  -- which is the bisimilarity relation defined below.

-}






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


  {-
  iso1 : ∀ {m m'} -> (p : m ≈ m') -> enc (dec p) ≡ p
  iso1' : ∀ {s s'} -> (p : s ≈'' s') -> enc' (dec' p) ≡ p
  -}

  {-
  iso2 : ∀ {m m'} -> (p : m ≡ m') -> dec (enc p) ≡ p
  iso2' : ∀ {s s'} -> (p : s ≡ s') -> dec' (enc' p) ≡ p

  view (iso2 p i j) = iso2' (cong view p) i j
  
  iso2' {done x} {done y} p = λ i j → {!!}
  iso2' {done x} {running d'} p = {!!}
  iso2' {running d} {done y} p = {!!}
  iso2' {running m} {running m'} p i j = {!!}
  -}

{-

  bisim : ∀ {m m'} -> m ≈ m' -> m ≡ m'
  bisim' : ∀ {m m'} -> m ≈' m' -> m ≡ m'

  -- bisim' {result x} {result y} (con (xRy , yRx)) = cong result (antisym X x y xRy yRx)
  bisim' {done x} {done y} (con p) = cong done p
  bisim' {running m} {running m'} (con m≈m') = cong running (bisim m≈m')

  view (bisim m≈m' i) = bisim' (prove m≈m') i

  misib : ∀ {m m'} → m ≡ m' → m ≈ m'
  misib' : ∀ {m m'} → m ≡ m' → m ≈' m'

  misib' {done x} {done y} eq = con (result-inj eq)
  misib' {running m} {running m'} p = con (misib (cong pred'' p))
  misib' {done x} {running m} = result≠running {X}
  misib' {running m} {done x} eq = result≠running {X} (sym eq)

  prove (misib m≡m') = misib' (cong view m≡m')

  iso1 : ∀ {m m'} -> (p : m ≈ m') -> misib (bisim p) ≡ p
  iso1' : ∀ {s s'} -> (p : s ≈' s') -> misib' (bisim' p) ≡ p

  iso1' {done x} {done y} (con p) = refl
  iso1' {running m} {running m'} (con p) = cong con (iso1 p)

  prove (iso1 p i) = iso1' (prove p) i


  iso2 : ∀ {m m'} -> (p : m ≡ m') -> bisim (misib p) ≡ p
  iso2' : ∀ {s s'} -> (p : s ≡ s') -> bisim' (misib' p) ≡ p

  iso2' {running m} {running m'} p = {!!}
  iso2' _ = {!!}

  iso2 = {!!}


module Evaluate {ℓ : Level} (X : Type ℓ) where

  _↓_ : Delay X -> X -> Type ℓ
  d ↓ x = X


module WeakBisim {ℓ ℓ' : Level}
  (X : Type ℓ) (Y : Type ℓ') (R : X -> Y -> Type (ℓ-max ℓ ℓ')) where
  module EvX = Evaluate X
  module EvY = Evaluate Y
  _↓X_ = EvX._↓_
  _↓Y_ = EvY._↓_

   -- Coinductive lock-step bisimilarity on delays
  record _≈_ (d : Delay X) (d' : Delay Y) : Type (ℓ-suc (ℓ-max ℓ ℓ'))

  -- Bisimilarity on states
  {- _≈''_ : State X -> State Y -> Type -}

  -- Inductive type of proofs of bisimilarity
  data _≈'_ : (s : State X) (s' : State Y) -> Type (ℓ-suc (ℓ-max ℓ ℓ'))
   where
    -- con : s ≈'' s' -> s ≈' s'
    done-done : ∀ x y -> R x y -> done x ≈' done y
    done-run : ∀ x y d' -> d' ↓Y y -> R x y -> done x ≈' running d'
    run-done : ∀ x y d -> d ↓X x -> R x y -> running d ≈' done y
    run-run : ∀ d d' -> d ≈ d' -> running d ≈' running d'

  record _≈_ m m' where
    coinductive
    field prove : view m ≈' view m'


-- Ret and Ext for Delays
ret-delay : {X : Type} -> X -> Delay X
ret-delay = doneD

ext-delay : {X Y : Type} -> (X -> Delay Y) -> Delay X -> Delay Y
ext-state : {X Y : Type} -> (X -> State Y) -> State X -> State Y

view (ext-delay f mx) = ext-state (view ∘ f) (view mx)

ext-state f (done x) = f x
ext-state f (running m) = running (ext-delay (delay ∘ f) m)

-}


{-
∀-to-delay : (L℧F X) -> (Delay (X ⊎ ⊤))
view (∀-to-delay l) with (l k0)
... | η x   = inl (inl x)  -- done (inl x) }
... | ℧     = inl (inr tt) -- done (inr tt) }
... | θ lx~ = inr (tt , (∀-to-delay l)) -- running }

{-# TERMINATING #-}
delay-to-∀ : Delay (X ⊎ ⊤) -> L℧F X
delay-to-∀ m with (view m)
... | inl (inl x) = λ k -> η x
... | inl (inr tt) = λ k -> ℧
... | inr (tt , m') = λ k -> θ λ t → delay-to-∀ m' k

isom : {X : Type} -> Iso (L℧F X) (Delay (X ⊎ ⊤))
isom {X} = iso ∀-to-delay delay-to-∀ sec retr
  where
    sec : section ∀-to-delay delay-to-∀
    sec m with (view m)
    ... | inl (inl x) = {!!}
    ... | inl (inr tt) = {!!}
    ... | inr (_ , m') = {!!}

    retr : retract ∀-to-delay delay-to-∀
    retr l with (l k0) in eq
    ... | η x = clock-ext {!!}
    ... | ℧ = clock-ext {!!}
    ... | θ l~ = {!!}
   
-}
