{-# OPTIONS --guardedness --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


module Semantics.Adequacy.Coinductive.DelayMonad where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Nat
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Instances.Sets

open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq

open import Common.Preorder.Base
open import Semantics.Adequacy.Coinductive.Delay
open import Semantics.Adequacy.Coinductive.DelayErrorOrdering

private
  variable
    ℓ ℓ' : Level



-- ************************************
--  Utility functions
-- ************************************

private 
  S : Type ℓ -> Type ℓ
  S X = State (X ⊎ ⊤)

  T : Type ℓ -> Type ℓ
  T X = Delay (X ⊎ ⊤)

-- DelayCod→StateCod
DFun→SFun : {Γ X Y : Type ℓ} -> (Γ -> X -> T Y) -> (Γ -> X -> S Y)
DFun→SFun f γ x = view (f γ x)

-- SFun→DFun
SFun→DFun : {Γ X Y : Type ℓ} -> (Γ -> X -> S Y) -> (Γ -> X -> T Y)
SFun→DFun f γ x = fromState (f γ x)


-- ************************************
--  Strong unit and bind
-- ************************************


unit-d : {X : Type ℓ} -> X -> T X
view (unit-d x) = done (inl x)

-- Unit of the strong monad
unitΓ-d : {Γ X : Type ℓ} -> Γ -> X -> T X
unitΓ-d γ x = unit-d x

unitΓ-s : {Γ X : Type ℓ} -> Γ -> X -> S X
unitΓ-s γ x = done (inl x)



strong-bind-d : ∀ {Γ X Y : Type ℓ} -> (Γ -> X -> T Y) -> (Γ -> T X -> T Y)
strong-bind-s : ∀ {Γ X Y : Type ℓ} -> (Γ -> X -> S Y) -> (Γ -> S X -> S Y)

strong-bind-s f γ (done (inl x)) = f γ x
strong-bind-s f γ (done (inr tt)) = done (inr tt)
strong-bind-s f γ (running d) =
  running (strong-bind-d (λ γ' x' -> fromState (f γ' x')) γ d)

(strong-bind-d f γ d) .view = strong-bind-s (λ γ' x' -> view (f γ' x')) γ (view d)


{-
fromState-lem2 : ∀ {Γ X Y Z : Type ℓ} ->
  (f : Γ -> Y -> State Z) -> (g : (Γ -> X -> State Y)) -> (γ : Γ) -> (x : X) ->
  (fromState (strong-bind-s f γ (g γ x))) ≡ strong-bind-d (SFun→DFun f) γ (fromState (g γ x))
fromState-lem2 f g γ x i .view = strong-bind-s f γ (g γ x)
-}

-- ************************************
--  Properties
-- ************************************

-- Left unit

unitL-s : {Γ X : Type ℓ} -> (γ : Γ) -> (s : S X) ->
   (strong-bind-s unitΓ-s) γ s ≡ s
unitL-d : {Γ X : Type ℓ} -> (γ : Γ) -> (d : T X) ->
   (strong-bind-d unitΓ-d) γ d ≡ d
 
unitL-s γ (done (inl x)) = refl
unitL-s γ (done (inr tt)) = refl
unitL-s {Γ = Γ} γ (running d) i = running (goal _ (Eq.pathToEq fromState-lem) i)
  -- cong running ((λ j -> strong-bind-d (fromState-lem j) γ d) ∙ unitL-d γ d)
  where
    fromState-lem : ∀ {Γ X : Type ℓ} -> (λ γ x -> fromState (unitΓ-s γ x)) ≡ unitΓ-d
    fromState-lem {Γ = Γ} {X = X} = funExt λ γ -> funExt (λ x -> aux γ x)
      where
        aux : (γ : Γ) (x : X) -> fromState (unitΓ-s γ x) ≡ unitΓ-d γ x
        aux γ x i .view = done (inl x)

    goal : ∀ f -> f Eq.≡ unitΓ-d -> strong-bind-d f γ d ≡ d
    goal .unitΓ-d Eq.refl = unitL-d γ d

-- NTS: strong-bind-d (λ γ' x' → fromState (unitΓ-s γ' x')) γ d ≡ d 

unitL-d γ d i .view = unitL-s γ (view d) i



-- Right unit

unitR-s : {Γ X Y : Type ℓ} -> (f : Γ -> X -> S Y) -> (γ : Γ) -> (x : X) ->
   strong-bind-s f γ (unitΓ-s γ x) ≡ f γ x
unitR-s f γ x = refl

unitR-d : {Γ X Y : Type ℓ} -> (f : Γ -> X -> T Y) -> (γ : Γ) -> (x : X) ->
   strong-bind-d f γ (unitΓ-d γ x) ≡ f γ x
unitR-d f γ x i .view = unitR-s (λ γ' x' -> view (f γ' x')) γ x i



-- Composition

comp-s : {Γ X Y Z : Type ℓ} -> (f : Γ -> Y -> S Z) -> (g : (Γ -> X -> S Y)) ->
  (γ : Γ) -> (x : X) -> (s : S X) ->
  strong-bind-s f γ (strong-bind-s g γ s) ≡
  strong-bind-s (λ γ' x' -> strong-bind-s f γ' (g γ' x')) γ s
comp-d : {Γ X Y Z : Type ℓ} -> (f : Γ -> Y -> T Z) -> (g : (Γ -> X -> T Y)) ->
  (γ : Γ) -> (x : X) -> (d : T X) ->
  strong-bind-d f γ (strong-bind-d g γ d) ≡
  strong-bind-d (λ γ' x' -> strong-bind-d f γ' (g γ' x')) γ d

comp-s f g γ x (done (inl y)) = refl
comp-s f g γ x (done (inr tt)) = refl
comp-s {Γ = Γ} {X = X} {Z = Z} f g γ x (running d) i =
  running (goal
    (λ γ' x' -> fromState (strong-bind-s f γ' (g γ' x')))
    (Eq.pathToEq (funExt (λ γ' -> funExt λ x' -> lem γ' x'))) i)
  {- cong running (comp-d (SFun→DFun f) (SFun→DFun g) γ x d ∙
    λ j -> strong-bind-d (λ γ' x' -> lem γ' x' j) γ d) -}
  where
    lem : ∀ γ' x' ->
      fromState (strong-bind-s f γ' (g γ' x')) ≡
      strong-bind-d (SFun→DFun f) γ' (SFun→DFun g γ' x')
    (lem γ' x' i) .view = strong-bind-s f γ' (g γ' x')

    goal : ∀ (f' : Γ -> X -> T Z) ->
      f' Eq.≡ (λ γ' x' -> strong-bind-d (SFun→DFun f) γ' (SFun→DFun g γ' x')) ->
      strong-bind-d (λ γ' x' -> fromState (f γ' x')) γ
        (strong-bind-d (λ γ' x' -> fromState (g γ' x')) γ d) ≡
      strong-bind-d f' γ d
    goal .(λ γ' x' → strong-bind-d (SFun→DFun f) γ' (SFun→DFun g γ' x')) Eq.refl =
      comp-d (SFun→DFun f) (SFun→DFun g) γ x d

{-
  Know:
  strong-bind-d (SFun→DFun f) γ (SFun→DFun g γ x) ≡
  fromState (strong-bind-s f γ (g γ x))

  Informally, we have the following chain of equalities:

 strong-bind-d (λ γ' x' → fromState (f γ' x')) γ (strong-bind-d (λ γ' x' → fromState (g γ' x')) γ d) ≡ [by coind hyp]

 strong-bind-d (λ γ' x' → strong-bind-d (SFun→DFun f) γ' (SFun→DFun g γ' x')) γ d ≡ [by lem]
                          ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^

 strong-bind-d (λ γ' x' → fromState (strong-bind-s f γ' (g γ' x'))) γ d
                          ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^
-}

comp-d f g γ x d i .view = comp-s (DFun→SFun f) (DFun→SFun g) γ x (view d) i




-- ************************************
--  Monotonicity
-- ************************************

{-

-- The operations are monotone with respect to the ordering on Delay
module Monotone (X : Preorder ℓ ℓ') where
  open ResultPreorder X   -- Ordering on ⟨ X ⟩ ⊎ ⊤
  open Ord X              -- Ordering on Delay (⟨ X ⟩ ⊎ ⊤)
  open Alternative (⟨ X ⟩ ⊎ ⊤) -- Function-based definition of Delay


  fromDelay-unit : ∀ x? -> fromDelay (unit-d x?) zero ≡ {!!}
  fromDelay-unit x? = refl

  lem : ∀ x? y? -> terminatesWith (fromDelay (unit-d x?)) y? -> {!!}
  lem x? y? (n , eq) = {!!}

  unit-d-monotone : {Γ : Preorder ℓ ℓ'} -> {x y : ⟨ X ⟩} {γ : ⟨ Γ ⟩} ->
    rel X x y -> (unitΓ-d γ x) ⊑ (unitΓ-d γ y)
  unit-d-monotone x≤y = ∣ {!!} ∣₁



 -- Need lemmas:
 -- FromDelay (unit-d x?) terminates in zero steps.
 --
 -- If fromDelay (unit-d x?) n ≡ inl (inl x), then x? = inl x
 -- More generally: If fromDelay (unit-d x?) ↓ y? , then x? ≡ y?

strong-bind-d-monotone : {Γ X Y : Preorder ℓ ℓ'} ->
  {d d' : T ⟨ X ⟩} -> {γ γ' : ⟨ Γ ⟩} ->
  {f : ⟨ Γ ⟩ -> (⟨ X ⟩) -> T (⟨ Y ⟩)} ->
  rel Γ γ γ' ->
  Ord._⊑_ X d d' ->
  Ord._⊑_ Y (strong-bind-d f γ d) (strong-bind-d f γ d')
strong-bind-d-monotone {d = d} {d' = d'} {γ = γ} {γ' = γ'} {f = f}
  γ≤γ' d≤d' with d .view | d' .view
... | done (inl x) | done (inl x₁) = {!!}
... | done (inl x) | done (inr x₁) = {!!}
... | done (inr x) | done (inl x₁) = {!!}
... | done (inr x) | done (inr x₁) = {!!}
... | done x | running x₁ = {!!}
... | running x | done x₁ = {!!}
... | running x | running x₁ = {!!}

-}





{-

 -- Functor structure
mapState : {X Y : Type ℓ} -> (X -> Y) -> (State X -> State Y)
mapDelay : {X Y : Type ℓ} -> (X -> Y) -> (Delay X -> Delay Y)

mapState f (done x) = done (f x)
mapState f (running d') = running (mapDelay f d')

view (mapDelay f d) = mapState f (view d)


mapIdS : {X : Type ℓ} -> Path (State X -> State X) (mapState (λ x -> x)) (λ x -> x)
mapIdD : {X : Type ℓ} -> Path (Delay X -> Delay X) (mapDelay (λ x -> x)) (λ x -> x)
mapIdS i (done x) = done x
mapIdS i (running d) = running (mapIdD i d)
mapIdD i x .view = mapIdS i (x .view)



-- Monad on Set
DELAY : Monad (SET ℓ)
Functor.F-ob (fst DELAY) x = (Delay ⟨ x ⟩) , isSetDelay (x .snd)
Functor.F-hom (fst DELAY) = mapDelay
Functor.F-id (fst DELAY) = mapIdD
Functor.F-seq (fst DELAY) = {!!}
snd DELAY = {!!}

-}
