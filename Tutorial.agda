{-# OPTIONS --cubical --rewriting --guarded #-}

module Tutorial where

  open import Cubical.Data.Nat
  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Function
  open import Cubical.Foundations.Transport

  open import Later

  -- Example proof by induction
  
  plus-assoc : (x y z : ℕ) -> x + y + z ≡ x + (y + z)
  plus-assoc zero y z = refl
  plus-assoc (suc x') y z = cong suc (plus-assoc x' y z)


  ----------------------------------------------------
  -- Cubical stuff

  -- Interval I
  -- i : I is an arbitrary point in the interval [0,1]
  -- i0 : I     "left endpoint"
  -- i1 : I     "right endpoint"
  -- ~ i        "negation"
  -- i ∨ j      "maximum"
  -- i ∧ j      "minimum"

  -- Equality within in a type A corresponds to paths in A
  -- A path in A is represented as a function I -> A

  refl' : {X : Type} -> (x : X) -> x ≡ x
  refl' {X} x = λ i → x

  sym' : {X : Type} -> (x y : X) -> x ≡ y -> y ≡ x
  sym' {X} x y eq = λ i → eq (~ i)

  funExt' : {X Y : Type} -> {f g : X -> Y} -> (∀ (x : X) -> f x ≡ g x) -> f ≡ g
  funExt' {X} {Y} {f} {g} eq = λ i → λ x → eq x i

  cong' : {X Y : Type} -> (f : X -> Y) -> (x y : X) -> x ≡ y -> f x ≡ f y
  cong' {X} {Y} f x y eq = λ i → f (eq i)

  -- transport : {A B : Type} → A ≡ B → A → B
  -- Given a path from A to B, and an element of A, we can get
  -- an element of B


  ----------------------------------------------------
  -- Guarded stuff

  module Guarded (k : Clock) where

    private
      variable
        l : Level
    private
        ▹_ : Set l → Set l
        ▹_ A = ▹_,_ k A

  -- ▹ : Type -> Type (pronounced "later")
  -- Given X : Type
  -- ▹ X : Type (X one time step from now)
  -- ▹ X ≡ (Tick -> X)

  -- A Tick is evidence that one time step passed.
  -- t : Tick in context means that one time step has passed

  -- next : X -> ▹ X
  -- next x = λ t -> x (we don't actually use t here)

  -- fix : (▹ A -> A) -> A      "guarded recursion"
  -- fix f ≡ f (next (fix f))

    next' : {X : Type} -> X -> ▹ X
    next' x = λ t → x

    map : {X Y : Type} -> (X -> Y) -> ▹ X -> ▹ Y
    map f x~ = λ t → f (x~ t)

    ap : {X Y : Type} -> ▹ (X -> Y) -> ▹ X -> ▹ Y
    ap f~ x~ = λ t → f~ t (x~ t)

 
    -- a ▹-algebra is a pair (A , θA) where A is a type and  θA : ▹ A -> A

    -- Type is a ▹-algebra
    -- i.e. there's a map ▸ : ▹ Type -> Type

    ▸' : ▹ Type -> Type
    ▸' T~ = ∀ (t : Tick k) -> T~ t

    -- This lets us write down types that mention ticks.
    -- Example:
    -- ▸' (λ t -> x~ t ≡ y~ t)  : Type

    -- Example:
    -- Given A : ▹ Type
    -- Can't write x : A     (Agda won't accept this... A is not of type Type but rather ▹ T)
    -- Can write   x : ▸' A  (Agda will accept this, since ▸' A has type Type)


    --------------------------------------------
    -- lift monad

    data L℧' (X : Type) : Type where
      η : X -> L℧' X           -- "computation returns a value of type X"
      ℧ : L℧' X                -- "computation errors"
      θ : ▹ (L℧' X) -> L℧' X   -- "computation is still running"

    -- Infinite loop computation via fix
    loop : {X : Type} -> L℧' X
    loop = fix θ

    -- Monadic extend function for lift
    -- We define this by guarded recursion
    ext : {X Y : Type} -> (X -> L℧' Y) -> (L℧' X -> L℧' Y)
    ext {X} {Y} f = fix f'
      where
        f' : ▹ (L℧' X → L℧' Y) → (L℧' X → L℧' Y)
        f' rec (η x) = f x
        f' rec ℧ = ℧
        f' rec (θ x~) = θ (λ t → rec t (x~ t)) -- Since we're under a θ, we can introduce a t
        

    
   
  
  
