
{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}


open import Common.Later

module Semantics.Concrete.Predomain.GuardedTheory.Instances.FinPowerset (k : Clock) where

open import Cubical.Foundations.Prelude hiding (Σ)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation renaming (elim to PTElim ; rec to PTRec)

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv

open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Sigma hiding (Σ)
open import Cubical.Data.Sum
open import Cubical.Data.Empty

open import Common.LaterProperties

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Constructions
  renaming (module Clocked to PredomainClocked)
  hiding (ℕ)
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Combinators

private
  variable
    ℓ  ℓ≤  ℓ≈  : Level
    ℓ' ℓ'≤ ℓ'≈ : Level
    ℓΓ ℓ≤Γ ℓ≈Γ ℓA ℓ≤A ℓ≈A ℓA' ℓ≤A' ℓ≈A' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ : Level
    ℓA₃ ℓ≤A₃ ℓ≈A₃ ℓA₄ ℓ≤A₄ ℓ≈A₄ : Level

    ℓR : Level


private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


-- Finite powerset of X, i.e., the free join semilattice on X.

data |P| (X : Type ℓ) : Type ℓ where

  -- inclusion of generators
  [_] : X → |P| X

  -- Empty set (nullary operation)
  ∅ : |P| X

  -- Union (binary operation)
  _∪_ : |P| X → |P| X → |P| X

  -- Laws
  idem  : ∀ (m : |P| X)     → m ∪ m ≡ m
  comm  : ∀ (m n : |P| X)   → m ∪ n ≡ n ∪ m
  assoc : ∀ (m n p : |P| X) → (m ∪ n) ∪ p ≡ m ∪ (n ∪ p)

  -- h-level
  isSetP : isSet (|P| X)

-------------------------------------------------------------


-- Free join semilattice on the *predomain* X.
--
-- Since the ordering relation on predomains is antisymmetric, we need
-- to quotient the underlying set by order equivalence. Thus, we
-- define the underlying datatype simultaneously with its ordering
-- relation.
--
-- In other words, the free join semilattice on X is a quotient of the
-- finite powerset on ⟨ X ⟩.

module _ (X : Predomain ℓ ℓ≤ ℓ≈) where

  private
    module X = PredomainStr (X .snd)

  data |P≤| : Type (ℓ-max ℓ ℓ≤)

  data _⊑_ : |P≤| → |P≤| → Type (ℓ-max ℓ ℓ≤)

  data |P≤| where

    -- inclusion of generators
    [_] : ⟨ X ⟩ → |P≤|

    -- Empty set (nullary operation)
    ∅ : |P≤|

    -- Union (binary operation)
    _∪_ : |P≤| → |P≤| → |P≤|

    -- Laws
    idem  : ∀ (m : |P≤|)     → m ∪ m ≡ m
    comm  : ∀ (m n : |P≤|)   → m ∪ n ≡ n ∪ m
    assoc : ∀ (m n p : |P≤|) → (m ∪ n) ∪ p ≡ m ∪ (n ∪ p)

    -- h-level
    isSetP : isSet |P≤|

    -- antisymmetry
    antisym : ∀ (m n : |P≤|) → m ⊑ n → n ⊑ m → m ≡ n


  data _⊑_ where

    [_] : ∀ {x y : ⟨ X ⟩}
      → x X.≤ y → [ x ] ⊑ [ y ]

    -- Congruences for the operations
    ∅ : ∅ ⊑ ∅
    _∪_ : ∀ {m₁ m₂ n₁ n₂}
      → m₁ ⊑ n₁ → m₂ ⊑ n₂ → (m₁ ∪ m₂) ⊑ (n₁ ∪ n₂)

    isProp⊑ : ∀ m n → isProp (m ⊑ n)

    -- Note: Reflexivity and transitivity follow from the above rules.


module _ {X : Predomain ℓ ℓ≤ ℓ≈} where

  private
    module X = PredomainStr (X .snd)

  _∈_ : ⟨ X ⟩ → |P≤| X → hProp ℓ
  x ∈ [ y ] = (x ≡ y) , X.is-set x y
  x ∈ ∅ = ⊥* , isProp⊥*
  x ∈ (m ∪ n) = ∥ ⟨ x ∈ m ⟩ ⊎ ⟨ x ∈ n ⟩ ∥₁ , isPropPropTrunc
  

  x ∈ idem m i = {!!}
  x ∈ comm m n i = {!!}
  x ∈ assoc m n p i = {!!}
  x ∈ isSetP m n p q i j = {!!}
  x ∈ antisym m n e e' i = {!!}


  -- Egli-Milner-style ordering
  EM : |P≤| X → |P≤| X → hProp (ℓ-max ℓ ℓ≤)
  EM A B .fst =
      (∀ a → ⟨ a ∈ A ⟩ → ∃[ b ∈ ⟨ X ⟩ ] ⟨ b ∈ B ⟩ × (a X.≤ b))
    × (∀ b → ⟨ b ∈ B ⟩ → ∃[ a ∈ ⟨ X ⟩ ] ⟨ a ∈ A ⟩ × (a X.≤ b))
  EM A B .snd = isProp×
    (isPropΠ (λ a → isProp→ isPropPropTrunc))
    (isPropΠ (λ b → isProp→ isPropPropTrunc))


  -- Note that just from the types, these are not a priori mutually
  -- exclusive possibilities.
  -- But we need this to be a Prop in order to define a map from _⊑_ 
  data OrdResult (A B : |P≤| X) : Type (ℓ-max ℓ ℓ≤) where
    BothEmpty   : A ≡ ∅ → B ≡ ∅ → OrdResult A B
    NonEmptyOrd : ⟨ EM A B ⟩    → OrdResult A B
    

  lem : ∀ {A B} → _⊑_ X A B → OrdResult A B
    -- → ((A ≡ ℧) ⊎ ((A ≡ ∅) × (B ≡ ∅))) ⊎ ⟨ EM A B ⟩
    
  lem ([_] {x} {y} p) = NonEmptyOrd
    ((λ a e → ∣ (y , (refl , subst (λ z → z X.≤ y) (sym e) p)) ∣₁) ,
     (λ b e → ∣ (x , (refl , subst (λ z → x X.≤ z) (sym e) p)) ∣₁))
     
  lem ∅ = BothEmpty refl refl
  
  lem (_∪_ {m₁} {m₂} {n₁} {n₂} H₁ H₂) =
    NonEmptyOrd
      ((λ a a∈∪ → PTRec isPropPropTrunc (λ {
          (inl a∈m₁) → {!lem H₁!}
        ; (inr a∈m₂) → {!!}}) a∈∪) ,
       {!!})
  
  lem (isProp⊑ m n H H₁ i) = {!!}

  -- Using the symmetry


module _ {X : Predomain ℓ ℓ≤ ℓ≈} where

  -- Note: we define this function using only induction, even with the
  -- θ case, because ▹ A is just (Tick → A).
  --
  -- The definition using only induction is equivalent to one where we
  -- take an explicit guarded fixpoint.

  quo : (|P| ⟨ X ⟩) → |P≤| X
  quo [ x ] = [ x ]
  quo ∅ = ∅
  quo (m ∪ n) = (quo m) ∪ (quo n)
  quo (idem m i) = idem (quo m) i
  quo (comm m n i) = comm (quo m) (quo n) i
  quo (assoc m n p i) = assoc (quo m) (quo n) (quo p) i
  quo (isSetP m n p q i j) = {!!}


-- fix f ≡ f (next (fix f))


module Test (X : hSet ℓ) where

  dX : Predomain ℓ ℓ ℓ
  dX = flat X

  inv : |P≤| dX → (|P| ⟨ dX ⟩)
  inv [ x ] = [ x ]
  inv ∅ = ∅
  inv (m ∪ n) = (inv m) ∪ (inv n)
  inv (idem m i) = idem (inv m) i
  inv (comm m n i) = comm (inv m) (inv n) i
  inv (assoc m n p i) = assoc (inv m) (inv n) (inv p) i
  inv (isSetP m n p q i j) = {!!}
  inv (antisym m n e e' i) = {!!}
  -- congP (λ _ z → inv z) (antisym m n e e') i

  -- Given: m ⊑ n
  --        n ⊑ m
  --
  -- Show: inv m ≡ inv n
