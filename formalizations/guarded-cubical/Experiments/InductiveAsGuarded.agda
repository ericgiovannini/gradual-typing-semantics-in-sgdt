{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --polarity #-}

open import Common.Later

module Experiments.InductiveAsGuarded (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty as ⊥


private
  variable
    ℓ ℓ' : Level

private
  ▹_ : Type ℓ -> Type ℓ
  ▹ A = ▹_,_ k A


-- The inductive analogue of the guarded lift monad. Unlike the
-- guarded lift monad, this type does not allow for infinite
-- computations.

data LiftFinite (X : Type ℓ) : Type ℓ where
  ret : X → LiftFinite X
  theta : LiftFinite X → LiftFinite X


-- The same type, but now using a later to make clear the similarity
-- with the guarded lift monad.  The difference is the additional
-- natural number parameter, which ensures that we cannot construct
-- infinitary/nonterminating elements of the type.

data LiftTest (X : Type ℓ) : {n : ℕ} → Type ℓ where
  ret : {n : ℕ} → X → LiftTest X {n}
  theta : {n : ℕ} → ▹ (LiftTest X {n}) → LiftTest X {suc n}


module _ (X : Type ℓ) (B : Type ℓ') where
  
  LTrec : (X → B)
    → (▹ B → B)
    → ▹ ({n : ℕ} → LiftTest X {n} → B)
    →    {n : ℕ} → LiftTest X {n} → B
  LTrec ret* theta* IH (ret x) = ret* x
  LTrec ret* theta* IH (theta l~) = theta* (λ t → IH t (l~ t))

  foo : LiftTest X {100}
  foo = {!fix theta!}


-- The same type again, this time using the equivalent approach of
-- guarded recursion rather than defining it as an Agda datatype
-- involving later.

LiftTest2 : (X : Type ℓ) → {n : ℕ} → Type ℓ
LiftTest2 X = fix aux
  where
    aux : {!▹ Type → Type!}
    aux  T~ = {!!}



-- Given a strictly-positive functor, we construct a type of "guarded
-- least fixpoint".  When globalized using clock-quantification, the
-- resulting coinductive type/final coalgebra is isomorphic to the
-- corresponding inductive type/initial algebra.

module _ (F : Type ℓ → Type ℓ) where

  -- data Mu : Type ℓ where
  --   fold : ▹ (F Mu) → Mu

  Mu : Type ℓ
  Mu = fix Mu'
    where
      Mu' : ▹ Type ℓ → Type ℓ
      Mu' T~ = ▸ (λ t → F (T~ t))



  MuTest : {n : ℕ} → Type ℓ
  MuTest {n} = fix Mu' {n}
    where
      Mu' : ▹ ({n : ℕ} → Type ℓ) → {n : ℕ} → Type ℓ
      Mu' T~ {zero} = ⊥*
      Mu' T~ {suc n} = ▸ (λ t → T~ t {n})


