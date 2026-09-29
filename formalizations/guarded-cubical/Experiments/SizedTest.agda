{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --sized-types #-}

module SizedTest where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Agda.Builtin.Size


private
  variable
    ℓ ℓ' : Level

-- Attempt 1
data Test (α : Size) : Type ℓ-zero where
  foo : ∀ (β : Size< α) → Test α
  bar : ∀ (β : Size< α) → Test β → Test α

foo-eq : ∀ α (β : Size< (↑ α)) → foo α ≡ foo β
foo-eq α β = {!!}

TestIso : ∀ α → Iso (Test (↑ α)) (⊤ ⊎ Test α)
TestIso α .Iso.fun (foo β) = inl tt
TestIso α .Iso.fun (bar β x) = inr x

TestIso α .Iso.inv (inl tt) = foo α
TestIso α .Iso.inv (inr x) = bar α x

TestIso α .Iso.sec (inl tt) = refl
TestIso α .Iso.sec (inr x) = refl

TestIso α .Iso.ret (foo β) = {!!}
TestIso α .Iso.ret (bar β a) = {!!}

-------------------------------------------------------

-- Attempt 2
data Test2 (α : Size) : Type ℓ-zero where
  foo : Test2 α
  bar : ∀ (β : Size< α) → Test2 β → Test2 α

Test2Iso : ∀ α → Iso (Test2 (↑ α)) (⊤ ⊎ Test2 α)
Test2Iso α .Iso.fun foo = inl tt
Test2Iso α .Iso.fun (bar β x) = inr x

Test2Iso α .Iso.inv (inl tt) = foo
Test2Iso α .Iso.inv (inr x) = bar α x

Test2Iso α .Iso.sec (inl tt) = refl
Test2Iso α .Iso.sec (inr x) = refl

Test2Iso α .Iso.ret foo = refl
Test2Iso α .Iso.ret (bar β a) = {!!}


-------------------------------------------------------

-- Attempt 3 (note that α is an index, not a parameter.)

data Test3 : (α : Size) → Type ℓ-zero where
  foo : ∀ α → Test3 α
  bar : ∀ α → Test3 α → Test3 (↑ α)

Test3Iso : ∀ α → Iso (Test3 (↑ α)) (⊤ ⊎ Test3 α)
Test3Iso α .Iso.fun (foo .(↑ α)) = inl tt
Test3Iso α .Iso.fun (bar .α x) = inr x

Test3Iso α .Iso.inv (inl tt) = foo α
Test3Iso α .Iso.inv (inr x) = bar α x

Test3Iso α .Iso.sec (inl tt) = refl
Test3Iso α .Iso.sec (inr x) = refl

Test3Iso α .Iso.ret (foo .(↑ α)) = refl
Test3Iso α .Iso.ret (bar .α a) = refl
