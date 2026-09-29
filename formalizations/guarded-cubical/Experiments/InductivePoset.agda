{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --termination-depth=5 #-}
{-# OPTIONS --polarity #-}

open import Common.Later
open import Common.Common

module Experiments.InductivePoset (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

import Cubical.Data.List as List
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Nat
open import Cubical.Data.Empty

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Base

open BinaryRelation


private
  variable
    ℓ ℓ' : Level
    ℓA ℓA' ℓB ℓB' : Level
    ℓR ℓR₁ ℓR₂ : Level


-- Unfortunately, the standard library definitions of sum, product, and Lift
-- are not annotated with their polarities, so in order to use them
-- with Mu, we must re-declare them here.

data _⊎'_ (@++ A : Type ℓ)(@++ B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  inl : A → A ⊎' B
  inr : B → A ⊎' B

data _×'_ (@++ A : Type ℓ)(@++ B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  pair : A → B → A ×' B

record Lift' {i j} (@++ A : Type i) : Type (ℓ-max i j) where
  constructor lift
  field
    lower : A

iso⊎⊎' : ∀ (A : Type ℓ) (B : Type ℓ') → Iso (A ⊎ B) (A ⊎' B)
iso⊎⊎' A B .Iso.fun (inl x) = inl x
iso⊎⊎' A B .Iso.fun (inr x) = inr x
iso⊎⊎' A B .Iso.inv (inl x) = inl x
iso⊎⊎' A B .Iso.inv (inr x) = inr x
iso⊎⊎' A B .Iso.rightInv (inl x) = refl
iso⊎⊎' A B .Iso.rightInv (inr x) = refl
iso⊎⊎' A B .Iso.leftInv (inl x) = refl
iso⊎⊎' A B .Iso.leftInv (inr x) = refl

iso××' : ∀ (A : Type ℓ) (B : Type ℓ') → Iso (A × B) (A ×' B)
iso××' A B .Iso.fun (x , y) = pair x y
iso××' A B .Iso.inv (pair x y) = x , y
iso××' A B .Iso.rightInv (pair x y) = refl
iso××' A B .Iso.leftInv x = refl


------------------------------------------------

data Mu (F : @++ Type ℓ → Type ℓ) : Type ℓ where
  fold : F (Mu F) → Mu F


module _
  (F : @++ Type ℓ → Type ℓ) where

  unfoldMu : Mu F → F (Mu F)
  unfoldMu (fold x) = x



module Mu-Ord
  (F : @++ Type ℓ → Type ℓ)
  (F-ord : ∀ {ℓ⊑ : Level} →
    @++ (Mu F     → Mu F     → Type ℓ⊑) →
        (F (Mu F) → F (Mu F) → Type ℓ⊑))
  where

  data _⊑_ : Mu F → Mu F → Type ℓ where
    ord-fold : ∀ (x y : F (Mu F))
      → F-ord _⊑_ x y
      → fold x ⊑ fold y


  {-# TERMINATING #-}
  ord-refl : (H : isRefl _⊑_ → isRefl (F-ord _⊑_)) → isRefl _⊑_
  ord-refl H (fold x) = ord-fold x x (H (ord-refl H) x)


{-
  ord : Mu F → Mu F → Type ℓ
  ord (fold x) (fold y) = F-ord ord x y
-}

-- module _ (F : Poset ℓ ℓ' → Poset ℓ ℓ') where



------------------------------------------------

-- Defining a list of Nats as an inductive type.

NatListF : @++ Type ℓ-zero → Type ℓ-zero
NatListF X = Unit ⊎' (ℕ ×' X)

NatList : Type ℓ-zero
NatList = Mu NatListF

F-NatList : Type ℓ-zero
F-NatList = NatListF NatList

_ : F-NatList → NatList
_ = fold

unfold : NatList → F-NatList
unfold (fold x) = x


-- Constructors

nil : NatList
nil = fold (inl tt)

_∷_ : ℕ → NatList → NatList
n ∷ ns = fold (inr (pair n ns))


-- Eliminator and recursor

elimNatList : {B : NatList → Type ℓ}
  → (B nil)
  → (∀ {n ns} → B ns → B (n ∷ ns))
  → (∀ ns → B ns)
elimNatList nil* cons* (fold (inl tt)) = nil*
elimNatList {B = B} nil* cons* (fold (inr (pair n ns))) =
  cons* (elimNatList {B = B} nil* cons* ns)

elimNatList' : {B : NatList → Type ℓ}
  → (B nil)
  → (∀ n ns → B ns → B (n ∷ ns))
  → (∀ ns → B ns)
elimNatList' nil* cons* (fold (inl tt)) = nil*
elimNatList' nil* cons* (fold (inr (pair n ns))) =
  cons* _ _ (elimNatList' nil* cons* ns)

recNatList : {B : Type ℓ}
  → B
  → (ℕ → B → B)
  → (NatList → B)
recNatList {B = B} nil* cons* =
  elimNatList' {B = λ _ → B} nil* (λ n _ b → cons* n b)



-- Now defining the ordering relation on list of Nats.

UnitOrd : Unit → Unit → Type ℓ-zero
UnitOrd tt tt = Unit

NatOrd : ℕ → ℕ → Type
NatOrd x y = x ≡ y

⊎-ord : ∀ {ℓR₁ ℓR₂ : Level}
  → {A : Type ℓA} {A' : Type ℓA'}
  → {B : Type ℓB} {B' : Type ℓB'}
  → @++ (A → A' → Type ℓR₁)
  → @++ (B → B' → Type ℓR₂)
  → (A ⊎' B) → (A' ⊎' B') → Type (ℓ-max ℓR₁ ℓR₂)
⊎-ord {ℓR₂ = ℓR₂} RAA' RBB' (inl a) (inl a') = Lift' {j = ℓR₂} (RAA' a a')
⊎-ord {ℓR₁ = ℓR₁} RAA' RBB' (inr b) (inr b') = Lift' {j = ℓR₁} (RBB' b b')
⊎-ord _ _ _ _ = ⊥*


×-ord : ∀ {ℓR₁ ℓR₂ : Level}
  → {A : Type ℓA} {A' : Type ℓA'}
  → {B : Type ℓB} {B' : Type ℓB'}
  → @++ (A → A' → Type ℓR₁)
  → @++ (B → B' → Type ℓR₂)
  → (A ×' B) → (A' ×' B') → Type (ℓ-max ℓR₁ ℓR₂)
×-ord RAA' RBB' (pair a b) (pair a' b') = (RAA' a a') ×' (RBB' b b')





NatListF-Ord :
  @++ (NatList   → NatList   → Type ℓR) →
      (F-NatList → F-NatList → Type ℓR)
NatListF-Ord R x y = ⊎-ord UnitOrd (×-ord NatOrd R) x y


NatListOrd : NatList → NatList → Type
NatListOrd = _⊑_
  where open Mu-Ord NatListF NatListF-Ord
