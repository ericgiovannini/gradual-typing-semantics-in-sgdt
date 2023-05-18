module Syntax.Context where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Prelude
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Data.Nat
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
-- open import Cubical.Data.Fin hiding (_/_)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors

private
  variable
    ℓ ℓ' ℓ'' : Level

record Ctx (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ-zero)) where
  field
    var : Type
    isFinSetVar : isFinSet var
    el : var → A

  varFinSet : FinSet ℓ-zero
  varFinSet = var , isFinSetVar

open Ctx

module _ {A : Type ℓ} where

  Var : Ctx A → Type
  Var Γ = Γ .var

  Ctx≡ : (Γ Δ : Ctx A)
       → (p : Var Γ ≡ Var Δ)
       → PathP (λ i → p i → A) (Γ .el) (Δ .el)   
       → Γ ≡ Δ
  Ctx≡ Γ Δ p q i .var = p i
  Ctx≡ Γ Δ p q i .isFinSetVar = lem i
    where
      lem : PathP (λ i → isFinSet (p i)) (Γ .isFinSetVar) (Δ .isFinSetVar)
      lem = (isProp→PathP (λ i → isPropIsFinSet) (Γ .isFinSetVar) (Δ .isFinSetVar))
  Ctx≡ Γ Δ p q i .el x = q i x

  empty-ctx : Ctx A
  empty-ctx .var         = ⊥
  empty-ctx .isFinSetVar = isFinSetFin
  empty-ctx .el          = λ ()

  singleton : A → Ctx A
  singleton a .var = Unit
  singleton a .isFinSetVar = isFinSetUnit
  singleton a .el = λ _ → a

  -- the-var : (a : A) → singleton a .var
  -- the-var a = tt

  append : Ctx A → Ctx A → Ctx A
  var (append Γ₁ Γ₂) = Γ₁ .var ⊎ Γ₂ .var
  isFinSetVar (append Γ₁ Γ₂) = isFinSet⊎ (varFinSet Γ₁) (varFinSet Γ₂)
  el (append Γ₁ Γ₂) (inl x₁) = Γ₁ .el x₁
  el (append Γ₁ Γ₂) (inr x₂) = Γ₂ .el x₂

  append-i₁-el : ∀ Γ₁ Γ₂ (x₁ : Γ₁ .var) → (append Γ₁ Γ₂) .el (inl x₁) ≡ Γ₁ .el x₁
  append-i₁-el = λ Γ₁ Γ₂ x₁ → refl

  cons : Ctx A → A → Ctx A
  cons Γ a = append Γ (singleton a)

  module _ (B : A → Type ℓ')  where
    substitution : ∀ (Γ : Ctx A) → Type ℓ'
    substitution Γ = ∀ (x : Γ . var) → B (Γ .el x)

    singleton-subst : (x : A) → B x → substitution (singleton x)
    singleton-subst x b tt = b

    append-subst : ∀ {Γ₁ Γ₂} → substitution Γ₁ → substitution Γ₂ → substitution (append Γ₁ Γ₂)
    append-subst γ₁ γ₂ (inl x) = γ₁ x
    append-subst γ₁ γ₂ (inr x) = γ₂ x

    append-subst-inl : {Γ₁ Γ₂ : Ctx A} → (γ₁ : substitution Γ₁) → (γ₂ : substitution Γ₂)
                     → (x₁ : Var Γ₁)
                     → (append-subst {Γ₁ = Γ₁}{Γ₂ = Γ₂} γ₁ γ₂ (inl x₁)) ≡ (γ₁ x₁)
    append-subst-inl γ₁ Γ₂ x₁ = refl

    cons-subst : ∀ {Γ x} → substitution Γ → B x → substitution (cons Γ x)
    cons-subst γ v = append-subst γ (singleton-subst _ v)

  finProd : (X : FinSet ℓ-zero) → (X .fst → Ctx A) → Ctx A
  finProd X Γs .var = Σ[ x ∈ X .fst ] Γs x .var
  finProd X Γs .isFinSetVar = isFinSetΣ X λ x → _ , (Γs x .isFinSetVar)
  finProd X Γs .el (x , y) = Γs x .el y

  append-inj-el : ∀ (X : FinSet ℓ-zero) (Γs : X .fst → Ctx A) (x : X .fst) (y : Γs x .var)
                → finProd X Γs .el (x , y) ≡ Γs x .el y
  append-inj-el X Γs x y = refl

  module _ (B : A → Type ℓ') (X : FinSet ℓ-zero) (Γs : X .fst → Ctx A) where
    finProdSubsts : (∀ (x : X .fst) → substitution B (Γs x)) → substitution B (finProd X Γs)
    finProdSubsts γs (x , y) = γs x y

map : ∀ {A : Type ℓ}{A' : Type ℓ'} → (A → A') → Ctx A → Ctx A'
map f Γ .var = Γ .var
map f Γ .isFinSetVar = Γ .isFinSetVar
map f Γ .el x = f (Γ .el x)
