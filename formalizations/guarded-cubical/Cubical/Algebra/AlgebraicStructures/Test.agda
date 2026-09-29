{-# OPTIONS --polarity --guardedness #-}

{-

Formalization of algebraic structures as an hSet A equipped with a
type-indexed collection of operations and equations.

-}


module Cubical.Algebra.AlgebraicStructures.Test where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.Sum as Sum

open import Cubical.Data.Nat
open import Cubical.Data.FinData


private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓar ℓE ℓq : Level
    ℓY : Level
    ℓA ℓB : Level


module _ (sig : ℕ → Type) where

  data Tm (X : Type) : Type where
    var  : {n : ℕ} → X → Tm X
    node : {n : ℕ} → (op : sig n) → (Fin n → Tm X) → Tm X


record Theory : Type (ℓ-suc ℓ-zero) where
  field
    sig : ℕ → Type
    E : ℕ → Type
    lhs rhs : (n : ℕ) → E n → Tm sig (Fin n)


module _ (sig : ℕ → Type) where

  record Structure (ℓ : Level) : Type (ℓ-suc ℓ) where
    field
      B : Type ℓ
      ⟦_⟧ : {n : ℕ} → (op : sig n) → (Fin n → B) → B

  module _ (S : Structure ℓ) where
    private module S = Structure S
    
    interp : {X : Type} → (ρ : X → S.B) → (Tm sig X → S.B)
    interp ρ (var x) = ρ x
    interp ρ (node op f) = S.⟦ op ⟧ (λ k → interp ρ (f k))
  

module _ (T : Theory) where

  private
    module T = Theory T

  data Free (X : Type) : Type ℓ-zero where

    -- Inclusion of generators
    var : X → Free X

    -- interpreting a term with n free variables, given a map ρ
    -- sending each variable to Free X.
    tm : (n : ℕ) → (τ : Tm T.sig (Fin n)) → (ρ : Fin n → Free X) → Free X

    -- Flattening a term. Given an operation op of arity n, and a map
    -- τ sending each of the n variables to a Term with m variables,
    -- and a map ρ sending each of the m variables to an element of
    -- Free X, we can either:
    -- 
    -- 1. interpret the Term `node op τ`,   of type Tm T.sig (Fin m), using ρ
    -- 2. interpret the term `node op var`, of type Tm T.sig (Fin n), using ρ'
    -- where ρ' : Fin n → Free X takes k : Fin n and interprets τ k.
    flt : (n m : ℕ) → (op : T.sig n)
      → (τ : Fin n → Tm T.sig (Fin m))
      → (ρ : Fin m → Free X)
      → tm m (node op τ) ρ ≡
        tm n (node op (var {n = n})) (λ k → tm m (τ k) ρ)

    -- Equations hold
    eq : (n : ℕ) → (e : T.E n) → (ρ : Fin n → Free X)
      → tm n (T.lhs n e) ρ ≡ tm n (T.rhs n e) ρ

    -- isSet
    trunc : isSet (Free X)


module _ (T : Theory) where
  private module T = Theory T
  
  record Model (ℓ : Level) : Type (ℓ-suc ℓ) where
    field
      S : Structure T.sig ℓ
    open Structure S public
    field
      ⟦_⟧e : {n : ℕ} → (e : T.E n)
        → (ρ : Fin n → B)
        → interp _ S ρ (T.lhs _ e) ≡ interp _ S ρ (T.rhs _ e)

{-
module _ (T : Theory) where

  private
    module T = Theory T

  module _ {X : Type} {B : Type}
    (var* : X → B)
    (op* : (n : ℕ) → (op : T.sig n) → (Fin n → B) → B)
    where

    struct : Structure T.sig ℓ-zero
    struct .Structure.B = B
    struct .Structure.⟦_⟧ {n = n} op = op* n op

    recFree : (m : Free T X) → B
    recFree (var x) = var* x
    recFree (tm n τ ρ) = interp T.sig struct (λ k → recFree (ρ k)) τ
    recFree (flt n m op τ ρ i) = {!!}
    recFree (eq n e ρ i) = {!!}
    recFree (trunc m n p q i j) = {!!}
-}   

module _ (T : Theory) where

  private
    module T = Theory T

    module _ {X : Type} {M : Model T ℓ-zero} (var* : X → M .Model.B) where
      private module M = Model M

      recF : (m : Free T X) → M.B
      recF (var x) = var* x
      recF (tm n τ ρ) =
        interp T.sig M.S (λ k → recF (ρ k)) τ
      recF (flt n m op τ ρ i) =
        M.⟦ op ⟧ (λ l → interp T.sig M.S (λ k → recF (ρ k)) (τ l))
      recF (eq n e ρ i) =
        M.⟦ e ⟧e (λ k → recF (ρ k)) i
      recF (trunc m n p q i j) = {!!}
