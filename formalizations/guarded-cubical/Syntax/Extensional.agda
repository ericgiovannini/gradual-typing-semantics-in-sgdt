module Syntax.Extensional  where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Cubical.Data.Prod hiding (map)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.Empty renaming (rec to exFalso)

open import Syntax.Types

open TyPrec

private
 variable
   Δ Δ' Γ Γ' Θ Z : Ctx
   R S S' T T' U : Ty
   B B' C C' D D' : Γ ⊑ctx Γ'
   b b' c c' d d' : S ⊑ S'

data Var : (Γ : Ctx) (S : Ty) → Type where
  zero : Var (S ∷ Γ) S
  succ : Var Γ S → Var (T ∷ Γ) S

data Term Γ : (S : Ty) → Type

private
  variable
    M M' N N' : Term Γ S

data Term Γ where
  var : Var Γ S → Term Γ S
  lda : Term (S ∷ Γ) T → Term Γ (S ⇀ T)
  app : Term Γ (S ⇀ T) → Term Γ S → Term Γ T
  zro : Term Γ nat
  suc : Term Γ nat → Term Γ nat
  matchNat : Term Γ nat → Term (nat ∷ Γ) T → Term (nat ∷ Γ) T
           → Term Γ T
  cast : ∀ S T → Term Γ S → Term Γ T

data Var⊑ : (C : Γ ⊑ctx Γ') (c : S ⊑ S') → Type where
  zero : Var⊑ (c ∷ C) c
  suc : Var⊑ C c → Var⊑ (d ∷ C) c

data Term⊑ (C : Γ ⊑ctx Γ') : (c : S ⊑ S') → Type where
  var : Var⊑ C c → Term⊑ C c
  lda : Term⊑ (c ∷ C) d → Term⊑ C (c ⇀ d)
  app : Term⊑ C (c ⇀ d) → Term⊑ C c → Term⊑ C d
  zro : Term⊑ C nat
  suc : Term⊑ C nat → Term⊑ C nat
  matchNat : Term⊑ C nat → Term⊑ (nat ∷ C) c → Term⊑ (nat ∷ C) c
           → Term⊑ C c
  castL : ∀ S S' → (c : S ⊑ T)(c' : S' ⊑ T)
        → Term⊑ C c
        → Term⊑ C c'
  castR : ∀ T T' → (c : S ⊑ T) (c' : S ⊑ T')
        → Term⊑ C c
        → Term⊑ C c'

var⊑-l : {C : Γ ⊑ctx Γ'} {c : S ⊑ S'} → Var⊑ C c → Var Γ S
var⊑-l zero = zero
var⊑-l (suc x) = succ (var⊑-l x)

var⊑-r : {C : Γ ⊑ctx Γ'} {c : S ⊑ S'} → Var⊑ C c → Var Γ' S'
var⊑-r zero = zero
var⊑-r (suc x) = succ (var⊑-r x)

term⊑-l : {C : Γ ⊑ctx Γ'} {c : S ⊑ S'} → Term⊑ C c → Term Γ S
term⊑-l (var x) = var (var⊑-l x)
term⊑-l (lda m) = lda (term⊑-l m)
term⊑-l (app m m₁) = app (term⊑-l m) (term⊑-l m₁)
term⊑-l zro = zro
term⊑-l (suc m) = suc (term⊑-l m)
term⊑-l (matchNat m m₁ m₂) = matchNat (term⊑-l m) (term⊑-l m₁) (term⊑-l m₂)
term⊑-l (castL S S' c _ m) = cast S S' (term⊑-l m)
term⊑-l (castR T T' c _ m) = term⊑-l m

term⊑-r : {C : Γ ⊑ctx Γ'} {c : S ⊑ S'} → Term⊑ C c → Term Γ' S'
term⊑-r (var x) = var (var⊑-r x)
term⊑-r (lda m) = lda (term⊑-r m)
term⊑-r (app m m₁) = app (term⊑-r m) (term⊑-r m₁)
term⊑-r zro = zro
term⊑-r (suc m) = suc (term⊑-r m)
term⊑-r (matchNat m m₁ m₂) = matchNat (term⊑-r m) (term⊑-r m₁) (term⊑-r m₂)
term⊑-r (castL S S' c _ m) = term⊑-r m
term⊑-r (castR T T' c _ m) = cast T T' (term⊑-r m)
