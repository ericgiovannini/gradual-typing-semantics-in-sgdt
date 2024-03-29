{-# OPTIONS --cubical -W noUnsupportedIndexedMatch #-}
 -- to allow opening this module in other files while there are still holes
-- {-# OPTIONS --allow-unsolved-metas #-}
module Syntax.Types  where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Cubical.Data.List hiding (nil)
open import Cubical.Data.Prod hiding (map)
open import Cubical.Data.Empty renaming (rec to exFalso)

-- Types --
data Ty : Type where
  nat : Ty
  dyn : Ty
  _⇀_ : Ty -> Ty -> Ty

private -- should we make this public???
 variable
   R R' S S' T T' U U' : Ty

data _⊑_ : Ty → Ty → Type where
  nat : nat ⊑ nat
  dyn : dyn ⊑ dyn
  _⇀_ : R ⊑ R' → S ⊑ S' → (R ⇀ S) ⊑ (R' ⇀ S')
  inj-nat : nat ⊑ dyn
  inj-arr : S ⊑ (dyn ⇀ dyn) → S ⊑ dyn

refl-⊑ : ∀ S → S ⊑ S
refl-⊑ nat = nat
refl-⊑ dyn = dyn
refl-⊑ (S ⇀ T) = refl-⊑ S ⇀ refl-⊑ T

trans-⊑ : S ⊑ T → T ⊑ U → S ⊑ U
trans-⊑ nat nat = nat
trans-⊑ dyn dyn = dyn
trans-⊑ inj-nat dyn = inj-nat
trans-⊑ (inj-arr c) dyn = inj-arr c
trans-⊑ (c ⇀ c') (d ⇀ d') = trans-⊑ c d ⇀ trans-⊑ c' d'
trans-⊑ nat inj-nat = inj-nat
trans-⊑ (c ⇀ c') (inj-arr d) = inj-arr (trans-⊑ (c ⇀ c') d)

_∘⊑_ : S ⊑ T → T ⊑ U → S ⊑ U
_∘⊑_ = trans-⊑

isPropTy⊑ : isProp (S ⊑ T)
isPropTy⊑ nat nat = refl
isPropTy⊑ dyn dyn = refl
isPropTy⊑ (c ⇀ c') (d ⇀ d') = cong₂ _⇀_ (isPropTy⊑ c d) (isPropTy⊑ c' d')
isPropTy⊑ inj-nat inj-nat = refl
isPropTy⊑ (inj-arr c) (inj-arr d) = cong inj-arr (isPropTy⊑ c d)

dyn-⊤ : S ⊑ dyn
dyn-⊤ {nat} = inj-nat
dyn-⊤ {dyn} = dyn
dyn-⊤ {S ⇀ S₁} = inj-arr (dyn-⊤ ⇀ dyn-⊤)

record TyPrec : Type where
  field
    ty-left  : Ty
    ty-right : Ty
    ty-prec  : ty-left ⊑ ty-right

open TyPrec
mkTyPrec : S ⊑ T → TyPrec
mkTyPrec p = record { ty-left = _ ; ty-right = _ ; ty-prec = p }

refl-TP : ∀ (S : Ty) → TyPrec
refl-TP S = record { ty-left = S ; ty-right = S ; ty-prec = refl-⊑ S }

_⇀TP_ : TyPrec → TyPrec → TyPrec
(c ⇀TP d) .ty-left = ty-left c ⇀ ty-left d
(c ⇀TP d) .ty-right = ty-right c ⇀ ty-right d
(c ⇀TP d) .ty-prec = c .ty-prec ⇀ d .ty-prec

Ctx = List Ty
private
  variable
    Γ Γ' Δ Δ' Θ Θ' : Ctx

-- Couldn't find anything in the stdlib. Data.List.Dependent is close
-- but only works for one parameter
data _⊑ctx_ : Ctx → Ctx → Type where
  [] : [] ⊑ctx []
  _∷_ : S ⊑ S' → Γ ⊑ctx Γ' → (S ∷ Γ) ⊑ctx (S' ∷ Γ')

refl-⊑ctx : ∀ Γ → Γ ⊑ctx Γ
refl-⊑ctx [] = []
refl-⊑ctx (S ∷ Γ) = (refl-⊑ S) ∷ (refl-⊑ctx Γ)

trans-⊑ctx : Γ ⊑ctx Δ → Δ ⊑ctx Θ → Γ ⊑ctx Θ
trans-⊑ctx [] [] = []
trans-⊑ctx (c ∷ C) (d ∷ D) = (trans-⊑ c d) ∷ (trans-⊑ctx C D)

record CtxPrec : Type where
  field
    ctx-left : Ctx
    ctx-right : Ctx
    ctx-prec : ctx-left ⊑ctx ctx-right

open CtxPrec
nil : CtxPrec
nil .ctx-left = []
nil .ctx-right = []
nil .ctx-prec = []

cons : TyPrec → CtxPrec → CtxPrec
cons c C .ctx-left = c .ty-left ∷ C .ctx-left
cons c C .ctx-right = c .ty-right ∷ C .ctx-right
cons c C .ctx-prec = (ty-prec c) ∷ (ctx-prec C)

refl-CP : Ctx → CtxPrec
refl-CP [] = nil
refl-CP (S ∷ Γ) = cons (refl-TP S) (refl-CP Γ)

module _ where
  open import Cubical.Foundations.HLevels
  open import Cubical.Data.W.Indexed
  open import Cubical.Data.Sum
  open import Cubical.Data.Unit

  private
    X = Unit
    St : Unit → Type
    St tt = Unit ⊎ (Unit ⊎ Unit)
    P : ∀ x → St x → Type
    P tt (inl x) = ⊥
    P tt (inr (inl x)) = ⊥
    P tt (inr (inr x)) = Unit ⊎ Unit
    inX : ∀ x → (s : St x) → P x s → X
    inX x s p = tt
    W = IW St P inX tt

    Ty→W : Ty → W
    Ty→W nat = node (inl tt) exFalso
    Ty→W dyn = node (inr (inl tt)) exFalso
    Ty→W (A ⇀ B) = node (inr (inr tt)) trees where
      trees : Unit ⊎ Unit → W
      trees (inl x) = Ty→W A
      trees (inr x) = Ty→W B

    W→Ty : W → Ty
    W→Ty (node (inl x) subtree) = nat
    W→Ty (node (inr (inl x)) subtree) = dyn
    W→Ty (node (inr (inr x)) subtree) = W→Ty (subtree (inl tt)) ⇀ W→Ty (subtree (inr tt))

    rtr : (x : Ty) → W→Ty (Ty→W x) ≡ x
    rtr nat = refl
    rtr dyn = refl
    rtr (A ⇀ B) = cong₂ _⇀_ (rtr A) (rtr B)

  isSetTy : isSet Ty
  isSetTy = isSetRetract Ty→W W→Ty rtr (isOfHLevelSuc-IW 1 (λ tt → isSet⊎ isSetUnit (isSet⊎ isSetUnit isSetUnit)) tt)
