
module Syntax.SyntacticBisimilarity where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Data.Sum
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.Empty renaming (rec to exFalso)

open import Syntax.Types
open import Syntax.IntensionalTerms

open TyPrec
open CtxPrec

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T U R' S' T' U' : Ty
   B B' C C' D D' : Γ ⊑ctx Γ'
   b b' c c' d d' : S ⊑ S'

private
  variable
    γ γ' γ'' : Subst Δ Γ
    δ δ' δ'' : Subst Θ Δ
    θ θ' θ'' : Subst Z Θ

    V V' V'' : Val Γ S
    M M' M'' N N' : Comp Γ S
    E E' E'' F F' : EvCtx Γ S T

-- The congruence closure of the relation with generators:
--   tick ; M ≈ M
--   V.δl ≈ id
--   V.δr ≈ id
--   E.δl ≈ id
--   E.δr ≈ id

-- TODO do we need bisimilarity to interact with the equations,
-- e.g. identity and associativity?


infix 4 _≈c_
infix 4 _≈e_
infix 4 _≈v_
infix 4 _≈s_


-- Bisimilarity for substitutions, values, ev ctxs, and computations
data _≈s_ : Subst Γ Δ -> Subst Γ Δ -> Type
data _≈v_ : Val Γ S -> Val Γ S -> Type
data _≈e_ : EvCtx Γ S T -> EvCtx Γ S T -> Type
data _≈c_ : Comp Γ S -> Comp Γ S -> Type


data _≈s_  where
  ≈-refl : γ ≈s γ
  -- ≈-ids : (ids {Γ = Γ}) ≈s ids
  ≈-∘s : γ ≈s γ' -> δ ≈s δ' -> (γ ∘s δ) ≈s (γ' ∘s δ')
  -- ≈-!s : (!s {Γ = Γ}) ≈s !s
  ≈-,s : ∀ {γ γ' : Subst Γ Δ} {V V' : Val Γ S} ->
    γ ≈s γ' ->
    V ≈v V' ->
    (γ ,s V) ≈s (γ' ,s V')
  -- ≈-wk : (wk {S = S} {Γ = Γ}) ≈s wk


data _≈v_ where
  ≈-refl : V ≈v V
  ≈-substV : V ≈v V' ->
             γ ≈s γ' ->
             V [ γ ]v ≈v V' [ γ' ]v
 -- ≈-var : (var {S = S} {Γ = Γ}) ≈v var
 -- ≈-zro : zro ≈v zro
 -- ≈-suc : suc ≈v suc
  ≈-lda : M ≈c M' ->
          lda M ≈v lda M'
 -- ≈-up : ∀ S⊑T -> up S⊑T ≈v up S⊑T -- follows from reflexivity?

  -- If δl and δr were made admissible, then these two rules wouldn't be needed
  -- ≈-δl : ∀ S⊑T (V : Val Γ (ty-left S⊑T))  -> δl S⊑T [ !s ,s V ]v ≈v V
  -- ≈-δr : ∀ S⊑T (V : Val Γ (ty-right S⊑T)) -> δr S⊑T [ !s ,s V ]v ≈v V


data _≈e_ where
  ≈-refl : E ≈e E
  ≈-∘E : E ≈e E' -> F ≈e F' -> E ∘E F ≈e E' ∘E F'
  ≈-substE : E ≈e E' -> γ ≈s γ' -> E [ γ ]e ≈e E' [ γ' ]e
  ≈-bind : M ≈c M' -> bind M ≈e bind M'
  -- ≈-dn : ∀ S⊑T -> dn S⊑T ≈e dn S⊑T -- follows from reflexivity?

  -- If δl and δr were made admissible, then these two rules wouldn't be needed
  -- ≈-δl : ∀ S⊑T -> δl S⊑T ≈e ∙E
  -- ≈-δr : ∀ S⊑T -> δr S⊑T ≈e ∙E


data _≈c_ where
  ≈-refl : M ≈c M
  ≈-tick : (M M' : Comp Γ S) -> M ≈c M' -> tick M ≈c M'
  ≈-plugE :
    E ≈e E' ->
    M ≈c M' ->
   (E [ M ]∙) ≈c (E' [ M' ]∙) -- redundant by tick-strictness + ≈-tick?
  ≈-substC : {M M' : Comp Γ S} {γ γ' : Subst Δ Γ} ->
    M ≈c M' ->
    γ ≈s γ' ->
    M [ γ ]c ≈c M' [ γ' ]c
  ≈-matchNat : {Kz Kz' : Comp Γ S} {Ks Ks' : Comp (nat ∷ Γ) S} ->
    Kz ≈c Kz' ->
    Ks ≈c Ks' ->
    (matchNat Kz Ks) ≈c matchNat Kz' Ks'


-- TODO: add symmetry


{-
≈s-refl : (γ : Subst Γ Δ) -> γ ≈s γ
≈s-refl ids = ≈-ids
≈s-refl (γ ∘s γ₁) = {!!}
≈s-refl (∘IdL i) = {!!}
≈s-refl (∘IdR i) = {!!}
≈s-refl (∘Assoc i) = {!!}
≈s-refl (isSetSubst γ γ₁ x y i i₁) = {!!}
≈s-refl (isPosetSubst x x₁ i) = {!!}
≈s-refl !s = {!!}
≈s-refl ([]η i) = {!!}
≈s-refl (γ ,s x) = {!!}
≈s-refl wk = {!!}
≈s-refl (wkβ i) = {!!}
≈s-refl (,sη i) = {!!}

≈v-refl : (V : Val Γ S) -> V ≈v V
≈v-refl (V [ γ ]v) = ≈-substV (≈v-refl V) (≈s-refl γ)
≈v-refl (substId i) = {!≈v-refl V!}
≈v-refl (substAssoc i) = {!!}
≈v-refl var = ≈-var
≈v-refl (varβ i) = {!!}
≈v-refl zro = ≈-zro
≈v-refl suc = ≈-suc
≈v-refl (lda M) = ≈-lda {!!}
≈v-refl (fun-η i) = {!!}
≈v-refl (up S⊑T) = ≈-up S⊑T
≈v-refl (δl S⊑T) = {!!}
≈v-refl (δr S⊑T) = {!!}
≈v-refl (isSetVal V V₁ x y i i₁) = {!!}
≈v-refl (isPosetVal x x₁ i) = {!!}
  
-}
