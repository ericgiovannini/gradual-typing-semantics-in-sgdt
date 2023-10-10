module Syntax.Surface where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List

open import Syntax.Types

open TyPrec
open CtxPrec


private
  variable
    Γ Γ' : Ctx
    S S' T : Ty
    S⊑T : TyPrec
    B B' C C' D D' : Γ ⊑ctx Γ'
    b b' c c' d d' : S ⊑ S'



-- "Contains" relation stating that a context Γ contains a type T

data _∋_ : Ctx -> Ty -> Type where
  vz : ∀ {Γ S} -> S ∷ Γ ∋ S
  vs : ∀ {Γ S T} (x : Γ ∋ T) -> (S ∷ Γ ∋ T)


data _∋prec_ : CtxPrec -> TyPrec -> Type where
  vz : ∀ {C c} -> (cons c C) ∋prec c
  vs : ∀ {C c d} (x : C ∋prec d) -> (cons c C) ∋prec d


{-
data _∋prec_ : (C : Γ ⊑ctx Γ') -> (c : S ⊑ S') -> Type where
  vz : (c ∷ C) ∋prec c
  vs : (x : C ∋prec d) -> (c ∷ C) ∋prec d
-}

∋prec→∋-l : (C : CtxPrec) (S⊑T : TyPrec) ->
  C ∋prec S⊑T ->
  C .ctx-left ∋ S⊑T .ty-left
∋prec→∋-l _ c vz = vz
∋prec→∋-l _ c (vs {C = C'} x) = vs (∋prec→∋-l C' c x)


∋prec→∋-r : (C : CtxPrec) (S⊑T : TyPrec) ->
  C ∋prec S⊑T ->
  C .ctx-right ∋ S⊑T .ty-right
∋prec→∋-r _ c vz = vz
∋prec→∋-r _ c (vs {C = C'} x) = vs (∋prec→∋-r C' c x)


infix 4 _∋_
infix 4 _∋prec_

-- Extensional cast calculus "surface" syntax, *not* quotiented
-- by order equivalence
data Tm : Ctx -> Ty -> Set where
  var : Γ ∋ T -> Tm Γ T
  lda : Tm (S ∷ Γ) T -> Tm Γ (S ⇀ T)
  app : Tm Γ (S ⇀ T) -> Tm Γ S -> Tm Γ T
  err : Tm Γ S
  up  : (S⊑T : TyPrec) -> Tm Γ (ty-left S⊑T) -> Tm Γ (ty-right S⊑T)
  dn  : (S⊑T : TyPrec) -> Tm Γ (ty-right S⊑T) -> Tm Γ (ty-left S⊑T)
  zro : Tm Γ nat
  suc : Tm Γ nat -> Tm Γ nat
  matchNat : Tm Γ nat -> Tm Γ S -> Tm (nat ∷ Γ) S -> Tm Γ S
--  matchNat : Tm Γ S -> Tm (nat ∷ Γ) S -> Tm (nat ∷ Γ) S


-- Term precision for the surface syntax
data TmPrec : (C : Γ ⊑ctx Γ') (c : S ⊑ S') (M : Tm Γ S) (M' : Tm Γ' S') ->
  Type where
  var : ∀ {Γ⊑Γ' S⊑T} ->
    (x : Γ⊑Γ' ∋prec S⊑T) ->
    TmPrec (ctx-prec Γ⊑Γ') (ty-prec S⊑T)
           (var (∋prec→∋-l Γ⊑Γ' S⊑T x)) (var (∋prec→∋-r Γ⊑Γ' S⊑T x))
  lda : ∀ {M M'} ->
    TmPrec (c ∷ C) d M M' -> TmPrec C (c ⇀ d) (lda M) (lda M')
  app : ∀ {M M' N N'} ->
    TmPrec C (c ⇀ d) M M' -> TmPrec C c N N' -> TmPrec C d (app M N) (app M' N')
  err : TmPrec C c err err
  zro : TmPrec C nat zro zro
  suc : ∀ {M M'} -> TmPrec C nat M M' -> TmPrec C nat (suc M) (suc M')
  matchNat : ∀ {N N' Kz Kz' Ks Ks'} ->
    TmPrec C nat N N' ->
    TmPrec C c Kz Kz' ->
    TmPrec (nat ∷ C) c Ks Ks' ->
    TmPrec C c (matchNat N Kz Ks ) (matchNat N' Kz' Ks')

-- TODO these should be the more general cast rules
  upL : ∀ S⊑T {M M'} ->
    TmPrec C (ty-prec S⊑T) M M' ->
    TmPrec C (refl-⊑ (ty-right S⊑T)) (up (S⊑T) M) M'
  upR : ∀ S⊑T {M M'} ->
    TmPrec C (refl-⊑ (ty-left S⊑T)) M M' ->
    TmPrec C (ty-prec S⊑T) M (up (S⊑T) M')
  dnL : ∀ S⊑T {M M'} ->
    TmPrec C (refl-⊑ (ty-right S⊑T)) M M' ->
    TmPrec C (ty-prec S⊑T) (dn (S⊑T) M) M'
  dnR : ∀ S⊑T {M M'} ->
    TmPrec C (ty-prec S⊑T) M M' ->
    TmPrec C (refl-⊑ (ty-left S⊑T)) M (dn (S⊑T) M')
-- TODO error is bottom
-- Retraction
