{-# OPTIONS --cubical #-}
 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}
module Syntax.Logic  where

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
open import Syntax.Terms

data ValPrec : (Γ : PrecCtx) (A : TyPrec) (V : Val (ctx-endpt l Γ) (ty-endpt l A)) (V' : Val (ctx-endpt r Γ) (ty-endpt r A)) → Type (ℓ-suc ℓ-zero)
data CompPrec : (Γ : PrecCtx) (A : TyPrec) (M : Comp (ctx-endpt l Γ) (ty-endpt l A)) (M' : Comp (ctx-endpt r Γ) (ty-endpt r A)) → Type (ℓ-suc ℓ-zero)
data EvCtxPrec : (Γ : PrecCtx) (A : TyPrec) (B : TyPrec) (E : EvCtx (ctx-endpt l Γ) (ty-endpt l A) (ty-endpt l B)) (E' : EvCtx (ctx-endpt r Γ) (ty-endpt r A) (ty-endpt r B)) → Type (ℓ-suc ℓ-zero)

data ValPrec where
data CompPrec where
data EvCtxPrec where

