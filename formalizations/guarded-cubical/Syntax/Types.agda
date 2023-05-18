{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}


open import Common.Later hiding (next)

module Syntax.Types  where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Data.Nat hiding (_·_) renaming (ℕ to Nat)
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Cubical.Data.Prod hiding (map)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
  using (List ; length ; map ; _++_ ; cons-inj₁ ; cons-inj₂)
  renaming ([] to · ; _∷_ to _::_)
open import Cubical.Data.Empty renaming (rec to exFalso)

open import Syntax.Context as Context

private
 variable
   ℓ : Level


-- Types --

data Interval : Type where
  l r : Interval

data iCtx : Type where
  Empty : iCtx
  Full : iCtx


data Ty : iCtx -> Type

ty-endpt : Interval -> Ty Full -> Ty Empty

_⊑_ : Ty Empty -> Ty Empty -> Type
A ⊑ B = Σ[ c ∈ Ty Full ] ((ty-endpt l c ≡ A) × (ty-endpt r c ≡ B))

data Ty where
  nat : ∀ {Ξ} -> Ty Ξ
  dyn : ∀ {Ξ} -> Ty Ξ
  _⇀_ : ∀ {Ξ} -> Ty Ξ -> Ty Ξ -> Ty Ξ
  inj-nat : Ty Full
  inj-arr : Ty Full
  comp : ∀ (c : Ty Full) -> (d : Ty Full) ->
    (ty-endpt l c ≡ ty-endpt r d) -> Ty Full
  -- isProp⊑ : ∀ {A B : Ty }

ty-endpt p nat = nat
ty-endpt p dyn = dyn
ty-endpt p (cin ⇀ cout) = ty-endpt p cin ⇀ ty-endpt p cout
ty-endpt l inj-nat = nat
ty-endpt r inj-nat = dyn
ty-endpt l inj-arr = (dyn ⇀ dyn) -- inj-arr : (dyn -> dyn) ⊑ dyn
ty-endpt r inj-arr = dyn
ty-endpt l (comp c d _) = ty-endpt l d
ty-endpt r (comp c d _) = ty-endpt r c




_[_/i] : Ty Full -> Interval -> Ty Empty
c [ p /i] = ty-endpt p c

ty-left : Ty Full -> Ty Empty
ty-left = ty-endpt l

ty-right : Ty Full -> Ty Empty
ty-right = ty-endpt r

CompTyRel : Type
CompTyRel = Σ (Ty Full × Ty Full)
  λ { (c' , c) -> (ty-left c') ≡ (ty-right c) }

CompTyRel-comp : CompTyRel -> Ty Full
CompTyRel-comp ((c' , c) , pf) = comp c' c pf

CompTyRel-endpt : Interval -> CompTyRel -> Ty Full
CompTyRel-endpt l ((c , d) , _) = c
CompTyRel-endpt r ((c , d) , _) = d




-- Given a "normal" type A, view it as its reflexivity precision derivation c : A ⊑ A.
ty-refl : Ty Empty -> Ty Full
ty-refl nat = nat
ty-refl dyn = dyn
ty-refl (Ai ⇀ Ao) = ty-refl Ai ⇀ ty-refl Ao

ty-endpt-refl : {A : Ty Empty} -> (p : Interval) -> ty-endpt p (ty-refl A) ≡ A
ty-endpt-refl {nat} p = refl
ty-endpt-refl {dyn} p = refl
ty-endpt-refl {A ⇀ B} p = cong₂ _⇀_ (ty-endpt-refl p) (ty-endpt-refl p)

-- ############### Contexts ###############
open Ctx

TyCtx : iCtx → Type (ℓ-suc ℓ-zero)
TyCtx Ξ = Ctx (Ty Ξ)

-- Endpoints of a full context
ctx-endpt : (p : Interval) -> TyCtx Full -> TyCtx Empty
ctx-endpt p = Context.map (ty-endpt p)

CompCtx : (Δ Γ : TyCtx Full)
        -> (pf : ctx-endpt l Δ ≡ ctx-endpt r Γ)
        -> TyCtx Full
CompCtx Δ Γ pf .var = Δ .var
CompCtx Δ Γ pf .isFinSetVar = Δ .isFinSetVar
CompCtx Δ Γ pf .el x = comp (Δ .el x)
                            (Γ .el (transport (cong var pf) x))
                            λ i → pf i .el (transport-filler (cong var pf) x i)

-- -- "Contains" relation stating that a context Γ contains a type T
-- data _∋_ : ∀ {Ξ} -> Ctx Ξ -> Ty Ξ -> Set where
--   vz : ∀ {Ξ Γ S} -> _∋_ {Ξ} (S :: Γ) S
--   vs : ∀ {Ξ Γ S T} (x : _∋_ {Ξ} Γ T) -> (S :: Γ ∋ T)

-- infix 4 _∋_

-- ∋-ctx-endpt : {Γ : Ctx Full} {c : Ty Full} -> (p : Interval) ->
--   (Γ ∋ c) -> ((ctx-endpt p Γ) ∋ (ty-endpt p c))
-- ∋-ctx-endpt p vz = vz
-- ∋-ctx-endpt p (vs Γ∋c) = vs (∋-ctx-endpt p Γ∋c)



-- View a "normal" typing context Γ as a type precision context where the derivation
-- corresponding to each type A in Γ is just the reflexivity precision derivation A ⊑ A.
ctx-refl : TyCtx Empty -> TyCtx Full
ctx-refl = Context.map ty-refl

-- For a given typing context, the endpoints of the corresponding reflexivity precision
-- context are the typing context itself.
ctx-endpt-refl : {Γ : TyCtx Empty} -> (p : Interval) -> ctx-endpt p (ctx-refl Γ) ≡ Γ
ctx-endpt-refl {Γ} p = Ctx≡ _ _ refl (funExt λ x → ty-endpt-refl {A = Γ .el x} p)


