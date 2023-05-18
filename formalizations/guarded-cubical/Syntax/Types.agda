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


import Syntax.DeBruijnCommon


private
 variable
   ℓ : Level


-- Types --

data Interval : Type where
  l r : Interval

data IntExt : Type where
  Int Ext : IntExt

data iCtx : Type where
  Empty : iCtx
  Full : iCtx


private
  variable
    α : IntExt

data Ty : {α : IntExt} -> iCtx -> Type

ty-endpt : ∀ {α} -> Interval -> Ty {α} Full -> Ty {α} Empty

data Ty where
  nat : ∀ {α Ξ} -> Ty {α} Ξ
  dyn : ∀ {α Ξ} -> Ty {α} Ξ
  _⇀_ : ∀ {α Ξ} -> Ty {α} Ξ -> Ty {α} Ξ -> Ty {α} Ξ
  inj-nat : ∀ {α} -> Ty {α} Full
  inj-arr : ∀ {α} -> Ty {α} Full
  comp : ∀ {α} -> (c : Ty {α} Full) -> (d : Ty {α} Full) ->
    (ty-endpt l c ≡ ty-endpt r d) -> Ty {α} Full
  -- order-set : isSet (Ty Full)
  ▹ : ∀ {Ξ} -> Ty {Int} Ξ -> Ty {Int} Ξ


ty-endpt p nat = nat
ty-endpt p dyn = dyn
ty-endpt p (cin ⇀ cout) = ty-endpt p cin ⇀ ty-endpt p cout
ty-endpt l inj-nat = nat
ty-endpt r inj-nat = dyn
ty-endpt l inj-arr = (dyn ⇀ dyn) -- inj-arr : (dyn -> dyn) ⊑ dyn
ty-endpt r inj-arr = dyn
ty-endpt l (comp c d _) = ty-endpt l d
ty-endpt r (comp c d _) = ty-endpt r c
ty-endpt p (▹ A) = ▹ (ty-endpt p A)


_[_/i] : ∀ {α} -> Ty {α} Full -> Interval -> Ty {α} Empty
c [ p /i] = ty-endpt p c

ty-left : ∀ {α} -> Ty {α} Full -> Ty Empty
ty-left = ty-endpt l

ty-right : ∀ {α} -> Ty {α} Full -> Ty Empty
ty-right = ty-endpt r

CompTyRel : ∀ {α} -> Type
CompTyRel {α} = Σ (Ty {α} Full × Ty Full)
  λ { (c' , c) -> (ty-left c') ≡ (ty-right c) }

CompTyRel-comp : ∀ {α} -> CompTyRel {α} -> Ty Full
CompTyRel-comp ((c' , c) , pf) = comp c' c pf

CompTyRel-endpt : ∀ {α} -> Interval -> CompTyRel {α} -> Ty Full
CompTyRel-endpt l ((c , d) , _) = c
CompTyRel-endpt r ((c , d) , _) = d




-- Given a "normal" type A, view it as its reflexivity precision derivation c : A ⊑ A.
ty-refl : Ty {α} Empty -> Ty {α} Full
ty-refl nat = nat
ty-refl dyn = dyn
ty-refl (Ai ⇀ Ao) = ty-refl Ai ⇀ ty-refl Ao
ty-refl (▹ A) = ▹ (ty-refl A)

ty-endpt-refl : {A : Ty {α} Empty} -> (p : Interval) -> ty-endpt p (ty-refl A) ≡ A
ty-endpt-refl {_} {nat} p = refl
ty-endpt-refl {_} {dyn} p = refl
ty-endpt-refl {_} {A ⇀ B} p = cong₂ _⇀_ (ty-endpt-refl p) (ty-endpt-refl p)
ty-endpt-refl {_} {▹ A} p = cong ▹ (ty-endpt-refl p)


_⊑_ : Ty {α} Empty -> Ty Empty -> Type
A ⊑ B = Σ[ c ∈ Ty Full ] ((ty-left c ≡ A) × (ty-right c ≡ B))



-- ############### Contexts ###############


Ctx : ∀ {α : IntExt} -> iCtx -> Type
Ctx {α} Ξ = List (Ty {α} Ξ)



-- Endpoints of a full context
ctx-endpt : (p : Interval) -> Ctx {α} Full -> Ctx Empty
ctx-endpt p = map (ty-endpt p)

CompCtx : (Δ Γ : Ctx {α} Full) -> (pf : ctx-endpt l Δ ≡ ctx-endpt r Γ) ->
  Ctx {α} Full
CompCtx Δ Γ pf = {!!}





-- "Contains" relation stating that a context Γ contains a type T
data _∋_ : ∀ {Ξ} -> Ctx {α} Ξ -> Ty {α} Ξ -> Set where
  vz : ∀ {Ξ Γ S} -> _∋_ {α} {Ξ} (S :: Γ) S
  vs : ∀ {Ξ Γ S T} (x : _∋_ {α} {Ξ} Γ T) -> (S :: Γ ∋ T)

infix 4 _∋_

∋-ctx-endpt : {Γ : Ctx {α} Full} {c : Ty Full} -> (p : Interval) ->
  (Γ ∋ c) -> ((ctx-endpt p Γ) ∋ (ty-endpt p c))
∋-ctx-endpt p vz = vz
∋-ctx-endpt p (vs Γ∋c) = vs (∋-ctx-endpt p Γ∋c)



-- View a "normal" typing context Γ as a type precision context where the derivation
-- corresponding to each type A in Γ is just the reflexivity precision derivation A ⊑ A.
ctx-refl : Ctx {α} Empty -> Ctx Full
ctx-refl = map ty-refl
--ctx-refl · = ·
--ctx-refl (A :: Γ) = ty-refl A :: ctx-refl Γ

-- For a given typing context, the endpoints of the corresponding reflexivity precision
-- context are the typing context itself.
ctx-endpt-refl : {Γ : Ctx {α} Empty} -> (p : Interval) -> ctx-endpt p (ctx-refl Γ) ≡ Γ
ctx-endpt-refl {_} {·} p = refl
ctx-endpt-refl {_} {A :: Γ} p = cong₂ _::_  (ty-endpt-refl p) (ctx-endpt-refl p)


