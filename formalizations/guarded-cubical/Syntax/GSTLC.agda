{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Later

module Syntax.GSTLC (k : Clock)  where


open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Cubical.Data.Prod
open import Cubical.Foundations.Isomorphism

import Syntax.DeBruijnCommon


private
 variable
   ℓ : Level

private
  ▹_ : Set ℓ → Set ℓ
  ▹_ A = ▹_,_ k A

-- Types --

data Interval : Type where
  l r : Interval

data iCtx : Type where
  Empty :  iCtx
  Full : iCtx


data Ty : iCtx -> Type where
  nat : ∀ {Ξ} -> Ty Ξ
  dyn : ∀ {Ξ} -> Ty Ξ
  _=>_ : ∀ {Ξ} -> Ty Ξ -> Ty Ξ -> Ty Ξ
  inj-nat : Ty Full 
  inj-arrow : Ty Full -> Ty Full


-- From a "full" type, i.e. a type precision derivation, we can completely recover its left and
-- right "endpoints"
{-
lft : Ty Full -> Ty Empty
lft nat = nat
lft dyn = dyn
lft (cin => cout) = lft cin => lft cout
lft inj-nat = nat
lft (inj-arrow c) = lft c -- here, c : A ⊑ (dyn => dyn), and inj-arrow c : A ⊑ dyn

rgt : Ty Full -> Ty Empty
rgt nat = nat
rgt dyn = dyn
rgt (cin => cout) = rgt cin => rgt cout
rgt inj-nat = dyn
rgt (inj-arrow c) = dyn
-}

endpoint : Interval -> Ty Full -> Ty Empty
endpoint p nat = nat
endpoint p dyn = dyn
endpoint p (cin => cout) = endpoint p cin => endpoint p cout
endpoint l inj-nat = nat
endpoint r inj-nat = dyn
endpoint l (inj-arrow c) = endpoint l c -- here, c : A ⊑ (dyn => dyn), and inj-arrow c : A ⊑ dyn
endpoint r (inj-arrow c) = dyn

_[_/i] : Ty Full -> Interval -> Ty Empty
c [ p /i] = endpoint p c

left : Ty Full -> Ty Empty
left = endpoint l

right : Ty Full -> Ty Empty
right = endpoint r


_⊑_ : Ty Empty -> Ty Empty -> Type
A ⊑ B = Σ[ c ∈ Ty Full ] ((left c ≡ A) × (right c ≡ B))


infixr 5 _=>_

⊑-ref : (A : Ty Empty) -> A ⊑ A
⊑-ref nat = nat , (refl , refl)
⊑-ref dyn = dyn , (refl , refl)
⊑-ref (Ai => Ao) with ⊑-ref Ai | ⊑-ref Ao
... | ci , (eq-left-i , eq-right-i) | co , (eq-left-o , eq-right-o) =
  (ci => co) ,
    ((cong₂ _=>_ eq-left-i eq-left-o) ,
     (cong₂ _=>_ eq-right-i eq-right-o))

{-

{-
data _⊑_ : Ty Empty -> Ty Empty -> Set where
  dyn : dyn ⊑ dyn
  _=>_ : {A A' B B' : Ty Empty} ->
    A ⊑ A' -> B ⊑ B' -> (A => B) ⊑ (A' => B')
  nat : nat ⊑ nat
  inj-nat : nat ⊑ dyn
  inj-arrow : {A : Ty Empty} ->
    A ⊑ (dyn => dyn) -> A ⊑ dyn
  -- inj-arrow : {A A' : Ty} ->
  --   (A => A') ⊑ (dyn => dyn) -> (A => A') ⊑ dyn
-}


⊑comp : {A B C : Ty} ->
  A ⊑ B -> B ⊑ C -> A ⊑ C
⊑comp dyn dyn = dyn
⊑comp {Ai => Ao} {Bi => Bo} {Ci => Co} (cin => cout) (din => dout) =
  (⊑comp cin din) => (⊑comp cout dout)
⊑comp {Ai => Ao} {Bi => Bo} (cin => cout) (inj-arrow (cin' => cout')) =
  inj-arrow ((⊑comp cin cin') => (⊑comp cout cout'))
⊑comp nat nat = nat
⊑comp nat inj-nat = inj-nat
⊑comp inj-nat dyn = inj-nat
⊑comp (inj-arrow c) dyn = inj-arrow c



module ⊑-properties where
  -- experiment with modules
  ⊑-prop : ∀ A B → isProp (A ⊑ B)
  ⊑-prop .dyn .dyn dyn dyn = refl
  ⊑-prop .(_ => _) .(_ => _) (p1 => p3) (p2 => p4) = λ i → (⊑-prop _ _ p1 p2 i) => (⊑-prop _ _ p3 p4 i)
  ⊑-prop .nat .nat nat nat = refl
  ⊑-prop .nat .dyn inj-nat inj-nat = refl
  ⊑-prop A .dyn (inj-arrow p1) (inj-arrow p2) = λ i → inj-arrow (⊑-prop _ _ p1 p2 i)

  dyn-⊤ : ∀ A → A ⊑ dyn
  dyn-⊤ nat = inj-nat
  dyn-⊤ dyn = dyn
  dyn-⊤ (A => B) = inj-arrow (dyn-⊤ A => dyn-⊤ B)

  ⊑-dec : ∀ A B → Dec (A ⊑ B)
  ⊑-dec A dyn = yes (dyn-⊤ A)
  ⊑-dec nat nat = yes nat
  ⊑-dec nat (B => B₁) = no (λ ())
  ⊑-dec dyn nat = no (λ ())
  ⊑-dec dyn (B => B₁) = no (λ ())
  ⊑-dec (A => A₁) nat = no ((λ ()))
  ⊑-dec (A => B) (A' => B') with (⊑-dec A A') | (⊑-dec B B')
  ... | yes p | yes q = yes (p => q)
  ... | yes p | no ¬p = no (refute ¬p)
    where refute : ∀ {A A' B B'} → (¬ (B ⊑ B')) → ¬ ((A => B) ⊑ (A' => B'))
          refute ¬p (_ => p) = ¬p p
  ... | no ¬p | _ = no (refute ¬p)
    where refute : ∀ {A A' B B'} → (¬ (A ⊑ A')) → ¬ ((A => B) ⊑ (A' => B'))
          refute ¬p (p => _) = ¬p p
    
-}


-- Contexts --

data Ctx : iCtx -> Type where
  · : ∀ {Ξ} -> Ctx Ξ
  _::_ : ∀ {Ξ} -> Ctx Ξ -> Ty Ξ -> Ctx Ξ

infixr 5 _::_

-- Given a "normal" type A, view it as its reflexivity precision derivation c : A ⊑ A.
ty-refl : Ty Empty -> Ty Full
ty-refl nat = nat
ty-refl dyn = dyn
ty-refl (Ai => Ao) = ty-refl Ai => ty-refl Ao

-- View a "normal" typing context Γ as a type precision context where the derivation
-- corresponding to each type A in Γ is just the reflexivity precision derivation A ⊑ A.
ctx-refl : Ctx Empty -> Ctx Full
ctx-refl · = ·
ctx-refl (Γ :: A) = ctx-refl Γ :: ty-refl A

-- Flag determining whether the syntax is intensional (i.e., with θ) or extensional
data IntExt : Type where
  Int Ext : IntExt

-- "Contains" relation stating that a context Γ contains a type T
data _∋_ : ∀ {Ξ} -> Ctx Ξ -> Ty Ξ -> Set where
  vz : ∀ {Ξ Γ S} -> _∋_ {Ξ} (Γ :: S) S
  vs : ∀ {Ξ Γ S T} (x : _∋_ {Ξ} Γ T) -> (Γ :: S ∋ T)

infix 4 _∋_


-- All constructors below except for those for upcast and downcast are simultaneously
-- the term constructors, as well as the constructors for the corresponding term
-- precision congruence rule.
-- This explains why Ξ is generic in all but the up and dn constructors,
-- where it is Empty to indicate that we do not obtain term precision congruence rules.

-- All constructors below except for θ simultaneously belong to the extensional
-- and intensional languages. θ only exists in the intensional language.
data Tm : (α : IntExt) {Ξ : iCtx} -> (Γ : Ctx Ξ) -> Ty Ξ -> Set where
  var : ∀ {α Ξ Γ T}   -> Γ ∋ T -> Tm α {Ξ} Γ T
  lda : ∀ {α Ξ Γ S T} -> (Tm α {Ξ} (Γ :: S) T) -> Tm α Γ (S => T)
  app : ∀ {α Ξ Γ S T} -> (Tm α {Ξ} Γ (S => T)) -> (Tm α Γ S) -> (Tm α Γ T)
  err : ∀ {α Ξ Γ A} -> Tm α {Ξ} Γ A
  up  : ∀ {α Γ} (c : Ty Full) -> Tm α {Empty} Γ (left c) -> Tm α {Empty} Γ (right c)
  dn  : ∀ {α Γ} (c : Ty Full) -> Tm α {Empty} Γ (right c) -> Tm α {Empty} Γ (left c)
  zro : ∀ {α Ξ Γ} -> Tm α {Ξ} Γ nat
  suc : ∀ {α Ξ Γ} -> Tm α {Ξ} Γ nat -> Tm α Γ nat
  θ   : ∀ {Ξ Γ A} -> ▹ Tm Int {Ξ} Γ A -> Tm Int {Ξ} Γ A

 


  -- Equational theory

  -- Other term precision rules
  err-bot : ∀ {α Γ} (c : Ty Full) (M : Tm α {Empty} Γ (right c)) -> Tm α {Full} (ctx-refl Γ) c


-- TODO need to quotient by the equational theory!

-- TODO non-congruence term precision rules



-- Substitution and Renaming using De Bruijn framework
module DB_Base = Syntax.DeBruijnCommon (Ty Empty) (Ctx Empty) · (_::_) _∋_ vz vs (Tm Ext {Empty})
open DB_Base
  -- Brings in definitions of ProofT, Kit, Subst


  -- Lift function --

lft : {Δ Γ : Ctx Empty} {S : Ty Empty} {_◈_ : ProofT}
       (K : Kit _◈_) (τ : Subst Δ Γ _◈_) {T : Ty Empty} (h : (Γ :: S) ∋ T) -> (Δ :: S) ◈ T       
lft (kit vr tm wk) τ vz = vr vz
lft (kit vr tm wk) τ (vs x) = wk (τ x)
  -- Note that the type of lft can also be written as (Subst Δ Γ _◈_) -> (Subst (Δ ∷ S) (Γ ∷ S) _◈_)

  -- Traversal function --


trav : {Δ Γ : Ctx Empty} {T : Ty Empty} {_◈_ : ProofT} (K : Kit _◈_)
         (τ : Subst Δ Γ _◈_) (t : Tm Ext Γ T) -> Tm Ext Δ T
trav (kit vr tm wk) τ (var x) = tm (τ x)
trav K τ (lda t') = (lda (trav K (lft K τ) t'))
trav K τ (app f s) =  (app (trav K τ f) (trav K τ s))
trav K τ (up deriv t') =  (up deriv (trav K τ t'))
trav K τ (dn deriv t') = (dn deriv (trav K τ t'))
trav K τ err = err
trav K τ zro = zro
trav K τ (suc t') = (suc (trav K τ t'))


open DB_Base.DeBruijn trav var
-- Gives us renaming and substitution

-- Single substitution
-- N[M/x]


_[_] : ∀ {Γ A B}
  → Tm Ext (Γ :: B) A
  → Tm Ext Γ B
  → Tm Ext Γ A
_[_] {Γ} {A} {B} N M = {!!} -- sub Γ (Γ :: B) σ A N
  where
    σ : Subst Γ (Γ :: B) (Tm Ext) -- i.e., {T : Ty} → Γ :: B ∋ T → Tm Γ T
    σ vz = M
    σ (vs x) = var x





