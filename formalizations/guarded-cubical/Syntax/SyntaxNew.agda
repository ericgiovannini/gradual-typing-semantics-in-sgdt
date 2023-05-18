{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}


open import Common.Later hiding (next)

module Syntax.SyntaxNew  where



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



open import Syntax.Types




private
  variable
    α : IntExt
     








-- ############### Terms / Term Precision ###############

-- All constructors below except for those for upcast and downcast are simultaneously
-- the term constructors, as well as the constructors for the corresponding term
-- precision congruence rule.
-- This explains why Ξ is generic in all but the up and dn constructors,
-- where it is Empty to indicate that we do not obtain term precision congruence rules.

data PureImpure : Type where
  Pure Impure : PureImpure

data Tm : {v : PureImpure} -> {α : IntExt} -> {Ξ : iCtx} -> (Γ : Ctx {α} Ξ) -> Ty {α} Ξ -> Type ℓ-zero

-- data Val : {α : IntExt} -> {Ξ : iCtx} -> (Γ : Ctx {α} Ξ) -> Ty {α} Ξ -> Type ℓ-zero


tm-endpt : ∀ {v} {α} (p : Interval) -> {Γ : Ctx {α} Full} -> {c : Ty {α} Full} ->
  Tm {v} {α} {Full} Γ c ->
  Tm {v} {α} {Empty} (ctx-endpt p Γ) (ty-endpt p c)



_[_] : ∀ {α Γ A B}
  → Tm {Impure} {α} {Empty} (B :: Γ) A
  → Tm {Pure} {α} {Empty} Γ B
  → Tm {Impure} {α} {Empty} Γ A
_[_] = {!!}

wk : ∀ {v α Γ A B} -> Tm {v} {α} {Empty} Γ A ->
  Tm {v} {α} {Empty} (B :: Γ) A
wk = {!!}




-- data Val where
 

data Tm where
  var : ∀ {α Ξ Γ T} -> Γ ∋ T -> Tm {Pure} {α} {Ξ} Γ T
  lda : ∀ {α Ξ Γ S T} -> (Tm {Impure} {α} {Ξ} (S :: Γ) T) -> Tm {Pure} Γ (S ⇀ T)
  app : ∀ {α Ξ Γ S T} -> (Tm {Pure} {α} {Ξ} Γ (S ⇀ T)) -> (Tm {Pure} Γ S) -> (Tm {Impure} Γ T)
  err : ∀ {α Ξ Γ A} -> Tm {Impure} {α} {Ξ} Γ A
  zro : ∀ {α Ξ Γ} -> Tm {Pure} {α} {Ξ} Γ nat
  suc : ∀ {α Ξ Γ} -> Tm {Pure} {α} {Ξ} Γ nat -> Tm {Pure} Γ nat
  ret : ∀ {α Ξ Γ A} -> Tm {Pure} {α} {Ξ} Γ A -> Tm {Impure} Γ A
  bind : ∀ {α Ξ Γ A B} -> Tm {Pure} {α} {Ξ} Γ A ->
                          Tm {Impure} {α} {Ξ} (A :: Γ) B -> Tm {Impure} {α} {Ξ} Γ B

  inj-nat : ∀ {α Ξ Γ} -> Tm {Pure} {α} {Ξ} Γ nat -> Tm {Pure} Γ dyn
  inj-arr-ext : ∀ {Ξ Γ} -> Tm {Pure} {Ext} {Ξ} Γ (dyn ⇀ dyn)     -> Tm {Pure} {Ext} Γ dyn
  inj-arr-int : ∀ {Ξ Γ} -> Tm {Pure} {Int} {Ξ} Γ (▹ (dyn ⇀ dyn)) -> Tm {Pure} {Int} Γ dyn
  case-nat :     ∀ {α Ξ Γ B} -> Tm {Pure} {α}   {Ξ} Γ dyn ->
                                Tm {Impure} {α}   {Ξ} (nat :: Γ) B             -> Tm {Impure} {α} Γ B 
  case-arr-ext : ∀ {Ξ Γ B}   -> Tm {Pure} {Ext} {Ξ} Γ dyn ->
                                Tm {Impure} {Ext} {Ξ} ((dyn ⇀ dyn) :: Γ) B     -> Tm {Impure} {Ext} Γ B 
  case-arr-int : ∀ {Ξ Γ B}   -> Tm {Pure} {Int} {Ξ} Γ dyn ->
                                Tm {Impure} {Int} {Ξ} ((▹ (dyn ⇀ dyn)) :: Γ) B -> Tm {Impure} {Int} Γ B 


  -- Other term precision rules:
 
  err-bot : ∀ {α Γ} (B : Ty {α} Empty) (M : Tm {Impure} {α} {Empty} Γ B) -> Tm {Impure} {α} {Full} (ctx-refl Γ) (ty-refl B)
  --err-bot : ∀ {α} {Γ : Ctx Full} (c : Ty Full)
  --  (M : Tm {Impure} {α} {Empty} (ctx-endpt r Γ) (ty-right c)) -> Tm {Impure} {α} {Full} Γ c
  -- TODO do we need to restrict the left endpoint of Γ?

  trans : ∀ {v : PureImpure} {Γ Δ : Ctx {α} Full} -> {A B : Ty Full} ->
    (M : Tm {v} Γ A) -> (N : Tm {v} Δ B) ->
    (ctx-p : ctx-endpt l Δ ≡ ctx-endpt r Γ) ->
    (ty-p :  ty-endpt l B ≡ ty-endpt r A)
    (tm-p : PathP (λ i → Tm {v} (ctx-p i) (ty-p i)) (tm-endpt l {Δ} {B} N) (tm-endpt r {Γ} {A} M)) ->
    Tm {v} (CompCtx Δ Γ ctx-p) (comp B A ty-p)

  -- Cast rules



  -- Equational theory:
  
  β-fun : ∀ {α Γ A B} {M : Tm {Impure} {α} {Empty} (A :: Γ) B} {V : Tm {Pure} {α} {Empty} Γ A} ->
    app (lda M) V ≡ M [ V ]


  η-fun : ∀ {α Γ A B} {Vf : Tm {Pure} {α} {Empty} Γ (A ⇀ B)} {x : (A :: Γ) ∋ A} ->
    lda (app (wk Vf) (var x)) ≡ Vf

{-
  β-case :

  η-case :

  β-ret :

  η-ret :
-}

  -- Propositional truncation:
  
  -- squash : ∀ {v α Ξ Γ A} -> (M N : Tm {v} {α} {Ξ} Γ A) -> (p q : M ≡ N) -> p ≡ q
  squash : ∀ {v α Ξ Γ A} -> isSet (Tm {v} {α} {Ξ} Γ A)

  -- Quotient the ordering:
  
  ord-squash : ∀ {v α Γ c}
    (M : Tm {v} {α} {Empty} (ctx-endpt l Γ) (ty-left c))
    (N : Tm {v} {α} {Empty} (ctx-endpt r Γ) (ty-right c)) ->
    (leq leq' : Tm {v} {α} {Full} Γ c) ->
    (tm-endpt l {Γ} {c} leq  ≡ M) -> (tm-endpt r {Γ} {c} leq  ≡ N) ->
    (tm-endpt l {Γ} {c} leq' ≡ M) -> (tm-endpt r {Γ} {c} leq' ≡ N) ->
    leq ≡ leq'


_⊑tm_ : ∀ {v α Γ A B} {c : A ⊑ B} ->
  Tm {v} {α} {Empty} (ctx-endpt l Γ) A -> Tm {v} {α} {Empty} (ctx-endpt r Γ) B -> Type


_⊑tm_ {v} {α} {Γ} {A} {B} {c , eq1 , eq2} M N = Σ[ M⊑N ∈ Tm {v} {α} {Full} Γ c ]
  ((tm-endpt l {Γ} {c} M⊑N ≡ subst (Tm (ctx-endpt l Γ)) (sym eq1) M) ×
   (tm-endpt r {Γ} {c} M⊑N ≡ subst (Tm (ctx-endpt r Γ)) (sym eq2) N))


-- Recall:
-- tm-endpt : (p : Interval) -> {Γ : Ctx Full} -> {c : Ty Full} ->
--   Tm {Full} Γ c ->
--   Tm {Empty} (ctx-endpt p Γ) (ty-endpt p c)


tm-endpt p {Γ} {c} (var x) = var (∋-ctx-endpt p x)

tm-endpt p {Γ} {(_ ⇀ cout)} (lda M1⊑M2) = lda (tm-endpt p {(_ ::  Γ)} {cout} M1⊑M2)
tm-endpt p {Γ} {cout} (app {S = cin} M1⊑M2 N1⊑N2) =
  app (tm-endpt p {Γ} {(cin ⇀ cout)} M1⊑M2) (tm-endpt p {Γ} {cin} N1⊑N2)

tm-endpt p {Γ} {c} err = err
tm-endpt p {Γ} zro = zro
tm-endpt p {Γ} (suc M1⊑M2) = suc (tm-endpt p {Γ} {nat} M1⊑M2)

-- Term-precision-only rules
--tm-endpt l .(ctx-refl _) c (err-bot .c N) = err
--tm-endpt r .(ctx-refl _) c (err-bot {Γ} .c N) =
--  transport (sym (λ i → Tm (ctx-endpt-refl {Γ} r i) (ty-right c))) N
-- Goal:  Tm Γ (ty-right c) ≡ Tm (ctx-endpt r (ctx-refl Γ)) (ty-right c)

tm-endpt p (err-bot B x) = {!!}



tm-endpt l {Γ} (trans c _ _ _ _) = {!!}
tm-endpt r {Γ} (trans c _ _ _ _) = {!!}

-- Truncation
tm-endpt p {Γ} {c} (squash M1⊑M2 M1'⊑M2' eq eq' i j) =
  squash (tm-endpt p {Γ} {c} M1⊑M2) (tm-endpt p {Γ} {c} M1'⊑M2')
    (λ k → tm-endpt p {Γ} {c} (eq k)) (λ k → tm-endpt p {Γ} {c} (eq' k)) i j

tm-endpt p (ret x) = {!!}
tm-endpt p (bind x x₁) = {!!}
tm-endpt p (inj-nat x) = {!!}
tm-endpt p (inj-arr-ext x) = {!!}
tm-endpt p (inj-arr-int x) = {!!}
tm-endpt p (case-nat x x₁) = {!!}
tm-endpt p (case-arr-ext x x₁) = {!!}
tm-endpt p (case-arr-int x x₁) = {!!}
tm-endpt p (ord-squash x x₁ x₂ x₃ x₄ x₅ x₆ x₇ i) = {!!}






{-

-- Substitution and Renaming using De Bruijn framework
module DB_Base = Syntax.DeBruijnCommon (Ty Empty) (Ctx Empty) · (_::_) _∋_ vz vs (Tm Ext {Empty})
open DB_Base -- Brings in definitions of ProofT, Kit, Subst


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

-}
