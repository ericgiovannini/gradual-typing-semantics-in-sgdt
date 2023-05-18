{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}


open import Common.Later hiding (next)

module Syntax.SyntaxNew  where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Cubical.Data.Prod hiding (map)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
  using (List ; length ; map ; _++_ ; cons-inj₁ ; cons-inj₂)
  renaming ([] to · ; _∷_ to _::_)

open import Cubical.Data.Empty renaming (rec to exFalso)

open import Syntax.Context
-- import Syntax.DeBruijnCommon

private
 variable
   ℓ ℓ' ℓ'' : Level

open import Syntax.Types
open Ctx
-- ############### Terms / Term Precision ###############

-- All constructors below except for those for upcast and downcast are simultaneously
-- the term constructors, as well as the constructors for the corresponding term
-- precision congruence rule.
-- This explains why Ξ is generic in all but the up and dn constructors,
-- where it is Empty to indicate that we do not obtain term precision congruence rules.

data Val   : (Ξ : iCtx) -> (Γ : TyCtx Ξ) -> Ty Ξ -> Type (ℓ-suc ℓ-zero)
data Comp  : (Ξ : iCtx) -> (Γ : TyCtx Ξ) -> Ty Ξ -> Type (ℓ-suc ℓ-zero)
data EvCtx : (Ξ : iCtx) -> (Γ : TyCtx Ξ) -> Ty Ξ -> Ty Ξ -> Type (ℓ-suc ℓ-zero)
val-endpt : ∀ (p : Interval) -> {Γ : TyCtx Full} -> {c : Ty Full} ->
  Val Full Γ c ->
  Val Empty (ctx-endpt p Γ) (ty-endpt p c)
comp-endpt : ∀ (p : Interval) -> {Γ : TyCtx Full} -> {c : Ty Full} ->
  Comp Full Γ c ->
  Comp Empty (ctx-endpt p Γ) (ty-endpt p c)
evctx-endpt : ∀ (p : Interval) -> {Γ : TyCtx Full} -> {c : Ty Full} {d : Ty Full} ->
  EvCtx Full Γ c d ->
  EvCtx Empty (ctx-endpt p Γ) (ty-endpt p c) (ty-endpt p d)

-- TODO: strengthen the inductive hypothesis
--
-- Substitution : ∀ {Ξ} → TyCtx Ξ → TyCtx Ξ → Type (ℓ-suc ℓ-zero)

_[_]v : ∀ {Δ Γ A}
  → Val Empty Γ A
  → substitution (Val Empty Δ) Γ
  → Val Empty Δ A
_[_]c : ∀ {Δ Γ A}
  → Comp Empty Γ A
  → substitution (Val Empty Δ) Γ
  → Comp Empty Δ A
_[_]c1 : ∀ {Γ A B}
  → Comp Empty (cons Γ A) B
  → (Val Empty Γ A)
  → Comp Empty Γ B
-- wk : ∀ {v α Γ A B} -> Tm {v} {Empty} Γ A ->
--   Tm {v} {Empty} (B :: Γ) A
-- wk = {!!}




data Val where
  varVal : ∀ {Ξ Γ} -> (x : Γ .var) -> Val Ξ Γ (Γ .el x)
  lda : ∀ {Ξ Γ S T} -> (Comp Ξ (cons Γ S) T) -> Val Ξ Γ (S ⇀ T)
  zro : ∀ {Ξ Γ} -> Val Ξ Γ nat
  suc : ∀ {Ξ Γ} -> Val Ξ Γ nat -> Val Ξ Γ nat
  up : ∀ {Γ} -> (S⊑T : Ty Full) -> Val Empty Γ (ty-left S⊑T) -> Val Empty Γ (ty-right S⊑T) 
  up-UB  : ∀ {Γ} → (S⊑T : Ty Full) → Val Full Γ (ty-refl (ty-left S⊑T)) -> Val Full Γ S⊑T
  up-LUB : ∀ {Γ} → (S⊑T : Ty Full) → Val Full Γ S⊑T -> Val Full Γ (ty-refl (ty-right S⊑T))

  η-fun : ∀ {Γ A B} (Vf : Val Empty Γ (A ⇀ B)) ->
    Vf ≡ lda (app ? ?)
    -- lda (app (wk Vf) (var x)) ≡ Vf

  trans : ∀ {Γ Δ : TyCtx Full} -> {A B : Ty Full} ->
    (V : Val Full Γ A) -> (U : Val Full Δ B) ->
    (ctx-p : ctx-endpt l Δ ≡ ctx-endpt r Γ) ->
    (ty-p : ty-endpt l B ≡ ty-endpt r A)
    (tm-p : PathP (λ i → Val Empty (ctx-p i) (ty-p i))
                  (val-endpt l {Δ} {B} U)
                  (val-endpt r {Γ} {A} V)) ->
    Val Full (CompCtx Δ Γ ctx-p) (comp B A ty-p)
  ord-squash : ∀ {Γ c} (leq leq' : Val Full Γ c) ->
    (val-endpt l leq ≡ val-endpt l leq') →
    (val-endpt r leq ≡ val-endpt r leq') ->
    leq ≡ leq'
  isSetVal : ∀ {Γ S} → isSet (Val Empty Γ S)

data Comp where
  app : ∀ {Ξ Γ S T} → Val Ξ Γ (S ⇀ T) → Val Ξ Γ S → Comp Ξ Γ T
  err : ∀ {Ξ Γ S} → Comp Ξ Γ S
  ret : ∀ {Ξ Γ S} → Val Ξ Γ S → Comp Ξ Γ S
  bind : ∀ {Ξ Γ S T} → Comp Ξ Γ S → Comp Ξ (cons Γ S) T → Comp Ξ Γ T
  matchNat : ∀ {Ξ Γ S} → Val Ξ Γ nat → Comp Ξ Γ S → Comp Ξ (cons Γ nat) S → Comp Ξ Γ S
  dn : ∀ {Γ} → (S⊑T : Ty Full) → Comp Empty Γ (ty-right S⊑T) → Comp Empty Γ (ty-left S⊑T)
  dn-LB  : ∀ {Γ} → (S⊑T : Ty Full) → Comp Full Γ (ty-refl (ty-right S⊑T)) -> Comp Full Γ S⊑T
  dn-GLB : ∀ {Γ} → (S⊑T : Ty Full) → Comp Full Γ S⊑T -> Comp Full Γ (ty-refl (ty-left S⊑T))

  -- effect rules
  err-bot : ∀ {Γ} (B : Ty Empty) (M : Comp Empty Γ B) -> Comp Full (ctx-refl Γ) (ty-refl B)
  -- TODO: strictness

  -- βη
  
  β-fun : ∀ {Γ A B} (M : Comp Empty (cons Γ A) B) (V : Val Empty Γ A) ->
    app (lda M) V ≡ (M [ V ]c1)
  
  trans : ∀ {Γ Δ : TyCtx Full} -> {A B : Ty Full} ->
    (M : Comp Full Γ A) -> (N : Comp Full Δ B) ->
    (ctx-p : ctx-endpt l Δ ≡ ctx-endpt r Γ) ->
    (ty-p : ty-endpt l B ≡ ty-endpt r A)
    (tm-p : PathP (λ i → Comp Empty (ctx-p i) (ty-p i))
                  (comp-endpt l {Δ} {B} N)
                  (comp-endpt r {Γ} {A} M)) ->
    Comp Full (CompCtx Δ Γ ctx-p) (comp B A ty-p)
  
  ord-squash : ∀ {Γ c} (leq leq' : Comp Full Γ c) ->
    (comp-endpt l leq ≡ comp-endpt l leq') →
    (comp-endpt r leq ≡ comp-endpt r leq') ->
    leq ≡ leq'
  isSetComp : ∀ {Γ S} → isSet (Comp Empty Γ S)
data EvCtx where

val-endpt = {!!}
comp-endpt = {!!}
evctx-endpt = {!!}

_[_]v = {!!}
_[_]c = {!!}
M [ V ]c1 = M [ cons-subst (Val Empty _) varVal V ]c

-- data Tm where
--   app : ∀ {α Ξ Γ S T} -> (Tm {Pure} {Ξ} Γ (S ⇀ T)) -> (Tm {Pure} Γ S) -> (Tm {Impure} Γ T)
--   err : ∀ {α Ξ Γ A} -> Tm {Impure} {Ξ} Γ A
--   ret : ∀ {α Ξ Γ A} -> Tm {Pure} {Ξ} Γ A -> Tm {Impure} Γ A
--   bind : ∀ {α Ξ Γ A B} -> Tm {Pure} {Ξ} Γ A ->
--                           Tm {Impure} {Ξ} (A :: Γ) B -> Tm {Impure} {Ξ} Γ B

--   inj-nat : ∀ {α Ξ Γ} -> Tm {Pure} {Ξ} Γ nat -> Tm {Pure} Γ dyn
--   inj-arr-ext : ∀ {Ξ Γ} -> Tm {Pure} {Ext} {Ξ} Γ (dyn ⇀ dyn)     -> Tm {Pure} {Ext} Γ dyn
--   inj-arr-int : ∀ {Ξ Γ} -> Tm {Pure} {Int} {Ξ} Γ (▹ (dyn ⇀ dyn)) -> Tm {Pure} {Int} Γ dyn
--   case-nat :     ∀ {α Ξ Γ B} -> Tm {Pure}   {Ξ} Γ dyn ->
--                                 Tm {Impure}   {Ξ} (nat :: Γ) B             -> Tm {Impure} Γ B 
--   case-arr-ext : ∀ {Ξ Γ B}   -> Tm {Pure} {Ext} {Ξ} Γ dyn ->
--                                 Tm {Impure} {Ext} {Ξ} ((dyn ⇀ dyn) :: Γ) B     -> Tm {Impure} {Ext} Γ B 
--   case-arr-int : ∀ {Ξ Γ B}   -> Tm {Pure} {Int} {Ξ} Γ dyn ->
--                                 Tm {Impure} {Int} {Ξ} ((▹ (dyn ⇀ dyn)) :: Γ) B -> Tm {Impure} {Int} Γ B 


--   -- Other term precision rules:
 
--   err-bot : ∀ {α Γ} (B : Ty Empty) (M : Tm {Impure} {Empty} Γ B) -> Tm {Impure} {Full} (ctx-refl Γ) (ty-refl B)
--   --err-bot : ∀ {Γ : TyCtx Full} (c : Ty Full)
--   --  (M : Tm {Impure} {Empty} (ctx-endpt r Γ) (ty-right c)) -> Tm {Impure} {Full} Γ c
--   -- TODO do we need to restrict the left endpoint of Γ?

--   trans : ∀ {v : PureImpure} {Γ Δ : TyCtx Full} -> {A B : Ty Full} ->
--     (M : Tm {v} Γ A) -> (N : Tm {v} Δ B) ->
--     (ctx-p : ctx-endpt l Δ ≡ ctx-endpt r Γ) ->
--     (ty-p :  ty-endpt l B ≡ ty-endpt r A)
--     (tm-p : PathP (λ i → Tm {v} (ctx-p i) (ty-p i)) (tm-endpt l {Δ} {B} N) (tm-endpt r {Γ} {A} M)) ->
--     Tm {v} (CompCtx Δ Γ ctx-p) (comp B A ty-p)

--   -- Cast rules



--   -- Equational theory:
  
-- {-
--   β-case :

--   η-case :

--   β-ret :

--   η-ret :
-- -}

--   -- Propositional truncation:
  
--   -- squash : ∀ {v α Ξ Γ A} -> (M N : Tm {v} {Ξ} Γ A) -> (p q : M ≡ N) -> p ≡ q
--   squash : ∀ {v α Ξ Γ A} -> isSet (Tm {v} {Ξ} Γ A)

--   -- Quotient the ordering:
  


-- _⊑tm_ : ∀ {v α Γ A B} {c : A ⊑ B} ->
--   Tm {v} {Empty} (ctx-endpt l Γ) A -> Tm {v} {Empty} (ctx-endpt r Γ) B -> Type


-- _⊑tm_ {v} {Γ} {A} {B} {c , eq1 , eq2} M N = Σ[ M⊑N ∈ Tm {v} {Full} Γ c ]
--   ((tm-endpt l {Γ} {c} M⊑N ≡ subst (Tm (ctx-endpt l Γ)) (sym eq1) M) ×
--    (tm-endpt r {Γ} {c} M⊑N ≡ subst (Tm (ctx-endpt r Γ)) (sym eq2) N))


-- Recall:
-- tm-endpt : (p : Interval) -> {Γ : TyCtx Full} -> {c : Ty Full} ->
--   Tm {Full} Γ c ->
--   Tm {Empty} (ctx-endpt p Γ) (ty-endpt p c)

-- tm-endpt = ?
-- tm-endpt p {Γ} {c} (var x) = var (∋-ctx-endpt p x)
-- tm-endpt p {Γ} {(_ ⇀ cout)} (lda M1⊑M2) = lda (tm-endpt p {(_ ::  Γ)} {cout} M1⊑M2)
-- tm-endpt p {Γ} {cout} (app {S = cin} M1⊑M2 N1⊑N2) =
--   app (tm-endpt p {Γ} {(cin ⇀ cout)} M1⊑M2) (tm-endpt p {Γ} {cin} N1⊑N2)

-- tm-endpt p {Γ} {c} err = err
-- tm-endpt p {Γ} zro = zro
-- tm-endpt p {Γ} (suc M1⊑M2) = suc (tm-endpt p {Γ} {nat} M1⊑M2)

-- -- Term-precision-only rules
-- --tm-endpt l .(ctx-refl _) c (err-bot .c N) = err
-- --tm-endpt r .(ctx-refl _) c (err-bot {Γ} .c N) =
-- --  transport (sym (λ i → Tm (ctx-endpt-refl {Γ} r i) (ty-right c))) N
-- -- Goal:  Tm Γ (ty-right c) ≡ Tm (ctx-endpt r (ctx-refl Γ)) (ty-right c)

-- tm-endpt p (err-bot B x) = {!!}



-- tm-endpt l {Γ} (trans c _ _ _ _) = {!!}
-- tm-endpt r {Γ} (trans c _ _ _ _) = {!!}

-- -- Truncation
-- tm-endpt p {Γ} {c} (squash M1⊑M2 M1'⊑M2' eq eq' i j) =
--   squash (tm-endpt p {Γ} {c} M1⊑M2) (tm-endpt p {Γ} {c} M1'⊑M2')
--     (λ k → tm-endpt p {Γ} {c} (eq k)) (λ k → tm-endpt p {Γ} {c} (eq' k)) i j

-- tm-endpt p (ret x) = {!!}
-- tm-endpt p (bind x x₁) = {!!}
-- tm-endpt p (inj-nat x) = {!!}
-- tm-endpt p (inj-arr-ext x) = {!!}
-- tm-endpt p (inj-arr-int x) = {!!}
-- tm-endpt p (case-nat x x₁) = {!!}
-- tm-endpt p (case-arr-ext x x₁) = {!!}
-- tm-endpt p (case-arr-int x x₁) = {!!}
-- tm-endpt p (ord-squash x x₁ x₂ x₃ x₄ x₅ x₆ x₇ i) = {!!}






{-

-- Substitution and Renaming using De Bruijn framework
module DB_Base = Syntax.DeBruijnCommon (Ty Empty) (TyCtx Empty) · (_::_) _∋_ vz vs (Tm Ext {Empty})
open DB_Base -- Brings in definitions of ProofT, Kit, Subst


-- Lift function --

lft : {Δ Γ : TyCtx Empty} {S : Ty Empty} {_◈_ : ProofT}
       (K : Kit _◈_) (τ : Subst Δ Γ _◈_) {T : Ty Empty} (h : (Γ :: S) ∋ T) -> (Δ :: S) ◈ T       
lft (kit vr tm wk) τ vz = vr vz
lft (kit vr tm wk) τ (vs x) = wk (τ x)
  -- Note that the type of lft can also be written as (Subst Δ Γ _◈_) -> (Subst (Δ ∷ S) (Γ ∷ S) _◈_)

-- Traversal function --

trav : {Δ Γ : TyCtx Empty} {T : Ty Empty} {_◈_ : ProofT} (K : Kit _◈_)
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
