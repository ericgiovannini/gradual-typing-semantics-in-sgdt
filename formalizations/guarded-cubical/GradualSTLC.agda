{-# OPTIONS --cubical --rewriting --guarded #-}

module GradualSTLC where


open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

-- Types --


data Ty : Set where
  nat : Ty
  dyn : Ty
  _=>_ : Ty -> Ty -> Ty

infixr 5 _=>_

data _⊑_ : Ty -> Ty -> Set where
  dyn : dyn ⊑ dyn
  _=>_ : {A A' B B' : Ty} ->
    A ⊑ A' -> B ⊑ B' -> (A => B) ⊑ (A' => B')
  nat : nat ⊑ nat
  inj-nat : nat ⊑ dyn
  inj-arrow : {A : Ty} ->
    A ⊑ (dyn => dyn) -> A ⊑ dyn
  -- inj-arrow : {A A' : Ty} ->
  --   (A => A') ⊑ (dyn => dyn) -> (A => A') ⊑ dyn

-- Contexts --

data Ctx : Set where
  · : Ctx
  _::_ : Ctx -> Ty -> Ctx

infixr 5 _::_


-- "Contains" relation stating that a context Γ contains a type T

data _∋_ : Ctx -> Ty -> Set where
  vz : ∀ {Γ S} -> Γ :: S ∋ S
  vs : ∀ {Γ S T} (x : Γ ∋ T) -> (Γ ::  S ∋ T)

infix 4 _∋_


-- Simply-typed terms, presented via their typing rules

data Tm : Ctx -> Ty -> Set where
  var : ∀ {Γ T}   -> Γ ∋ T -> Tm Γ T
  lda : ∀ {Γ S T} -> (Tm (Γ :: S) T) -> Tm Γ (S => T)
  app : ∀ {Γ S T} -> (Tm Γ (S => T)) -> (Tm Γ S) -> (Tm Γ T)
  err : ∀ {Γ A} -> Tm Γ A
  up  : ∀ {Γ A B} -> A ⊑ B -> Tm Γ A -> Tm Γ B
  dn  : ∀ {Γ A B} -> A ⊑ B -> Tm Γ B -> Tm Γ A

-- infix 4 _▸_


--  ================================================================= --

-- Type of "proofs" --


ProofT = Ctx -> Ty -> Set


VarToProof : ProofT -> Set
VarToProof _◆_ = ∀ {Γ T} -> (Γ ∋ T) -> (Γ ◆ T)
-- The diamond is a function, and the underscores around it allow us to use it in infix

ProofToTm : ProofT -> Set
ProofToTm _◆_ = ∀ {Γ T} -> (Γ ◆ T) -> (Tm Γ T)

WeakeningMap : ProofT -> Set
WeakeningMap _◆_ = ∀ {Γ S T} -> (Γ ◆ T) -> ((Γ :: S) ◆ T)



-- Kits --

data Kit (◆ : ProofT) : Set where
  kit : ∀ (vr : VarToProof ◆) (tm : ProofToTm ◆) (wk : WeakeningMap ◆) -> Kit ◆


-- Substitutions --

Subst : Ctx -> Ctx -> ProofT -> Set
Subst Δ Γ _◈_ = ∀ {T} -> (Γ ∋ T) -> (Δ ◈ T)


-- Lift function --

lft : {Δ Γ : Ctx} {S : Ty} {_◈_ : ProofT}
       (K : Kit _◈_) (τ : Subst Δ Γ _◈_) {T : Ty} (h : (Γ :: S) ∋ T) -> (Δ :: S) ◈ T
lft (kit vr tm wk) τ vz = vr vz
lft (kit vr tm wk) τ (vs x) = wk (τ x)

-- Note that the type of lft can also be written as (Subst Δ Γ _◈_) -> (Subst (Δ ∷ S) (Γ ∷ S) _◈_)


-- Traversal function --

trav : {Δ Γ : Ctx} {T : Ty} {_◈_ : ProofT} (K : Kit _◈_)
       (τ : Subst Δ Γ _◈_) (t : Tm Γ T) -> Tm Δ T
trav (kit vr tm wk) τ (var x) = tm (τ x)
trav K τ (lda t') = lda (trav K (lft K τ) t')
trav K τ (app f s) = app (trav K τ f) (trav K τ s)
trav K τ (up deriv t') = up deriv (trav K τ t')
trav K τ (dn deriv t') = dn deriv (trav K τ t')
trav K τ err = err

-- Renaming --

idContains : {Γ : Ctx} {T : Ty} (t : Γ ∋ T) -> Γ ∋ T
idContains t = t

varKit : Kit _∋_
varKit = kit idContains var vs

rename : {Γ Δ : Ctx} {T : Ty} (ρ : Subst Δ Γ _∋_) (t : Tm Γ T) -> Tm Δ T
rename ρ t = trav varKit ρ t



-- Substitution --

idTerm : {Γ : Ctx} {T : Ty} (t : Tm Γ T) -> Tm Γ T
idTerm t = t

weakenTerm : WeakeningMap Tm
weakenTerm = rename vs

termKit : Kit Tm
termKit = kit var idTerm weakenTerm

sub : (Δ Γ : Ctx) (σ : Subst Δ Γ Tm) (T : Ty) (t : Tm Γ T) -> Tm Δ T
sub Δ Γ σ T t = trav termKit σ t


  
