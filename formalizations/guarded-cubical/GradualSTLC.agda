{-# OPTIONS --cubical --rewriting --guarded #-}

module GradualSTLC where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary

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
  
  -- inj-arrow could be made more compositional by having a
  -- case for composition of EP pairs and a case for
  -- dyn => dyn ⊑ dyn

⊑ref : (A : Ty) -> A ⊑ A
⊑ref nat = nat
⊑ref dyn = dyn
⊑ref (A1 => A2) = (⊑ref A1) => (⊑ref A2)

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

{-
ltdyn-transitive {A => B} {A' => B'} {A'' => B''} {n} {m} {p}
  eq (_=>_ {eq = eq1} dAA' dBB') (_=>_ {eq = eq2} dA'A'' dB'B'') =
  _=>_ {n = {!?!}} {m = {!!}} {p = {!!}} {eq = {!!}}
    (ltdyn-transitive {!!} dAA' dA'A'')
    (ltdyn-transitive {!!} dBB' dB'B'')
ltdyn-transitive eq (dAA' => dBB') (inj-arrow dBC) = {!!}
ltdyn-transitive _ nat nat = nat
ltdyn-transitive _ nat inj-nat = inj-nat
ltdyn-transitive _ inj-nat dyn = inj-nat
ltdyn-transitive eq (inj-arrow dA-dyn-dyn) dyn =
  inj-arrow (ltdyn-transitive _ dA-dyn-dyn (dyn => dyn))

-}

{-
data ltdyn : ℕ -> Ty -> Ty -> Set where
  dyn : {n : ℕ} -> ltdyn n dyn dyn
  _=>_ : {A A' B B' : Ty} {n m p : ℕ} ->
    {eq : p ≡ n + m} ->
    ltdyn n A A' -> ltdyn m B B' ->
    ltdyn p (A => B) (A' => B')
  nat : {n : ℕ} -> ltdyn n nat nat
  inj-nat : {n : ℕ} -> ltdyn n nat dyn
  inj-arrow : {A : Ty} -> {n : ℕ} ->
    ltdyn n A (dyn => dyn) -> ltdyn n A dyn


_⊑[_]_ : Ty -> ℕ -> Ty -> Set
A ⊑[ n ] B = ltdyn n A B
-}


{-
max-sum : (a b c d : ℕ) ->
  max (a + b) (c + d) ≡ max a c + max b d
max-sum zero b zero d = refl
max-sum zero b (suc c) d = {!!}
max-sum (suc a) b c d = {!!}
-}

{-
ltdyn-transitive : {A B C : Ty} -> {n m p : ℕ} ->
   p ≡ n + m -> A ⊑[ n ] B -> B ⊑[ m ] C -> A ⊑[ p ] C
ltdyn-transitive _ dyn dyn = dyn
ltdyn-transitive {A => B} {A' => B'} {A'' => B''} {n} {m} {p}
  eq (_=>_ {eq = eq1} dAA' dBB') (_=>_ {eq = eq2} dA'A'' dB'B'') =
  _=>_ {n = {!?!}} {m = {!!}} {p = {!!}} {eq = {!!}}
    (ltdyn-transitive {!!} dAA' dA'A'')
    (ltdyn-transitive {!!} dBB' dB'B'')
ltdyn-transitive eq (dAA' => dBB') (inj-arrow dBC) = {!!}
ltdyn-transitive _ nat nat = nat
ltdyn-transitive _ nat inj-nat = inj-nat
ltdyn-transitive _ inj-nat dyn = inj-nat
ltdyn-transitive eq (inj-arrow dA-dyn-dyn) dyn =
  inj-arrow (ltdyn-transitive _ dA-dyn-dyn (dyn => dyn))
-}


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
  zro : ∀ {Γ} -> Tm Γ nat
  suc : ∀ {Γ} -> Tm Γ nat -> Tm Γ nat

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
trav K τ zro = zro
trav K τ (suc t') = suc (trav K τ t')

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

-- Single substitution
-- N[M/x]

_[_] : ∀ {Γ A B}
  → Tm (Γ :: B) A
  → Tm Γ B
  → Tm Γ A
_[_] {Γ} {A} {B} N M = sub Γ (Γ :: B) σ A N -- sub {!!} {!!} {!!} {!!} {!!}
  where
    σ : Subst Γ (Γ :: B) Tm -- i.e., {T : Ty} → Γ :: B ∋ T → Tm Γ T
    σ vz = M
    σ (vs x) = var x


-- Values --

data Value : ∀ {Γ} {A} -> Tm Γ A -> Set where
  VLam : ∀ {Γ A B} -> {N : Tm (Γ :: A) B} -> Value (lda N)
  VZero : ∀ {Γ} -> Value {Γ} zro
  VSuc : ∀ {Γ} -> {V : Tm Γ nat} ->
    Value V ->
    Value (suc V)
  VUpFun : ∀ {Γ} {Ain Aout Bin Bout} ->
    {cin : Ain ⊑ Bin} {cout : Aout ⊑ Bout} ->
    {V : Tm Γ (Ain => Aout)} ->
    Value V ->
    Value (up (cin => cout) V)
  VDnFun : ∀ {Γ} {Ain Aout Bin Bout} ->
    {cin : Ain ⊑ Bin} {cout : Aout ⊑ Bout} ->
    {V : Tm Γ (Bin => Bout)} ->
    Value V ->
    Value (dn (cin => cout) V)

-- Upcasts are values, downcasts are evaluation contexts

{-
data Value : Type where
  Zero : {Γ} -> Value
  Suc : Value -> Value
-}



