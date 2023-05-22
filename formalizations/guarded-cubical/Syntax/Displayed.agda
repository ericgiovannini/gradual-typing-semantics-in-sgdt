{-# OPTIONS --cubical --rewriting --guarded -W noUnsupportedIndexedMatch #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}


open import Common.Later hiding (next)

module Syntax.Displayed  where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Cubical.Data.Prod hiding (map)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
  using (List ; length ; map ; _++_ ; cons-inj₁ ; cons-inj₂)
  renaming ([] to · ; _∷_ to _::_)

open import Cubical.Data.Empty renaming (rec to exFalso)

open import Syntax.Context as Context hiding (Renaming)
-- import Syntax.DeBruijnCommon

private
 variable
   ℓ ℓ' ℓ'' : Level

open import Syntax.Types
open Ctx

SynType = Ty Empty
TyPrec = Ty Full

TypeCtx = TyCtx Empty
PrecCtx = TyCtx Full

-- A renaming is a mapping of names that preserves the typing
Renaming = Context.Renaming {A = SynType}

wk-ren : ∀ {Γ Δ T} → Renaming Γ Δ → Renaming (cons Γ T) (cons Δ T)
wk-ren ρ (inl x) .fst = inl (ρ x .fst)
wk-ren ρ (inl x) .snd = ρ x .snd
wk-ren ρ (inr x) .fst = inr x
wk-ren ρ (inr x) .snd = refl

-- Values, Computations and Evaluation contexts,
-- quotiented by βη equivalence but *not* by order equivalence (i.e., up/dn laws)
data Val : (Γ : TypeCtx) (A : SynType) → Type (ℓ-suc ℓ-zero)
data Comp : (Γ : TypeCtx) (A : SynType) → Type (ℓ-suc ℓ-zero)
data EvCtx : (Γ : TypeCtx) (A : SynType) (B : SynType) → Type (ℓ-suc ℓ-zero)

Substitution : TypeCtx → TypeCtx → Type _
Substitution Δ Γ = substitution (Val Δ) Γ

cons-Subst : ∀ {Δ Γ S} → Substitution Δ Γ → Val Δ S → Substitution Δ (cons Γ S)
cons-Subst {Δ} γ V = cons-subst (Val Δ) γ V

idSubst : ∀ Γ → Substitution Γ Γ
compSubst : ∀ {Γ Δ Ξ} → Substitution Δ Ξ → Substitution Γ Δ → Substitution Γ Ξ
renToSubst : ∀ {Γ Δ} → Renaming Γ Δ → Substitution Γ Δ

app' : ∀ {Γ S T} → Val Γ (S ⇀ T) → Val Γ S → Comp Γ T
varV' : ∀ {Γ} → (x : Γ .var) → Val Γ (Γ .el x)

_[_]vr : ∀ {Δ Γ A}
  → Val Γ A
  → Renaming Δ Γ
  → Val Δ A

_[_]cr : ∀ {Δ Γ A}
  → Comp Γ A
  → Renaming Δ Γ
  → Comp Δ A

_[_]er : ∀ {Δ Γ A B}
  → EvCtx Γ A B
  → Renaming Δ Γ
  → EvCtx Δ A B

ρWk : ∀ {Γ A} -> Renaming (cons Γ A) Γ
ρWk x = inl x , refl
wkV : ∀ {Γ A B} -> Val Γ A -> Val (cons Γ B) A
wkV v = v [ ρWk ]vr
wkC : ∀ {Γ A B} -> Comp Γ A -> Comp (cons Γ B) A
wkC M = M [ ρWk ]cr
wkE : ∀ {Γ A B C} -> EvCtx Γ A B -> EvCtx (cons Γ C) A B
wkE E = E [ ρWk ]er
wkS : ∀ {Γ Δ S} → Substitution Γ Δ → Substitution (cons Γ S) Δ
wkS {Γ} {Δ} {S} γ x = wkV (γ x)

_[_]v : ∀ {Δ Γ A}
  → Val Γ A
  → Substitution Δ Γ
  → Val Δ A
_[_]c : ∀ {Δ Γ A}
  → Comp Γ A
  → Substitution Δ Γ
  → Comp Δ A
_[_]c1 : ∀ {Γ A B}
  → Comp (cons Γ A) B
  → (Val Γ A)
  → Comp Γ B

_[_]eγ : ∀ {Δ Γ A B}
  → EvCtx Γ A B
  → Substitution Δ Γ
  → EvCtx Δ A B
_[_]e1 : ∀ {Γ A B C}
  → EvCtx (cons Γ A) B C
  → (Val Γ A)
  → EvCtx Γ B C

-- Should there be a single combined plug and chug operations?
_[_]e∙ : ∀ {Γ A B}
  → EvCtx Γ A B
  → Comp Γ A
  → Comp Γ B

data Val where
  -- a way to avoid "green slime" in McBride's terminology
  varV : ∀ {Γ A} → (x : Γ .var) → (Γ .el x ≡ A) → Val Γ A
  lda : ∀ {Γ S T} -> (Comp (cons Γ S) T) -> Val Γ (S ⇀ T)
  zro : ∀ {Γ} -> Val Γ nat
  suc : ∀ {Γ} -> Val Γ nat -> Val Γ nat
  up : ∀ {Γ} -> (S⊑T : TyPrec) -> Val Γ (ty-left S⊑T) -> Val Γ (ty-right S⊑T)
  -- as written the following rule is not stable under renaming, or is it?
  ⇀-ext : ∀ {Γ A B} (Vf Vf' : Val Γ (A ⇀ B))
    → app' (wkV Vf) (varV' (inr _)) ≡ app' (wkV Vf') (varV' (inr _))
    → Vf ≡ Vf'
  -- | Should we make these admissible or postulate them?
  -- ren≡ : ∀ {Δ Γ S} → (ρ : Renaming Δ Γ) (V V' : Val Γ S)
  --        → V ≡ V' → _[_]vr {Δ}{Γ} V ρ ≡ V' [ ρ ]vr
  -- subst≡ : ∀ {Δ Γ S} → (γ : Substitution Δ Γ) (V V' : Val Γ S)
  --        → V ≡ V' → V [ γ ]v ≡ V' [ γ ]v
  isSetVal : ∀ {Γ S} → isSet (Val Γ S)
data Comp where
  err : ∀ {Γ S} → Comp Γ S
  ret : ∀ {Γ S} → Val Γ S → Comp Γ S
  bind : ∀ {Γ S T} → Comp Γ S → Comp (cons Γ S) T → Comp Γ T
  app : ∀ {Γ S T} → Val Γ (S ⇀ T) → Val Γ S → Comp Γ T
  matchNat : ∀ {Γ S} → Val Γ nat → Comp Γ S → Comp (cons Γ nat) S → Comp Γ S
  dn : ∀ {Γ} → (S⊑T : TyPrec) → Comp Γ (ty-right S⊑T) → Comp Γ (ty-left S⊑T)

  -- Strictness of all evaluation contexts
  strictness : ∀ {Γ S T} → (E : EvCtx Γ S T) → E [ err ]e∙ ≡ err
  ret-β : ∀ {Γ S T} → (V : Val Γ S) → (K : Comp (cons Γ S) T) → bind (ret V) K ≡ K [ V ]c1
  fun-β : ∀ {Γ S T} → (M : Comp (cons Γ S) T) → (V : Val Γ S) → app (lda M) V ≡ M [ V ]c1
  nat-βz : ∀ {Γ S} → (Kz : Comp Γ S) (Ks : Comp (cons Γ nat) S) → matchNat zro Kz Ks ≡ Kz
  nat-βs : ∀ {Γ S} → (V : Val Γ nat) (Kz : Comp Γ S) (Ks : Comp (cons Γ nat) S) → matchNat (suc V) Kz Ks ≡ Ks [ V ]c1
  -- η for matchNat
  -- some notation would probably help here...
  nat-η : ∀ {Γ S} → (M : Comp (cons Γ nat) S)
          → M ≡
            (matchNat (varV' (inr _))
                      (M [ cons-subst (Val (cons Γ nat)) (λ x → varV' (inl x)) zro ]c)
                      (M [ cons-subst ((Val (cons (cons Γ nat) nat))) (λ x → varV' (inl (inl x))) (suc (varV' (inr _))) ]c))
  -- this allows cong wrt plugging be admissible
  ret-η : ∀ {Γ S T} → (E : EvCtx Γ S T) (M : Comp Γ S) → E [ M ]e∙ ≡ bind M (wkE E [ ret (varV' (inr _)) ]e∙)
  isSetComp : ∀ {Γ A} → isSet (Comp Γ A)

data EvCtx where
  ∙E : ∀ {Γ S} → EvCtx Γ S S
  bind : ∀ {Γ S T U} → EvCtx Γ S T → Comp (cons Γ T) U → EvCtx Γ S U
  dn : ∀ {Γ} (S⊑T : TyPrec) {U} → EvCtx Γ U (ty-right S⊑T) → EvCtx Γ U (ty-left S⊑T)

  ret-η : ∀ {Γ S T} → (E : EvCtx Γ S T) → E ≡ bind ∙E (wkE E [ ret (varV' (inr _)) ]e∙)
  isSetEvCtx : ∀ {Γ A B} → isSet (EvCtx Γ A B)

varV' x = varV x refl
app' = app
idSubst Γ = varV'
compSubst δ γ x = δ x [ γ ]v
renToSubst ρ x = varV (ρ x .fst) (ρ x .snd)

_[_]c1 {Γ} M V = M [ cons-subst (Val Γ) varV' V ]c
_[_]e1 {Γ} E V = E [ cons-subst (Val Γ) varV' V ]eγ

_[_]vr {Γ}{Δ} (varV x p) ρ = varV (ρ x .fst) (ρ x .snd ∙ p)
_[_]vr {Γ}{Δ} (lda {S}{T} M) ρ = lda (M [ wk-ren ρ ]cr)
zro [ ρ ]vr = zro
suc V [ ρ ]vr = suc (V [ ρ ]vr)
up S⊑T V [ ρ ]vr = up S⊑T (V [ ρ ]vr)
⇀-ext V V' x i [ ρ ]vr = {!!} -- needs equivariance of renaming to prove
-- _[_]vr {Γ}{Δ} (ren≡ {Δ} ρ' V V' p i) ρ = ren≡ {Γ}{Δ} ρ (V [ ρ' ]vr) (V' [ ρ' ]vr) (ren≡ ρ' V V' p) i
isSetVal V V' x y i j [ ρ ]vr = isSetVal (V [ ρ ]vr) (V' [ ρ ]vr) (λ i → x i [ ρ ]vr) ((λ i → y i [ ρ ]vr)) i j

err [ ρ ]cr = err
ret V [ ρ ]cr = ret (V [ ρ ]vr)
bind M K [ ρ ]cr = bind (M [ ρ ]cr) (K [ wk-ren ρ ]cr)
app V V' [ ρ ]cr = app (V [ ρ ]vr) (V' [ ρ ]vr)
matchNat V Kz Ks [ ρ ]cr = matchNat (V [ ρ ]vr) (Kz [ ρ ]cr) (Ks [ wk-ren ρ ]cr)
dn S⊑T M [ ρ ]cr = dn S⊑T (M [ ρ ]cr)
-- rest are tedious but straightforward
strictness E i [ ρ ]cr = {!!}
ret-β V M i [ ρ ]cr = {!!}
fun-β M V i [ ρ ]cr = {!!}
nat-βz M M₁ i [ ρ ]cr = {!!}
nat-βs V M M₁ i [ ρ ]cr = {!!}
nat-η M i [ ρ ]cr = {!!}
ret-η E M i [ ρ ]cr = {!!}
isSetComp M M' p q i j [ ρ ]cr = isSetComp (M [ ρ ]cr) (M' [ ρ ]cr) ((cong (_[ ρ ]cr)) p) ((cong (_[ ρ ]cr)) q) i j

∙E [ ρ ]er = ∙E
bind E K [ ρ ]er = bind (E [ ρ ]er) (K [ wk-ren ρ ]cr)
dn S⊑T E [ ρ ]er = dn S⊑T (E [ ρ ]er)
ret-η E i [ ρ ]er = {!!}
isSetEvCtx E E' p q i j [ ρ ]er = isSetEvCtx (E [ ρ ]er) (E' [ ρ ]er) (λ i → p i [ ρ ]er) ((λ i → q i [ ρ ]er)) i j

_[_]v {Δ} (varV x p) γ = transport (cong (Val Δ) p) (γ x)
_[_]v {Δ}{Γ} (lda M) γ = lda (M [ cons-Subst (wkS {Δ}{Γ} γ) (varV' (inr _)) ]c)
zro [ γ ]v = zro
suc V [ γ ]v = suc (V [ γ ]v)
up S⊑T V [ γ ]v = up S⊑T (V [ γ ]v)
⇀-ext V V₁ x i [ γ ]v = {!!}
isSetVal V V₁ x y i i₁ [ γ ]v = {!!}

err [ γ ]c = err
ret V [ γ ]c = ret (V [ γ ]v)
bind M K [ γ ]c = bind (M [ γ ]c) {!K [ cons-Subst (wkS {Δ}{Γ} γ) (varV' (inr _)) ]c!}
app Vf Va [ γ ]c = app (Vf [ γ ]v) (Va [ γ ]v)
matchNat V Kz Ks [ γ ]c = matchNat (V [ γ ]v) (Kz [ γ ]c) {!!}
dn S⊑T M [ γ ]c = dn S⊑T (M [ γ ]c)
strictness E i [ γ ]c = {!!}
ret-β V M i [ γ ]c = {!!}
fun-β M V i [ γ ]c = {!!}
nat-βz M M₁ i [ γ ]c = {!!}
nat-βs V M M₁ i [ γ ]c = {!!}
nat-η M i [ γ ]c = {!!}
ret-η E M i [ γ ]c = {!!}
isSetComp M M' p q i j [ γ ]c = {!!}

∙E [ γ ]eγ = ∙E
bind E M [ γ ]eγ = bind (E [ γ ]eγ) {!!}
dn S⊑T E [ γ ]eγ = dn S⊑T (E [ γ ]eγ)
ret-η E i [ γ ]eγ = {!!}
isSetEvCtx E E' p q i j [ γ ]eγ = {!!}

∙E [ M ]e∙ = M
bind E K [ M ]e∙ = bind (E [ M ]e∙) K
dn S⊑T E [ M ]e∙ = dn S⊑T (E [ M ]e∙)
ret-η E i [ M ]e∙ = ret-η E M i
isSetEvCtx E E' p q i j [ M ]e∙ = isSetComp (E [ M ]e∙) (E' [ M ]e∙) (λ i → p i [ M ]e∙) ((λ i → q i [ M ]e∙)) i j

data ValPrec : (Γ : PrecCtx) (A : TyPrec) (V : Val (ctx-endpt l Γ) (ty-endpt l A)) (V' : Val (ctx-endpt r Γ) (ty-endpt r A)) → Type (ℓ-suc ℓ-zero)
data CompPrec : (Γ : PrecCtx) (A : TyPrec) (M : Comp (ctx-endpt l Γ) (ty-endpt l A)) (M' : Comp (ctx-endpt r Γ) (ty-endpt r A)) → Type (ℓ-suc ℓ-zero)
data EvCtxPrec : (Γ : PrecCtx) (A : TyPrec) (B : TyPrec) (E : EvCtx (ctx-endpt l Γ) (ty-endpt l A) (ty-endpt l B)) (E' : EvCtx (ctx-endpt r Γ) (ty-endpt r A) (ty-endpt r B)) → Type (ℓ-suc ℓ-zero)

data ValPrec where
data CompPrec where
data EvCtxPrec where


