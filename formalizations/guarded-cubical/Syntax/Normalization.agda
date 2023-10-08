module Syntax.Normalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Trunc

open import Syntax.IntensionalTerms
import Syntax.Nbe as Nbe
open import Syntax.IntensionalTerms.Induction
open import Syntax.Types

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T U R' S' T' U' : Ty

   γ γ' γ'' : Subst Δ Γ
   δ δ' δ'' : Subst Θ Δ
   θ θ' θ'' : Subst Z Θ

   V V' V'' : Val Γ S
   M M' M'' N N' : Comp Γ S
   E E' E'' F F' : EvCtx Γ S T
   ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

TySem = Ty → Type (ℓ-suc ℓ-zero)

SemSubst : (V : TySem) → (Γ : Ctx) → Type (ℓ-suc ℓ-zero)
SemSubst V [] = Unit*
SemSubst V (R ∷ Γ) = SemSubst V Γ × V R

data Var : ∀ (Γ : Ctx) (R : Ty) → Type (ℓ-suc ℓ-zero) where
  Zero : Var (R ∷ Γ) R
  Succ : Var Γ R → Var (S ∷ Γ) R

lookup : {V : TySem} → SemSubst V Γ → Var Γ R → V R
lookup γ Zero = γ .snd
lookup γ (Succ x) = lookup (γ .fst) x

Ren : ∀ (Δ Γ : Ctx) → Type (ℓ-suc ℓ-zero)
Ren Δ = SemSubst (Var Δ)

_[_]rvar : Var Δ R → Ren Θ Δ → Var Θ R
Zero [ ρ ]rvar = ρ .snd
Succ x [ ρ ]rvar = x [ ρ .fst ]rvar

wkRen : Ren Θ Δ → Ren (R ∷ Θ) Δ
wkRen {Δ = []} ρ = tt*
wkRen {Δ = R ∷ Δ} ρ = wkRen (ρ .fst) , Succ (ρ .snd)

↑ren : Ren Θ Δ → Ren (S ∷ Θ) (S ∷ Δ)
↑ren ρ = wkRen ρ , Zero

idRen : Ren Γ Γ
idRen {Γ = []} = tt*
idRen {Γ = R ∷ Γ} = (wkRen idRen) , Zero

data VNfm (Γ : Ctx) : ∀ (R : Ty) → Type (ℓ-suc ℓ-zero)
data CNfm (Γ : Ctx) (R : Ty) : Type (ℓ-suc ℓ-zero)
data CNeu (Γ : Ctx) (R : Ty) : Type (ℓ-suc ℓ-zero)
data CBnd (Γ : Ctx) (R : Ty) : Type (ℓ-suc ℓ-zero)
data ENfm (Γ : Ctx) (R : Ty) (S : Ty) : Type (ℓ-suc ℓ-zero)

SNfm : ∀ (Δ : Ctx) (Γ : Ctx) → Type (ℓ-suc ℓ-zero)
SNfm Δ = SemSubst (VNfm Δ)

data VNfm Γ where
  var : Var Γ R → VNfm Γ R
  zro : VNfm Γ nat
  suc : VNfm Γ nat → VNfm Γ nat
  lda : CNfm (S ∷ Γ) R → VNfm Γ (S ⇀ R)
  injN : VNfm Γ nat → VNfm Γ dyn
  injArr : VNfm Γ (dyn ⇀ dyn) → VNfm Γ dyn
  mapDyn : VNfm Γ dyn → VNfm [ nat ] nat → VNfm [ dyn ⇀ dyn ] (dyn ⇀ dyn) → VNfm Γ dyn

data CNfm Γ R where
  ret : VNfm Γ R → CNfm Γ R
  err  : CNfm Γ R
  tick : CNfm Γ R → CNfm Γ R
  bnd : CBnd Γ R → CNfm Γ R
  -- neu : CNeu Γ R → CNfm Γ R

data CBnd Γ R where
  bind : CNeu Γ S → CNfm (S ∷ Γ) R → CBnd Γ R

data CNeu Γ R where
  app : VNfm Γ (S ⇀ R) → VNfm Γ S → CNeu Γ R
  matchNat : VNfm Γ nat → CNfm Γ R → CNfm (nat ∷ Γ) R
    → CNeu Γ R
  matchDyn : VNfm Γ dyn → CNfm (nat ∷ Γ) R → CNfm (dyn ⇀ dyn ∷ Γ) R → CNeu Γ R

unVar : Var Γ R → Val Γ R
unVar Zero = var
unVar (Succ x) = unVar x [ wk ]v

-- Need to show all of these preserve substitution
unVNfm : VNfm Γ R → Val Γ R
unCNfm : CNfm Γ R → Comp Γ R
unCNeu : CNeu Γ R → Comp Γ R

unVNfm (var x) = unVar x
unVNfm zro = zro [ !s ]v
unVNfm (suc V) = suc [ !s ,s unVNfm V ]v
unVNfm (lda M[x]) = lda (unCNfm M[x])
unVNfm (injN V) = injectN [ !s ,s unVNfm V ]v
unVNfm (injArr V) = injectArr [ !s ,s unVNfm V ]v
unVNfm (mapDyn V V₁ V₂) = mapDyn (unVNfm V₁) (unVNfm V₂) [ !s ,s unVNfm V ]v

unCNfm (ret V) = ret [ !s ,s unVNfm V ]c
unCNfm err = err [ !s ]c
unCNfm (tick M) = tick (unCNfm M)
unCNfm (bnd (bind M N[x])) = bind (unCNfm N[x]) [ unCNeu M ]∙

unCNeu (app V V') = app [ !s ,s unVNfm V ,s unVNfm V' ]c
unCNeu (matchNat V M N) = matchNat (unCNfm M) (unCNfm N) [ ids ,s unVNfm V ]c
unCNeu (matchDyn V M N) = matchDyn (unCNfm M) (unCNfm N) [ ids ,s unVNfm V ]c

unSNfm : SNfm Δ Γ → Subst Δ Γ
unSNfm {Γ = []} γ = !s
unSNfm {Γ = x ∷ Γ} γ = unSNfm (γ .fst) ,s unVNfm (γ .snd)

-- Action of renaming
_[_]rs : SNfm Δ Γ → Ren Θ Δ → SNfm Θ Γ
_[_]rv : VNfm Δ R → Ren Θ Δ → VNfm Θ R
_[_]rc : CNfm Δ R → Ren Θ Δ → CNfm Θ R
_[_]rneu : CNeu Δ R → Ren Θ Δ → CNeu Θ R

_[_]rs {Γ = []} γ ρ = tt*
_[_]rs {Γ = x ∷ Γ} γ ρ = (γ .fst [ ρ ]rs) , (γ .snd [ ρ ]rv)

var x [ ρ ]rv = var (lookup ρ x)
lda M [ ρ ]rv = lda (M [ ↑ren ρ ]rc)
zro [ ρ ]rv = zro
suc V [ ρ ]rv = suc (V [ ρ ]rv)
injN V [ ρ ]rv = injN (V [ ρ ]rv)
injArr V [ ρ ]rv = injArr (V [ ρ ]rv)
mapDyn V V₁ V₂ [ ρ ]rv = mapDyn (V [ ρ ]rv) V₁ V₂

ret V [ ρ ]rc = ret (V [ ρ ]rv)
err [ ρ ]rc = err
tick M [ ρ ]rc = tick (M [ ρ ]rc)
bnd (bind M N[x]) [ ρ ]rc = bnd (bind (M [ ρ ]rneu) (N[x] [ ↑ren ρ ]rc))

app V V' [ ρ ]rneu = app (V [ ρ ]rv) (V' [ ρ ]rv)
matchNat V M N [ ρ ]rneu = matchNat (V [ ρ ]rv) (M [ ρ ]rc) (N [ ↑ren ρ ]rc)
matchDyn V M N [ ρ ]rneu = matchDyn (V [ ρ ]rv) (M [ ↑ren ρ ]rc) (N [ ↑ren ρ ]rc)

-- Action of substitution

wkSubst : SNfm Θ Δ → SNfm (R ∷ Θ) Δ
wkSubst δ = δ [ wkRen idRen ]rs

idsnf : SNfm Γ Γ
idsnf {Γ = []} = tt*
idsnf {Γ = R ∷ Γ} = wkSubst idsnf , var Zero

wkS : SNfm (R ∷ Γ) Γ
wkS = wkSubst idsnf

↑snf : SNfm Θ Δ → SNfm (S ∷ Θ) (S ∷ Δ)
↑snf δ = (δ [ wkRen idRen ]rs) , (var Zero)

_[_]snf : SNfm Δ Γ → SNfm Θ Δ → SNfm Θ Γ
_[_]vnf : VNfm Γ R → SNfm Δ Γ → VNfm Δ R
_[_]cnf : CNfm Γ R → SNfm Δ Γ → CNfm Δ R
_[_]cneu : CNeu Γ R → SNfm Δ Γ → CNeu Δ R

_[_]snf {Γ = []} γ δ = tt*
_[_]snf {Γ = R ∷ Γ} γ δ = (γ .fst [ δ ]snf ) , (γ .snd [ δ ]vnf)

var x [ γ ]vnf = lookup γ x
zro [ γ ]vnf = zro
suc V [ γ ]vnf = suc (V [ γ ]vnf)
injN V [ γ ]vnf = injN (V [ γ ]vnf)
injArr V [ γ ]vnf = injArr (V [ γ ]vnf)
mapDyn V V₁ V₂ [ γ ]vnf = mapDyn (V [ γ ]vnf) V₁ V₂
lda M [ γ ]vnf = lda (M [ ↑snf γ ]cnf)

ret V [ γ ]cnf = ret (V [ γ ]vnf)
err [ γ ]cnf = err
tick M [ γ ]cnf = tick (M [ γ ]cnf)
bnd (bind Mneu Nnfm) [ γ ]cnf = bnd (bind (Mneu [ γ ]cneu) (Nnfm [ ↑snf γ ]cnf))

app V V' [ γ ]cneu = app (V [ γ ]vnf) (V' [ γ ]vnf)
matchNat V M N[x] [ γ ]cneu = matchNat (V [ γ ]vnf) (M [ γ ]cnf) (N[x] [ ↑snf γ ]cnf)
matchDyn V M[x] N[x] [ γ ]cneu = matchDyn (V [ γ ]vnf) (M[x] [ ↑snf γ ]cnf) (N[x] [ ↑snf γ ]cnf)

bindNF : CNfm Γ S → CNfm (S ∷ Γ) R → CNfm Γ R
bindNF (ret x) N[x] = N[x] [ idsnf , x ]cnf
bindNF err N[x] = err
bindNF (tick M) N[x] = tick (bindNF M N[x])
bindNF (bnd (bind M P[y])) N[x] = bnd (bind M (bindNF P[y] (N[x] [ (wkS [ wkS ]snf) , (var Zero) ]cnf)))

unSNfm-wk : ∀ (γ : SNfm Δ Γ)
  → unSNfm (wkSubst {R = R} γ) ≡ unSNfm γ ∘s wk
unSNfm-wk = {!!}

unSNfm-↑ : ∀ (γ : SNfm Δ Γ)
  → unSNfm (↑snf {S = S} γ) ≡ ↑subst (unSNfm γ)
unSNfm-↑ {Γ = Γ} γ = {!!}

unVNfm-lookup : ∀ (x : Var Γ R) (γ : SNfm Δ Γ) → unVNfm (lookup γ x) ≡ unVar x [ unSNfm γ ]v
unVNfm-lookup Zero γ = Nbe.by-vsimpl refl
unVNfm-lookup (Succ x) γ = unVNfm-lookup x (γ .fst)
  ∙ Nbe.by-vsimpl refl

-- | Correctness of all of the above operations with respect to the "semantics"
unVNfm-subst : ∀ (V : VNfm Γ R) (γ : SNfm Δ Γ) → unVNfm (V [ γ ]vnf) ≡ (unVNfm V) [ unSNfm γ ]v
unCNfm-subst : ∀ (M : CNfm Γ R) (γ : SNfm Δ Γ) → unCNfm (M [ γ ]cnf) ≡ (unCNfm M) [ unSNfm γ ]c

unVNfm-subst (var x) γ = unVNfm-lookup x γ
unVNfm-subst {Γ = Γ} (lda {S = S}{R = R} M) γ =
  cong Syntax.IntensionalTerms.lda ((unCNfm-subst M (↑snf γ)) ∙ cong (unCNfm M [_]c) (cong (_,s var) (unSNfm-wk γ)))
  -- Unfortunately the solver can't prove this as written because it wants to pattern match on M
  -- We would need to add some support for uninterpreted function symbols in the solver to get this.
  ∙ {!!}
unVNfm-subst zro γ = Nbe.by-vsimpl refl
unVNfm-subst (suc V) γ = cong (suc [_]v) (cong (!s ,s_) (unVNfm-subst V γ))
  ∙ Nbe.by-vsimpl refl
unVNfm-subst (injN V) γ =
  cong (injectN [_]v) (cong (!s ,s_) (unVNfm-subst V γ))
  ∙ Nbe.by-vsimpl refl
unVNfm-subst (injArr V) γ = cong (injectArr [_]v) (cong (!s ,s_) (unVNfm-subst V γ))
  ∙ Nbe.by-vsimpl refl
unVNfm-subst (mapDyn V V₁ V₂) γ = cong (mapDyn (unVNfm V₁) (unVNfm V₂) [_]v) (cong (!s ,s_) (unVNfm-subst V γ))
  ∙ Nbe.by-vsimpl refl

unCNfm-subst (ret V) γ =
  cong (ret [_]c) (cong (!s ,s_) (unVNfm-subst V γ))
  ∙ Nbe.by-csimpl refl
unCNfm-subst err γ = Nbe.by-csimpl refl
unCNfm-subst (tick M) γ =
  cong tick (unCNfm-subst M γ)
  ∙ Nbe.by-csimpl refl
unCNfm-subst (bnd x) γ = {!!}

-- unCNfm-subst : CNfm Γ R → Comp Γ R
-- unCNeu-subst : CNeu Γ R → Comp Γ R


bindNF-correct : (M : CNfm Γ S) → (N[x] : CNfm (S ∷ Γ) R)
  → unCNfm (bindNF M N[x]) ≡ (bind (unCNfm N[x]) [ unCNfm M ]∙)
bindNF-correct (ret x) N[x] = {!!}
bindNF-correct err N[x] = {!!}
bindNF-correct (tick M) N[x] = {!!}
bindNF-correct (bnd (bind M P[y])) N[x] = {!!}

module Sem = SynInd
  (λ γ → ∥ fiber unSNfm γ ∥₁ , squash₁)
  (λ V → ∥ fiber unVNfm V ∥₁ , squash₁)
  (λ M → ∥ fiber unCNfm M ∥₁ , squash₁)
  (λ {Γ}{R}{S} E →
    (∀ (M : CNfm Γ R) → ∥ (Σ[ E[M] ∈ CNfm Γ S ] unCNfm E[M] ≡ E [ unCNfm M ]∙) ∥₁)
    , isPropΠ λ _ → squash₁)

open SynInd.indCases
cases : Sem.indCases
cases .indIds = {!!}
cases .ind∘s = {!!}
cases .ind!s = {!!}
cases .ind,s = {!!}
cases .indwk = {!!}
cases .ind[]v = {!!}

cases .indVar = {!!}
cases .indZero = {!!}
cases .indSuc = {!!}
cases .indLda = {!!}
cases .indInjN = {!!}
cases .indInjArr = {!!}
cases .indMapDyn = {!!}

cases .ind[]∙ {E = E}{M = M} ihE = rec squash₁ λ ihM →
  rec squash₁ (λ ihE[M] → ∣ ihE[M] .fst , ihE[M] .snd ∙ cong (E [_]∙) (ihM .snd) ∣₁)
    (ihE (ihM .fst))
cases .ind[]c = {!!}
cases .indErr = ∣ err , {!!} ∣₁
cases .indTick = rec squash₁ λ ihM →
  ∣ (tick (ihM .fst)) , (cong tick (ihM .snd)) ∣₁
cases .indRet = ∣ ret (var Zero) , {!!} ∣₁
cases .indApp = {!!}
cases .indMatchNat = {!!}
cases .indMatchDyn = {!!}

cases .ind∙ M = ∣ M , (sym plugId) ∣₁
cases .ind∘E M ihE ihF = {!!}
cases .ind[]e ihE = {!rec squash₁ ?!}
cases .indbind {M = M} = rec (isPropΠ λ _ → squash₁) λ ihN[x] ihM →
  ∣ (bindNF ihM (ihN[x] .fst)) ,
    bindNF-correct ihM (ihN[x] .fst) ∙ cong (_[ unCNfm ihM ]∙) (cong bind (ihN[x] .snd))
  ∣₁

readOut : ∥ fiber unCNfm M ∥₁ → singl M
readOut = rec isPropSingl (λ x → (unCNfm (x .fst)) , (sym (x .snd)))

cnf : Comp Γ R → ∥ CNfm Γ R ∥₁
cnf M = Trunc.map fst (Sem.indPc cases M)

csimpl : Comp Γ R → Comp Γ R
csimpl M = fst (readOut (Sem.indPc cases M))

csimpl-eq : (M : Comp Γ R) → M ≡ csimpl M
csimpl-eq M = snd (readOut (Sem.indPc cases M))

proof-by-normalization : {M N : Comp Γ R} →
  csimpl M ≡ csimpl N → M ≡ N
proof-by-normalization p = csimpl-eq _ ∙ p ∙ sym (csimpl-eq _)
