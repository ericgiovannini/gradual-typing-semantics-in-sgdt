{-# OPTIONS --allow-unsolved-metas #-}


{-

  A language based on fine-grained call-by-value, intended as the
  target of a translation from the gradual surface calculus.

  Notes:

    1. The syntax is NOT quotiented by β-η equality.
    2. The syntax has arbitrary casts, not just the ones involving dyn.
    3. There is no mutually-defined datatype of evaluation contexts.
       Instead, evaluation contexts are defined after defining values and
       computations.
    4. The effects are error for gradual typing, as well as get/put for
       global state. There is no explicit "delay" or "step" effect, i.e.,
       this is not an intensional syntax.

    

-}
module Effects.State.Syntax.FineGrained where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List

open import Syntax.Types

open TyPrec'


private
  variable
    Γ Γ' : Ctx
    R S S' T U : Ty
    S⊑T : TyPrec
    B B' C C' D D' : Γ ⊑ctx Γ'
    b b' c c' d d' : S ⊑' S'


data Val   (Γ : Ctx) : (S : Ty) → Type
data Comp  (Γ : Ctx) : (S : Ty) → Type


data Val Γ where
  var  : Γ ∋ T → Val Γ T
  pair : Val Γ S → Val Γ T → Val Γ (S × T)
  -- lda  : Comp (S ∷ Γ) T → Val Γ (S ⇀ T)
  zro  : Val Γ nat
  suc  : Val Γ nat → Val Γ nat
  up   : (S⊑T : TyPrec') → Val Γ (ty-left S⊑T) → Val Γ (ty-right S⊑T)
  -- pm   : Val Γ (S × T) → Val (S ∷ T ∷ Γ) R → Val Γ R

  -- TODO: should we allow pattern mathing of a product into a value?
  -- Should the result of lda be a Val instead of a Comp?


data Comp Γ where
  err : Comp Γ S
  ret : Val Γ S → Comp Γ S
  lda : Comp (S ∷ Γ) T → Comp Γ (S ⇀ T)
  app : Comp Γ (S ⇀ T) → Val Γ S → Comp Γ T 
  bind : Comp Γ S → Comp (S ∷ Γ) T → Comp Γ T
  pm  : Val Γ (S × T) → Comp (S ∷ T ∷ Γ) R → Comp Γ R
  matchNat :
      Val Γ nat
    → Comp Γ S         -- zero case
    → Comp (nat ∷ Γ) S -- successor case
    → Comp Γ S
  dn  : (S⊑T : TyPrec') → Comp Γ (ty-right S⊑T) → Comp Γ (ty-left S⊑T)
  up :  (S⊑T : TyPrec') → Comp Γ (ty-left S⊑T) → Comp Γ (ty-right S⊑T)
  get : Comp Γ S
  put : Comp Γ unit

  -- TODO: do we actually need an upcast for Comp?
  -- TODO: in matchNat, should the zero and successor cases be Vals rather than Comps?
  -- TODO: should we add a pair constructor for computations?
  -- Should the first arg to app be a Val or a Comp?
  


-- suc V cannot be an evaluation context, because V is a value.
-- But if we don't include suc V as an EC, how will we make sure that
-- if V steps to W, then suc V steps to suc W

data EvCtxC : Ctx → Ty → Ty → Type where
  ∙E : ∀ {Γ T} → EvCtxC Γ T T
  BindE : ∀ {Γ R S T} → EvCtxC Γ R S → Comp (S ∷ Γ) T → EvCtxC Γ R T
  EV : ∀ {Γ R S T} → EvCtxC Γ R (S ⇀ T) → Val Γ S → EvCtxC Γ R T
  UpE : ∀ {Γ R} → (S⊑T : TyPrec') → EvCtxC Γ R (ty-left S⊑T) → EvCtxC Γ R (ty-right S⊑T)
  DnE : ∀ {Γ R} → (S⊑T : TyPrec') → EvCtxC Γ R (ty-right S⊑T) → EvCtxC Γ R (ty-left S⊑T)
  -- matchNatE : ∀ {Γ T} → EvCtxV Γ T nat → Comp Γ S → Comp (nat ∷ Γ) S → EvCtxC Γ T S


fillE : ∀ {Γ} {S T : Ty} → EvCtxC Γ S T → Comp Γ S → Comp Γ T
fillE ∙E M = M
fillE (BindE E N) M = bind (fillE E M) N
fillE (EV E V) M = app (fillE E M) V
fillE (UpE S⊑T E) M = up S⊑T (fillE E M)
fillE (DnE S⊑T E) M = dn S⊑T (fillE E M)
-- fillE {Γ} (matchNatE E Kz Ks) M = matchNat (fillEV E M) Kz Ks


_[_]E = fillE


-- Renaming and substitution

renameV : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Δ ∋ S)
  → (∀ {S} → Val Γ S → Val Δ S)

renameC : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Δ ∋ S)
  → (∀ {S} → Comp Γ S → Comp Δ S)


renameV ρ (var x) = var (ρ x)
renameV ρ zro = zro
renameV ρ (suc M) = suc (renameV ρ M)
renameV ρ (pair x y) = {!!}
renameV ρ (up S⊑T V) = {!!}


renameC ρ err = err
renameC ρ (ret V) = ret (renameV ρ V)
renameC ρ (lda M) = lda (renameC (ext ρ) M)
renameC ρ (app M N) = app (renameC ρ M) (renameV ρ N)
renameC ρ (bind x₁ x₂) = {!!}
renameC ρ (pm x₁ x₂) = {!!}
renameC ρ (matchNat x₁ x₂ x₃) = {!!}
renameC ρ (up S⊑T x₁) = {!!}
renameC ρ (dn S⊑T x₁) = {!!}
renameC ρ get = {!!}
renameC ρ put = {!!}


wkV : ∀ {Γ S T}
  → Val Γ S
  → Val (T ∷ Γ) S
wkV V = renameV vs V

wkC : ∀ {Γ S T}
  → Comp Γ S
  → Comp (T ∷ Γ) S
wkC M = renameC vs M




extsV : ∀ {Γ Δ}
  → (∀ {S} →       Γ ∋ S → Val Δ S)
  → (∀ {S T} → T ∷ Γ ∋ S → Val (T ∷ Δ) S)
extsV ρ vz = var vz
extsV ρ (vs x) = renameV vs (ρ x)

extsC : ∀ {Γ Δ}
  → (∀ {S} →       Γ ∋ S → Comp Δ S)
  → (∀ {S T} → T ∷ Γ ∋ S → Comp (T ∷ Δ) S)
extsC ρ vz = ret (var vz)
extsC ρ (vs x) = renameC vs (ρ x)




{-
subV : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Val Δ S)
  → (∀ {S} → Val Γ S → Val Δ S)

subC : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Comp Δ S)
  → (∀ {S} → Comp Γ S → Comp Δ S)

-}
  



subV : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Val Δ S)
  → (∀ {S} → Val Γ S → Val Δ S)

subC : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Val Δ S)
  → (∀ {S} → Comp Γ S → Comp Δ S)



subV σ (var x) = σ x
subV σ zro = zro
subV σ (suc V) = suc (subV σ V)
subV σ (pair x y) = {!!}
subV σ (up S⊑T V) = {!!}


subC σ err = err
subC σ (ret V) = ret (subV σ V) -- bind (extsC σ {!!}) [ ret {!!} ]∙ -- ret (subV {!!} V)
subC σ (lda M) = lda (subC (extsV σ) M) 
subC σ (app M N) = app (subC σ M) (subV σ N)
subC σ (bind x₁ x₂) = {!!}
subC σ (pm x₁ x₂) = {!!}
subC σ (matchNat x₁ x₂ x₃) = {!!}
subC σ (up S⊑T x₁) = {!!}
subC σ (dn S⊑T x₁) = {!!}
subC σ get = {!!}
subC σ put = {!!}


_[_]V : ∀ {Γ S T}
  → Val (T ∷ Γ) S
  → Val Γ T
  → Val Γ S
_[_]V {Γ} {S} {T} N M = subV {T ∷ Γ} {Γ} σ {S} N
  where
    σ : ∀ {S'} → (T ∷ Γ ∋ S') → Val Γ S'
    σ vz = M
    σ (vs x) = var x


_[_]C : ∀ {Γ S T}
  → Comp (T ∷ Γ) S
  → Val Γ T
  → Comp Γ S
_[_]C {Γ} {S} {T} N M = subC {T ∷ Γ} {Γ} σ {S} N
  where
    σ : ∀ {S'} → (T ∷ Γ ∋ S') → Val Γ S'
    σ vz = M
    σ (vs x) = var x




-- downcast a dyn to a nat and upcast it back

test : Comp (dyn ∷ []) dyn
test = {!!} -- matchDyn (ret (inj-nat (var vz))) err err [ ret (var vz) ]∙
