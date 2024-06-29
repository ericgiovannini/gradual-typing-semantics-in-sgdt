{-

  A core language based on Levy's fine-grained CBV, which is easier to
  map to the semantics than the surface language directly.

  Notable features:
  1. Fine grained means we use distinct syntactic categories of values from arbitrary terms
  2. We use explicit substitutions
  3. We quotient terms by β/η equality
  4. But we do *not* quotient by order equivalence, because this maps
  only to bisimilarity in the intensional semantics.

-}
module Syntax.FineGrained.Terms  where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Data.List
open import Syntax.Types

open TyPrec

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T U R' S' T' U' : Ty
   b b' c c' d d' : S ⊑ S'

-- Substitutions, Values, Computations and Evaluation contexts.
data Subst : (Δ : Ctx) (Γ : Ctx) → Type
data Val   : (Γ : Ctx) (S : Ty) → Type
data Comp  : (Γ : Ctx) (S : Ty) → Type
data EvCtx : (Γ : Ctx) (S : Ty) (T : Ty) → Type

private
  variable
    γ γ' γ'' : Subst Δ Γ
    δ δ' δ'' : Subst Θ Δ
    θ θ' θ'' : Subst Z Θ

    V V' V'' : Val Γ S
    M M' M'' N N' : Comp Γ S
    E E' E'' F F' : EvCtx Γ S T

-- This isn't actually induction-recursion, this is just a hack to get
-- around limitations of Agda's mutual recursion for HITs
-- https://github.com/agda/agda/issues/5362
_[_]vP : Val Γ S → Subst Δ Γ → Val Δ S
_[_]cP : Comp Γ S → Subst Δ Γ → Comp Δ S
_[_]∙P : EvCtx Γ S T → Comp Γ S → Comp Γ T
varP : Val (S ∷ Γ) S
retP : Comp [ S ] S
appP : Comp (S ∷ (S ⇀ T) ∷ []) T

data Subst where
  -- Subst is a cat
  ids : Subst Γ Γ
  _∘s_ : Subst Δ Θ → Subst Γ Δ → Subst Γ Θ
  ∘IdL : ids ∘s γ ≡ γ
  ∘IdR : γ ∘s ids ≡ γ
  ∘Assoc : γ ∘s (δ ∘s θ) ≡ (γ ∘s δ) ∘s θ

  -- [] is terminal
  !s : Subst Γ []
  []η : γ ≡ !s

  -- universal property of S ∷ Γ
  -- β (other one is in Val), η and naturality
  _,s_ : Subst Γ Δ → Val Γ S → Subst Γ (S ∷ Δ)
  wk : Subst (S ∷ Γ) Γ
  wkβ : wk ∘s (δ ,s V) ≡ δ
  ,sη : δ ≡ (wk ∘s δ ,s varP [ δ ]vP)

-- copied from similar operators
infixl 4 _,s_
infixr 9 _∘s_

data Val where
  -- values form a presheaf over substitutions
  _[_]v : Val Γ S → Subst Δ Γ → Val Δ S
  substId : V [ ids ]v ≡ V
  substAssoc : V [ δ ∘s γ ]v ≡ (V [ δ ]v) [ γ ]v

  -- with explicit substitutions we only need the one variable, which
  -- we can combine with weakening
  var : Val (S ∷ Γ) S
  varβ : var [ δ ,s V ]v ≡ V

  -- by making these function symbols we avoid more substitution equations
  zro : Val [] nat
  suc : Val [ nat ] nat

  -- TODO: prove substitution under lambdas is admissible
  lda : Comp (S ∷ Γ) T -> Val Γ (S ⇀ T)
  -- V = λ x. V x
  fun-η : V ≡ lda (appP [ (!s ,s (V [ wk ]v)) ,s var ]cP)

  injectN   : Val [ nat ] dyn
  injectArr : Val [ dyn ⇀ dyn ] dyn
  -- TODO: do we need this?
  -- mapDyn : Val [ nat ] nat → Val [ dyn ⇀ dyn ] (dyn ⇀ dyn) → Val [ dyn ] dyn
  -- TODO: add products

  up : (S⊑T : TyPrec) -> Val [ ty-left S⊑T ] (ty-right S⊑T)

_[_]vP = _[_]v
varP = var

↑subst : Subst Δ Γ → Subst (R ∷ Δ) (R ∷ Γ)
↑subst γ = γ ∘s wk ,s var

data EvCtx where
  -- Evaluation contexts form a category...
  ∙E : EvCtx Γ S S
  _∘E_ : EvCtx Γ T U → EvCtx Γ S T → EvCtx Γ S U
  ∘IdL : ∙E ∘E E ≡ E
  ∘IdR : E ∘E ∙E ≡ E
  ∘Assoc : E ∘E (F ∘E F') ≡ (E ∘E F) ∘E F'

  -- ...enriched in presheaves over contexts.
  _[_]e : EvCtx Γ S T → Subst Δ Γ → EvCtx Δ S T
  substId : E [ ids ]e ≡ E
  substAssoc : E [ γ ∘s δ ]e ≡ E [ γ ]e [ δ ]e
  ∙substDist : ∙E {S = S} [ γ ]e ≡ ∙E
  ∘substDist : (E ∘E F) [ γ ]e ≡ (E [ γ ]e) ∘E (F [ γ ]e)

  bind : Comp (S ∷ Γ) T → EvCtx Γ S T
  -- E[∙] ≡ x <- ∙; E[ret x]
  ret-η : E ≡ bind (E [ wk ]e [ retP [ !s ,s var ]cP ]∙P)

  dn : (S⊑T : TyPrec) → EvCtx [] (ty-right S⊑T) (ty-left S⊑T)

data Comp where
  -- computations are a module of the category of evaluation contexts...
  _[_]∙ : EvCtx Γ S T → Comp Γ S → Comp Γ T
  plugId : ∙E [ M ]∙ ≡ M
  plugAssoc : (F ∘E E) [ M ]∙ ≡ F [ E [ M ]∙ ]∙

  -- ...enriched in presheaves over contexts of course
  _[_]c : Comp Δ S → Subst Γ Δ → Comp Γ S
  substId : M [ ids ]c ≡ M
  substAssoc : M [ δ ∘s γ ]c ≡ (M [ δ ]c) [ γ ]c
  -- Interchange law
  substPlugDist : (E [ M ]∙) [ γ ]c ≡ (E [ γ ]e) [ M [ γ ]c ]∙

  err : Comp [] S
  -- E[err] ≡ err
  strictness : E [ err [ !s ]c ]∙ ≡ err [ !s ]c

  ret : Comp [ S ] S
  -- x <- ret x; M ≡ M
  ret-β : (bind M [ wk ]e [ ret [ !s ,s var ]c ]∙) ≡ M

  app : Comp (S ∷ S ⇀ T ∷ []) T
  -- (λ x. M) x ≡ M
  fun-β : app [ (!s ,s ((lda M) [ wk ]v)) ,s var ]c ≡ M

  matchNat : Comp Γ S → Comp (nat ∷ Γ) S → Comp (nat ∷ Γ) S
  -- match 0 Kz (x . Ks) ≡ Kz
  matchNatβz : (Kz : Comp Γ S)(Ks : Comp (nat ∷ Γ) S)
             → matchNat Kz Ks [ ids ,s (zro [ !s ]v) ]c ≡ Kz
  -- match (S y) Kz (x . Ks) ≡ Ks [ y / x ]
  matchNatβs : (Kz : Comp Γ S) (Ks : Comp (nat ∷ Γ) S)
             → matchNat Kz Ks [ wk ,s (suc [ !s ,s var ]v) ]c ≡ Ks
  -- M[x] ≡ match x (M[0/x]) (x. M[S x/x])
  matchNatη : M ≡ matchNat
       (M [ ids ,s (zro [ !s ]v) ]c)
       (M [ wk ,s (suc [ !s ,s var ]v) ]c)

  matchDyn : Comp (nat ∷ Γ) S → Comp ((dyn ⇀ dyn) ∷ Γ) S → Comp (dyn ∷ Γ) S

  matchDynβn : (Kn : Comp (nat ∷ Γ) S) (Kf : Comp ((dyn ⇀ dyn) ∷ Γ) S)
               (V : Val Γ nat) ->
    matchDyn Kn Kf [ ids ,s (injectN [ !s ,s V ]v) ]c ≡
    Kn [ ids ,s V ]c

  matchDynβf : (Kn : Comp (nat ∷ Γ) S) (Kf : Comp ((dyn ⇀ dyn) ∷ Γ) S)
               (V : Val Γ (dyn ⇀ dyn)) ->
    matchDyn Kn Kf [ ids ,s (injectArr [ !s ,s V ]v) ]c ≡
    Kf [ ids ,s V ]c

  matchDynSubst :
    ∀ (M : Comp (nat ∷ Γ) R) (N : Comp ((dyn ⇀ dyn) ∷ Γ) R) (γ : Subst Δ Γ)
    → matchDyn M N [ ↑subst γ ]c ≡ matchDyn (M [ ↑subst γ ]c) (N [ ↑subst γ ]c)

appP = app
retP = ret
_[_]cP = _[_]c
_[_]∙P = _[_]∙
------------------------------------------------
-- Convenience definitions

_∘V_ : Val (S ∷ Γ) T -> Val Γ S -> Val Γ T
V ∘V W  =  V [ ids ,s W ]v

_∘V'_ : Val [ S ] T -> Val Γ S -> Val Γ T
V ∘V' W = (V [ !s ,s var ]v) ∘V W

compCompose : Comp (S ∷ Γ) T -> Comp Γ S -> Comp Γ T
compCompose N M = (bind N) [ M ]∙

vToE : Val [ S ] T → EvCtx [] S T
vToE V = bind (ret [ !s ,s V ]c)

upE : (S⊑T : TyPrec) → EvCtx [] (ty-left S⊑T) (ty-right S⊑T)
upE c = vToE (up c)

-- Sequencing computations via bind and [ _ ]∙
bind' : Comp Γ S -> Comp (S ∷ Γ) T -> Comp Γ T
bind' M N = (bind N) [ M ]∙

ret' : Val Γ S → Comp Γ S
ret' V = ret [ !s ,s V ]c

-- Sequencing with a value
seqVal : Comp Γ S -> Val (S ∷ Γ) T -> Comp Γ T
seqVal M V = bind' M (ret' V)

eToC : EvCtx [] S T → Comp [ S ] T
eToC E = (E [ wk ]e) [ ret' var ]∙


zro' : Val Γ nat
zro' = zro [ !s ]v

suc' : Val Γ nat -> Val Γ nat
suc' V = suc [ !s ,s V ]v

err' : Comp Γ S
err' = err [ !s ]c

app' : Comp (S ∷ S ⇀ T ∷ Γ) T
app' = app [ (!s ,s (var [ wk ]v)) ,s var ]c

app'' : Comp Γ (S ⇀ T) -> Comp Γ S -> Comp Γ T
app'' M N = bind' M (bind' (N [ wk ]c) app')

appVal : (Vf : Val Γ (S ⇀ T)) (Va : Val Γ S) → Comp Γ T
appVal Vf Va = app [ !s ,s Vf ,s Va ]c

π2 : Val (S ∷ T ∷ Γ) T
π2 = var [ wk ]v

reverseArg : Subst (S ∷ T ∷ Γ) (T ∷ S ∷ Γ)
reverseArg = (wk ∘s wk ,s var) ,s (var [ wk ]v)

drop2nd : Subst (S ∷ T ∷ U ∷ Γ) (S ∷ U ∷ Γ)
drop2nd = ((wk ∘s wk ∘s wk) ,s (var [ wk ∘s wk ]v)) ,s  var 
