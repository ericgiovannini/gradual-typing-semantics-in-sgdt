{-# OPTIONS --cubical #-}
 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}
module Syntax.Terms  where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Cubical.Data.Prod hiding (map)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.Empty renaming (rec to exFalso)

open import Syntax.Types

open TyPrec

private
 variable
   Δ Γ Θ Z : Ctx
   R S T U : Ty

-- Values, Computations and Evaluation contexts,
-- quotiented by βη equivalence but *not* by order equivalence (i.e., up/dn laws)
data Subst : (Δ : Ctx) (Γ : Ctx) → Type
data Val : (Γ : Ctx) (S : Ty) → Type
data EvCtx : (Γ : Ctx) (S : Ty) (T : Ty) → Type
data Comp : (Γ : Ctx) (S : Ty) → Type

private
  variable
    γ : Subst Δ Γ
    δ : Subst Θ Δ
    θ : Subst Z Θ

    V V' : Val Γ S
    M M' N N' : Comp Γ S
    E E' F F' : EvCtx Γ S T

-- This isn't actually induction-recursion, this is just a hack to get
-- around limitations of Agda's mutual recursion for HITs
-- https://github.com/agda/agda/issues/5362
_[_]vP : Val Γ S → Subst Δ Γ → Val Δ S
_[_]cP : Comp Γ S → Subst Δ Γ → Comp Δ S
_[_]∙P : EvCtx Γ S T → Comp Γ S → Comp Γ T
varP : Val (S ∷ Γ) S
retP : Comp [ S ] S
appP : Comp (S ∷ (S ⇀ T) ∷ []) T

-- Explicit substitutions roughly following https://arxiv.org/pdf/1809.08646.pdf
-- but with some changes
-- Idea:
-- 1. Subst is a category
-- 2. Subst Γ (S ∷ Δ) ≅ Subst Γ Δ × Val Γ S
-- 3 Val - S , Comp - S, EvCtx - S T are Presheaves over Subst
-- 4. EvCtx Γ - = is a category enriched in Psh over Subst
-- 5. Comp Γ is a Psh(Subst)-enriched covariant presheaf over EvCtx Γ
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

  -- with explicit substitutions we only need the one variable, which we can combine with weakening
  var : Val (S ∷ Γ) S
  varβ : var [ δ ,s V ]v ≡ V

  -- by making these function symbols we avoid more substitution equations
  zro : Val [] nat
  suc : Val [ nat ] nat

  lda : Comp (S ∷ Γ) T -> Val Γ (S ⇀ T) -- TODO: prove substitution under lambdas is admissible
  -- V = λ x. V x
  fun-η : V ≡ lda (appP [ (!s ,s (V [ wk ]v)) ,s var ]cP)

  up : (S⊑T : TyPrec) -> Val [ ty-left S⊑T ] (ty-right S⊑T)

  isSetVal : isSet (Val Γ S)

_[_]vP = _[_]v
varP = var

data EvCtx where
  ∙E : EvCtx Γ S S
  _∘E_ : EvCtx Γ T U → EvCtx Γ S T → EvCtx Γ S U
  ∘IdL : ∙E ∘E E ≡ E
  ∘IdR : E ∘E ∙E ≡ E
  ∘Assoc : E ∘E (F ∘E F') ≡ (E ∘E F) ∘E F'

  _[_]e : EvCtx Γ S T → Subst Δ Γ → EvCtx Δ S T
  substId : E [ ids ]e ≡ E
  substAssoc : E [ γ ∘s δ ]e ≡ E [ γ ]e [ δ ]e

  ∙substDist : ∙E {S = S} [ γ ]e ≡ ∙E
  ∘substDist : (E ∘E F) [ γ ]e ≡ (E [ γ ]e) ∘E (F [ γ ]e)

  bind : Comp (S ∷ Γ) T → EvCtx Γ S T
  -- E[∙] ≡ x <- ∙; E[ret x]
  ret-η : E ≡ bind (E [ wk ]e [ retP [ !s ,s var ]cP ]∙P)

  dn : (S⊑T : TyPrec) → EvCtx [] (ty-right S⊑T) (ty-left S⊑T)

  isSetEvCtx : isSet (EvCtx Γ S T)

data Comp where
  _[_]∙ : EvCtx Γ S T → Comp Γ S → Comp Γ T
  plugId : ∙E [ M ]∙ ≡ M
  plugAssoc : (F ∘E E) [ M ]∙ ≡ F [ E [ M ]∙ ]∙

  _[_]c : Comp Δ S → Subst Γ Δ → Comp Γ S
  -- presheaf
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
  -- match (S V) Kz (x . Ks) ≡ Ks [ V / x ]
  matchNatβs : (Kz : Comp Γ S)(Ks : Comp (nat ∷ Γ) S) (V : Val Γ nat)
             → matchNat Kz Ks [ ids ,s (suc [ !s ,s V ]v) ]c ≡ (Ks [ ids ,s V ]c)
  -- M[x] ≡ match x (M[0/x]) (x. M[S x/x])
  matchNatη : M ≡ matchNat (M [ ids ,s (zro [ !s ]v) ]c) (M [ wk ,s (suc [ !s ,s var ]v) ]c)

  isSetComp : isSet (Comp Γ S)
appP = app
retP = ret
_[_]cP = _[_]c
_[_]∙P = _[_]∙

-- More ordinary term constructors are admissible
-- up, dn, zro, suc, err, app, bind
app' : (Vf : Val Γ (S ⇀ T)) (Va : Val Γ S) → Comp Γ T
app' Vf Va = app [ !s ,s Vf ,s Va ]c

-- As well as substitution principles for them
!s-nat : (γ : Subst Γ []) → !s ∘s γ ≡ !s
!s-nat γ = []η

!s-ext : {γ : Subst Γ []} → γ ≡ δ
!s-ext = []η ∙ sym []η

,s-nat : (γ ,s V) ∘s δ ≡ ((γ ∘s δ) ,s (V [ δ ]v))
,s-nat =
  ,sη ∙ cong₂ _,s_ (∘Assoc ∙ cong₂ (_∘s_) wkβ refl)
               (substAssoc ∙ cong₂ _[_]v varβ refl)

,s-ext : wk ∘s γ ≡ wk ∘s δ → (var [ γ ]v ≡ var [ δ ]v) → γ ≡ δ
,s-ext wkp varp = ,sη ∙ cong₂ _,s_ wkp varp ∙ sym ,sη

-- Some examples for functions
app'-nat : (γ : Subst Δ Γ) (Vf : Val Γ (S ⇀ T)) (Va : Val Γ S)
         → app' Vf Va [ γ ]c ≡ app' (Vf [ γ ]v) (Va [ γ ]v)
app'-nat γ Vf Va =
  sym substAssoc
  ∙ cong (app [_]c) (,s-nat ∙ cong₂ _,s_ (,s-nat  ∙ cong₂ _,s_ []η refl) refl)

lda-nat : (γ : Subst Δ Γ) (M : Comp (S ∷ Γ) T)
        → (lda M) [ γ ]v ≡ lda (M [ γ ∘s wk ,s var ]c)
lda-nat {Δ = Δ}{Γ = Γ}{S = S} γ M =
  fun-η
  ∙ cong lda (cong (app [_]c) (cong₂ _,s_ (cong₂ _,s_ (sym ([]η)) (sym substAssoc
                                                                                    ∙ cong (lda M [_]v) (sym wkβ)
                                                                                    ∙ substAssoc))
                                                      (sym varβ)
                              ∙ cong (_,s (var [ the-subst ]v)) (sym ,s-nat)
                              ∙ sym ,s-nat)
             ∙ substAssoc
             ∙ cong (_[ the-subst ]c) fun-β) where
  the-subst : Subst (S ∷ Δ) (S ∷ Γ)
  the-subst = γ ∘s wk ,s var

fun-β' : (M : Comp (S ∷ Γ) T) (V : Val Γ S)
       → app' (lda M) V ≡ M [ ids ,s V ]c
fun-β' M V =
  cong (app [_]c) (cong₂ _,s_ (cong₂ _,s_ (sym []η) ((sym substId ∙ cong (lda M [_]v) (sym wkβ)) ∙ substAssoc) ∙ sym ,s-nat)
                              (sym varβ)
                  ∙ sym ,s-nat)
  ∙ substAssoc
  ∙ cong (_[ ids ,s V ]c) fun-β

fun-η' : V ≡ lda (app' (V [ wk ]v) var)
fun-η' = fun-η

err' : Comp Γ S
err' = err [ !s ]c

ret' : Val Γ S → Comp Γ S
ret' V = ret [ !s ,s V ]c

bind' : Comp Γ S → Comp (S ∷ Γ) T → Comp Γ T
bind' M K = bind K [ M ]∙

bind-nat : (bind M) [ γ ]e ≡ bind (M [ γ ∘s wk ,s var ]c)
bind-nat {M = M} {γ = γ} = ret-η ∙ cong bind (cong (_[ ret [ !s ,s var ]c ]∙) (sym substAssoc)
                             ∙ cong₂ _[_]∙ (cong (bind M [_]e) (sym wkβ) ∙ substAssoc)
                                           (cong (ret [_]c) (cong₂ _,s_ !s-ext (sym varβ) ∙ sym ,s-nat) ∙ substAssoc)
                             ∙ sym substPlugDist
                             ∙ cong (_[ γ ∘s wk ,s var ]c) ret-β)

bind'-nat : (bind' M N) [ γ ]c ≡ bind' (M [ γ ]c) (N [ γ ∘s wk ,s var ]c)
bind'-nat = substPlugDist ∙ cong₂ _[_]∙ bind-nat refl

ret-β' : bind' (ret' V) M ≡ (M [ ids ,s V ]c)
ret-β' =
  (cong₂ _[_]∙ ((sym substId ∙ cong₂ _[_]e refl (sym wkβ)) ∙ substAssoc)
               (cong (ret [_]c) (,s-ext !s-ext (varβ ∙ (sym varβ ∙ sym varβ) ∙ cong (var [_]v) (sym ,s-nat))) ∙ substAssoc)
  ∙ sym substPlugDist)
  ∙ cong₂ _[_]c ret-β refl

ret-η' : M ≡ bind' M (ret' var)
ret-η' = sym plugId ∙ cong₂ _[_]∙ (ret-η ∙ cong bind (cong₂ _[_]∙ ∙substDist refl ∙ plugId)) refl

up' : ∀ S⊑T → Val Γ (ty-left S⊑T) → Val Γ (ty-right S⊑T)
up' S⊑T V = up S⊑T [ !s ,s V ]v

upC : ∀ S⊑T → Val Γ (ty-left S⊑T) → Comp Γ (ty-right S⊑T)
upC S⊑T V = ret' (up' S⊑T V)

upE : ∀ S⊑T → EvCtx Γ (ty-left S⊑T) (ty-right S⊑T)
upE S⊑T = bind (ret' (up' S⊑T var))

dn' : ∀ S⊑T → Comp Γ (ty-right S⊑T) → Comp Γ (ty-left S⊑T)
dn' S⊑T M = dn S⊑T [ !s ]e [ M ]∙

ids1-expand : Path (Subst (S ∷ []) (S ∷ [])) ids (!s ,s var)
ids1-expand = ,sη ∙ cong₂ _,s_ []η substId

var0 : Val (S ∷ Γ) S
var0 = var

var1 : Val (S ∷ T ∷ Γ) T
var1 = var [ wk ]v

var2 : Val (S ∷ T ∷ U ∷ Γ) U
var2 = var1 [ wk ]v

wk-expand : Path (Subst (S ∷ T ∷ []) (T ∷ [])) wk (!s ,s var1)
wk-expand = ,s-ext !s-ext (sym varβ)

big-η-expand-fun : ∀ (V : Val [ U ] (S ⇀ T)) →
  V ≡ lda (bind' (ret' var)
          (bind' (app' (V [ !s ,s var2 ]v) var)
          (ret' var)))
big-η-expand-fun V =
  fun-η ∙ cong lda ((ret-η'
  ∙ cong₂ bind'
    (cong (app [_]c) (cong₂ _,s_ (cong₂ _,s_ !s-ext (cong (V [_]v) (wk-expand ∙ ,s-ext !s-ext (varβ ∙ (((sym substId ∙ cong₂ _[_]v refl (sym wkβ)) ∙ substAssoc) ∙ cong₂ _[_]v (sym varβ) refl) ∙ sym substAssoc)) ∙ substAssoc) ∙ sym ,s-nat) (sym varβ) ∙ sym ,s-nat) ∙ substAssoc)
    (cong (ret [_]c) (,s-ext !s-ext (((varβ ∙ sym varβ) ∙ cong₂ _[_]v (sym varβ) refl) ∙ sym substAssoc)) ∙ substAssoc) ∙ sym bind'-nat) ∙ sym ret-β')
