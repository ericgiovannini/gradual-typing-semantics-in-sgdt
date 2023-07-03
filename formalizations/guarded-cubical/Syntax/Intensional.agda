{-# OPTIONS --cubical #-}
module Syntax.Intensional  where

-- The intensional syntax, which is quotiented by βη equivalence and
-- order equivalence but where casts take observable steps.

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
open CtxPrec

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T U R' S' T' U' : Ty
   B B' C C' D D' : Γ ⊑ctx Γ'
   b b' c c' d d' : S ⊑ S'

-- Substitutions, Values, Computations and Evaluation contexts,
-- quotiented by *intensional* order equivalence, including βη equalities
data Subst : (Δ : Ctx) (Γ : Ctx) → Type
data Subst⊑ : (C : Δ ⊑ctx Δ') (D : Γ ⊑ctx Γ') (γ : Subst Δ Γ) (γ' : Subst Δ' Γ') → Type

data Val : (Γ : Ctx) (S : Ty) → Type
data Val⊑ : (C : Γ ⊑ctx Γ') (c : S ⊑ S') (V : Val Γ S) (V' : Val Γ' S') → Type

data EvCtx : (Γ : Ctx) (S : Ty) (T : Ty) → Type
data EvCtx⊑ : (C : Γ ⊑ctx Γ') (c : S ⊑ S') (d : T ⊑ T') (E : EvCtx Γ S T) (E' : EvCtx Γ' S' T') → Type

data Comp : (Γ : Ctx) (S : Ty) → Type
data Comp⊑ : (C : Γ ⊑ctx Γ') (c : S ⊑ S') (M : Comp Γ S) (M' : Comp Γ' S') → Type


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
  isSetSubst : isSet (Subst Δ Γ)
  isPosetSubst : Subst⊑ (refl-⊑ctx Δ) (refl-⊑ctx Γ) γ γ'
               → Subst⊑ (refl-⊑ctx Δ) (refl-⊑ctx Γ) γ' γ
               → γ ≡ γ'

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

data Subst⊑ where
  !s : Subst⊑ C [] !s !s
  _,s_ : Subst⊑ C D γ γ' → Val⊑ C c V V' → Subst⊑ C (c ∷ D) (γ ,s V) (γ' ,s V')
  _∘s_ : Subst⊑ C D γ γ' → Subst⊑ B C δ δ' → Subst⊑ B D (γ ∘s δ) (γ' ∘s δ')
  _ids_ : Subst⊑ C C ids ids
  -- in principle we could add βη equations instead but truncating is simpler
  isProp⊑ : isProp (Subst⊑ C D γ γ')
  hetTrans : Subst⊑ C D γ γ' → Subst⊑ C' D' γ' γ'' → Subst⊑ (trans-⊑ctx C C') (trans-⊑ctx D D') γ γ''

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
  δl  : (S⊑T : TyPrec) → Val [ ty-left S⊑T ] (ty-left S⊑T)
  δr  : (S⊑T : TyPrec) → Val [ ty-right S⊑T ] (ty-right S⊑T)

  isSetVal : isSet (Val Γ S)
  isPosetVal : Val⊑ (refl-⊑ctx Γ) (refl-⊑ S) V V'
             → Val⊑ (refl-⊑ctx Γ) (refl-⊑ S) V' V
             → V ≡ V'

_[_]vP = _[_]v
varP = var

data Val⊑ where
  _[_]v : Val⊑ C c V V' → Subst⊑ B C γ γ' → Val⊑ B c (V [ γ ]v) (V' [ γ' ]v)
  var : Val⊑ (c ∷ C) c var var
  zro : Val⊑ [] nat zro zro
  suc : Val⊑ (nat ∷ []) nat suc suc

  -- if x <= y then e x <= δr y
  up-L : ∀ S⊑T → Val⊑ ((ty-prec S⊑T) ∷ []) (refl-⊑ (ty-right S⊑T)) (up S⊑T) (δr S⊑T)
  -- if x <= y then δl x <= e y
  up-R : ∀ S⊑T → Val⊑ ((refl-⊑ (ty-left S⊑T)) ∷ []) (ty-prec S⊑T) (δl S⊑T) (up S⊑T)

  isProp⊑ : isProp (Val⊑ C c V V')
  hetTrans : Val⊑ C c V V' → Val⊑ D d V' V'' → Val⊑ (trans-⊑ctx C D) (trans-⊑ c d) V V''

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
  δl  : (S⊑T : TyPrec) → EvCtx [] (ty-left S⊑T) (ty-left S⊑T)
  δr  : (S⊑T : TyPrec) → EvCtx [] (ty-right S⊑T) (ty-right S⊑T)

  isSetEvCtx : isSet (EvCtx Γ S T)
  isPosetEvCtx : EvCtx⊑ (refl-⊑ctx Γ) (refl-⊑ S) (refl-⊑ T) E E'
               → EvCtx⊑ (refl-⊑ctx Γ) (refl-⊑ S) (refl-⊑ T) E' E
               → E ≡ E'

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
  isPosetComp : Comp⊑ (refl-⊑ctx Γ) (refl-⊑ S) M M'
              → Comp⊑ (refl-⊑ctx Γ) (refl-⊑ S) M' M
              → M ≡ M'

appP = app
retP = ret
_[_]cP = _[_]c
_[_]∙P = _[_]∙

err' : Comp Γ S
err' = err [ !s ]c

ret' : Val Γ S → Comp Γ S
ret' V = ret [ !s ,s V ]c

vToE : Val [ S ] T → EvCtx [] S T
vToE V = bind (ret [ !s ,s V ]c)

upE : ∀ S⊑T → EvCtx [] (ty-left S⊑T) (ty-right S⊑T)
upE S⊑T = vToE (up S⊑T)

data EvCtx⊑ where
  ∙E : EvCtx⊑ C c c ∙E ∙E
  _∘E_ : EvCtx⊑ C c d E E' → EvCtx⊑ C b c F F' → EvCtx⊑ C b d (E ∘E F) (E' ∘E F')
  _[_]e : EvCtx⊑ C c d E E' → Subst⊑ B C γ γ' → EvCtx⊑  B c d (E [ γ ]e) (E' [ γ' ]e)
  bind : Comp⊑ (c ∷ C) d M M' → EvCtx⊑ C c d (bind M) (bind M')

  dn-L : ∀ S⊑T → EvCtx⊑ [] (refl-⊑ (ty-right S⊑T)) (ty-prec S⊑T) (dn S⊑T) (δr S⊑T)
  dn-R : ∀ S⊑T → EvCtx⊑ [] (ty-prec S⊑T) (refl-⊑ (ty-left S⊑T)) (δl S⊑T) (dn S⊑T)
  retractionR : ∀ S⊑T → EvCtx⊑ [] (refl-⊑ (ty-right S⊑T)) (refl-⊑ (ty-right S⊑T))
    (vToE (δr S⊑T) ∘E δr S⊑T)
    (vToE (up S⊑T) ∘E dn S⊑T)

  hetTrans : EvCtx⊑ C b c E E' → EvCtx⊑ C' b' c' E' E'' → EvCtx⊑ (trans-⊑ctx C C') (trans-⊑ b b') (trans-⊑ c c') E E''
  isProp⊑ : isProp (EvCtx⊑ C c d E E')

data Comp⊑ where
  _[_]∙ : EvCtx⊑ C c d E E' → Comp⊑ C c M M' → Comp⊑ C d (E [ M ]∙) (E' [ M' ]∙)
  _[_]c : Comp⊑ C c M M' → Subst⊑ D C γ γ' → Comp⊑ D c (M [ γ ]c) (M' [ γ' ]c)
  ret : Comp⊑ (c ∷ []) c ret ret
  app : Comp⊑ (c ∷ c ⇀ d ∷ []) d app app
  matchNat : ∀ {Kz Kz' Ks Ks'} → Comp⊑ C c Kz Kz' → Comp⊑ (nat ∷ C) c Ks Ks' → Comp⊑ (nat ∷ C) c (matchNat Kz Ks) (matchNat Kz' Ks')

  err⊥ : Comp⊑ (refl-⊑ctx Γ) (refl-⊑ S) err' M

  hetTrans : Comp⊑ C c M M' → Comp⊑ D d M' M'' → Comp⊑ (trans-⊑ctx C D) (trans-⊑ c d) M M''
  isProp⊑ : isProp (Comp⊑ C c M M')

-- -- TODO: admissibility of Reflexivity of each ⊑
-- refl-Subst⊑ : ∀ γ → Subst⊑ (refl-⊑ctx Δ) (refl-⊑ctx Γ) γ γ
-- refl-Subst⊑ γ = {!!}

-- refl-Val⊑ : ∀ V → Val⊑ (refl-⊑ctx Γ) (refl-⊑ S) V V
-- refl-Val⊑ V = {!!}

-- refl-Comp⊑ : ∀ M → Comp⊑ (refl-⊑ctx Γ) (refl-⊑ S) M M
-- refl-Comp⊑ M = {!!}

-- refl-EvCtx⊑ : ∀ E → EvCtx⊑ (refl-⊑ctx Γ) (refl-⊑ S) (refl-⊑ S) E E
-- refl-EvCtx⊑ E = {!!}
