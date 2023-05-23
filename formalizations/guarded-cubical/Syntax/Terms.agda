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

SynType = Ty Empty
TyPrec = Ty Full

TypeCtx = Ctx Empty
PrecCtx = Ctx Full

private
 variable
   ℓ ℓ' ℓ'' : Level
   Δ Γ Θ Z : TypeCtx
   R S T U : SynType

-- Values, Computations and Evaluation contexts,
-- quotiented by βη equivalence but *not* by order equivalence (i.e., up/dn laws)
data Subst : (Δ : TypeCtx) (Γ : TypeCtx) → Type (ℓ-suc ℓ-zero)
data Val : (Γ : TypeCtx) (A : SynType) → Type (ℓ-suc ℓ-zero)
data EvCtx : (Γ : TypeCtx) (A : SynType) (B : SynType) → Type (ℓ-suc ℓ-zero)
data Comp : (Γ : TypeCtx) (A : SynType) → Type (ℓ-suc ℓ-zero)

-- This isn't actually induction-recursion, this is just a hack to get
-- around limitations of Agda's mutual recursion for HITs
-- https://github.com/agda/agda/issues/5362
_[_]v : Val Γ S → Subst Δ Γ → Val Δ S
_[_]c : Comp Γ S → Subst Δ Γ → Comp Δ S
_[_]e : EvCtx Γ S T → Subst Δ Γ → EvCtx Δ S T
_[_]∙ : EvCtx Γ S T → Comp Γ S → Comp Γ T
var : Val (S ∷ Γ) S
ret : Comp [ S ] S
app : Comp (S ∷ (S ⇀ T) ∷ []) T

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
  ∘IdL : (γ : Subst Γ Γ) → ids ∘s γ ≡ γ
  ∘IdR : (γ : Subst Γ Γ) → γ ∘s ids ≡ γ
  ∘Assoc : (γ : Subst Δ Γ) (δ : Subst Θ Δ)(θ : Subst Z Θ) → γ ∘s (δ ∘s θ) ≡ (γ ∘s δ) ∘s θ

  -- [] is terminal
  !s : Subst Γ []
  []η : (γ : Subst Γ []) → γ ≡ !s

  -- universal property of S ∷ Γ
  -- β (other one is in Val), η and naturality
  _,s_ : Subst Γ Δ → Val Γ S → Subst Γ (S ∷ Δ)
  wk : Subst (S ∷ Γ) Γ
  wkβ : (δ : Subst Γ Δ)(V : Val Γ S) → wk ∘s (δ ,s V) ≡ δ
  ,sη : (δ : Subst Γ (S ∷ Δ)) → δ ≡ (wk ∘s δ ,s var [ δ ]v)

-- copied from similar operators
infixl 4 _,s_
infixr 9 _∘s_

data Val where
  -- with explicit substitutions we only need the one variable, which we can combine with weakening
  varPrim : Val (S ∷ Γ) S
  varβ : (δ : Subst Γ Δ) (V : Val Γ S) → var [ δ ,s V ]v ≡ V

  -- by making these function symbols we avoid more substitution equations
  zro : Val [] nat
  suc : Val [ nat ] nat

  lda : Comp (S ∷ Γ) T -> Val Γ (S ⇀ T) -- TODO: prove substitution under lambdas is admissible
  fun-η : (V : Val Γ (S ⇀ T))
        -- V = λ x. V x
        → V ≡ lda (app [ (!s ,s (V [ wk ]v)) ,s var ]c)

  up : (S⊑T : TyPrec) -> Val [ ty-left S⊑T ] (ty-right S⊑T)

  -- values form a presheaf over substitutions
  _[_]v' : Val Γ S → Subst Δ Γ → Val Δ S
  substId : (V : Val Γ S) → V [ ids ]v ≡ V
  substAssoc : (V : Val Δ S) (δ : Subst Γ Δ)(γ : Subst Θ Γ)
          → V [ δ ∘s γ ]v ≡ (V [ δ ]v) [ γ ]v

  isSetVal : isSet (Val Γ S)

_[_]v = _[_]v'
var = varPrim

data EvCtx where
  ∙E : EvCtx Γ S S
  _∘E_ : EvCtx Γ T U → EvCtx Γ S T → EvCtx Γ S U
  ∘IdL : (E : EvCtx Γ S T) → ∙E ∘E E ≡ E
  ∘IdR : (E : EvCtx Γ S T) → E ∘E ∙E ≡ E
  ∘Assoc : (E : EvCtx Γ T U) (F : EvCtx Γ S T)(G : EvCtx Γ R S)
         → E ∘E (F ∘E G) ≡ (E ∘E F) ∘E G

  _[_]e' : EvCtx Γ S T → Subst Δ Γ → EvCtx Δ S T
  substId : (E : EvCtx Γ S T) → E [ ids ]e ≡ E
  substAssoc : (E : EvCtx Γ S T)(γ : Subst Δ Γ)(δ : Subst Θ Δ)
            → E [ γ ∘s δ ]e ≡ E [ γ ]e [ δ ]e

  ∘substDist : (E : EvCtx Γ T U)(F : EvCtx Γ S T)(γ : Subst Δ Γ)
             → (E ∘E F) [ γ ]e ≡ (E [ γ ]e) ∘E (F [ γ ]e)

  bind : Comp (S ∷ Γ) T → EvCtx Γ S T
  -- E[∙] ≡ x <- ∙; E[ret x]
  ret-η : (E : EvCtx Γ S T) → E ≡ bind (E [ wk ]e [ ret [ !s ,s var ]c ]∙)

  dn : (S⊑T : TyPrec) → EvCtx Γ (ty-right S⊑T) (ty-left S⊑T)

  isSetEvCtx : isSet (EvCtx Γ S T)

data Comp where
  _[_]∙' : EvCtx Γ S T → Comp Γ S → Comp Γ T
  plugId : (M : Comp Γ S) → ∙E [ M ]∙ ≡ M
  plugAssoc : (M : Comp Γ S)(E : EvCtx Γ S T)(F : EvCtx Γ T U) → (F ∘E E) [ M ]∙ ≡ F [ E [ M ]∙ ]∙

  _[_]c' : Comp Δ S → Subst Γ Δ → Comp Γ S
  -- presheaf
  substId : (M : Comp Γ S) → M [ ids ]c ≡ M
  substAssoc : (M : Comp Δ S) (δ : Subst Γ Δ)(γ : Subst Θ Γ)
         → M [ δ ∘s γ ]c ≡ (M [ δ ]c) [ γ ]c

  -- Interchange law
  substPlugDist : (E : EvCtx Γ S T) (M : Comp Γ S) → (γ : Subst Δ Γ)
                → (E [ M ]∙) [ γ ]c ≡ (E [ γ ]e) [ M [ γ ]c ]∙

  err : Comp [] S
  -- E[err] ≡ err
  strictness : (E : EvCtx Γ S T) → E [ err [ !s ]c ]∙ ≡ err [ !s ]c

  retPrim : Comp [ S ] S
  -- x <- ret x; M ≡ M
  ret-β : (M : Comp (S ∷ Γ) T) → (bind M [ wk ]e [ ret [ !s ,s var ]c ]∙) ≡ M

  appPrim : Comp (S ∷ S ⇀ T ∷ []) T
  -- (λ x. M) x ≡ M
  fun-β : (M : Comp (S ∷ Γ) T) → app [ (!s ,s ((lda M) [ wk ]v)) ,s var ]c ≡ M

  matchNat : Comp Γ S → Comp (nat ∷ Γ) S → Comp (nat ∷ Γ) S
  -- match 0 Kz (x . Ks) ≡ Kz
  matchNatβz : (Kz : Comp Γ S)(Ks : Comp (nat ∷ Γ) S)
             → matchNat Kz Ks [ ids ,s (zro [ !s ]v) ]c ≡ Kz
  -- match (S V) Kz (x . Ks) ≡ Ks [ V / x ]
  matchNatβs : (Kz : Comp Γ S)(Ks : Comp (nat ∷ Γ) S) (V : Val Γ nat)
             → matchNat Kz Ks [ ids ,s (suc [ !s ,s V ]v) ]c ≡ (Ks [ ids ,s V ]c)
  -- M[x] ≡ match x (M[0/x]) (x. M[S x/x])
  matchNatη : (M : Comp (nat ∷ Γ) S) → M ≡ matchNat (M [ ids ,s (zro [ !s ]v) ]c) (M [ wk ,s (suc [ !s ,s var ]v) ]c)

  isSetComp : isSet (Comp Γ S)
app = appPrim
ret = retPrim
_[_]c = _[_]c'
_[_]e = _[_]e'
_[_]∙ = _[_]∙'

-- More ordinary term constructors are admissible
-- up, dn, zro, suc, err, app, bind
app' : (Vf : Val Γ (S ⇀ T)) (Va : Val Γ S) → Comp Γ T
app' Vf Va = app [ !s ,s Vf ,s Va ]c

-- As well as substitution principles for them
!s-nat : (γ : Subst Γ []) → !s ∘s γ ≡ !s
!s-nat γ = []η _

,s-nat : (δ : Subst Θ Δ) (γ : Subst Δ Γ) (V : Val Δ S)
       → (γ ,s V) ∘s δ ≡ ((γ ∘s δ) ,s (V [ δ ]v))
,s-nat δ γ V =
  ,sη _
  ∙ cong₂ _,s_ (∘Assoc _ _ _ ∙ cong (_∘s δ) (wkβ _ _))
               (substAssoc _ _ _ ∙ cong _[ δ ]v (varβ _ _))

-- Some examples for functions
app'-nat : (γ : Subst Δ Γ) (Vf : Val Γ (S ⇀ T)) (Va : Val Γ S)
         → app' Vf Va [ γ ]c ≡ app' (Vf [ γ ]v) (Va [ γ ]v)
app'-nat γ Vf Va =
  sym (substAssoc _ _ _)
  ∙ cong (app [_]c) (,s-nat _ _ _ ∙ cong₂ _,s_ (,s-nat _ _ _ ∙ cong₂ _,s_ ([]η _) refl) refl)

lda-nat : (γ : Subst Δ Γ) (M : Comp (S ∷ Γ) T)
        → (lda M) [ γ ]v ≡ lda (M [ γ ∘s wk ,s var ]c)
lda-nat {Δ = Δ}{Γ = Γ}{S = S} γ M =
  fun-η _
  ∙ cong lda (cong (app [_]c) (cong₂ _,s_ (cong₂ _,s_ (sym ([]η (!s ∘s the-subst))) (sym (substAssoc _ _ _)
                                                                                    ∙ cong (lda M [_]v) (sym (wkβ _ var))
                                                                                    ∙ substAssoc _ _ _))
                                                      (sym (varβ (γ ∘s wk) _))
                              ∙ cong (_,s (var [ the-subst ]v)) (sym (,s-nat _ _ _))
                              ∙ sym (,s-nat _ _ _))
             ∙ substAssoc _ _ _
             ∙ cong (_[ the-subst ]c) (fun-β _)) where
  the-subst : Subst (S ∷ Δ) (S ∷ Γ)
  the-subst = γ ∘s wk ,s var

fun-β' : (M : Comp (S ∷ Γ) T) (V : Val Γ S)
       → app' (lda M) V ≡ M [ ids ,s V ]c
fun-β' M V =
  cong (app [_]c) (cong₂ _,s_ (cong₂ _,s_ (sym ([]η _)) ((sym (substId _) ∙ cong (lda M [_]v) (sym (wkβ _ _))) ∙ substAssoc _ _ _) ∙ sym (,s-nat _ _ _))
                              (sym (varβ _ _))
                  ∙ sym (,s-nat _ _ _))
  ∙ substAssoc _ _ _
  ∙ cong (_[ ids ,s V ]c) (fun-β _)

fun-η' : (V : Val Γ (S ⇀ T)) → V ≡ lda (app' (V [ wk ]v) var)
fun-η' = fun-η
