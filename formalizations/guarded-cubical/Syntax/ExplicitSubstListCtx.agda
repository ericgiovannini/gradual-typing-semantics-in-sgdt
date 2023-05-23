{-# OPTIONS --cubical --rewriting --guarded -W noUnsupportedIndexedMatch #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}


module Syntax.ExplicitSubstListCtx  where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Cubical.Data.Prod hiding (map)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List

open import Cubical.Data.Empty renaming (rec to exFalso)

-- import Syntax.DeBruijnCommon

private
 variable
   ℓ ℓ' ℓ'' : Level

open import Syntax.Types

SynType = Ty Empty
TyPrec = Ty Full

TypeCtx = Ctx Empty
PrecCtx = Ctx Full

-- Values, Computations and Evaluation contexts,
-- quotiented by βη equivalence but *not* by order equivalence (i.e., up/dn laws)
data Subst : (Δ : TypeCtx) (Γ : TypeCtx) → Type (ℓ-suc ℓ-zero)
data Val : (Γ : TypeCtx) (A : SynType) → Type (ℓ-suc ℓ-zero)
data EvCtx : (Γ : TypeCtx) (A : SynType) (B : SynType) → Type (ℓ-suc ℓ-zero)
data Comp : (Γ : TypeCtx) (A : SynType) → Type (ℓ-suc ℓ-zero)

_[_]v : ∀ {Δ Γ S} → Val Γ S → Subst Δ Γ → Val Δ S
_[_]c : ∀ {Δ Γ S} → Comp Γ S → Subst Δ Γ → Comp Δ S
_[_]e : ∀ {Δ Γ S T} → EvCtx Γ S T → Subst Δ Γ → EvCtx Δ S T

var : ∀ {Γ A} → Val (A ∷ Γ) A
app : ∀ {S T} → Comp (S ∷ (S ⇀ T) ∷ []) T

-- Explicit substitutions roughly following https://arxiv.org/pdf/1809.08646.pdf
-- but with some changes
-- Idea: 
-- 1. Subst is a category
-- 2. Subst Γ (S ∷ Δ) ≅ Subst Γ Δ × Val Γ S
-- 3 Val - S , Comp - S, EvCtx - S T are Presheaves over Subst
-- 4. EvCtx Γ - = is a category enriched in Psh over Subst
-- 5. Comp Γ is a Psh(Subst)-enriched covariant presheaf over EvCtx Γ
data Subst where
  ids : ∀ {Γ} → Subst Γ Γ
  _∘s_ : ∀ {Γ Δ Θ} → Subst Δ Θ → Subst Γ Δ → Subst Γ Θ
  wk : ∀ {Γ S}  → Subst (S ∷ Γ) Γ
  _,s_ : ∀ {Γ Δ S} → Subst Γ Δ → Val Γ S → Subst Γ (S ∷ Δ)
  !s : ∀ {Γ} → Subst Γ []

  -- equations: Subst is a cat
  ∘IdL : ∀ {Γ} (γ : Subst Γ Γ) → ids ∘s γ ≡ γ
  ∘IdR : ∀ {Γ} (γ : Subst Γ Γ) → γ ∘s ids ≡ γ
  ∘Assoc : ∀ {Γ Δ Θ Z} (γ : Subst Δ Γ) (δ : Subst Θ Δ)(θ : Subst Z Θ) → γ ∘s (δ ∘s θ) ≡ (γ ∘s δ) ∘s θ

  -- [] is terminal
  []η : ∀ {Γ} → (γ : Subst Γ []) → γ ≡ !s

  -- universal property of S ∷ Γ
  -- β (other one is in Val), η and naturality 
  wkβ : ∀ {Γ Δ S} (δ : Subst Γ Δ)(V : Val Γ S) → wk ∘s (δ ,s V) ≡ δ
  ,sη : ∀ {Γ Δ S} → (δ : Subst Γ (S ∷ Δ)) → δ ≡ (wk ∘s δ) ,s (var [ δ ]v)

data Val where
  -- with explicit substitutions we only need the one variable, which we can combine with weakening
  var' : ∀ {Γ A} → Val (A ∷ Γ) A
  varβ : ∀ {Γ Δ S} → (δ : Subst Γ Δ) (V : Val Γ S) → var [ δ ,s V ]v ≡ V

  -- by making these function symbols we avoid more substitution equations
  zro : Val [] nat
  suc : Val ([ nat ]) nat

  lda : ∀ {Γ S T} -> (Comp (S ∷ Γ) T) -> Val Γ (S ⇀ T)
  fun-η : ∀ {Γ S T} → (V : Val Γ (S ⇀ T))
        → V ≡ lda (app [ (!s ,s (V [ wk ]v)) ,s var ]c)

  up : (S⊑T : TyPrec) -> Val [ ty-left S⊑T ] (ty-right S⊑T)

  -- values form a presheaf over substitutions
  _[_]v' : ∀ {Δ Γ S} → Val Γ S → Subst Δ Γ → Val Δ S
  compVId : ∀ {Γ S} → (V : Val Γ S) → V [ ids ]v ≡ V
  compV∘s : ∀ {Θ Γ Δ S} → (V : Val Δ S) (δ : Subst Γ Δ)(γ : Subst Θ Γ)
          → V [ δ ∘s γ ]v ≡ (V [ δ ]v) [ γ ]v

  isSetVal : ∀ {Γ S} → isSet (Val Γ S)

_[_]v = _[_]v'
var = var'

data EvCtx where
  ∙E : ∀ {Γ S} → EvCtx Γ S S
  _∘E_ : ∀ {Γ S T U} → EvCtx Γ T U → EvCtx Γ S T → EvCtx Γ S U
  _[_]e' : ∀ {Δ Γ S T} → EvCtx Γ S T → Subst Δ Γ → EvCtx Δ S T
  bind : ∀ {Γ S T} → Comp (S ∷ Γ) T → EvCtx Γ S T
  dn : ∀ {Γ} (S⊑T : TyPrec) → EvCtx Γ (ty-right S⊑T) (ty-left S⊑T)

  -- TODO: assoc, psh laws, η for bind
  -- ret-η : ∀ {Γ S T} → (E : EvCtx Γ S T) → E ≡ bind ∙E (wkE E [ ret (varV' (inr _)) ]e∙)
  isSetEvCtx : ∀ {Γ A B} → isSet (EvCtx Γ A B)

data Comp where
  err : ∀ {S} → Comp [] S
  ret : ∀ {S} → Comp [ S ] S
  app' : ∀ {S T} → Comp (S ∷ S ⇀ T ∷ []) T
  matchNat : ∀ {Γ S} → Comp Γ S → Comp (nat ∷ Γ) S → Comp (nat ∷ Γ) S

  _[_]∙ : ∀ {Γ S T} → EvCtx Γ S T → Comp Γ S → Comp Γ T
  compEId : ∀ {Γ S} → (M : Comp Γ S) → ∙E [ M ]∙ ≡ M
  compE∘E : ∀ {Γ S T U} → (M : Comp Γ S)(E : EvCtx Γ S T)(F : EvCtx Γ T U) → (F ∘E E) [ M ]∙ ≡ F [ E [ M ]∙ ]∙
  
  _[_]c' : ∀ {Γ Δ S} → Comp Δ S → Subst Γ Δ → Comp Γ S
  -- presheaf
  compId : ∀ {Γ S} → (M : Comp Γ S) → M [ ids ]c ≡ M
  comp∘s : ∀ {Θ Γ Δ S} → (M : Comp Δ S) (δ : Subst Γ Δ)(γ : Subst Θ Γ)
         → M [ δ ∘s γ ]c ≡ (M [ δ ]c) [ γ ]c

  -- Interchange law
  compES : ∀ {Δ Γ S T} (E : EvCtx Γ S T) (M : Comp Γ S) → (γ : Subst Δ Γ) → (E [ M ]∙) [ γ ]c ≡ (E [ γ ]e) [ M [ γ ]c ]∙

  -- TODO: strictness, βη for nat, β for app, β for ret
  -- Strictness of all evaluation contexts
  -- strictness : ∀ {Γ S T} → (E : EvCtx Γ S T) → E [ err ]e∙ ≡ err
  -- ret-β : ∀ {Γ S T} → (V : Val Γ S) → (K : Comp (cons Γ S) T) → bind (ret V) K ≡ K [ V ]c1
  -- fun-β : ∀ {Γ S T} → (M : Comp (cons Γ S) T) → (V : Val Γ S) → app (lda M) V ≡ M [ V ]c1
  -- nat-βz : ∀ {Γ S} → (Kz : Comp Γ S) (Ks : Comp (nat ∷ Γ) S) → matchNat zro Kz Ks ≡ Kz
  -- nat-βs : ∀ {Γ S} → (V : Val Γ nat) (Kz : Comp Γ S) (Ks : Comp (cons Γ nat) S) → matchNat (suc V) Kz Ks ≡ Ks [ V ]c1
  -- η for matchNat
  -- some notation would probably help here...
  -- nat-η : ∀ {Γ S} → (M : Comp (cons Γ nat) S)
  --         → M ≡
  --           (matchNat (varV' (inr _))
  --                     (M [ cons-subst (Val (cons Γ nat)) (λ x → varV' (inl x)) zro ]c)
  --                     (M [ cons-subst ((Val (cons (cons Γ nat) nat))) (λ x → varV' (inl (inl x))) (suc (varV' (inr _))) ]c))
  -- this allows cong wrt plugging be admissible
  -- ret-η : ∀ {Γ S T} → (E : EvCtx Γ S T) (M : Comp Γ S) → E [ M ]e∙ ≡ bind M (wkE E [ ret (varV' (inr _)) ]e∙)
  isSetComp : ∀ {Γ A} → isSet (Comp Γ A)
app = app'
_[_]c = _[_]c'
_[_]e = _[_]e'

data ValPrec : (Γ : PrecCtx) (A : TyPrec) (V : Val (ctx-endpt l Γ) (ty-endpt l A)) (V' : Val (ctx-endpt r Γ) (ty-endpt r A)) → Type (ℓ-suc ℓ-zero)
data CompPrec : (Γ : PrecCtx) (A : TyPrec) (M : Comp (ctx-endpt l Γ) (ty-endpt l A)) (M' : Comp (ctx-endpt r Γ) (ty-endpt r A)) → Type (ℓ-suc ℓ-zero)
data EvCtxPrec : (Γ : PrecCtx) (A : TyPrec) (B : TyPrec) (E : EvCtx (ctx-endpt l Γ) (ty-endpt l A) (ty-endpt l B)) (E' : EvCtx (ctx-endpt r Γ) (ty-endpt r A) (ty-endpt r B)) → Type (ℓ-suc ℓ-zero)

data ValPrec where
data CompPrec where
data EvCtxPrec where


