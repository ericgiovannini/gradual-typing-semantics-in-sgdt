{-# OPTIONS --cubical #-}
 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}
module Syntax.Logic  where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Cubical.Data.Prod hiding (map)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List hiding (nil)
open import Cubical.Data.Empty renaming (rec to exFalso)

open import Syntax.Types
open import Syntax.Terms

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T U R' S' T' U' : Ty
   B B' C C' D D' : Γ ⊑ctx Γ'
   b b' c c' d d' : S ⊑ S'
   γ γ' γ'' : Subst Δ Γ
   δ δ' δ'' : Subst Θ Δ
   V V' V'' : Val Γ S
   M M' M'' N N' N'' : Comp Γ S
   E E' E'' F F' F'' : EvCtx Γ S T

open TyPrec
open CtxPrec

data Subst⊑ : (C : Δ ⊑ctx Δ') (D : Γ ⊑ctx Γ') (γ : Subst Δ Γ) (γ' : Subst Δ' Γ') → Type
data Val⊑ : (C : Γ ⊑ctx Γ') (c : S ⊑ S') (V : Val Γ S) (V' : Val Γ' S') → Type
data EvCtx⊑ : (C : Γ ⊑ctx Γ') (c : S ⊑ S') (d : T ⊑ T') (E : EvCtx Γ S T) (E' : EvCtx Γ' S' T') → Type
data Comp⊑ : (C : Γ ⊑ctx Γ') (c : S ⊑ S') (M : Comp Γ S) (M' : Comp Γ' S') → Type

-- Three parts:
-- 1. Internalization to Preorders
--    - everything is monotone (including the actions of substitution/plugging)
--    - transitivity (reflexivity is admissible)
--    - propositionally truncate
-- 2. Errors are bottom
-- 3. Casts are LUBs/GLBs and retractions
data Subst⊑ where
  !s : Subst⊑ C [] !s !s
  _,s_ : Subst⊑ C D γ γ' → Val⊑ C c V V' → Subst⊑ C (c ∷ D) (γ ,s V) (γ' ,s V')
  _∘s_ : Subst⊑ C D γ γ' → Subst⊑ B C δ δ' → Subst⊑ B D (γ ∘s δ) (γ' ∘s δ')
  _ids_ : Subst⊑ C C ids ids
  -- in principle we could add βη equations instead but truncating is simpler
  isProp⊑ : isProp (Subst⊑ C D γ γ')

data Val⊑ where
  _[_]v : Val⊑ C c V V' → Subst⊑ B C γ γ' → Val⊑ B c (V [ γ ]v) (V' [ γ' ]v)
  var : Val⊑ (c ∷ C) c var var
  zro : Val⊑ [] nat zro zro
  suc : Val⊑ (nat ∷ []) nat suc suc

  up-L : ∀ S⊑T → Val⊑ ((ty-prec S⊑T) ∷ []) (refl-⊑ (ty-right S⊑T)) (up S⊑T) var
  up-R : ∀ S⊑T → Val⊑ ((refl-⊑ (ty-left S⊑T)) ∷ []) (ty-prec S⊑T) var (up S⊑T)

  trans : Val⊑ C c V V' → Val⊑ D d V' V'' → Val⊑ (trans-⊑ctx C D) (trans-⊑ c d) V V''
  isProp⊑ : isProp (Val⊑ C c V V')

data EvCtx⊑ where
  ∙E : EvCtx⊑ C c c ∙E ∙E
  _∘E_ : EvCtx⊑ C c d E E' → EvCtx⊑ C b c F F' → EvCtx⊑ C b d (E ∘E F) (E' ∘E F')
  _[_]e : EvCtx⊑ C c d E E' → Subst⊑ B C γ γ' → EvCtx⊑  B c d (E [ γ ]e) (E' [ γ' ]e)
  -- bind : Comp⊑ (c ∷ C) d M M' → EvCtx⊑ C c d ? ?

  dn-L : ∀ S⊑T → EvCtx⊑ [] (refl-⊑ (ty-right S⊑T)) (ty-prec S⊑T) (dn S⊑T) ∙E
  dn-R : ∀ S⊑T → EvCtx⊑ [] (ty-prec S⊑T) (refl-⊑ (ty-left S⊑T)) ∙E (dn S⊑T)
  retractionR : ∀ S⊑T → EvCtx⊑ [] (refl-⊑ (ty-right S⊑T)) (refl-⊑ (ty-right S⊑T)) ∙E (upE S⊑T ∘E dn S⊑T)

  trans : EvCtx⊑ C b c E E' → EvCtx⊑ C' b' c' E' E'' → EvCtx⊑ (trans-⊑ctx C C') (trans-⊑ b b') (trans-⊑ c c') E E''
  isProp⊑ : isProp (EvCtx⊑ C c d E E')

data Comp⊑ where
  _[_]∙ : EvCtx⊑ C c d E E' → Comp⊑ C c M M' → Comp⊑ C d (E [ M ]∙) (E' [ M' ]∙)
  _[_]c : Comp⊑ C c M M' → Subst⊑ D C γ γ' → Comp⊑ D c (M [ γ ]c) (M' [ γ' ]c)
  ret : Comp⊑ (c ∷ []) c ret ret
  app : Comp⊑ (c ∷ c ⇀ d ∷ []) d app app
  matchNat : ∀ {Kz Kz' Ks Ks'} → Comp⊑ C c Kz Kz' → Comp⊑ (nat ∷ C) c Ks Ks' → Comp⊑ (nat ∷ C) c (matchNat Kz Ks) (matchNat Kz' Ks')

  err⊥ : Comp⊑ (refl-⊑ctx Γ) (refl-⊑ S) err' M

  trans : Comp⊑ C c M M' → Comp⊑ D d M' M'' → Comp⊑ (trans-⊑ctx C D) (trans-⊑ c d) M M''
  isProp⊑ : isProp (Comp⊑ C c M M')

Subst⊑-homo : (γ γ' : Subst Δ Γ) → Type _
Subst⊑-homo = Subst⊑ (refl-⊑ctx _) (refl-⊑ctx _)

Val⊑-homo : (V V' : Val Γ S) → Type _
Val⊑-homo = Val⊑ (refl-⊑ctx _) (refl-⊑ _)

Comp⊑-homo : (M M' : Comp Γ S) → Type _
Comp⊑-homo = Comp⊑ (refl-⊑ctx _) (refl-⊑ _)

EvCtx⊑-homo : (E E' : EvCtx Γ S T) → Type _
EvCtx⊑-homo = EvCtx⊑ (refl-⊑ctx _) (refl-⊑ _) (refl-⊑ _)

_≈s_ : ∀ (γ γ' : Subst Δ Γ) → Type
γ ≈s γ' = Subst⊑-homo γ γ' × Subst⊑-homo γ' γ

_≈v_ : (V V' : Val Γ S) → Type _
V ≈v V' = Val⊑-homo V V' × Val⊑-homo V' V

_≈m_ : (M M' : Comp Γ S) → Type _
M ≈m M' = Comp⊑-homo M M' × Comp⊑-homo M' M

_≈e_ : (E E' : EvCtx Γ S T) → Type _
E ≈e E' = EvCtx⊑-homo E E' × EvCtx⊑-homo E' E

up-monotone : (S⊑S' : S ⊑ S')(S⊑T : S ⊑ T)(S'⊑T' : S' ⊑ T') (T⊑T' : T ⊑ T')
            → Val⊑ (S⊑T ∷ []) S'⊑T' (up (mkTyPrec S⊑S')) (up (mkTyPrec T⊑T'))
up-monotone {S}{S'}{T}{T'} S⊑S' S⊑T S'⊑T' T⊑T' =
  transport (λ i → Val⊑ (split-dom (~ i) ∷ []) (split-cod (~ i)) (substId {V = up (mkTyPrec S⊑S')} i) (varβ {δ = !s}{V = (up (mkTyPrec T⊑T'))} i))
  (trans (up-L (mkTyPrec (S⊑S'))) (var {C = []})
  [ transport (λ i → Subst⊑ (trans-⊑ S⊑T (refl-⊑ T) ∷ []) (swap-middle i) (ids1-expand (~ i)) (!s ,s up (mkTyPrec T⊑T')))
    (!s ,s trans ((var {C = []})) (up-R (mkTyPrec T⊑T'))) ]v)
  where
    split-cod : S'⊑T' ≡ trans-⊑ (refl-⊑ _) S'⊑T'
    split-cod = isPropTy⊑ _ _

    split-dom : S⊑T ≡ trans-⊑ S⊑T (refl-⊑ _)
    split-dom = isPropTy⊑ _ _

    swap-middle : Path ((S ∷ []) ⊑ctx (T' ∷ [])) (trans-⊑ S⊑T T⊑T' ∷ []) (trans-⊑ S⊑S' S'⊑T' ∷ [])
    swap-middle i = (isPropTy⊑ (trans-⊑ S⊑T T⊑T') (trans-⊑ S⊑S' S'⊑T') i) ∷ []

-- TODO: show down is monotone
-- EXERCISE
⇀-up-uniqueness : ∀ S⊑S' T⊑T' →
  up (S⊑S' ⇀TP T⊑T')
  ≈v lda (bind' (dn' S⊑S' (ret' var)) -- downcast the input
         (bind' (app' var2 var) -- apply the original function
         (ret' (up' T⊑T' var))) ) -- upcast the output
⇀-up-uniqueness S⊑S' T⊑T' =
  ( {!!}
  , {!!})

⇀-dn-uniqueness : ∀ S⊑S' T⊑T' →
  dn (S⊑S' ⇀TP T⊑T')
  ≈e bind (ret' (lda (dn' T⊑T' (app' var1 (up' S⊑S' var)))))
⇀-dn-uniqueness = {!!}
