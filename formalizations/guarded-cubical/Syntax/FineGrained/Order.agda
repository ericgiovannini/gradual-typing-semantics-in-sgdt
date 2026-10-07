module Syntax.FineGrained.Order where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Data.List

open import Syntax.Types
open import Syntax.FineGrained.Terms

open TyPrec
open CtxPrec

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T U R' S' T' U' : Ty
   B B' C C' D D' : Γ ⊑ctx Γ'
   b b' c c' d d' : S ⊑ S'


private
  variable
    γ γ' γ'' : Subst Δ Γ
    δ δ' δ'' : Subst Θ Δ
    θ θ' θ'' : Subst Z Θ

    V V' V'' : Val Γ S
    M M' M'' N N' : Comp Γ S
    E E' E'' F F' : EvCtx Γ S T

data Subst⊑ : (C : Δ ⊑ctx Δ') (D : Γ ⊑ctx Γ') (γ : Subst Δ Γ) (γ' : Subst Δ' Γ') → Type

data Val⊑ : (C : Γ ⊑ctx Γ') (c : S ⊑ S') (V : Val Γ S) (V' : Val Γ' S') → Type

data EvCtx⊑ : (C : Γ ⊑ctx Γ') (c : S ⊑ S') (d : T ⊑ T') (E : EvCtx Γ S T) (E' : EvCtx Γ' S' T') → Type

data Comp⊑ : (C : Γ ⊑ctx Γ') (c : S ⊑ S') (M : Comp Γ S) (M' : Comp Γ' S') → Type


data Subst⊑ where
  reflexive : Subst⊑ (refl-⊑ctx Δ) (refl-⊑ctx Γ) γ γ
  !s : Subst⊑ C [] !s !s
  _,s_ : Subst⊑ C D γ γ' → Val⊑ C c V V' → Subst⊑ C (c ∷ D) (γ ,s V) (γ' ,s V')
  _∘s_ : Subst⊑ C D γ γ' → Subst⊑ B C δ δ' → Subst⊑ B D (γ ∘s δ) (γ' ∘s δ')
  _ids_ : Subst⊑ C C ids ids
  wk : Subst⊑ (c ∷ C) C wk wk

data Val⊑ where
  reflexive : Val⊑ (refl-⊑ctx Γ) refl-⊑ V V
  _[_]v : Val⊑ C c V V' → Subst⊑ B C γ γ' → Val⊑ B c (V [ γ ]v) (V' [ γ' ]v)
  var : Val⊑ (c ∷ C) c var var
  zro : Val⊑ [] refl-⊑ zro zro
  suc : Val⊑ (refl-⊑ ∷ []) refl-⊑ suc suc
  -- lda may be admissible
  lda : ∀ {M M'} -> Comp⊑ (c ∷ C) d M M' → Val⊑ C (c ⇀ d) (lda M) (lda M')

data EvCtx⊑ where
  reflexive : EvCtx⊑ (refl-⊑ctx Γ) refl-⊑ refl-⊑ E E
  ∙E : EvCtx⊑ C c c ∙E ∙E
  _∘E_ : EvCtx⊑ C c d E E' → EvCtx⊑ C b c F F' → EvCtx⊑ C b d (E ∘E F) (E' ∘E F')
  _[_]e : EvCtx⊑ C c d E E' → Subst⊑ B C γ γ' → EvCtx⊑  B c d (E [ γ ]e) (E' [ γ' ]e)
  bind : Comp⊑ (c ∷ C) d M M' → EvCtx⊑ C c d (bind M) (bind M')

data Comp⊑ where
  reflexive : Comp⊑ (refl-⊑ctx Γ) refl-⊑ M M
  _[_]∙ : EvCtx⊑ C c d E E' → Comp⊑ C c M M' → Comp⊑ C d (E [ M ]∙) (E' [ M' ]∙)
  _[_]c : Comp⊑ C c M M' → Subst⊑ D C γ γ' → Comp⊑ D c (M [ γ ]c) (M' [ γ' ]c)
  err : Comp⊑ [] c err err
  ret : Comp⊑ (c ∷ []) c ret ret
  app : Comp⊑ (c ∷ c ⇀ d ∷ []) d app app
  matchNat : ∀ {Kz Kz' Ks Ks'} →
    Comp⊑ C c Kz Kz' →
    Comp⊑ (refl-⊑ ∷ C) c Ks Ks' →
    Comp⊑ (refl-⊑ ∷ C) c (matchNat Kz Ks) (matchNat Kz' Ks')

  err⊥ : Comp⊑ (refl-⊑ctx Γ) refl-⊑ err' M
  -- Equivalent type precision derivations give the same term precision.
  EquivTyPrec : Comp⊑ C c M M' → c ≈ c' → Comp⊑ C c' M M'
  -- The four cast rules, stated with composite derivations so that no
  -- transitivity of term precision is needed (Figure "Term Precision
  -- Rules" of the paper).
  UpL : Comp⊑ C (trans-⊑ c d) M M' → Comp⊑ C d (upC (mkTyPrec c) M) M'
  UpR : Comp⊑ C c M M' → Comp⊑ C (trans-⊑ c d) M (upC (mkTyPrec d) M')
  DnL : Comp⊑ C d M M' → Comp⊑ C (trans-⊑ c d) (dnC (mkTyPrec c) M) M'
  DnR : Comp⊑ C (trans-⊑ c d) M M' → Comp⊑ C c M (dnC (mkTyPrec d) M')
