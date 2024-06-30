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

  -- TODO: UpL/UpR laws
-- -- Cast rules are admissible

  -- up x <= x
  up-L : ∀ R R' (c : R ⊑ R') → Val⊑ (c ∷ []) refl-⊑ (up (mkTyPrec c)) var

-- -- if x <= y then δl x <= e y
-- up-R : ∀ R R' (c : R ⊑ R') → Val⊑ ((refl-⊑ R) ∷ []) c (δl-e c) (emb c)

-- dn-L : ∀ R R' (c : R ⊑ R') → EvCtx⊑ [] (refl-⊑ R') c (proj c) (δr-p c)
-- dn-R : ∀ R R' (c : R ⊑ R') → EvCtx⊑ [] c (refl-⊑ R) (δl-p c) (proj c)

data EvCtx⊑ where
  reflexive : EvCtx⊑ (refl-⊑ctx Γ) refl-⊑ refl-⊑ E E
  ∙E : EvCtx⊑ C c c ∙E ∙E
  _∘E_ : EvCtx⊑ C c d E E' → EvCtx⊑ C b c F F' → EvCtx⊑ C b d (E ∘E F) (E' ∘E F')
  _[_]e : EvCtx⊑ C c d E E' → Subst⊑ B C γ γ' → EvCtx⊑  B c d (E [ γ ]e) (E' [ γ' ]e)
  bind : Comp⊑ (c ∷ C) d M M' → EvCtx⊑ C c d (bind M) (bind M')

  -- TODO: DnL/DnR laws
  -- The other direction of retraction is admissible
  retraction : ∀ S⊑T → EvCtx⊑ [] refl-⊑ refl-⊑
    ∙E
    (vToE (up S⊑T) ∘E dn S⊑T)

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
