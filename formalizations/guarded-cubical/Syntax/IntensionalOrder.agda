{-# OPTIONS --lossy-unification #-}

{-# OPTIONS --allow-unsolved-metas #-}


module Syntax.IntensionalOrder where

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
open import Syntax.Perturbation
open import Syntax.IntensionalTerms

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
  reflexive-subst : Subst⊑ (refl-⊑ctx Δ) (refl-⊑ctx Γ) γ γ
  !s : Subst⊑ C [] !s !s
  _,s_ : Subst⊑ C D γ γ' → Val⊑ C c V V' → Subst⊑ C (c ∷ D) (γ ,s V) (γ' ,s V')
  _∘s_ : Subst⊑ C D γ γ' → Subst⊑ B C δ δ' → Subst⊑ B D (γ ∘s δ) (γ' ∘s δ')
  _ids_ : Subst⊑ C C ids ids
  wk : Subst⊑ (c ∷ C) C wk wk
  -- in principle we could add βη equations instead but truncating is simpler
  -- isProp⊑ : isProp (Subst⊑ C D γ γ')
  -- hetTrans : ∀ {B B'} -> Subst⊑ C D γ γ' → Subst⊑ C' D' γ' γ'' → Subst⊑ B B' γ γ''


data Val⊑ where
  reflexive-val : Val⊑ (refl-⊑ctx Γ) (refl-⊑ S) V V
  -- reflexive : {C : Γ ⊑ctx Γ} {c : S ⊑ S} -> Val⊑ C c V V
  _[_]v : Val⊑ C c V V' → Subst⊑ B C γ γ' → Val⊑ B c (V [ γ ]v) (V' [ γ' ]v)
  var : Val⊑ (c ∷ C) c var var
  zro : Val⊑ [] nat zro zro
  suc : Val⊑ (nat ∷ []) nat suc suc

  lda : ∀ {M M'} -> Comp⊑ (c ∷ C) d M M' → Val⊑ C (c ⇀ d) (lda M) (lda M') -- needed?

  injNatUpL :  Val⊑ [] inj-nat V V' →
               Val⊑ [] dyn (injectN [ !s ,s V ]v) V'
  injNatUpL' : Val⊑ (inj-nat ∷ []) dyn injectN var

  injNatUpR : Val⊑ [] nat V V' ->
              Val⊑ [] inj-nat V (injectN [ !s ,s V' ]v)

  injNatUpR' : Val⊑ (nat ∷ []) inj-nat var injectN

  injArrUpL : Val⊑ [] (inj-arr c ) V V' ->
              Val⊑ [] dyn (injectArr ∘V' (emb c ∘V V)) V'
  injArrUpL' : Val⊑ ((inj-arr c) ∷ []) dyn (injectArr ∘V' emb c) var
  -- TODO injArrUpL
  
  injArrUpR : Val⊑ [] (dyn ⇀ dyn) V V' ->
              Val⊑ [] (inj-arr (refl-⊑ _)) V (injectArr [ !s ,s V' ]v)
  injArrUpR' : Val⊑ ((dyn ⇀ dyn) ∷ []) (inj-arr (refl-⊑ _)) var injectArr
             -- ((injectArr {S = S} (V' [ wk ]v)) [ {!injectArr {S = S} (V' [ wk ]v)!} ]v) -- (injectArr (V' [ wk ]v) [ !s ,s V ]v)

  mapDyn-nat : ∀ {Vn Vn' Vf} →
    Val⊑ (nat ∷ []) nat Vn Vn' →
   -- Val⊑ (dyn ⇀ dyn ∷ []) (dyn ⇀ dyn) Vf Vf' →
    Val⊑ (inj-nat ∷ []) inj-nat Vn (mapDyn Vn' Vf)

  -- Vs : Val [ S ] S 
  -- Vf : Val [ dyn ⇀ dyn ] (dyn ⇀ dyn)
  mapDyn-arr : ∀ {Vn Vs Vf} →
    Val⊑ (c ∷ []) c Vs Vf →
    Val⊑ (inj-arr c ∷ []) (inj-arr c) Vs (mapDyn Vn Vf)


  -- isProp⊑ : isProp (Val⊑ C c V V')

  -- We make this an arbitrary E and e rather than
  -- Val⊑ (trans-⊑ctx C D) (trans-⊑ c d) V V'
  -- in order to avoid the "green slime" issue when pattern matching
  -- hetTrans : ∀ {E e} -> Val⊑ C c V V' → Val⊑ D d V' V'' → Val⊑ E e V V''


data EvCtx⊑ where
  reflexive-eval : EvCtx⊑ (refl-⊑ctx Γ) (refl-⊑ S) (refl-⊑ S) E E
  ∙E : EvCtx⊑ C c c ∙E ∙E
  _∘E_ : EvCtx⊑ C c d E E' → EvCtx⊑ C b c F F' → EvCtx⊑ C b d (E ∘E F) (E' ∘E F')
  _[_]e : EvCtx⊑ C c d E E' → Subst⊑ B C γ γ' → EvCtx⊑  B c d (E [ γ ]e) (E' [ γ' ]e)
  bind : Comp⊑ (c ∷ C) d M M' → EvCtx⊑ C c d (bind M) (bind M')

  
  -- retractionR : ∀ S⊑T → EvCtx⊑ [] (refl-⊑ (ty-right S⊑T)) (refl-⊑ (ty-right S⊑T))
  --   (vToE (δr S⊑T) ∘E δr S⊑T)
  --   (vToE (up S⊑T) ∘E dn S⊑T)

  -- retraction : ∀ S⊑T → EvCtx⊑ [] (refl-⊑ (ty-left S⊑T)) (refl-⊑ (ty-left S⊑T))
  --   ((dn S⊑T) ∘E vToE (up S⊑T))
  --   ((δl S⊑T) ∘E vToE (δl S⊑T))
  -- Opposite order is admissible

  {- hetTrans : EvCtx⊑ C b c E E' → EvCtx⊑ C' b' c' E' E'' →
    EvCtx⊑ (trans-⊑ctx C C') (trans-⊑ b b') (trans-⊑ c c') E E''
  isProp⊑ : isProp (EvCtx⊑ C c d E E') -}

data Comp⊑ where
  reflexive-comp : Comp⊑ (refl-⊑ctx Γ) (refl-⊑ S) M M
  _[_]∙ : EvCtx⊑ C c d E E' → Comp⊑ C c M M' → Comp⊑ C d (E [ M ]∙) (E' [ M' ]∙)
  _[_]c : Comp⊑ C c M M' → Subst⊑ D C γ γ' → Comp⊑ D c (M [ γ ]c) (M' [ γ' ]c)
  err : Comp⊑ [] c err err
  ret : Comp⊑ (c ∷ []) c ret ret
  app : Comp⊑ (c ∷ c ⇀ d ∷ []) d app app
  matchNat : ∀ {Kz Kz' Ks Ks'} →
    Comp⊑ C c Kz Kz' →
    Comp⊑ (nat ∷ C) c Ks Ks' →
    Comp⊑ (nat ∷ C) c (matchNat Kz Ks) (matchNat Kz' Ks')

  err⊥ : Comp⊑ (refl-⊑ctx Γ) (refl-⊑ S) err' M

{-   hetTrans : Comp⊑ C c M M' → Comp⊑ D d M' M'' →
    Comp⊑ (trans-⊑ctx C D) (trans-⊑ c d) M M''
  isProp⊑ : isProp (Comp⊑ C c M M') -}

vToE⊑ : Val⊑ (c ∷ []) d V V' → EvCtx⊑ [] c d (vToE V) (vToE V')
vToE⊑ V⊑V' = bind (ret [ !s ,s V⊑V' ]c)

lemma : ∀ (c : R ⊑ R') → (ret [ !s ,s emb c ]c) [ !s ,s var ]c ≡ (bind (ret [ !s ,s emb c ]c) [ !s ]e) [ ret [ !s ,s var ]c ]∙
lemma nat = {!!}
lemma dyn = {!!}
lemma (c ⇀ c₁) = {!!}
lemma inj-nat = {!!}
lemma (inj-arr c) = {!!}

-- Cast rules are admissible

-- if x <= y then e x <= δr y
up-L : ∀ R R' (c : R ⊑ R') → Val⊑ (c ∷ []) (refl-⊑ R') (emb c) (δr-e c)

-- if x <= y then δl x <= e y
up-R : ∀ R R' (c : R ⊑ R') → Val⊑ ((refl-⊑ R) ∷ []) c (δl-e c) (emb c)

dn-L : ∀ R R' (c : R ⊑ R') → EvCtx⊑ [] (refl-⊑ R') c (proj c) (δr-p c)
dn-R : ∀ R R' (c : R ⊑ R') → EvCtx⊑ [] c (refl-⊑ R) (δl-p c) (proj c)


up-L .nat .nat nat = var
up-L .dyn .dyn dyn = var
up-L .(_ ⇀ _) .(_ ⇀ _) (c ⇀ d) = lda (bind (bind ((bind (ret [ !s ,s up-L _ _ d ]c) [ !s ]e) [ ret [ !s ,s var ]c ]∙) [ (app [ wk ∘s wk ∘s wk ,s (var [ wk ∘s wk ]v) ,s var ]c) ]∙) [ (dn-L _ _ c [ !s ]e) [ ret [ !s ,s var ]c ]∙ ]∙)
up-L .nat .dyn inj-nat = injNatUpL'
up-L R .dyn (inj-arr c) = {!!}

up-R .nat .nat nat = var
up-R .dyn .dyn dyn = var
up-R .(_ ⇀ _) .(_ ⇀ _) (c ⇀ d) = lda (bind (bind ((bind (ret [ !s ,s up-R _ _ d ]c) [ !s ]e) [ ret [ !s ,s var ]c ]∙) [ app [ wk ∘s wk ∘s wk ,s (var [ wk ∘s wk ]v) ,s var ]c ]∙) [ (dn-R _ _ c [ !s ]e) [ ret [ !s ,s var ]c ]∙ ]∙)
up-R .nat .dyn inj-nat = injNatUpR'
up-R R .dyn (inj-arr c) = {!!}

dn-L .nat .nat nat = ∙E
dn-L .dyn .dyn dyn = ∙E
dn-L .(_ ⇀ _) .(_ ⇀ _) (c ⇀ d) =
  bind (ret [ !s ,s lda (bind (bind ((dn-L _ _ d [ !s ]e) [ ret [ !s ,s var ]c ]∙) [ app [ wk ∘s wk ∘s wk ,s (var [ wk ∘s wk ]v) ,s var ]c ]∙) [
    transport (λ i → Comp⊑ (c ∷ ((refl-⊑ _ ⇀ refl-⊑ _) ∷ [])) (refl-⊑ _) (lemma c i) ((vToE (Pertᴱ→Val (δr-e-pert c)) [ !s ]e) [ ret' var ]∙))
      ((bind (ret [ !s ,s up-L {!!} {!!} c ]c) [ !s ]e) [ ret [ !s ,s var ]c  ]∙) ]∙) ]c) 
dn-L .nat .dyn inj-nat = {!!}
-- Goal: EvCtx⊑ [] dyn inj-nat (bind (matchDyn (ret' var) (err [ wk ]c))) (δr-p inj-nat)
-- Have: Val⊑ (nat ∷ []) nat Vn Vn' → Val⊑ (inj-nat ∷ []) inj-nat Vn (mapDyn Vn' Vf)
dn-L R .dyn (inj-arr c) = {!!}

dn-R .nat .nat nat = ∙E
dn-R .dyn .dyn dyn = ∙E
dn-R .(_ ⇀ _) .(_ ⇀ _) (c ⇀ d) = bind (ret [ !s ,s (lda (bind {!bind ? [ ? ]!} [ {!!} ]∙)) ]c)
dn-R .nat .dyn inj-nat = {!!}
dn-R R .dyn (inj-arr c) = {!!}



-- Key lemmas about pushing and pulling perturbations across type precision.
-- If S ⊑ T, and if δs is a perturbation on S, then pushing it to a perturbation on T
-- produces a related perturbation.
-- Dually for pulling.

push-lemma-e : ∀ (c : S ⊑ T) δs ->
  Val⊑ (c ∷ []) c (Pertᴱ→Val δs) (Pertᴱ→Val (PushE c δs))
push-lemma-p : ∀ (c : S ⊑ T) δs ->
  EvCtx⊑ [] c c (Pertᴾ→EC δs) (Pertᴾ→EC (PushP c δs))

pull-lemma-e : ∀ (c : S ⊑ T) δt ->
  Val⊑ (c ∷ []) c (Pertᴱ→Val (PullE c δt)) (Pertᴱ→Val δt)
pull-lemma-p : ∀ (c : S ⊑ T) δt ->
  EvCtx⊑ [] c c (Pertᴾ→EC (PullP c δt)) (Pertᴾ→EC δt)

push-lemma-e nat id = var
push-lemma-e dyn id = var
push-lemma-e dyn (PertD δn δf) = reflexive-val
push-lemma-e (ci ⇀ co) id = var
push-lemma-e (ci ⇀ co) (δi ⇀ δo) =
  lda (bind (bind ((bind (ret [ !s ,s push-lemma-e co δo ]c) [ !s ]e) [ ret [ !s ,s var ]c ]∙) [ {!!} ]∙) [ ({!!} [ !s ]e) [ ret [ !s ,s var ]c ]∙ ]∙)
push-lemma-e inj-nat id = var
push-lemma-e (inj-arr c) id = var
push-lemma-e (inj-arr c) (δi ⇀ δo) = {!!}

push-lemma-p = {!!}


pull-lemma-e c id = var
pull-lemma-e (ci ⇀ co) (δi ⇀ δo) = {!!}
pull-lemma-e dyn (PertD δn δf) = reflexive-val
pull-lemma-e inj-nat (PertD δn δf) = mapDyn-nat reflexive-val
pull-lemma-e (inj-arr c) (PertD δn δf) = mapDyn-arr (pull-lemma-e c δf)

pull-lemma-p = {!!}



mapDyn-nat' : ∀ {Vn Vn' Vf} →
    Val⊑ (nat ∷ []) nat Vn Vn' →
   -- Val⊑ (dyn ⇀ dyn ∷ []) (dyn ⇀ dyn) Vf Vf' →
    Val⊑ (inj-nat ∷ []) inj-nat Vn (mapDyn Vn' Vf)
mapDyn-nat' H = {!!}


-- Admissibility of retraction

-- Given: M ⊑ M : A
-- By UpR, δl-e M ⊑ up M
-- By DnR, δl-p (δl-e M) ⊑ dn (up M)

-- Given : M ⊑ M : B
-- By DnL, dn M ⊑ δr-p M
-- By UpL, up (dn M) ⊑ δr-e (δr-e M)
