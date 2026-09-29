{-# OPTIONS --allow-unsolved-metas #-}

module Syntax.FineGrained.Operational  where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty

open import Cubical.Relation.Nullary

open import Syntax.Types
-- open import Syntax.FineGrained.Terms
open import Syntax.Surface

open TyPrec'

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T U R' S' T' U' : Ty
   b b' c c' d d' : S ⊑' S'


data Step : Type where
  0S : Step
  1S : Step

Step→ℕ : Step → ℕ
Step→ℕ 0S = 0
Step→ℕ 1S = 1

data Tag : Type where
  tagNat   : Tag
  tagArr   : Tag
  tagTimes : Tag

tag→c : Tag → TyPrec'
tag→c tagNat = inj-nat-p
tag→c tagArr = inj-arr-p refl-⊑'
tag→c tagTimes = inj-times-p refl-⊑'

tag→LHS : Tag → Ty
tag→LHS tagNat = nat
tag→LHS tagArr = dyn ⇀ dyn
tag→LHS tagTimes = dyn × dyn

tag→S⊑dyn : (t : Tag) → (tag→LHS t) ⊑' dyn
tag→S⊑dyn tagNat = inj-nat
tag→S⊑dyn tagArr = inj-arr refl-⊑'
tag→S⊑dyn tagTimes = (inj-times refl-⊑')

tagMatches : Tag → Tag → Type
tagMatches tagNat tagNat = ⊤
tagMatches tagArr tagArr = ⊤
tagMatches tagTimes tagTimes = ⊤
tagMatches _ _ = ⊥

tagMismatch : Tag → Tag → Type
tagMismatch t₁ t₂ = ¬ (tagMatches t₁ t₂)

tag→numSteps : Tag → Step
tag→numSteps tagNat = 0S
tag→numSteps tagArr = 1S
tag→numSteps tagTimes = 0S




-- Small-step semantics

data _→[_]_ : {T : Ty} → Tm Γ T → Step → Tm Γ T → Type where

  -- β rules for nat, functions, and products
  --------------------------------------------
  matchNat-zro : ∀ {Γ S} {Kz : Tm Γ S} {Ks : Tm (nat ∷ Γ) S}
    → (matchNat zro Kz Ks) →[ 0S ] Kz

  matchNat-suc : ∀ {Γ S} {Kz : Tm Γ S} {Ks : Tm (nat ∷ Γ) S}
    → {V : Value Γ nat}
    → (matchNat (suc ⟨ V ⟩v) Kz Ks) →[ 0S ] (Ks [ ⟨ V ⟩v ]tm)

  λ-β : ∀ {Γ S T} {M : Tm (S ∷ Γ) T} {V : Value Γ S}
    → (app (lda M) ⟨ V ⟩v) →[ 0S ] (M [ ⟨ V ⟩v ]tm)

  ×-β : ∀ {Γ R S T} {M : Tm (S ∷ T ∷ Γ) R} {V₁ : Value Γ S} {V₂ : Value Γ T}
--    → isValue V₁
--    → isValue V₂
    → (letTimes (pair ⟨ V₁ ⟩v  ⟨ V₂ ⟩v) M) →[ 0S ]
      ((M [ wk ⟨ V₁ ⟩v ]tm) [ ⟨ V₂ ⟩v ]tm)


  -- "Functoriality" of inj-arr and inj-times
  ---------------------------------------------

  inj-arr-comp-up : ∀ {Γ} {c : S ⊑' (dyn ⇀ dyn)} {M : Tm Γ S}
    → (up (inj-arr-p c) M) →[ 0S ] (up (inj-arr-p refl-⊑') (up (mkTyPrec' c) M))

  inj-arr-comp-down : ∀ {Γ} {c : S ⊑' (dyn ⇀ dyn)} {M : Tm Γ dyn}
    → (dn (inj-arr-p c) M) →[ 0S ] dn (mkTyPrec' c) (dn (inj-arr-p refl-⊑') M)
  
  inj-times-comp-up : ∀ {Γ} {c : S ⊑' (dyn × dyn)} {M : Tm Γ S}
    → (up (inj-times-p c) M) →[ 0S ] (up (inj-times-p refl-⊑') (up (mkTyPrec' c) M))

  inj-times-comp-down : ∀ {Γ} {c : S ⊑' (dyn × dyn)} {M : Tm Γ dyn}
    → (dn (inj-times-p c) M) →[ 0S ] dn (mkTyPrec' c) (dn (inj-times-p refl-⊑') M)


  -- Function casts
  ------------------
  up-arr : ∀ {Γ} {S⊑S' T⊑T'}
    -- → {E : EvCtx Γ (ty-right T⊑T') T}
    → {Vf : Tm Γ (ty-left S⊑S' ⇀ ty-left T⊑T')}
    → {V : Tm Γ (ty-right S⊑S')}
    → isValue Vf
    → isValue V
    → (app (up (S⊑S' ⇀TP' T⊑T') Vf) V)  →[ 0S ]
      (up T⊑T' (app Vf (dn S⊑S' V)))

  dn-arr : ∀ {Γ} {S⊑S' T⊑T'}
    → {Vf : Tm Γ (ty-right S⊑S' ⇀ ty-right T⊑T')}
    → {V : Tm Γ (ty-left S⊑S')}
    → isValue Vf
    → isValue V
    → (app (dn (S⊑S' ⇀TP' T⊑T') Vf) V)  →[ 0S ]
      (dn T⊑T' (app Vf (up S⊑S' V)))


  -- Product casts
  -----------------
  -- up-times : ∀ {Γ} {S⊑S' T⊑T'} {M : Tm (_ ∷ _ ∷ Γ) {!!}}
  --   → (letTimes (up (S⊑S' ×TP' T⊑T') {!!}) M) →[ 0S ] {!!}

  -- TODO do these need to be values?
  up-times : ∀ {Γ} {S⊑S' T⊑T'}
    → {V₁ : Tm Γ (ty-left S⊑S')} {V₂ : Tm Γ (ty-left T⊑T')}
    → (up (S⊑S' ×TP' T⊑T') (pair V₁ V₂)) →[ 0S ] pair (up S⊑S' V₁) (up T⊑T' V₂)

  dn-times : ∀ {Γ} {S⊑S' T⊑T'}
    → {V₁ : Tm Γ (ty-right S⊑S')} {V₂ : Tm Γ (ty-right T⊑T')}
    → (dn (S⊑S' ×TP' T⊑T') (pair V₁ V₂)) →[ 0S ] pair (dn S⊑S' V₁) (dn T⊑T' V₂)


  -- Casts involving dyn:
  -----------------------
  dn-dyn-good : ∀ {Γ} (t : Tag) {V : Value Γ (tag→c t .ty-left)} 
    → (dn (tag→c t) (up (tag→c t) ⟨ V ⟩v)) →[ tag→numSteps t ] ⟨ V ⟩v

  dn-dyn-bad : ∀ {Γ} (t-up t-dn : Tag) {V : Value Γ (tag→LHS t-up)}
    → dn (mkTyPrec' (tag→S⊑dyn t-dn)) (up (mkTyPrec' (tag→S⊑dyn t-up)) ⟨ V ⟩v) →[ 0S ] err


{-
  -- Casts involving dyn:
  -----------------------
  -- TODO should these really involve the "composed" forms of inj-arr
  -- and inj-times? Would it be sufficient to state them using the
  -- primitive injections?

  -- nat:
  dn-nat-nat : ∀ {Γ} {V : Value Γ nat}
--    → isValue V
    → (dn inj-nat-p (up inj-nat-p ⟨ V ⟩v)) →[ 0S ] (⟨ V ⟩v)

  dn-nat-arr : ∀ {Γ} {c : S ⊑' (dyn ⇀ dyn)} {V : Value Γ S}
--    → isValue V
    → (dn inj-nat-p (up (inj-arr-p c) ⟨ V ⟩v)) →[ 0S ] (err)

  dn-nat-times : ∀ {Γ} {c : S ⊑' (dyn × dyn)} {V : Value Γ S}
--    → isValue V
    → (dn inj-nat-p (up (inj-times-p c) ⟨ V ⟩v)) →[ 0S ] (err)
    
  -- arr:
  dn-arr-nat : ∀ {Γ} {c : S ⊑' (dyn ⇀ dyn)} {V : Value Γ nat}
--    → isValue V
    → (dn (inj-arr-p c) (up inj-nat-p ⟨ V ⟩v)) →[ 0S ] (err)

  dn-arr-arr : ∀ {Γ} {c : S ⊑' (dyn ⇀ dyn)} {V : Value Γ S}
--    → isValue V
    → (dn (inj-arr-p c) (up (inj-arr-p c) ⟨ V ⟩v)) →[ 1S ] (⟨ V ⟩v) -- one unfolding step
    -- What if c itself involves steps?

  dn-arr-times : ∀ {Γ S× S⇀} {c⇀ : S⇀ ⊑' (dyn ⇀ dyn)} {c× : S× ⊑' (dyn × dyn)} {V : Value Γ S×}
--    → isValue V
    → (dn (inj-arr-p c⇀) (up (inj-times-p c×) ⟨ V ⟩v)) →[ 0S ] err


  -- times:
  dn-times-nat : ∀ {Γ} {c : S ⊑' (dyn × dyn)} {V : Value Γ nat}
--    → isValue V
    → (dn (inj-times-p c) (up inj-nat-p ⟨ V ⟩v)) →[ 0S ] (err)

  dn-times-arr : ∀ {Γ S× S⇀} {c⇀ : S⇀ ⊑' (dyn ⇀ dyn)} {c× : S× ⊑' (dyn × dyn)} {V : Value Γ S⇀}
--    → isValue V
    → (dn (inj-times-p c×) (up (inj-arr-p c⇀) ⟨ V ⟩v)) →[ 0S ] err

  dn-times-times : ∀ {Γ} {c : S ⊑' (dyn × dyn)} {V : Value Γ S}
--    → isValue V
    → (dn (inj-times-p c) (up (inj-times-p c) ⟨ V ⟩v)) →[ 0S ] (⟨ V ⟩v)
-}



  -- Congruence
  --------------
  congE : ∀ {Γ S T}
    → {E : EvCtx Γ S T}
    → {M N : Tm Γ S}
    → {k : Step}
    → M →[ k ] N
    → (E [ M ]E) →[ k ] (E [ N ]E)

  

----------------------------
-- Transitive closure of →
----------------------------

data _→*[_]_ : {T : Ty} → Tm Γ T → ℕ → Tm Γ T → Type where
  →*-refl : {M : Tm Γ T}
    → M →*[ 0 ] M

  →*-trans : {M M' N : Tm Γ T} {k : Step} {m : ℕ}
    → M  →[ k ]     M'
    → M' →*[ m ]     N
    → M  →*[ (Step→ℕ k) + m ] N

------------------------------------
-- Guarded transitive closure of →
------------------------------------

data _⇒[_]_ : {T : Ty} → Tm Γ T → ℕ → Tm Γ T → Type where



{-

data Tm : Ctx -> Ty -> Set where
  var : Γ ∋ T -> Tm Γ T
  lda : Tm (S ∷ Γ) T -> Tm Γ (S ⇀ T)
  app : Tm Γ (S ⇀ T) -> Tm Γ S -> Tm Γ T
  err : Tm Γ S
  up  : (S⊑T : TyPrec) -> Tm Γ (ty-left S⊑T) -> Tm Γ (ty-right S⊑T)
  dn  : (S⊑T : TyPrec) -> Tm Γ (ty-right S⊑T) -> Tm Γ (ty-left S⊑T)
  zro : Tm Γ nat
  suc : Tm Γ nat -> Tm Γ nat
  matchNat : Tm Γ nat -> Tm Γ S -> Tm (nat ∷ Γ) S -> Tm Γ S

-}
