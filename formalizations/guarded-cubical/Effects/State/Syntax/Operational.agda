{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Effects.State.Syntax.Operational (k : Clock)  where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Foundations.Function

open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

open import Syntax.Types
-- open import Syntax.FineGrained.Terms
open import Effects.State.Syntax.FineGrained
open import Effects.State.Monad k as Monad

open TyPrec'

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S U R' S' U' : Ty
   b b' c c' d d' : S ⊑' S'

   ℓ ℓ' ℓSt : Level


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


{-
module _ (St : Type ℓSt) where

  StepsC : ∀ {S : Ty} → Comp Γ S → ⊤ ⊎ (SD St (Comp Γ S))
  StepsC err = inl tt
  StepsC (ret V) = inl tt
  StepsC (lda M) = inl tt
  StepsC (app M V) = ?
  
  StepsC (bind M N) = {!!}
  StepsC (pm V M) = {!!}
  StepsC (matchNat V Kz Ks) = {!!}
  StepsC (dn S⊑T M) = {!!}
  StepsC (up S⊑T M) = {!!}


data CanStepC : {S : Ty} → Comp Γ S → Type
data CanStepV : {S : Ty} → Val Γ S → Type


data CanStepC where
  matchNat-zro : ∀ {Γ S} {Kz : Comp Γ S} {Ks : Comp (nat ∷ Γ) S}
    → CanStepC (matchNat zro Kz Ks)

  matchNat-suc : ∀ {Γ S} {Kz : Comp Γ S} {Ks : Comp (nat ∷ Γ) S}
    → {V : Val Γ nat}
    → CanStepC (matchNat (suc V) Kz Ks)

  λ-β : ∀ {Γ S T} {M : Comp (S ∷ Γ) T} {V : Val Γ S}
    → CanStepC (app (lda M) V)

  ×-β : ∀ {Γ R S T} {M : Comp (S ∷ T ∷ Γ) R} {V₁ : Val Γ S} {V₂ : Val Γ T}
    → CanStepC (pm (pair V₁ V₂) M)

  up-arr : ∀ {Γ} {S⊑S' T⊑T'}
    → {Vf : Val Γ (ty-left S⊑S' ⇀ ty-left T⊑T')}
    → {V : Val Γ (ty-right S⊑S')}
    → CanStepC (app (ret (up (S⊑S' ⇀TP' T⊑T') Vf)) V) 

  dn-arr : ∀ {Γ} {S⊑S' T⊑T'}
    → {Mf : Comp Γ (ty-right S⊑S' ⇀ ty-right T⊑T')}
    → {V : Val Γ (ty-left S⊑S')}
    → CanStepC (app (dn (S⊑S' ⇀TP' T⊑T') Mf) V)


  inj-arr-comp-up : ∀ {Γ} {c : S ⊑' (dyn ⇀ dyn)} {M : Comp Γ S}
    → CanStepC (up (inj-arr-p c) M)

  inj-arr-comp-down : ∀ {Γ} {c : S ⊑' (dyn ⇀ dyn)} {M : Comp Γ dyn}
    → CanStepC (dn (inj-arr-p c) M) 
  
  inj-times-comp-up : ∀ {Γ} {c : S ⊑' (dyn × dyn)} {M : Comp Γ S}
    → CanStepC (up (inj-times-p c) M) 

  inj-times-comp-down : ∀ {Γ} {c : S ⊑' (dyn × dyn)} {M : Comp Γ dyn}
    → CanStepC (dn (inj-times-p c) M)

  dn-dyn-good : ∀ {Γ} (t : Tag) {V : Val Γ (tag→c t .ty-left)} 
    → CanStepC (dn (tag→c t) (ret (up (tag→c t) V)))

  dn-dyn-bad : ∀ {Γ} (t-up t-dn : Tag) {V : Val Γ (tag→LHS t-up)}
    → CanStepC (dn (mkTyPrec' (tag→S⊑dyn t-dn)) (ret (up (mkTyPrec' (tag→S⊑dyn t-up)) V)))


data CanStepV where
  up-times : ∀ {Γ} {S⊑S' T⊑T'}
    → {V₁ : Val Γ (ty-left S⊑S')} {V₂ : Val Γ (ty-left T⊑T')}
    → CanStepV (up (S⊑S' ×TP' T⊑T') (pair V₁ V₂)) 


stepDecC : ∀ {S : Ty} (M : Comp Γ S) → Dec (CanStepC M)
stepDecC err = no λ {()}
stepDecC (ret V) = no λ {()} 
stepDecC (lda M) = no λ {()}
stepDecC (app M x) = {!!}
stepDecC (bind M N) = {!!}
stepDecC (pm x M) = {!!}
stepDecC (matchNat zro Kz Ks) = yes matchNat-zro
stepDecC (matchNat (suc V) Kz Ks) = yes matchNat-suc
stepDecC (matchNat V Kz Ks) with V
... | var x = no λ {()}
... | zro = yes matchNat-zro
... | suc W = yes matchNat-suc
... | up S⊑T s = no (λ {()})
stepDecC (dn S⊑T M) = {!!}
stepDecC (up S⊑T M) = {!!}

module _ (St : Type ℓSt) where

  stepC : {S : Ty} → (M : Comp Γ S) → CanStepC M → SD St (Comp Γ S)
  
-} 
  



module _ (St : Type ℓSt) where

  data _→[TC]_ : {S : Ty} → Comp Γ S → T St (Comp Γ S) → Type ℓSt where

    matchNat-zro : ∀ {Γ S} {Kz : Comp Γ S} {Ks : Comp (nat ∷ Γ) S}
      → (matchNat zro Kz Ks) →[TC] (retT Kz)

    matchNat-suc : ∀ {Γ S} {Kz : Comp Γ S} {Ks : Comp (nat ∷ Γ) S}
      → {V : Val Γ nat}
      → (matchNat (suc V) Kz Ks) →[TC] (retT (Ks [ V ]C))
  


module _
  (St : Type ℓSt)
  (step : (M : Comp [] S) → (Σ[ V ∈ Val [] S ] M ≡ ret V) ⊎ (T St (Comp [] S)))
  where

  run : (M : Comp [] S) → T St (Val [] S)
  run M = iterateT {A = T St (Comp [] S)} g (retT M)
    where

      g : (T St (Comp [] S) → T St (Val [] S)) →
           T St (Comp [] S) → T St (Val [] S)
      g rec TM = Monad.ext (Comp [] S) (Val [] S) (rec ∘ retT) TM

      f : (rec : (M : T St (Comp [] S)) → T St (Val [] S))
        → (M : Comp [] S) → T St (Val [] S)
      f rec M = aux (step M)
        where
          aux : _ → T St (Val [] S)
          aux (inl (V , eq)) = retT V
          aux (inr M') = rec M'
    


-- Small-step semantics

data _→[_]V_ : {T : Ty} → Val Γ T → Step → Val Γ T → Type where

  up-times : ∀ {Γ} {S⊑S' T⊑T'}
    → {V₁ : Val Γ (ty-left S⊑S')} {V₂ : Val Γ (ty-left T⊑T')}
    → (up (S⊑S' ×TP' T⊑T') (pair V₁ V₂)) →[ 0S ]V (pair (up S⊑S' V₁) (up T⊑T' V₂))


data _→[_]C_ : {T : Ty} → Comp Γ T → Step → Comp Γ T → Type where

  matchNat-zro : ∀ {Γ S} {Kz : Comp Γ S} {Ks : Comp (nat ∷ Γ) S}
    → (matchNat zro Kz Ks) →[ 0S ]C Kz

  matchNat-suc : ∀ {Γ S} {Kz : Comp Γ S} {Ks : Comp (nat ∷ Γ) S}
    → {V : Val Γ nat}
    → (matchNat (suc V) Kz Ks) →[ 0S ]C (Ks [ V ]C)

  λ-β : ∀ {Γ S T} {M : Comp (S ∷ Γ) T} {V : Val Γ S}
    → (app (lda M) V) →[ 0S ]C (M [ V ]C)

  ×-β : ∀ {Γ R S T} {M : Comp (S ∷ T ∷ Γ) R} {V₁ : Val Γ S} {V₂ : Val Γ T}
    → (pm (pair V₁ V₂) M) →[ 0S ]C ((M [ wkV V₁ ]C) [ V₂ ]C)


  up-arr : ∀ {Γ} {S⊑S' T⊑T'}
    → {Vf : Val Γ (ty-left S⊑S' ⇀ ty-left T⊑T')}
    → {V : Val Γ (ty-right S⊑S')}
    → (app (ret (up (S⊑S' ⇀TP' T⊑T') Vf)) V) →[ 0S ]C {!!}

  dn-arr : ∀ {Γ} {S⊑S' T⊑T'}
    → {Mf : Comp Γ (ty-right S⊑S' ⇀ ty-right T⊑T')}
    → {V : Val Γ (ty-left S⊑S')}
    → (app (dn (S⊑S' ⇀TP' T⊑T') Mf) V) →[ 0S ]C (dn T⊑T' (app Mf (up S⊑S' V)))


  dn-times : ∀ {Γ} {S⊑S' T⊑T'}
    → {V₁ : Val Γ (ty-right S⊑S')} {V₂ : Val Γ (ty-right T⊑T')}
    → (dn (S⊑S' ×TP' T⊑T') (ret (pair V₁ V₂))) →[ 0S ]C
      bind
        (dn S⊑S' (ret V₁))
        (bind
          (wkC (dn T⊑T' (ret V₂)))
          (ret (pair (var (vs vz)) (var vz))))
    -- (pair (dn S⊑S' V₁) (dn T⊑T' V₂))
    -- doesn't work: pair expects values!


  inj-arr-comp-up : ∀ {Γ} {c : S ⊑' (dyn ⇀ dyn)} {M : Comp Γ S}
    → (up (inj-arr-p c) M) →[ 0S ]C (up (inj-arr-p refl-⊑') (up (mkTyPrec' c) M))

  inj-arr-comp-down : ∀ {Γ} {c : S ⊑' (dyn ⇀ dyn)} {M : Comp Γ dyn}
    → (dn (inj-arr-p c) M) →[ 0S ]C (dn (mkTyPrec' c) (dn (inj-arr-p refl-⊑') M))
  
  inj-times-comp-up : ∀ {Γ} {c : S ⊑' (dyn × dyn)} {M : Comp Γ S}
    → (up (inj-times-p c) M) →[ 0S ]C (up (inj-times-p refl-⊑') (up (mkTyPrec' c) M))

  inj-times-comp-down : ∀ {Γ} {c : S ⊑' (dyn × dyn)} {M : Comp Γ dyn}
    → (dn (inj-times-p c) M) →[ 0S ]C (dn (mkTyPrec' c) (dn (inj-times-p refl-⊑') M))


  dn-dyn-good : ∀ {Γ} (t : Tag) {V : Val Γ (tag→c t .ty-left)} 
    → (dn (tag→c t) (ret (up (tag→c t) V))) →[  tag→numSteps t ]C (ret V)

  dn-dyn-bad : ∀ {Γ} (t-up t-dn : Tag) {V : Val Γ (tag→LHS t-up)}
    → (dn (mkTyPrec' (tag→S⊑dyn t-dn)) (ret (up (mkTyPrec' (tag→S⊑dyn t-up)) V)))
      →[ 0S ]C err

  ret-cong : ∀ {Γ} (V W : Val Γ S) (j : Step)
    → V →[ j ]V W → (ret V) →[ j ]C (ret W)

  -- TODO: what about congruence for suc V, up c V, pair V W, and pm V M


  EC-cong : ∀ {Γ S T}
    → {E : EvCtxC Γ S T}
    → {M N : Comp Γ S}
    → {k : Step}
    → M →[ k ]C N
    → (E [ M ]E) →[ k ]C (E [ N ]E)





{-
  -- β rules for nat, functions, and products
  --------------------------------------------
  matchNat-zro : ∀ {Γ S} {Kz : Comp Γ S} {Ks : Comp (nat ∷ Γ) S}
    → (matchNat zro Kz Ks) →[ 0S ] Kz

  matchNat-suc : ∀ {Γ S} {Kz : Comp Γ S} {Ks : Comp (nat ∷ Γ) S}
    → {V : Value Γ nat}
    → (matchNat (suc ⟨ V ⟩v) Kz Ks) →[ 0S ] (Ks [ ⟨ V ⟩v ]tm)

  λ-β : ∀ {Γ S T} {M : Comp (S ∷ Γ) T} {V : Value Γ S}
    → (app (lda M) ⟨ V ⟩v) →[ 0S ] (M [ ⟨ V ⟩v ]tm)

  ×-β : ∀ {Γ R S T} {M : Comp (S ∷ T ∷ Γ) R} {V₁ : Value Γ S} {V₂ : Value Γ T}
--    → isValue V₁
--    → isValue V₂
    → (letTimes (pair ⟨ V₁ ⟩v  ⟨ V₂ ⟩v) M) →[ 0S ]
      ((M [ wk ⟨ V₁ ⟩v ]tm) [ ⟨ V₂ ⟩v ]tm)


  -- "Functoriality" of inj-arr and inj-times
  ---------------------------------------------

  inj-arr-comp-up : ∀ {Γ} {c : S ⊑' (dyn ⇀ dyn)} {M : Comp Γ S}
    → (up (inj-arr-p c) M) →[ 0S ] (up (inj-arr-p refl-⊑') (up (mkTyPrec' c) M))

  inj-arr-comp-down : ∀ {Γ} {c : S ⊑' (dyn ⇀ dyn)} {M : Comp Γ dyn}
    → (dn (inj-arr-p c) M) →[ 0S ] dn (mkTyPrec' c) (dn (inj-arr-p refl-⊑') M)
  
  inj-times-comp-up : ∀ {Γ} {c : S ⊑' (dyn × dyn)} {M : Comp Γ S}
    → (up (inj-times-p c) M) →[ 0S ] (up (inj-times-p refl-⊑') (up (mkTyPrec' c) M))

  inj-times-comp-down : ∀ {Γ} {c : S ⊑' (dyn × dyn)} {M : Comp Γ dyn}
    → (dn (inj-times-p c) M) →[ 0S ] dn (mkTyPrec' c) (dn (inj-times-p refl-⊑') M)


  -- Function casts
  ------------------
  up-arr : ∀ {Γ} {S⊑S' T⊑T'}
    -- → {E : EvCtx Γ (ty-right T⊑T') T}
    → {Vf : Comp Γ (ty-left S⊑S' ⇀ ty-left T⊑T')}
    → {V : Comp Γ (ty-right S⊑S')}
    → isValue Vf
    → isValue V
    → (app (up (S⊑S' ⇀TP' T⊑T') Vf) V)  →[ 0S ]
      (up T⊑T' (app Vf (dn S⊑S' V)))

  dn-arr : ∀ {Γ} {S⊑S' T⊑T'}
    → {Vf : Comp Γ (ty-right S⊑S' ⇀ ty-right T⊑T')}
    → {V : Comp Γ (ty-left S⊑S')}
    → isValue Vf
    → isValue V
    → (app (dn (S⊑S' ⇀TP' T⊑T') Vf) V)  →[ 0S ]
      (dn T⊑T' (app Vf (up S⊑S' V)))


  -- Product casts
  -----------------
  -- up-times : ∀ {Γ} {S⊑S' T⊑T'} {M : Comp (_ ∷ _ ∷ Γ) {!!}}
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

-}
