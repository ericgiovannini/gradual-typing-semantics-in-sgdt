module Semantics.Concrete.ClockedRel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Relation.Nullary
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Trunc

open import Cubical.Reflection.RecordEquiv
open import Cubical.Categories.Category hiding (isIso)

-- This is a concrete implementation of "step indexed big step semantics"

-- Clocked relations between X and Y that are propositional,
-- computable and functional should be isomorphic to Kleisli arrows of
-- the Delay monad

private
  variable
    ℓ ℓ' : Level

ClockedRel : (X Y : Type ℓ) → ∀ (ℓ' : Level) → Type _
ClockedRel X Y ℓ' = (x : X) → (y : Y) → (n : ℕ) → Type ℓ'

module _ {X Y : Type ℓ} (R : ClockedRel X Y ℓ') where
  isPropositional : Type _
  isPropositional = ∀ x y n → isProp (R x y n)

  isPropIsPropositional : isProp isPropositional
  isPropIsPropositional = isPropΠ3 (λ x y z → isPropIsProp)

  isComputable : Type _
  isComputable = ∀ x n → Dec (∃[ y ∈ Y ] R x y n)

  isFunctional : Type _
  isFunctional = ∀ x y n y' n' → R x y n → R x y' n' → (y ≡ y') × (n ≡ n')

record CompClockedRel {X Y Z : Type ℓ}
                      (R : ClockedRel X Y ℓ') (Q : ClockedRel Y Z ℓ')
                      (x : X) (z : Z) (n : ℕ)
       : Type (ℓ-max ℓ ℓ')
       where
  field
    nr : ℕ
    nq : ℕ
    y  : Y
    splits-n : nr + nq ≡ n
    r-holds : R x y nr
    q-holds : Q y z nq
open CompClockedRel
unquoteDecl CompClockedRelIsoΣ = declareRecordIsoΣ CompClockedRelIsoΣ (quote CompClockedRel)

module _ (ℓ : Level) where
  private
    variable
      X Y Z : Type ℓ

  open Category
  open Iso

  idCR : ClockedRel X X ℓ
  idCR x x' n = (x ≡ x') × Lift {j = ℓ} (n ≡ 0)

  lemCompRelL : ∀ x y n → (R : ClockedRel X Y ℓ)
              → CompClockedRel idCR R x y n
              → R x y n
  lemCompRelL x y' n R p = transport path (p .q-holds) where
    path' : p .nq ≡ n
    path' = transport (λ i → p .r-holds .snd .lower i + p .nq  ≡ n) (p .splits-n)

    path : R (p .y) y' (p .nq) ≡ R x y' n
    path i = R (p .r-holds .fst (~ i)) y' (path' i)
      -- have: p.r-holds .snd:       p .nr ≡ 0
      -- have: p.splits-n    : p.nr + p.nq ≡ n
      -- want: p.nq ≡ n
  
  CLOCKED-REL : Category (ℓ-suc ℓ) (ℓ-suc ℓ)
  CLOCKED-REL .ob = hSet ℓ
  CLOCKED-REL .Hom[_,_] X Y =
    Σ[ R ∈ ClockedRel ⟨ X ⟩ ⟨ Y ⟩ ℓ ] isPropositional R
  CLOCKED-REL .id {X} =
    idCR
    , λ x y n → isPropΣ (X .snd _ _) (λ _ → isOfHLevelLift 1 (isSetℕ _ _))
  CLOCKED-REL ._⋆_ Q R =
    (λ x y n → ∥ CompClockedRel (Q .fst) (R .fst) x y n ∥₁)
    , λ x y n → isPropPropTrunc
  CLOCKED-REL .⋆IdL (R , isPropR) =
    Σ≡Prop (λ _ → isPropIsPropositional _)
      (funExt λ x → funExt λ y → funExt λ n →
        hPropExt isPropPropTrunc (isPropR _ _ _)
        (Trunc.elim (λ _ → isPropR _ _ _) (λ z →
          lemCompRelL x y n R z))
        λ r → ∣ (record
                   { nr = 0
                   ; nq = n
                   ; y = x
                   ; splits-n = refl
                   ; r-holds = refl , lift refl
                   ; q-holds = r
                   }) ∣₁)
  CLOCKED-REL .⋆IdR = {!!}
  CLOCKED-REL .⋆Assoc = {!!}
  CLOCKED-REL .isSetHom {x = X}{y = Y} =
    isSetRetract {B = (x : ⟨ X ⟩) → (y : ⟨ Y ⟩) → (n : ℕ) → hProp ℓ}
      (λ (R , isPropR) x y n → (R x y n , isPropR x y n))
      (λ R → (λ x y n → ⟨ R x y n ⟩) , λ x y n → snd (R x y n))
      (λ _ → refl)
      (isSetΠ3 (λ x y n → isSetHProp))
