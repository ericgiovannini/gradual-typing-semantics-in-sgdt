{-
  Semantic combinators used by the interpretation of terms:
  natural-number case analysis, plugging of evaluation contexts,
  the constant arrow, and Kleisli composition of evaluation contexts.

  An evaluation context Γ ⊢ E : S ⇝ T denotes a homomorphism
  F ⟦S⟧ ⊸ (⟦Γ⟧ ⟶ F ⟦T⟧), so strength is handled by the arrow domain.
-}
{-# OPTIONS --rewriting --lossy-unification #-}
open import Common.Later
module Syntax.FineGrained.Denotation.Combinators (k : Clock) where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat using (zero ; suc)
open import Cubical.Data.Sigma

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions
  using (_×dp_ ; π1 ; π2 ; ℕ)
open import Semantics.Concrete.Predomain.Combinators
  using (Curry ; App ; PairFun ; _×mor_)
open import Semantics.Concrete.Predomain.ErrorDomain k

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓΓ ℓ≤Γ ℓ≈Γ : Level
    ℓA ℓ≤A ℓ≈A : Level
    ℓB ℓ≤B ℓ≈B : Level
    ℓB' ℓ≤B' ℓ≈B' : Level
    ℓB₁ ℓ≤B₁ ℓ≈B₁ : Level
    ℓB₂ ℓ≤B₂ ℓ≈B₂ : Level
    ℓB₃ ℓ≤B₃ ℓ≈B₃ : Level

open PMor
open ErrorDomMor


-----------------------------------------------------------------------
-- Case analysis on natural numbers
-----------------------------------------------------------------------

-- ℕ is the flat predomain, so its order and bisimilarity are equality
-- and monotonicity reduces to transport along an equality of numbers.
module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {B : Predomain ℓB ℓ≤B ℓ≈B}
         (z : PMor Γ B) (s : PMor (Γ ×dp ℕ) B) where

  private
    module B = PredomainStr (B .snd)
    module Γ = PredomainStr (Γ .snd)

    nc : ⟨ Γ ⟩ × ⟨ ℕ ⟩ → ⟨ B ⟩
    nc (γ , zero) = z .f γ
    nc (γ , suc n) = s .f (γ , n)

    nc-mon : ∀ γ γ' n → γ Γ.≤ γ' → nc (γ , n) B.≤ nc (γ' , n)
    nc-mon γ γ' zero γ≤γ' = z .isMon γ≤γ'
    nc-mon γ γ' (suc n) γ≤γ' = s .isMon (γ≤γ' , refl)

    nc-≈ : ∀ γ γ' n → γ Γ.≈ γ' → nc (γ , n) B.≈ nc (γ' , n)
    nc-≈ γ γ' zero γ≈γ' = z .pres≈ γ≈γ'
    nc-≈ γ γ' (suc n) γ≈γ' = s .pres≈ (γ≈γ' , refl)

  natCase : PMor (Γ ×dp ℕ) B
  natCase .f = nc
  natCase .isMon {γ , n} {γ' , n'} (γ≤γ' , n≡n') =
    subst (λ m → nc (γ , n) B.≤ nc (γ' , m)) n≡n' (nc-mon γ γ' n γ≤γ')
  natCase .pres≈ {γ , n} {γ' , n'} (γ≈γ' , n≡n') =
    subst (λ m → nc (γ , n) B.≈ nc (γ' , m)) n≡n' (nc-≈ γ γ' n γ≈γ')


-----------------------------------------------------------------------
-- Evaluation contexts as homomorphisms into the arrow domain
-----------------------------------------------------------------------

module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} where

  -- The empty evaluation context: B ⊸ (Γ ⟶ B), ignoring the environment.
  K-arrow : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} → ErrorDomMor B (Γ ⟶ob B)
  K-arrow .f = Curry π1
  K-arrow .f℧ = eqPMor _ _ refl
  K-arrow .fθ x~ = eqPMor _ _ refl

  -- Plugging a computation into an evaluation context.
  plugE : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'} →
    ErrorDomMor B (Γ ⟶ob B') → PMor Γ (U-ob B) → PMor Γ (U-ob B')
  plugE E M = App ∘p PairFun (U-mor E ∘p M) Id

  -- Kleisli composition of evaluation contexts:
  -- (E' ∘E E) b γ = E' (E b γ) γ.
  module _ {B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁} {B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂}
           {B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃}
           (E' : ErrorDomMor B₂ (Γ ⟶ob B₃)) (E : ErrorDomMor B₁ (Γ ⟶ob B₂)) where

    private
      -- (b , γ) ↦ E' (E b γ) γ
      h : PMor (U-ob B₁ ×dp Γ) (U-ob B₃)
      h = App ∘p PairFun (U-mor E' ∘p App ∘p (U-mor E ×mor Id)) π2

      module B₁ = ErrorDomainStr (B₁ .snd)
      module B₂ = ErrorDomainStr (B₂ .snd)
      module B₃ = ErrorDomainStr (B₃ .snd)

      -- pointwise unfoldings of the homomorphism conditions of E and E'
      E℧ : ∀ γ → E .fun B₁.℧ .f γ ≡ B₂.℧
      E℧ γ = funExt⁻ (cong PMor.f (E .f℧)) γ

      E'℧ : ∀ γ → E' .fun B₂.℧ .f γ ≡ B₃.℧
      E'℧ γ = funExt⁻ (cong PMor.f (E' .f℧)) γ

      Eθ : ∀ x~ γ → E .fun (B₁.θ .f x~) .f γ ≡ B₂.θ .f (λ t → E .fun (x~ t) .f γ)
      Eθ x~ γ = funExt⁻ (cong PMor.f (E .fθ x~)) γ

      E'θ : ∀ y~ γ → E' .fun (B₂.θ .f y~) .f γ ≡ B₃.θ .f (λ t → E' .fun (y~ t) .f γ)
      E'θ y~ γ = funExt⁻ (cong PMor.f (E' .fθ y~)) γ

    compE : ErrorDomMor B₁ (Γ ⟶ob B₃)
    compE .f = Curry h
    compE .f℧ = eqPMor _ _ (funExt (λ γ →
      cong (λ y → E' .fun y .f γ) (E℧ γ) ∙ E'℧ γ))
    compE .fθ x~ = eqPMor _ _ (funExt (λ γ →
      cong (λ y → E' .fun y .f γ) (Eθ x~ γ) ∙ E'θ _ γ))
