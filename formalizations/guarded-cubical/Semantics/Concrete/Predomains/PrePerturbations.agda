{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}


{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Later

module Semantics.Concrete.Predomains.PrePerturbations (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma


open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct


open import Common.Common
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k



private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level

    ℓMA₁ ℓMA₂ ℓMA₃ : Level
    ℓMB₁ ℓMB₂ ℓMB₃ : Level

open PBMor



-- Value pre-perturbations
--------------------------

-- Given a predomain X, a *value pre-perturbation* on X is an
-- endomorphism on X that is bisimilar to the identity.

PrePtb : (A : PosetBisim ℓ ℓ' ℓ'') → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
PrePtb A = Σ[ f ∈ PBMor A A ] _≈mon_ {X = A} {Y = A} f Id

PrePtbId : {A : PosetBisim ℓ ℓ' ℓ''} → PrePtb A
PrePtbId .fst = Id
PrePtbId {A = A} .snd = ≈mon-refl {X = A} {Y = A} Id

PrePtb∘ : {A : PosetBisim ℓ ℓ' ℓ''} → PrePtb A → PrePtb A → PrePtb A
PrePtb∘ g f .fst = (g .fst) ∘p (f .fst)
PrePtb∘ g f .snd = λ x y x≈y → g .snd (f .fst $ x) y (f .snd x y x≈y)


-- Equality of pre-perturbations follows from equality of the underlying endomorphisms.

PrePtb≡ : {A : PosetBisim ℓ ℓ' ℓ''} →
  (f1 f2 : PrePtb A) →
  f1 .fst .f ≡ f2 .fst .f → f1 ≡ f2
PrePtb≡ f g eq = Σ≡Prop (λ h → ≈mon-prop h Id) (eqPBMor _ _ eq)

EqEndomor→EqPrePtb : {A : PosetBisim ℓ ℓ' ℓ''} →
  (f1 f2 : PrePtb A) →
  f1 .fst ≡ f2 .fst → f1 ≡ f2
EqEndomor→EqPrePtb f1 f2 eq = Σ≡Prop (λ h → ≈mon-prop h Id) eq


-- The pre-perturbations on A form a monoid under composition.

Endo : (A : PosetBisim ℓ ℓ' ℓ'') -> Monoid (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
Endo A = makeMonoid {M = PrePtb A}
  PrePtbId PrePtb∘ {!!} -- TODO is set
  (λ f g h → PrePtb≡ _ _ refl)
  (λ f → PrePtb≡ _ _ refl)
  (λ f → PrePtb≡ _ _ refl)



ptbV : {A : PosetBisim ℓA ℓ≤A ℓ≈A} →
  (M : Monoid ℓM) (iA : MonoidHom M (Endo A)) → ⟨ M ⟩ → PBMor A A
ptbV M iA m = iA .fst m .fst




-- Computation pre-perturbations
--------------------------------

open CompErrorDomMor


CPrePtb : (B : ErrorDomain ℓ ℓ' ℓ'') → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
CPrePtb B = Σ[ ϕ ∈ ErrorDomMor B B ]
  _≈mon_ {X = U-ob B} {Y = U-ob B} (U-mor ϕ) Id


CPrePtbId : {B : ErrorDomain ℓ ℓ' ℓ''} → CPrePtb B
CPrePtbId .fst = IdE
CPrePtbId {B = B} .snd = ≈mon-refl {X = U-ob B} {Y = U-ob B} Id

CPrePtb∘ : {B : ErrorDomain ℓ ℓ' ℓ''} → CPrePtb B → CPrePtb B → CPrePtb B
CPrePtb∘ ϕ' ϕ .fst = (ϕ' .fst) ∘ed (ϕ .fst)
CPrePtb∘ ϕ' ϕ .snd = λ x y x≈y → ϕ' .snd _ _ (ϕ .snd x y x≈y)


-- Equality of pre-perturbations follows from equality of the
-- underlying endomorphisms.
CPrePtb≡ : {B : ErrorDomain ℓ ℓ' ℓ''} → (ϕ ϕ' : CPrePtb B) →
  ϕ .fst .ErrorDomMor.f .PBMor.f ≡ ϕ' .fst .ErrorDomMor.f .PBMor.f →
  ϕ ≡ ϕ'
  -- ErrorDomMor.fun (ϕ .fst) ≡ ErrorDomMor.fun (ϕ' .fst) → ϕ ≡ ϕ'
  -- This formulation causes an error when we provide refl as an
  -- argument to makeMonoid in the definition of CEndo.
CPrePtb≡ ϕ ϕ' eq =
  Σ≡Prop (λ h → ≈mon-prop (U-mor h) Id) (eqEDMor (ϕ .fst) (ϕ' .fst) eq)


EqEndomor→EqCPrePtb : {B : ErrorDomain ℓ ℓ' ℓ''} → (ϕ ϕ' : CPrePtb B) →
  ϕ .fst ≡ ϕ' .fst → ϕ ≡ ϕ'
EqEndomor→EqCPrePtb ϕ ϕ' eq = Σ≡Prop (λ h → ≈mon-prop (U-mor h) Id) eq


-- The pre-perturbations on B form a monoid under composition.
CEndo : (B : ErrorDomain ℓ ℓ' ℓ'') -> Monoid (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
CEndo B = makeMonoid {M = CPrePtb B}
  CPrePtbId CPrePtb∘ {!!} -- TODO is set
  (λ f g h → CPrePtb≡ _ _ refl)
  (λ f → CPrePtb≡ _ _ refl)
  (λ f → CPrePtb≡ _ _ refl)

ptbC : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  (M : Monoid ℓM) (iB : MonoidHom M (CEndo B)) → ⟨ M ⟩ → ErrorDomMor B B
ptbC M iB m = iB .fst m .fst


-- Convenience: action of ⟶ on pre-perturbations

_⟶PrePtb_ :
  -- {Aᵢ : PosetBisim ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aₒ : PosetBisim ℓAₒ ℓ≤Aₒ ℓ≈Aₒ}
  -- {Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ} {Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ} →
  {A : PosetBisim ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  (f : PrePtb A) (ϕ : CPrePtb B) → CPrePtb (A ⟶ob B)
(f ⟶PrePtb ϕ) .fst = (f .fst) ⟶mor (ϕ .fst) --  : ErrorDomMor (A ⟶ob B) (A ⟶ob B)
(f ⟶PrePtb ϕ) .snd g₁ g₂ g₁≈g₂ x y x≈y = ϕ .snd _ _ (g₁≈g₂ _ _ (f .snd _ _ x≈y))
  where
    -- There is also a "point-free" proof using the fact that composition preserves bisimilarity
    -- but in this case it's easier to just inline that proof here.
    
    -- aux : ((U-mor (ϕ .fst)) ∘p g₁ ∘p (f .fst)) ≈mon (Id ∘p g₁ ∘p Id)
    -- aux = ≈comp {!!} {!!} {!!} {!!} (f .snd) (≈comp {!!} {!!} {!!} {!!} g₁≈g₂ (ϕ .snd))

    -- Given g₁, g₂ : A → UB where g₁ ≈ g₂
    -- NTS : (ϕ ∘ g₁ ∘ f) ≈ g₂
    -- Have : (ϕ ∘ g₁ ∘ f) ≈ (id ∘ g₂ ∘ id) = g₂


-- Convenience: action of the U functor on pre-perturbations
U-PrePtb :
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} → CPrePtb B → PrePtb (U-ob B)
U-PrePtb ϕ .fst = U-mor (ϕ .fst)
U-PrePtb ϕ .snd = ϕ .snd



CEndo-B→Endo-UB : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  MonoidHom (CEndo B) (Endo (U-ob B))
CEndo-B→Endo-UB .fst = U-PrePtb
CEndo-B→Endo-UB .snd .IsMonoidHom.presε = refl
CEndo-B→Endo-UB .snd .IsMonoidHom.pres· ϕ ϕ' = refl
