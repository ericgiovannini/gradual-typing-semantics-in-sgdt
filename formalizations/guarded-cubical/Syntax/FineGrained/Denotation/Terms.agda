{-
  Denotational semantics of terms.

  Substitutions and values denote value morphisms, computations denote
  oblique morphisms Γ → U F S (Kleisli morphisms), and evaluation
  contexts denote homomorphisms F S ⊸ (Γ ⟶ F T) into the arrow domain.
  Contexts are right-nested products, newest variable on the right.

  The syntax is quotiented by the βη and substitution laws; each path
  constructor is interpreted by the corresponding equation of the
  model, which in all cases is either definitional or one of the two
  unit laws of the free error domain.
-}
{-# OPTIONS --rewriting --lossy-unification #-}
open import Common.Later
module Syntax.FineGrained.Denotation.Terms (k : Clock) where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Foundations.Structure
open import Cubical.Data.List
open import Cubical.Data.Nat using (zero ; suc)
open import Cubical.Data.Sigma

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism renaming (Comp to Compose)
open import Semantics.Concrete.Predomain.Constructions
  using (_×dp_ ; π1 ; π2 ; UnitP!)
open import Semantics.Concrete.Predomain.Combinators
  using (Curry ; App ; PairFun ; K ; SwapPair ; _×mor_ ; mSuc)
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Types k as SemTypes hiding (_×_)
open import Semantics.Concrete.Perturbation.QuasiRepresentation k

open import Syntax.Types
open import Syntax.FineGrained.Terms hiding (π2)
open import Syntax.FineGrained.Denotation.Types k
open import Syntax.FineGrained.Denotation.TypePrecision k
open import Syntax.FineGrained.Denotation.Combinators k

open TyPrec
open PMor
open ErrorDomMor
open ExtAsEDMorphism

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T R' S' T' : Ty
   b b' c c' d d' : S ⊑ S'


⟦_⟧S : Subst Δ Γ   → ValMor ⟦ Δ ⟧ctx ⟦ Γ ⟧ctx
⟦_⟧V : Val Γ S     → ValMor ⟦ Γ ⟧ctx ⟦ S ⟧ty
⟦_⟧C : Comp Γ S    → ObliqueMor ⟦ Γ ⟧ctx (F ⟦ S ⟧ty)
⟦_⟧E : EvCtx Γ S T → CompMor (F ⟦ S ⟧ty) (⟦ Γ ⟧ctx ⟶ F ⟦ T ⟧ty)


-- The two unit laws of the free error domain, in the form needed for
-- the ret-β and ret-η path constructors.
private
  module _ {A : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero} {B : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero}
           {Γ : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero} where

    private
      |Γ| = ValType→Predomain Γ
      |A| = ValType→Predomain A
      FB = CompType→ErrorDomain (F B)

    -- bind M [ wk ]e [ ret' var ]∙ ≡ M
    ret-β-lemma : (M : ObliqueMor (Γ SemTypes.× A) (F B)) →
      plugE ((π1 ⟶mor IdE) ∘ed Ext (Curry (M ∘p SwapPair))) ((η-mor ∘p π2) ∘p PairFun UnitP! π2) ≡ M
    ret-β-lemma M = eqPMor _ _ (funExt (λ { (γ , a) →
      cong (λ h → h .f γ) (funExt⁻ (cong PMor.f (Equations.Ext-η g)) a) }))
      where
        g : PMor |A| (U-ob (|Γ| ⟶ob FB))
        g = Curry (M ∘p SwapPair)

    -- E ≡ bind (E [ wk ]e [ ret' var ]∙)
    ret-η-lemma : (E : CompMor (F A) (Γ ⟶ F B)) →
      E ≡ Ext (Curry (plugE ((π1 ⟶mor IdE) ∘ed E) ((η-mor ∘p π2) ∘p PairFun UnitP! π2) ∘p SwapPair))
    ret-η-lemma E = F-extensionality E (Ext g)
      (eqPMor _ _ (funExt (λ a → eqPMor _ _ refl)) ∙ sym (Equations.Ext-η g))
      where
        g : PMor |A| (U-ob (|Γ| ⟶ob FB))
        g = Curry (plugE ((π1 ⟶mor IdE) ∘ed E) ((η-mor ∘p π2) ∘p PairFun UnitP! π2) ∘p SwapPair)
      -- the first path: U-mor E ∘p η-mor ≡ g, pointwise definitional

    -- E [ err' ]∙ ≡ err'
    strictness-lemma : (E : CompMor (F A) (Γ ⟶ F B)) →
      plugE E (℧-mor ∘p UnitP!) ≡ ℧-mor ∘p UnitP!
    strictness-lemma E = eqPMor _ _ (funExt (λ γ → funExt⁻ (cong PMor.f (E .f℧)) γ))


-- Substitutions
⟦ ids ⟧S = Id
⟦ γ ∘s δ ⟧S = ⟦ γ ⟧S ∘p ⟦ δ ⟧S
⟦ ∘IdL {γ = γ} i ⟧S = CompPD-IdL ⟦ γ ⟧S i
⟦ ∘IdR {γ = γ} i ⟧S = CompPD-IdR ⟦ γ ⟧S i
⟦ ∘Assoc {γ = γ} {δ = δ} {θ = θ} i ⟧S =
  eqPMor (⟦ γ ⟧S ∘p (⟦ δ ⟧S ∘p ⟦ θ ⟧S)) ((⟦ γ ⟧S ∘p ⟦ δ ⟧S) ∘p ⟦ θ ⟧S) refl i
⟦ !s ⟧S = UnitP!
⟦ []η {γ = γ} i ⟧S = eqPMor ⟦ γ ⟧S UnitP! refl i
⟦ γ ,s V ⟧S = PairFun ⟦ γ ⟧S ⟦ V ⟧V
⟦ wk ⟧S = π1
⟦ wkβ {δ = δ} {V = V} i ⟧S = eqPMor (π1 ∘p PairFun ⟦ δ ⟧S ⟦ V ⟧V) ⟦ δ ⟧S refl i
⟦ ,sη {δ = δ} i ⟧S = eqPMor ⟦ δ ⟧S (PairFun (π1 ∘p ⟦ δ ⟧S) (π2 ∘p ⟦ δ ⟧S)) refl i

-- Values
⟦ V [ γ ]v ⟧V = ⟦ V ⟧V ∘p ⟦ γ ⟧S
⟦ substId {V = V} i ⟧V = CompPD-IdR ⟦ V ⟧V i
⟦ substAssoc {V = V} {δ = δ} {γ = γ} i ⟧V =
  eqPMor (⟦ V ⟧V ∘p (⟦ δ ⟧S ∘p ⟦ γ ⟧S)) ((⟦ V ⟧V ∘p ⟦ δ ⟧S) ∘p ⟦ γ ⟧S) refl i
⟦ var ⟧V = π2
⟦ varβ {δ = δ} {V = V} i ⟧V = eqPMor (π2 ∘p PairFun ⟦ δ ⟧S ⟦ V ⟧V) ⟦ V ⟧V refl i
⟦ zro ⟧V = K _ zero
⟦ suc ⟧V = mSuc ∘p π2
⟦ lda M ⟧V = Curry ⟦ M ⟧C
⟦ fun-η {V = V} i ⟧V =
  eqPMor ⟦ V ⟧V
    (Curry ((App ∘p (π2 ×mor Id)) ∘p PairFun (PairFun UnitP! (⟦ V ⟧V ∘p π1)) π2))
    (funExt (λ γ → eqPMor _ _ refl)) i
⟦ injectN ⟧V     = embV _ _ _ (⟦ inj-nat ⟧ty⊑ .snd .fst) ∘p π2
⟦ injectArr ⟧V   = embV _ _ _ (⟦ inj-arr ⟧ty⊑ .snd .fst) ∘p π2
⟦ injectTimes ⟧V = embV _ _ _ (⟦ inj-times ⟧ty⊑ .snd .fst) ∘p π2
⟦ up c ⟧V        = embV _ _ _ (⟦ c .ty-prec ⟧ty⊑ .snd .fst) ∘p π2

-- Evaluation contexts
⟦ ∙E ⟧E = K-arrow
⟦ E ∘E E' ⟧E = compE ⟦ E ⟧E ⟦ E' ⟧E
⟦ ∘IdL {E = E} i ⟧E = eqEDMor (compE K-arrow ⟦ E ⟧E) ⟦ E ⟧E (funExt (λ x → eqPMor _ _ refl)) i
⟦ ∘IdR {E = E} i ⟧E = eqEDMor (compE ⟦ E ⟧E K-arrow) ⟦ E ⟧E (funExt (λ x → eqPMor _ _ refl)) i
⟦ ∘Assoc {E = E} {F = E'} {F' = E''} i ⟧E =
  eqEDMor (compE ⟦ E ⟧E (compE ⟦ E' ⟧E ⟦ E'' ⟧E)) (compE (compE ⟦ E ⟧E ⟦ E' ⟧E) ⟦ E'' ⟧E)
    (funExt (λ x → eqPMor _ _ refl)) i
⟦ E [ γ ]e ⟧E = (⟦ γ ⟧S ⟶mor IdE) ∘ed ⟦ E ⟧E
⟦ substId {E = E} i ⟧E = eqEDMor ((Id ⟶mor IdE) ∘ed ⟦ E ⟧E) ⟦ E ⟧E (funExt (λ x → eqPMor _ _ refl)) i
⟦ substAssoc {E = E} {γ = γ} {δ = δ} i ⟧E =
  eqEDMor (((⟦ γ ⟧S ∘p ⟦ δ ⟧S) ⟶mor IdE) ∘ed ⟦ E ⟧E)
    ((⟦ δ ⟧S ⟶mor IdE) ∘ed ((⟦ γ ⟧S ⟶mor IdE) ∘ed ⟦ E ⟧E))
    (funExt (λ x → eqPMor _ _ refl)) i
⟦ ∙substDist {γ = γ} i ⟧E = eqEDMor ((⟦ γ ⟧S ⟶mor IdE) ∘ed K-arrow) K-arrow (funExt (λ x → eqPMor _ _ refl)) i
⟦ ∘substDist {E = E} {F = E'} {γ = γ} i ⟧E =
  eqEDMor ((⟦ γ ⟧S ⟶mor IdE) ∘ed compE ⟦ E ⟧E ⟦ E' ⟧E)
    (compE ((⟦ γ ⟧S ⟶mor IdE) ∘ed ⟦ E ⟧E) ((⟦ γ ⟧S ⟶mor IdE) ∘ed ⟦ E' ⟧E))
    (funExt (λ x → eqPMor _ _ refl)) i
⟦ bind M ⟧E = Ext (Curry (⟦ M ⟧C ∘p SwapPair))
⟦ ret-η {E = E} i ⟧E = ret-η-lemma ⟦ E ⟧E i
⟦ dn c ⟧E = K-arrow ∘ed projC _ _ _ (⟦ c .ty-prec ⟧ty⊑ .snd .snd)

-- Computations
⟦ E [ M ]∙ ⟧C = plugE ⟦ E ⟧E ⟦ M ⟧C
⟦ plugId {M = M} i ⟧C = eqPMor (plugE K-arrow ⟦ M ⟧C) ⟦ M ⟧C refl i
⟦ plugAssoc {F = E'} {E = E} {M = M} i ⟧C =
  eqPMor (plugE (compE ⟦ E' ⟧E ⟦ E ⟧E) ⟦ M ⟧C) (plugE ⟦ E' ⟧E (plugE ⟦ E ⟧E ⟦ M ⟧C)) refl i
⟦ M [ γ ]c ⟧C = ⟦ M ⟧C ∘p ⟦ γ ⟧S
⟦ substId {M = M} i ⟧C = CompPD-IdR ⟦ M ⟧C i
⟦ substAssoc {M = M} {δ = δ} {γ = γ} i ⟧C =
  eqPMor (⟦ M ⟧C ∘p (⟦ δ ⟧S ∘p ⟦ γ ⟧S)) ((⟦ M ⟧C ∘p ⟦ δ ⟧S) ∘p ⟦ γ ⟧S) refl i
⟦ substPlugDist {E = E} {M = M} {γ = γ} i ⟧C =
  eqPMor (plugE ⟦ E ⟧E ⟦ M ⟧C ∘p ⟦ γ ⟧S) (plugE ((⟦ γ ⟧S ⟶mor IdE) ∘ed ⟦ E ⟧E) (⟦ M ⟧C ∘p ⟦ γ ⟧S)) refl i
⟦ err ⟧C = ℧-mor
⟦ strictness {E = E} i ⟧C = strictness-lemma ⟦ E ⟧E i
⟦ ret ⟧C = η-mor ∘p π2
⟦ ret-β {M = M} i ⟧C = ret-β-lemma ⟦ M ⟧C i
⟦ app ⟧C = App ∘p (π2 ×mor Id)
⟦ fun-β {M = M} i ⟧C =
  eqPMor ((App ∘p (π2 ×mor Id)) ∘p PairFun (PairFun UnitP! (Curry ⟦ M ⟧C ∘p π1)) π2) ⟦ M ⟧C refl i
⟦ matchNat Kz Ks ⟧C = natCase ⟦ Kz ⟧C ⟦ Ks ⟧C
⟦ matchNatβz Kz Ks i ⟧C =
  eqPMor (natCase ⟦ Kz ⟧C ⟦ Ks ⟧C ∘p PairFun Id (K _ zero ∘p UnitP!)) ⟦ Kz ⟧C refl i
⟦ matchNatβs Kz Ks i ⟧C =
  eqPMor (natCase ⟦ Kz ⟧C ⟦ Ks ⟧C ∘p PairFun π1 ((mSuc ∘p π2) ∘p PairFun UnitP! π2)) ⟦ Ks ⟧C refl i
⟦ matchNatη {M = M} i ⟧C =
  eqPMor ⟦ M ⟧C
    (natCase (⟦ M ⟧C ∘p PairFun Id (K _ zero ∘p UnitP!))
             (⟦ M ⟧C ∘p PairFun π1 ((mSuc ∘p π2) ∘p PairFun UnitP! π2)))
    (funExt (λ { (γ , zero) → refl ; (γ , suc n) → refl })) i
