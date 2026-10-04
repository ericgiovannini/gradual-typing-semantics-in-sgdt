{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}

open import Common.Later
module Semantics.Concrete.Perturbation.Kleisli (k : Clock) where 

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_)
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.FreeMonoid as Free

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism

open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Predomain.Monad k
open import Semantics.Concrete.Predomain.MonadCombinators k
import Semantics.Concrete.Predomain.Kleisli k as Kl
open import Semantics.Concrete.Perturbation.Semantic k
open import Semantics.Concrete.Types k as Types -- hiding (U; F; _⟶_)


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓ≤' ℓ≈' ℓM' : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
   
    ℓA₁   ℓ≤A₁   ℓ≈A₁   : Level
    ℓA₁'  ℓ≤A₁'  ℓ≈A₁'  : Level
    ℓA₂   ℓ≤A₂   ℓ≈A₂   : Level
    ℓA₂'  ℓ≤A₂'  ℓ≈A₂'  : Level
    ℓA₃   ℓ≤A₃   ℓ≈A₃   : Level
    ℓA₃'  ℓ≤A₃'  ℓ≈A₃'  : Level

    ℓB₁   ℓ≤B₁   ℓ≈B₁   : Level
    ℓB₁'  ℓ≤B₁'  ℓ≈B₁'  : Level
    ℓB₂   ℓ≤B₂   ℓ≈B₂   : Level
    ℓB₂'  ℓ≤B₂'  ℓ≈B₂'  : Level
    ℓB₃   ℓ≤B₃   ℓ≈B₃   : Level
    ℓB₃'  ℓ≤B₃'  ℓ≈B₃'  : Level


-- open ValTypeStr

-- Actions of Kleisli arrow on perturbations

open IsMonoidHom
nat^op→nat : MonoidHom (NatM ^op) NatM
nat^op→nat .fst n = n
nat^op→nat .snd .presε = refl
nat^op→nat .snd .pres· n m = +-comm m n

FM^op→FM : MonoidHom (Free.FM-1 ^op) Free.FM-1
FM^op→FM = opRec (FM-1-rec (FM-1 ^op) FM-1-gen)

module _
  {M : Monoid ℓ} {N : Monoid ℓ'}
  (ϕ ψ : MonoidHom (M ^op) N)
  where

  op-ind : ϕ ^opHom ≡ ψ ^opHom → ϕ ≡ ψ
  op-ind H = eqMonoidHom ϕ ψ (cong fst H)


Kl-Arrow-Ptb-L : (A : ValType ℓA ℓ≤A ℓ≈A ℓMA) (B : CompType ℓB ℓ≤B ℓ≈B ℓMB) →
  MonoidHom ((PtbC (Types.F A)) ^op) (PtbV (Types.U (A ⟶ B)))
Kl-Arrow-Ptb-L A B = (FP.rec
                        (i₁ ∘hom FM^op→FM) -- nat^op case
                        (i₂ ∘hom i₁))        -- MA^op case
          ∘hom ⊕op -- map out of op

Kl-Arrow-Ptb-R : (A : ValType ℓA ℓ≤A ℓ≈A ℓMA) (B : CompType ℓB ℓ≤B ℓ≈B ℓMB) →
  MonoidHom (PtbV ((Types.U B))) (PtbV (Types.U (A ⟶ B)))
Kl-Arrow-Ptb-R A B = FP.rec
           i₁           -- nat case
           (i₂ ∘hom i₂) -- MB case


-- Coherence lemma:
module _
  {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {B : CompType ℓB ℓ≤B ℓ≈B ℓMB}
  where

  private
    |A| = ValType→Predomain A
    |B| = CompType→ErrorDomain B
    module |B| = ErrorDomainStr (|B| .snd)

  -- Given a syntactic perturbation pFA on FA, we can either:
  -- 
  -- 1. First turn it into a syntactic perturbation of U(A ⟶ B), and
  -- then interpret the result as a semantic perturbation on U(A ⟶ B)
  --
  --          OR
  --
  -- 2. First interpret pFA as a semantic perturbation on FA, and then
  -- turn the result into a semantic perturbation on U(A ⟶ B) via the
  -- Kleisli action on semantic perturbations.
  --
  -- Either way, we should end up with the same semantic perturbation
  -- on U(A ⟶ B).

-- ∀ (pFA : ⟨ PtbC (F A) ⟩) →
  ⟶Kᴸ-lemma :
     (interpV (Types.U (A ⟶ B)) ∘hom (Kl-Arrow-Ptb-L A B)) 
   ≡ (⟶KB-SemPtb {A = |A|} {B = |B|}) ∘hom (interpC (Types.F A) ^opHom)
  ⟶Kᴸ-lemma = op-ind _ _
    (FP.ind
      -- nat case
      (Free.FM-1-ind _ _ (SemPtb≡ {ℓ = level} _ _ (funExt (λ g → eqPMor _ _ (funExt (λ x → sym
        ((ext ⟨ A ⟩ ⟨ B ⟩ |B|.℧ |B|.θ.f (g .PMor.f) (δ* .ErrorDomMor.fun (η-mor .PMor.f x)))
        ≡⟨ cong (ext ⟨ A ⟩ ⟨ B ⟩ |B|.℧ |B|.θ.f (g .PMor.f))
                (ExtAsEDMorphism.Equations-U.ext-η (δ-mor ∘p η-mor) x) ⟩
        (ext ⟨ A ⟩ ⟨ B ⟩ |B|.℧ |B|.θ.f (g .PMor.f) (δ-mor {A = |A|} .PMor.f (η-mor .PMor.f x)))
        ≡⟨ CBPVExt.Equations.ext-δ ⟨ A ⟩ ⟨ B ⟩ |B|.℧ |B|.θ.f (g .PMor.f) (η-mor .PMor.f x) ⟩
        |B|.δ .PMor.f (ext ⟨ A ⟩ ⟨ B ⟩ |B|.℧ |B|.θ.f (g .PMor.f) (η-mor {A = |A|} .PMor.f x))
        ≡⟨ cong (|B|.δ .PMor.f) (CBPVExt.Equations.ext-η ⟨ A ⟩ ⟨ B ⟩ |B|.℧ |B|.θ.f (g .PMor.f) x) ⟩
        |B|.δ .PMor.f (g .PMor.f x) ∎)))))))


      -- MA case
      (eqMonoidHom _ _ (funExt (λ pA → SemPtb≡ {ℓ = level} _ _ (funExt (λ g → eqPMor _ _ (funExt (λ x → sym
        ((ext ⟨ A ⟩ ⟨ B ⟩ |B|.℧ |B|.θ.f (g .PMor.f) (map (iA pA .PMor.f) (η-mor {A = |A|} .PMor.f x)))
        ≡⟨ cong (ext ⟨ A ⟩ ⟨ B ⟩ |B|.℧ |B|.θ.f (g .PMor.f)) (map-η (iA pA .PMor.f) x) ⟩
        (ext ⟨ A ⟩ ⟨ B ⟩ |B|.℧ |B|.θ.f (g .PMor.f) (η-mor {A = |A|} .PMor.f (iA pA .PMor.f x)))
        ≡⟨ CBPVExt.Equations.ext-η ⟨ A ⟩ ⟨ B ⟩ |B|.℧ |B|.θ.f (g .PMor.f) (iA pA .PMor.f x) ⟩
        g .PMor.f (iA pA .PMor.f x) ∎)))))))))
      where
        open CBPVExt
        open ExtAsEDMorphism
        open StrongExtCombinator
        open Map
        open MapProperties
        level : Level
        level = ℓ-max ℓA (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ≤A ℓ≈A) ℓB) ℓ≤B) ℓ≈B)

        iA : ⟨ PtbV A ⟩ → PMor |A| |A|
        iA pA = interpV A .fst pA .fst



{-
LHS:  B.θ (λ t → PMor.f g x)
RHS: 
-}


  -- The same for the right action: both sides send the generator of
  -- the nat component to δ on U(A ⟶ B), and a perturbation pB on B
  -- to post-composition with its interpretation.
  ⟶Kᴿ-lemma :
     (interpV (Types.U (A ⟶ B)) ∘hom (Kl-Arrow-Ptb-R A B))
   ≡ (A⟶K-SemPtb {A = |A|} {B = |B|} ∘hom interpV (Types.U B))
  ⟶Kᴿ-lemma = FP.ind
      -- nat case
      (Free.FM-1-ind _ _ (SemPtb≡ {A = U-ob (|A| ⟶ob |B|)} _ _
        (funExt (λ g → eqPMor {X = |A|} {Y = U-ob |B|} _ _ refl))))

      -- MB case
      (eqMonoidHom _ _ (funExt (λ pB → SemPtb≡ _ _ refl)))



-- Actions of Kleisli product on perturbations

module _
  (A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA) (A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA')
  where

  private
    |A₁| = ValType→Predomain A₁
    |A₂| = ValType→Predomain A₂

  -- The monoid of perturbations on F(A₁ × A₂) is ℕ ⊕ (MA₁ ⊕ MA₂). The
  -- Kleisli product actions send ℕ to the first injection, and MA₁
  -- (resp. MA₂) to the corresponding injection into the second summand.
  Kl-Prod-Ptb-L : MonoidHom (PtbC (Types.F A₁)) (PtbC (Types.F (A₁ Types.× A₂)))
  Kl-Prod-Ptb-L = FP.rec i₁ (i₂ ∘hom i₁)

  Kl-Prod-Ptb-R : MonoidHom (PtbC (Types.F A₂)) (PtbC (Types.F (A₁ Types.× A₂)))
  Kl-Prod-Ptb-R = FP.rec i₁ (i₂ ∘hom i₂)

  -- Coherence lemmas: interpreting the result of the syntactic action
  -- agrees with applying the semantic action to the interpretation.
  -- On the nat generator both sides are δ* on F(A₁ × A₂); on a
  -- perturbation of A₁ (resp. A₂) both sides are F applied to the
  -- perturbation acting on the corresponding component.
  ×Kᴸ-lemma :
      (interpC (Types.F (A₁ Types.× A₂)) ∘hom Kl-Prod-Ptb-L)
    ≡ (×KA-SemPtb {A₁ = |A₁|} {A₂ = |A₂|} ∘hom interpC (Types.F A₁))
  ×Kᴸ-lemma = FP.ind
    (Free.FM-1-ind _ _ (CSemPtb≡ _ _
      (cong (λ ψ → ψ .ErrorDomMor.f .PMor.f) (sym (Kl.KlProdᴸ-δ* |A₁| |A₂|)))))
    (eqMonoidHom _ _ (funExt (λ pA → CSemPtb≡ _ _
      (cong (λ ψ → ψ .ErrorDomMor.f .PMor.f)
            (sym (Kl.KlProdᴸ-F (interpV A₁ .fst pA .fst) |A₂|))))))

  ×Kᴿ-lemma :
      (interpC (Types.F (A₁ Types.× A₂)) ∘hom Kl-Prod-Ptb-R)
    ≡ (A×K-SemPtb {A₁ = |A₁|} {A₂ = |A₂|} ∘hom interpC (Types.F A₂))
  ×Kᴿ-lemma = FP.ind
    (Free.FM-1-ind _ _ (CSemPtb≡ _ _
      (cong (λ ψ → ψ .ErrorDomMor.f .PMor.f) (sym (Kl.KlProdᴿ-δ* |A₁| |A₂|)))))
    (eqMonoidHom _ _ (funExt (λ pA → CSemPtb≡ _ _
      (cong (λ ψ → ψ .ErrorDomMor.f .PMor.f)
            (sym (Kl.KlProdᴿ-F |A₁| (interpV A₂ .fst pA .fst)))))))
