{- Extension of pertubrations from types to relations, and push-pull -}
{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

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

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism

open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.Monad k
open import Semantics.Concrete.DoublePoset.MonadCombinators k
import Semantics.Concrete.DoublePoset.KleisliFunctors k as Kl
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
   ≡ (⟶KB-PrePtb {A = |A|} {B = |B|}) ∘hom (interpC (Types.F A) ^opHom)
  ⟶Kᴸ-lemma = op-ind _ _
    (FP.ind
      -- nat case
      (Free.FM-1-ind _ _ (PrePtb≡ {ℓ = level} _ _ (funExt (λ g → eqPBMor _ _ (funExt (λ x → sym
        ((ext ⟨ A ⟩ ⟨ B ⟩ |B|.℧ |B|.θ.f (g .PBMor.f) (δ* .ErrorDomMor.fun (η-mor .PBMor.f x)))
        ≡⟨ {!!} ⟩
        (ext ⟨ A ⟩ ⟨ B ⟩ |B|.℧ |B|.θ.f (g .PBMor.f) (δ-mor {A = |A|} .PBMor.f (η-mor .PBMor.f x)))
        ≡⟨ {!!} ⟩
        |B|.δ .PBMor.f (ext ⟨ A ⟩ ⟨ B ⟩ |B|.℧ |B|.θ.f (g .PBMor.f) (η-mor {A = |A|} .PBMor.f x)) 
        ≡⟨ {!!} ⟩
        |B|.δ .PBMor.f (g .PBMor.f x) ∎)))))))
       

      -- MA case
      {!!})
      where
        open CBPVExt
        open ExtAsEDMorphism
        open StrongExtCombinator
        level : Level
        level = ℓ-max ℓA (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ≤A ℓ≈A) ℓB) ℓ≤B) ℓ≈B)



{-
LHS:  B.θ (λ t → PBMor.f g x)
RHS: 
-}


{-
  ⟶Kᴿ-lemma :
     (interpV (Types.U (A ⟶ B)) ∘hom (Kl-Arrow-Ptb-R A B))
   ≡ (A⟶K-PrePtb {A = |A|} {B = |B|} ∘hom interpV (Types.U B))
  ⟶Kᴿ-lemma = FP.ind
      -- nat case
      (NatM-ind _ _ (PrePtb≡ _ _ (funExt (λ g →
        eqPBMor (((interpV (U (A ⟶ B)) ∘hom Kl-Arrow-Ptb-R A B) ∘hom i₁) .fst 1 .fst .PBMor.f g) _ refl))))

      -- MB case
      (eqMonoidHom _ _ (funExt (λ pB → PrePtb≡ _ _ refl)))

  
-}

--  MonoidHom ((CEndo (F-ob A)) ^op) (Endo (U-ob (A ⟶ob B)))



-- Actions of Kleisli product on perturbations
