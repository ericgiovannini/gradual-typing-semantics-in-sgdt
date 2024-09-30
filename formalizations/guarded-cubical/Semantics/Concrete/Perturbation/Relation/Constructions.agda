{- Extension of pertubrations from types to relations, and push-pull -}
{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
module Semantics.Concrete.Perturbation.Relation.Constructions (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_)
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary.Base


open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.Instances.CartesianProduct as Cart
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Sigma
open import Cubical.Algebra.Monoid.Displayed.Instances.Reindex

open import Common.Common
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions hiding (π1; π2)
open import Semantics.Concrete.DoublePoset.DPMorRelation as PRel hiding (⊎-inl ; ⊎-inr)
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.DblPosetCombinators hiding (U)
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.KleisliFunctors k
open import Semantics.Concrete.DoublePoset.MonadCombinators k

open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Types k as Types hiding (U; F; _⟶_)
--open import Semantics.Concrete.Perturbation.Relation.Base k
open import Semantics.Concrete.Perturbation.Relation.Alt k


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓ≤' ℓ≈' ℓM' : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓc ℓc' ℓd ℓd' : Level
  
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

    ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ : Level
    ℓAₒ ℓ≤Aₒ ℓ≈Aₒ : Level
    ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ : Level
    ℓBₒ ℓ≤Bₒ ℓ≈Bₒ : Level
   
    ℓc₁ ℓc₂ ℓc₃  : Level
    ℓd₁ ℓd₂ ℓd₃  : Level

    ℓMA₁ ℓMA₂ ℓMA₃ : Level
    ℓMA₁' ℓMA₂' ℓMA₃' : Level
    ℓMB₁ ℓMB₂ ℓMB₃ : Level
    ℓMAᵢ ℓMAₒ ℓMBᵢ ℓMBₒ : Level

-- open ValTypeStr
open MonoidStr
open IsMonoidHom
open IsSemigroup
open IsMonoid

-- identity and composition for value and comp relations
module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} where
  private
    iA = interpV A .fst
  IdRelV : VRelPP A A _
  IdRelV = mkVRelPP A A
    (idPRel _)
    (corecL (idMon _) (corecVRelPtb (λ pA → Predom-IdSqH (iA pA .fst))))
    (corecR (idMon _) (corecVRelPtb (λ pA → Predom-IdSqH (iA pA .fst))))

module _ {B : CompType ℓB ℓ≤B ℓ≈B ℓMB} where
  private
    iB = interpC B .fst
  IdRelC : CRelPP B B _
  IdRelC = mkCRelPP B B
    (idEDRel _)
    (corecL (idMon _) (corecCRelPtb (λ pB → ED-IdSqH (iB pB .fst))))
    (corecR (idMon _) (corecCRelPtb (λ pB → ED-IdSqH (iB pB .fst))))


module _
  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁} {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂} {A₃ : ValType ℓA₃ ℓ≤A₃ ℓ≈A₃ ℓMA₃}
  (c₁ : VRelPP A₁ A₂ ℓc₁)
  (c₂ : VRelPP A₂ A₃ ℓc₂)
  where

  private
    iA₁ = interpV A₁ .fst
    iA₂ = interpV A₂ .fst
    iA₃ = interpV A₃ .fst

  ⊙V : VRelPP A₁ A₃ _
  ⊙V = mkVRelPP _ _
    (VRelPP→PredomainRel c₁ ⊙ VRelPP→PredomainRel c₂)
    (corecL (pushV c₂ ∘hom pushV c₁) (corecVRelPtb (λ pA₁ →
      CompSqH
        {cᵢ₁ = c₁ .fst}
        {cᵢ₂ = c₂ .fst}
        {cₒ₁ = c₁ .fst}
        {cₒ₂ = c₂ .fst}
        {f = iA₁ pA₁ .fst}
        {g = iA₂ (pushV c₁ .fst pA₁) .fst}
        {h = iA₃ (pushV c₂ .fst _) .fst}
        (pushVSq c₁ pA₁) (pushVSq c₂ _))))
    (corecR (pullV c₁ ∘hom pullV c₂) (corecVRelPtb (λ pA₃ →
      CompSqH
        {cᵢ₁ = c₁ .fst}
        {cᵢ₂ = c₂ .fst}
        {cₒ₁ = c₁ .fst}
        {cₒ₂ = c₂ .fst}
        {f = iA₁ (pullV c₁ .fst _) .fst}
        {g = iA₂ (pullV c₂ .fst pA₃) .fst}
        {h = iA₃ pA₃ .fst}
        (pullVSq c₁ _) (pullVSq c₂ pA₃))))


module _
  {B₁ : CompType ℓB₁ ℓ≤B₁ ℓ≈B₁ ℓMB₁}
  {B₂ : CompType ℓB₂ ℓ≤B₂ ℓ≈B₂ ℓMB₂}
  {B₃ : CompType ℓB₃ ℓ≤B₃ ℓ≈B₃ ℓMB₃}
  (d₁ : CRelPP B₁ B₂ ℓd₁)
  (d₂ : CRelPP B₂ B₃ ℓd₂)
  where

  private
    iB₁ = B₁ .snd .snd .snd .fst
    iB₂ = B₂ .snd .snd .snd .fst
    iB₃ = B₃ .snd .snd .snd .fst

  ⊙C : CRelPP B₁ B₃ _
  ⊙C = mkCRelPP _ _
    (CRelPP→ErrorDomRel d₁ ⊙ed CRelPP→ErrorDomRel d₂)
    (corecL {Mᴰ = CRelPtb B₁ B₃ _} (pushC d₂ ∘hom pushC d₁) (corecCRelPtb (λ pB₁ →
      ED-CompSqH
        {ϕ₁ = iB₁ pB₁ .fst}
        {ϕ₂ = iB₂ _ .fst}
        {ϕ₃ = iB₃ _ .fst}
        (pushCSq d₁ _)
        (pushCSq d₂ _))))
    (corecR {Mᴰ = CRelPtb B₁ B₃ _} (pullC d₁ ∘hom pullC d₂) (corecCRelPtb (λ pB₃ →
      ED-CompSqH
        {ϕ₁ = iB₁ _ .fst}
        {ϕ₂ = iB₂ _ .fst}
        {ϕ₃ = iB₃ pB₃ .fst}
        (pullCSq d₁ _)
        (pullCSq d₂ _))))



module _  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁}{A₁' : ValType ℓA₁' ℓ≤A₁' ℓ≈A₁' ℓMA₁'}
          {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂}{A₂' : ValType ℓA₂' ℓ≤A₂' ℓ≈A₂' ℓMA₂'}
  where
  _×PP_ : (c₁ : VRelPP A₁ A₁' ℓc₁) (c₂ : VRelPP A₂ A₂' ℓc₂)
        → VRelPP (A₁ Types.× A₂) (A₁' Types.× A₂') _
  c₁ ×PP c₂ = mkVRelPP _ _
    (VRelPP→PredomainRel c₁ ×pbmonrel VRelPP→PredomainRel c₂)
    
    -- push
    (FP.elim
      (Σl (VRelPtb (A₁ Types.× A₂) (A₁' Types.× A₂') _))
      -- (corecL (i₁ ∘hom pushV c₁) (corecVRelPtb (λ pA₁ → ×-Sq (pushVSq c₁ pA₁) (Predom-IdSqV (VRelPP→PredomainRel c₂)))))
      (corecL (i₁ ∘hom pushV c₁) (corecVRelPtb (λ pA₁ (a₁ , a₂) (a₁' , a₂') ×-rel →
        pushVSq c₁ pA₁ _ _ (×-rel .fst) , ×-rel .snd)))
      (corecL (i₂ ∘hom pushV c₂) (corecVRelPtb (λ pA₂ (a₁ , a₂) (a₁' , a₂') ×-rel →
        (×-rel .fst) , (pushVSq c₂ pA₂ _ _ (×-rel .snd))))))

    -- pull
    (FP.elim
      (Σr (VRelPtb (A₁ Types.× A₂) (A₁' Types.× A₂') _))
      (corecR (i₁ ∘hom pullV c₁) (corecVRelPtb (λ pA₁' _ _ ×-rel →
        pullVSq c₁ pA₁' _ _ (×-rel .fst) , ×-rel .snd )))
      (corecR (i₂ ∘hom pullV c₂) (corecVRelPtb (λ pA₂' _ _ ×-rel →
        ×-rel .fst , pullVSq c₂ pA₂' _ _ (×-rel .snd)))))

module _
  {A : ValType ℓA ℓ≤A ℓ≈A ℓMA}{A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  {B : CompType ℓB ℓ≤B ℓ≈B ℓMB}{B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
  where
  _⟶_ : VRelPP A A' ℓc → CRelPP B B' ℓd → CRelPP (A Types.⟶ B) (A' Types.⟶ B') _
  c ⟶ d = mkCRelPP _ _
    (VRelPP→PredomainRel c ⟶rel CRelPP→ErrorDomRel d)

    -- push
    (FP.elim (Σl (CRelPtb (A Types.⟶ B) (A' Types.⟶ B') _))
      (corecL (i₁ ∘hom (pushV c ^opHom)) (corecCRelPtb (λ pA f f' f~f' a a a~a' →
        f~f' _ _ (pushVSq c pA _ _ a~a'))))
      (corecL (i₂ ∘hom pushC d) (corecCRelPtb (λ pB f f' f~f' a a' a~a' →
        pushCSq d pB _ _ (f~f' _ _ a~a')))))

    -- pull
    (FP.elim (Σr (CRelPtb (A Types.⟶ B) (A' Types.⟶ B') _))
      (corecR (i₁ ∘hom (pullV c ^opHom)) (corecCRelPtb (λ pA f f' f~f' a a a~a' →
        f~f' _ _ (pullVSq c pA _ _ a~a'))))
      (corecR (i₂ ∘hom pullC d) (corecCRelPtb (λ pB' f f' f~f' a a' a~a' →
        pullCSq d pB' _ _ (f~f' _ _ a~a')))))



module _ {B : CompType ℓB ℓ≤B ℓ≈B ℓMB}{B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
  where
  private
    module B = ErrorDomainStr (B .snd .fst)
    module B' = ErrorDomainStr (B .snd .fst)
    open ErrorDomRel
    
  U : CRelPP B B' ℓd → VRelPP (Types.U B) (Types.U B') _
  U d = mkVRelPP (Types.U B) (Types.U B') (U-rel |d|)
    -- push
    (FP.elim (Σl VRelPtb-Ud)
      -- Nat case
      (elimNatLS i₁ (Σl VRelPtb-Ud) (i₁ .fst 1 ,
        Sq→VRelPtb (Types.U B) (Types.U B') (U-rel |d|)
          (λ b b' bRb' → |d| .Rθ (next b) (next b') (next bRb'))))

      -- MB case
      (corecL (i₂ ∘hom pushC d) (corecVRelPtb (λ pB b b' bRb' → pushCSq d pB _ _ bRb'))))

    -- pull
    (FP.elim (Σr VRelPtb-Ud)
      -- Nat case
      (elimNatLS i₁ (Σr VRelPtb-Ud) (i₁ .fst 1 ,
        Sq→VRelPtb (Types.U B) (Types.U B') (U-rel |d|)
          (λ b b' bRb' → |d| .Rθ (next b) (next b') (next bRb'))))

      -- MB' case
      (corecR (i₂ ∘hom pullC d) (corecVRelPtb (λ pB b b' bRb' → pullCSq d pB _ _ bRb'))))
    where
      |d| = CRelPP→ErrorDomRel d
      VRelPtb-Ud = VRelPtb (Types.U B) (Types.U B') (U-rel |d|)



module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA}{A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  where
  open F-rel
  open F-sq
  F : VRelPP A A' ℓc → CRelPP (Types.F A) (Types.F A') _
  F c = mkCRelPP (Types.F A) (Types.F A') (F-rel |c|)
    -- push
    (FP.elim (Σl CRelPtb-Fc)
      (corecL i₁ (elimNatLS (Cart.corec i₁ i₁) CRelPtb-Fc (Sq→CRelPtb _ _ (F-rel |c|) (δ*Sq (c .fst)))))
      (corecL (i₂ ∘hom pushV c) (corecCRelPtb push-sq)))

    -- pull
    (FP.elim (Σr (CRelPtb (Types.F A) (Types.F A') _))
      (elimNatLS i₁ _ ((i₁ .fst 1) , Sq→CRelPtb (Types.F A) (Types.F A') _ (δ*Sq (c .fst))))
      (corecR (i₂ ∘hom pullV c) (corecCRelPtb pull-sq )))
      where
        |c| = VRelPP→PredomainRel c
        CRelPtb-Fc = CRelPtb (Types.F A) (Types.F A') (F-rel |c|)
        
        push-sq : ∀ pA → CRelPtbSq (Types.F A) (Types.F A') (F-rel |c|) (i₂ .fst pA) ((i₂ ∘hom pushV c) .fst pA)
        push-sq pA = F-sq |c| |c| (interpV A .fst pA .fst) (interpV A' .fst _ .fst) (pushVSq c pA)

        pull-sq : ∀ pA' → CRelPtbSq (Types.F A) (Types.F A') (F-rel |c|) ((i₂ ∘hom pullV c) .fst pA') (i₂ .fst pA')
        pull-sq pA' = F-sq |c| |c| (interpV A .fst _ .fst) (interpV A' .fst pA' .fst) (pullVSq c pA')

     -- F-sq (c .fst) (c .fst)
     --       (interpV A .fst pA .fst) (interpV A' .fst _ .fst)
     --       (pushVSq c pA)))))

{-
  F c .fst = F-rel (c .fst) where open F-rel
  F c .snd .fst = elimSection _
    (elimNat _ _ (((i₁ .fst 1) , i₁ .fst 1 , δ*Sq (c .fst)) , refl))
    (corecCFact1 _ _ _ (i₂ ∘hom pushV c) λ pA →
      F-sq (c .fst) (c .fst)
           (interpV A .fst pA .fst) (interpV A' .fst _ .fst)
           (pushVSq c pA))

  F c .snd .snd = elimSection _
    (elimNat _ _ (((i₁ .fst 1) , ((i₁ .fst 1) , (δ*Sq (c .fst)))) , refl))
    (corecCFact2 _ _ _ (i₂ ∘hom pullV c) (λ pA' →
      F-sq (c .fst) (c .fst)
           (interpV A .fst _ .fst) (interpV A' .fst _ .fst)
           (pullVSq c pA')))
-}


-- Injections for coproduct
-- Note that this is not the action of the coproduct on push-pull relations!
module _  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁}
          {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂}
  where
  private
    |A₁| = ValType→Predomain A₁
    |A₂| = ValType→Predomain A₂

    module |A₁| = PosetBisimStr (|A₁| .snd)
    module |A₂| = PosetBisimStr (|A₂| .snd)
    
    module MA₁ = MonoidStr (PtbV A₁ .snd)
    module MA₂ = MonoidStr (PtbV A₂ .snd)

    module iA₁ = IsMonoidHom (interpV A₁ .snd)
    module iA₂ = IsMonoidHom (interpV A₂ .snd)
    
  ⊎-inl : VRelPP A₁ (A₁ Types.⊎ A₂) _
  ⊎-inl = mkVRelPP A₁ (A₁ Types.⊎ A₂) (PRel.⊎-inl |A₁| |A₂|)
    -- Push
    (corecL i₁ (corecVRelPtb sq1))

    -- Pull
    (FP.elim (Σr (VRelPtb A₁ (A₁ Types.⊎ A₂) (PRel.⊎-inl |A₁| |A₂|)))

      -- Case inl
      (corecR (idMon (PtbV A₁)) (corecVRelPtb sq1))

      -- Case inr
      (corecR ε-hom (corecVRelPtb sq2)))
    where
      sq1 : ∀ (pA₁ : ⟨ PtbV A₁ ⟩) →
        VRelPtbSq A₁ (A₁ Types.⊎ A₂) (PRel.⊎-inl _ _) pA₁ (i₁ .fst pA₁)
      sq1 pA₁ x (inl y) xRy = lift (interpV A₁ .fst pA₁ .fst .PBMor.isMon (lower xRy))

      sq2 : ∀ (pA₂ : ⟨ PtbV A₂ ⟩) →
        VRelPtbSq A₁ (A₁ Types.⊎ A₂) (PRel.⊎-inl _ _) (ε-hom .fst pA₂) (i₂ .fst pA₂)
      sq2 pA₂ x (inl y) xRy = lift
        (transport
          (λ i → (sym iA₁.presε i .fst .PBMor.f x) |A₁|.≤ y)
          (lower xRy))

  ⊎-inr : VRelPP A₂ (A₁ Types.⊎ A₂) _
  ⊎-inr = mkVRelPP A₂ (A₁ Types.⊎ A₂) (PRel.⊎-inr |A₁| |A₂|)
  -- Push
    (corecL i₂ (corecVRelPtb sq2))

  -- Pull
    (FP.elim (Σr (VRelPtb A₂ (A₁ Types.⊎ A₂) (PRel.⊎-inr |A₁| |A₂|)))

      -- Case inl
      (corecR ε-hom (corecVRelPtb sq1))

      -- Case inr
      (corecR (idMon (PtbV A₂)) (corecVRelPtb sq2)))
    where
    sq1 : ∀ (pA₁ : ⟨ PtbV A₁ ⟩) →
      VRelPtbSq A₂ (A₁ Types.⊎ A₂) (PRel.⊎-inr _ _) (ε-hom .fst pA₁) (i₁ .fst pA₁)
    sq1 pA₁ x (inr y) xRy = lift
      (transport
        (λ i → (sym iA₂.presε i .fst .PBMor.f x) |A₂|.≤ y)
        (lower xRy))

    sq2 : ∀ (pA₂ : ⟨ PtbV A₂ ⟩) →
      VRelPtbSq A₂ (A₁ Types.⊎ A₂) (PRel.⊎-inr _ _) pA₂ (i₂ .fst pA₂)
    sq2 pA₂ x (inr y) xRy = lift (interpV A₂ .fst pA₂ .fst .PBMor.isMon (lower xRy))

-- TODO: inj-arr , inj-× , inj-nat

module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA}
  where

  private
    module C = ClockedCombinators k
    iA = interpV A

  Next : VRelPP A (V▹ A) ℓ≤A
  Next = mkVRelPP _ _
    (relNext (ValType→Predomain A))

    -- push
    (corecL (idMon _) (corecVRelPtb (λ pA →
      λ x y~ H t → PBMor.isMon (iA .fst pA .fst) (H t)))) -- NTS: (iA pA x) ⊑A (iA pA (y~ t))

    -- pull
    (corecR (idMon _) (corecVRelPtb (λ pA →
      λ x y~ H t → PBMor.isMon (iA .fst pA .fst) (H t))))

  Next .snd .snd = corecVFact2 A (V▹ A) (Next .fst) (idMon _)
    λ pA → λ x y~ H t → PBMor.isMon (iA .fst pA .fst) (H t)

