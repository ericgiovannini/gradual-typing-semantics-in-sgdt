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
open import Cubical.Data.Sigma as Sig hiding (_×_)
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_)
open import Cubical.Data.Sum as Sum hiding (_⊎_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary


open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.Instances.CartesianProduct as Cart hiding (_×_)
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.FreeProduct.Indexed as IFP
open import Cubical.Algebra.Monoid.FreeMonoid as Free
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Sigma
open import Cubical.Algebra.Monoid.Displayed.Instances.Reindex

open import Common.Common
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Convenience
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions hiding (π1; π2)
open import Semantics.Concrete.Predomain.Relation as PRel hiding (⊎-inl ; ⊎-inr)
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.Combinators hiding (U)
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Predomain.Kleisli k
open import Semantics.Concrete.Predomain.MonadCombinators k

open import Semantics.Concrete.Perturbation.Semantic k
open import Semantics.Concrete.Types k as Types hiding (U; F; _⟶_ ; _×_ ; _⊎_)
open import Semantics.Concrete.Perturbation.Relation.Base k


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



-- Action of × on push-pull
module _  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁}{A₁' : ValType ℓA₁' ℓ≤A₁' ℓ≈A₁' ℓMA₁'}
          {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂}{A₂' : ValType ℓA₂' ℓ≤A₂' ℓ≈A₂' ℓMA₂'}
  where
  _×_ : (c₁ : VRelPP A₁ A₁' ℓc₁) (c₂ : VRelPP A₂ A₂' ℓc₂)
        → VRelPP (A₁ Types.× A₂) (A₁' Types.× A₂') _
  c₁ × c₂ = mkVRelPP _ _
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


-- Action of ⊎ on push-pull
module _  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁} {A₁' : ValType ℓA₁' ℓ≤A₁' ℓ≈A₁' ℓMA₁'}
          {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂} {A₂' : ValType ℓA₂' ℓ≤A₂' ℓ≈A₂' ℓMA₂'}   
  where

  private
    A₁⊎A₂ = A₁ Types.⊎ A₂
    A₁'⊎A₂' = A₁' Types.⊎ A₂'
    |A₁⊎A₂| = ValType→Predomain A₁ ⊎p ValType→Predomain A₂
    |A₁'⊎A₂'| = ValType→Predomain A₁' ⊎p ValType→Predomain A₂'

  _⊎_ : (c₁ : VRelPP A₁ A₁' ℓc₁) (c₂ : VRelPP A₂ A₂' ℓc₂)
    → VRelPP (A₁ Types.⊎ A₂) (A₁' Types.⊎ A₂') (ℓ-max ℓc₁ ℓc₂)
  c₁ ⊎ c₂ = mkVRelPP _ _ |c₁⊎c₂|

    -- push
    (FP.elim (Σl (VRelPtb (A₁ Types.⊎ A₂) (A₁' Types.⊎ A₂') _))

      (corecL (i₁ ∘hom pushV c₁) (corecVRelPtb (λ pA₁ → push-sq₁ pA₁)))

      (corecL (i₂ ∘hom pushV c₂) (corecVRelPtb (λ pA₂ → push-sq₂ pA₂))))

    -- pull
    (FP.elim (Σr (VRelPtb (A₁ Types.⊎ A₂) (A₁' Types.⊎ A₂') _))

      (corecR (i₁ ∘hom pullV c₁) (corecVRelPtb (λ pA₁' → pull-sq₁ pA₁')))

      (corecR (i₂ ∘hom pullV c₂) (corecVRelPtb (λ pA₂' → pull-sq₂ pA₂'))))
      where
        |c₁⊎c₂| = (VRelPP→PredomainRel c₁ PRel.⊎-rel VRelPP→PredomainRel c₂)

        push-sq₁ : ∀ pA₁ → VRelPtbSq A₁⊎A₂ A₁'⊎A₂' |c₁⊎c₂| (i₁ .fst pA₁) ((i₁ ∘hom pushV c₁) .fst pA₁)
        push-sq₁ pA₁ = (pushVSq c₁ pA₁) ⊎-Sq (Predom-IdSqV (VRelPP→PredomainRel c₂))

        push-sq₂ : ∀ pA₂ → VRelPtbSq A₁⊎A₂ A₁'⊎A₂' |c₁⊎c₂| (i₂ .fst pA₂) ((i₂ ∘hom pushV c₂) .fst pA₂)
        push-sq₂ pA₂ = (Predom-IdSqV (VRelPP→PredomainRel c₁)) ⊎-Sq (pushVSq c₂ pA₂)

        pull-sq₁ : ∀ pA₁' → VRelPtbSq A₁⊎A₂ A₁'⊎A₂' |c₁⊎c₂| ((i₁ ∘hom pullV c₁) .fst pA₁') (i₁ .fst pA₁')
        pull-sq₁ pA₁' = (pullVSq c₁ pA₁') ⊎-Sq (Predom-IdSqV (VRelPP→PredomainRel c₂))

        pull-sq₂ : ∀ pA₂' → VRelPtbSq A₁⊎A₂ A₁'⊎A₂' |c₁⊎c₂| ((i₂ ∘hom pullV c₂) .fst pA₂') (i₂ .fst pA₂')
        pull-sq₂ pA₂' = (Predom-IdSqV (VRelPP→PredomainRel c₁)) ⊎-Sq (pullVSq c₂ pA₂')


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
      (Free.FM-1-elimLocal i₁ (Σl VRelPtb-Ud) (i₁ .fst FM-1-gen ,
        Sq→VRelPtb (Types.U B) (Types.U B') (U-rel |d|)
          (λ b b' bRb' → |d| .Rθ (next b) (next b') (next bRb'))))

      -- MB case
      (corecL (i₂ ∘hom pushC d) (corecVRelPtb (λ pB b b' bRb' → pushCSq d pB _ _ bRb'))))

    -- pull
    (FP.elim (Σr VRelPtb-Ud)
      -- Nat case
      (Free.FM-1-elimLocal i₁ (Σr VRelPtb-Ud) (i₁ .fst FM-1-gen ,
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
      (corecL i₁ (Free.FM-1-elimLocal (Cart.corec i₁ i₁) CRelPtb-Fc (Sq→CRelPtb _ _ (F-rel |c|) (δ*Sq (c .fst)))))
      (corecL (i₂ ∘hom pushV c) (corecCRelPtb push-sq)))

    -- pull
    (FP.elim (Σr (CRelPtb (Types.F A) (Types.F A') _))
      (Free.FM-1-elimLocal i₁ _ ((i₁ .fst Free.FM-1-gen) , Sq→CRelPtb (Types.F A) (Types.F A') _ (δ*Sq (c .fst))))
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

    module |A₁| = PredomainStr (|A₁| .snd)
    module |A₂| = PredomainStr (|A₂| .snd)
    
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
      sq1 pA₁ x (inl y) xRy = lift (interpV A₁ .fst pA₁ .fst .PMor.isMon (lower xRy))

      sq2 : ∀ (pA₂ : ⟨ PtbV A₂ ⟩) →
        VRelPtbSq A₁ (A₁ Types.⊎ A₂) (PRel.⊎-inl _ _) (ε-hom .fst pA₂) (i₂ .fst pA₂)
      sq2 pA₂ x (inl y) xRy = lift
        (transport
          (λ i → (sym iA₁.presε i .fst .PMor.f x) |A₁|.≤ y)
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
        (λ i → (sym iA₂.presε i .fst .PMor.f x) |A₂|.≤ y)
        (lower xRy))

    sq2 : ∀ (pA₂ : ⟨ PtbV A₂ ⟩) →
      VRelPtbSq A₂ (A₁ Types.⊎ A₂) (PRel.⊎-inr _ _) pA₂ (i₂ .fst pA₂)
    sq2 pA₂ x (inr y) xRy = lift (interpV A₂ .fst pA₂ .fst .PMor.isMon (lower xRy))



{-
module _ {ℓX₁ ℓX₂ : Level}
  (X₁ : DiscreteTy ℓX₁)
  (X₂ : DiscreteTy ℓX₂)
  (A₁ : ⟨ X₁ ⟩ → ValType ℓA ℓ≤A ℓ≈A ℓMA)
  (A₂ : ⟨ X₂ ⟩ → ValType ℓA ℓ≤A ℓ≈A ℓMA)
  where

  private
    X₁⊎X₂ : DiscreteTy (ℓ-max ℓX₁ ℓX₂)
    X₁⊎X₂ = (⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩ , Sum.discrete⊎ (X₁ .snd) (X₂ .snd))

    Sigma₁ = ΣV X₁ A₁
    Sigma₂ = ΣV X₂ A₂
   
    Sum = Sigma₁ Types.⊎ Sigma₂

    Sigma : ValType _ _ _ _
    Sigma = ΣV X₁⊎X₂ (Sum.rec A₁ A₂)

    X₁Set : hSet ℓX₁
    X₁Set = (⟨ X₁ ⟩ , Discrete→isSet (X₁ .snd))

    X₂Set : hSet ℓX₂
    X₂Set = (⟨ X₂ ⟩ , Discrete→isSet (X₂ .snd))

    fun : PMor (ValType→Predomain (Sigma₁ Types.⊎ Sigma₂)) (ValType→Predomain Sigma)
    fun =  ⊎p-rec
        (Σ-mor' X₁Set ((⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩) , Discrete→isSet (X₁⊎X₂ .snd)) Sum.inl _ _ (λ x₁ → Id))
        (Σ-mor' X₂Set ((⟨ X₁ ⟩ Sum.⊎ ⟨ X₂ ⟩) , Discrete→isSet (X₁⊎X₂ .snd)) Sum.inr _ _ (λ x₂ → Id))

    iSum = fst ∘ interpV Sum .fst
    iSigma = fst ∘ interpV Sigma .fst

    rA₁ : (x₁ : ⟨ X₁ ⟩) → _
    rA₁ x₁ = idPRel (ValType→Predomain (A₁ x₁))

    rA₂ : (x₂ : ⟨ X₂ ⟩) → _
    rA₂ x₂ = idPRel (ValType→Predomain (A₂ x₂))

  opaque
    unfolding IFP.rec IFP.elim IFP.elimLocal
    relPP-Σ⊎Σ-Σ : VRelPP (Sigma₁ Types.⊎ Sigma₂) Sigma (ℓ-max (ℓ-max ℓX₁ ℓX₂) ℓ≤A)
    relPP-Σ⊎Σ-Σ = mkVRelPP _ _ relation
      (FP.elim (Σl _)
        (IFP.elimLocal _ _ _ _ λ x₁ → corecL (IFP.σ _ _ (Sum.inl x₁)) {!!})
        (IFP.elimLocal _ _ _ _ λ x₂ → corecL (IFP.σ _ _ (Sum.inr x₂)) {!!}))

      (IFP.elim (X₁⊎X₂ .fst) (λ x → PtbV (Sum.rec A₁ A₂ x)) (Σr (VRelPtb (Sigma₁ Types.⊎ Sigma₂) Sigma _))
        (Sum.elim
          (λ x₁ → corecR (i₁ ∘hom IFP.σ _ _ x₁) (corecVRelPtb (λ pA₁ → pull-sq₁ x₁ pA₁)))
          (λ x₂ → corecR (i₂ ∘hom IFP.σ _ _ x₂) (corecVRelPtb (λ pA₂ → pull-sq₂ x₂ pA₂)))))
          where
            relation : PRel (ValType→Predomain (Sigma₁ Types.⊎ Sigma₂)) (ValType→Predomain Sigma)
              (ℓ-max (ℓ-max ℓX₁ ℓX₂) ℓ≤A)
            relation = (functionalRel fun Id (idPRel (ValType→Predomain Sigma)))
            
            pull-sq₁ : ∀ (x₁ : ⟨ X₁ ⟩) (pA₁ : ⟨ PtbV (A₁ x₁) ⟩) →
              PSq relation relation
                (iSum (i₁ .fst (IFP.σ _ _ x₁ .fst pA₁))) (iSigma (IFP.σ _ _ (inl x₁) .fst pA₁))
            pull-sq₁ x₁ pA₁ (inl (x₁' , a₁')) (inl x₁'' , a'') (eq , rel) = eq , {!!} --aux (X₁ .snd x₁ x₁')
              where
                aux : ∀ (x₁≡x₁'? : Dec (x₁ ≡ x₁')) → rA₁ x₁'' .PRel.R
                  ((subst (λ x → ⟨ ValType→Predomain (Sum.rec A₁ A₂ x) ⟩) eq
                  (PMor.f fun (iSum (i₁ .fst (|⊕ᵢ|.gen x₁ pA₁)) .PMor.f (inl (x₁' , a₁'))) .snd)))
                  
                  ((iSigma (|⊕ᵢ|.gen (inl x₁) pA₁) .PMor.f (inl x₁'' , a'') .snd))
                aux (yes eq) = {!!}
                aux (no neq) = {!!}
            pull-sq₁ x₁ pA₁ (inl (x₁' , a₁')) (inr x₂ , a₂) (eq , rel) = ⊥.rec (inl≠inr _ _ eq) 
            pull-sq₁ x₁ pA₁ (inr (x₂ , a')) (inl x₁' , a'') (eq , rel) = ⊥.rec (inl≠inr _ _ (sym eq))
            pull-sq₁ x₁ pA₁ (inr (x₂ , a')) (inr x₂' , a'') (eq , rel) = eq , {!!}

            pull-sq₂ : ∀ (x₂ : ⟨ X₂ ⟩) (pA₂ : ⟨ PtbV (A₂ x₂) ⟩) →
              PSq relation relation
                (iSum (i₂ .fst (IFP.σ _ _ x₂ .fst pA₂))) (iSigma (IFP.σ _ _ (inr x₂) .fst pA₂))
            pull-sq₂ = {!!}
-}               
  
  
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
      λ x y~ H t → PMor.isMon (iA .fst pA .fst) (H t)))) -- NTS: (iA pA x) ⊑A (iA pA (y~ t))

    -- pull
    (corecR (idMon _) (corecVRelPtb (λ pA →
      λ x y~ H t → PMor.isMon (iA .fst pA .fst) (H t))))



module _
  {A  : ValType ℓA  ℓ≤A  ℓ≈A  ℓMA}
  {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  (isom : PredomIso (ValType→Predomain A) (ValType→Predomain A'))
  (M→M' : MonoidHom (PtbV A) (PtbV A'))
  (M'→M : MonoidHom (PtbV A') (PtbV A))
  where
    private
      module isom = PredomIso isom
      𝔸 = ValType→Predomain A
      𝔸' = ValType→Predomain A'
      rA = idPRel 𝔸
      rA' = idPRel 𝔸'
      iA  = fst ∘ interpV A  .fst
      iA' = fst ∘ interpV A' .fst

      rel : PRel 𝔸 𝔸' ℓ≤A'
      rel = (functionalRel isom.fun Id rA')

      RHS₁ = PredomIso→EndoHom (PredomIso-Inv isom)
              ∘hom (interpV A')
              ∘hom M→M'

      RHS₂ = PredomIso→EndoHom isom
               ∘hom interpV A
               ∘hom M'→M

    Iso→PredomRel : PRel 𝔸 𝔸' ℓ≤A'
    Iso→PredomRel = rel

    module _
      (eq₁ : interpV A  ≡ RHS₁)
      (eq₂ : interpV A' ≡ RHS₂)
      where
      eq₁' : ∀ pA → (interpV A .fst pA .fst) ≡ (RHS₁ .fst pA .fst)
      eq₁' pA = cong fst (funExt⁻ (cong fst eq₁) pA)

      eq₂' : ∀ pA' → (interpV A' .fst pA' .fst) ≡ (RHS₂ .fst pA' .fst)
      eq₂' pA' = cong fst (funExt⁻ (cong fst eq₂) pA')

      pushSq : ∀ pA → VRelPtbSq A A' rel pA (M→M' .fst pA)
      pushSq pA = subst (λ z → PSq rel rel z (Id ∘p (iA' pushed ∘p Id))) (sym (eq₁' pA)) comp123 
        where
          pushed = (M→M' .fst pA)

          sq-lem : PSq rA' rel isom.inv Id
          sq-lem x y xRy = subst (λ z → rA' .PRel.R z y) (sym (isom.invRight x)) xRy
          
          comp12 : PSq rel rA' (iA' pushed ∘p isom.fun) (iA' pushed ∘p Id)
          comp12 = CompSqV {c₁ = rel} {c₂ = rA'} {c₃ = rA'}
                           {f₁ = isom.fun} {g₁ = Id} {f₂ = iA' pushed} {g₂ = iA' pushed}
                           (SqV-functionalRel isom.fun Id rA') (Predom-IdSqH (iA' pushed))

          comp123 : PSq rel rel (isom.inv ∘p (iA' pushed ∘p isom.fun)) (Id ∘p (iA' pushed ∘p Id))
          comp123 = CompSqV {c₁ = rel} {c₂ = rA'} {c₃ = rel}
                            {f₁ = iA' pushed ∘p isom.fun} {g₁ = iA' pushed ∘p Id}
                            {f₂ = isom.inv} {g₂ = Id}
                            comp12 sq-lem


      pullSq : ∀ pA' → VRelPtbSq A A' rel (M'→M .fst pA') pA'
      pullSq pA' = subst (λ z → PSq rel rel (Id ∘p (iA pulled ∘p Id)) z) (sym (eq₂' pA')) comp123
        where
          pulled = M'→M .fst pA'

          sq-lem1 : PSq rel rA Id (isom .PredomIso.inv)
          sq-lem1 x y xRy = subst
              (λ z → rA .PRel.R z (isom.inv .PMor.f y))
              (isom.invLeft x)
              (isom.inv .PMor.isMon xRy)
          -- Given: (isom.fun x) ⊑A' y
          -- NTS: x ⊑A (isom.inv y)
          -- But x = isom.inv (isom.fun x) so sufficies to show
          --   (isom.inv (isom.fun x)) ⊑A (isom.inv y)
          -- Then by monotonicity of isom.inv, sufficies to show
          --   (isom.fun x) ⊑A' y

          sq-lem2 : PSq rA rel Id (isom .PredomIso.fun)
          sq-lem2 x y xRy = isom.fun .PMor.isMon xRy

          comp12 : PSq rel rA (iA pulled ∘p Id) (iA pulled ∘p isom.inv)
          comp12 = CompSqV {c₁ = rel} {c₂ = rA} {c₃ = rA}
                           {f₁ = Id} {g₁ = isom.inv} {f₂ = iA pulled} {g₂ = iA pulled}
                           sq-lem1 (Predom-IdSqH (iA pulled))

          comp123 : PSq rel rel (Id ∘p (iA pulled ∘p Id)) (isom.fun ∘p (iA pulled ∘p isom.inv))
          comp123 = CompSqV
                    {c₁ = rel} {c₂ = rA} {c₃ = rel}
                    {f₁ = iA pulled ∘p Id} {g₁ = iA pulled ∘p isom.inv}
                    {f₂ = Id} {g₂ = isom.fun}
                    comp12 sq-lem2


      Iso→VRelPP : VRelPP A A' ℓ≤A'
      Iso→VRelPP = mkVRelPP A A' rel push pull
        where
          push : PushV A A' rel
          push = corecL
            {Mᴰ = VRelPtb A A' rel} {ϕ = idMon (PtbV A)}
            M→M' (corecVRelPtb pushSq)

          pull : PullV A A' rel
          pull = corecR
            {Mᴰ = VRelPtb A A' rel} {ϕ' = idMon (PtbV A')}
            M'→M (corecVRelPtb pullSq)
          

-- A strong isomorphism of value types induces a relation with push-pull

module _
  {A  : ValType ℓA  ℓ≤A  ℓ≈A  ℓMA}
  {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  (isom : StrongIsoV A A') where

  private
    |A| = ValType→Predomain A
    |A'| = ValType→Predomain A'
    
    predomIso : PredomIso (ValType→Predomain A) (ValType→Predomain A')
    predomIso = StrongIsoV→PredomIso isom

    monoidIso : MonoidIso (PtbV A) (PtbV A')
    monoidIso = StrongIsoV→MonoidIso isom

    module monoidIso = MonoidIso monoidIso

    M→M' : MonoidHom (PtbV A) (PtbV A')
    M→M' = monoidIso.fun

    M'→M : MonoidHom (PtbV A') (PtbV A)
    M'→M = monoidIso.inv

    coherence : (interpV A') ∘hom M→M' ≡ (PredomIso→EndoHom (isom .fst)) ∘hom (interpV A)
    coherence = StrongIsoV→coherence isom

    EndoA≅EndoA' : MonoidIso (Endo |A|) (Endo |A'|)
    EndoA≅EndoA' = mkMonoidIso
      (PredomIso→EndoHom predomIso)
      (PredomIso→EndoHom (PredomIso-Inv predomIso))
      (PredomIso→EndoHom-inv₁ predomIso)
      (PredomIso→EndoHom-inv₂ predomIso)

  ValTyIso→VRelPP : VRelPP A A' ℓ≤A'
  ValTyIso→VRelPP = Iso→VRelPP predomIso M→M' M'→M eq₁ eq₂
    where
      eq₁ : interpV A ≡ (PredomIso→EndoHom (PredomIso-Inv predomIso)) ∘hom (interpV A') ∘hom M→M'
      eq₁ = sym
        (cong₂ _∘hom_ refl coherence
        ∙ sym (∘hom-Assoc _ _ _)
        ∙ cong₂ _∘hom_ (PredomIso→EndoHom-inv₂ predomIso) refl
        ∙ ∘hom-IdL _)

      eq₂ : interpV A' ≡ PredomIso→EndoHom predomIso ∘hom interpV A ∘hom M'→M
      eq₂ = sym
        (sym (∘hom-Assoc _ _ _)
        ∙ cong₂ _∘hom_ (sym coherence) refl
        ∙ ∘hom-Assoc _ _ _
        ∙ cong₂ _∘hom_ refl (MonoidIso→RightInv monoidIso)
        ∙ ∘hom-IdR _)


{-      
    module _
      (eq₁ : ∀ (pA  : ⟨ PtbV A ⟩)  → (isom.fun ∘p iA pA)              ≡ (iA' (M→M' .fst pA) ∘p isom.fun))
      (eq₂ : ∀ (pA' : ⟨ PtbV A' ⟩) → (isom.fun ∘p iA (M'→M .fst pA')) ≡ (iA' pA'            ∘p isom.fun))
      where
       

      pushSq : ∀ pA  → VRelPtbSq A A' rel pA (M→M' .fst pA)
      pushSq pA = subst (λ z → PSq rel rel z (Id ∘p (iA' pushed ∘p Id))) (eq₁') comp123
        where
          pushed = (M→M' .fst pA)

          eq₁' : isom.inv ∘p (iA' pushed ∘p isom.fun) ≡ iA pA
          eq₁' = eqPMor _ _ (funExt (λ x → sym
                (sym (isom.invLeft _)
              ∙ (cong (isom.inv .PMor.f) (funExt⁻ (cong PMor.f (eq₁ pA)) x)))))

          sq-lem : PSq rA' rel isom.inv Id
          sq-lem x y xRy = subst (λ z → rA' .PRel.R z y) (sym (isom.invRight x)) xRy
          
          comp12 : PSq rel rA' (iA' pushed ∘p isom.fun) (iA' pushed ∘p Id)
          comp12 = CompSqV {c₁ = rel} {c₂ = rA'} {c₃ = rA'}
                           {f₁ = isom.fun} {g₁ = Id} {f₂ = iA' pushed} {g₂ = iA' pushed}
                           (SqV-functionalRel isom.fun Id rA') (Predom-IdSqH (iA' pushed))

          comp123 : PSq rel rel (isom.inv ∘p (iA' pushed ∘p isom.fun)) (Id ∘p (iA' pushed ∘p Id))
          comp123 = CompSqV {c₁ = rel} {c₂ = rA'} {c₃ = rel}
                            {f₁ = iA' pushed ∘p isom.fun} {g₁ = iA' pushed ∘p Id}
                            {f₂ = isom.inv} {g₂ = Id}
            comp12 sq-lem



      pullSq : ∀ pA' → VRelPtbSq A A' rel (M'→M .fst pA') pA'
      pullSq pA' = {!!}

      Iso→VRelPP : VRelPP A A' ℓ≤A'
      Iso→VRelPP = mkVRelPP A A' rel push pull
        where
          push : PushV A A' rel
          push = corecL
            {Mᴰ = VRelPtb A A' rel} {ϕ = idMon (PtbV A)}
            M→M' (corecVRelPtb pushSq)

          pull : PullV A A' rel
          pull = corecR
            {Mᴰ = VRelPtb A A' rel} {ϕ' = idMon (PtbV A')}
            M'→M (corecVRelPtb pullSq)
-}


{-
module _
  {A : ValType ℓA ℓ≤A ℓ≈A ℓMA}
  {|A'| : Predomain ℓA' ℓ≤A' ℓ≈A'} {MA' : Monoid ℓMA'}
  (inj-A : PRel (ValType→Predomain A) |A'| ℓ)
  (emb-MA : MonoidHom (PtbV (A .snd)) MA')
  (emb-A : PMor (ValType→Predomain A) |A'|)
  (dec-A : ∀ (x' : ⟨ |A'| ⟩) →
    Dec (Σ[ x ∈ ⟨ A ⟩ ] emb-A .PMor.f x ≡ x'))
  (dec-MA : ∀ (mA' : ⟨ MA' ⟩) →
    Dec (Σ[ mA ∈ ⟨ PtbV (A .snd) ⟩ ] emb-MA .fst mA ≡ mA'))
  where

  interp : MonoidHom MA' (Endo |A'|)
  interp .fst mA' = aux (dec-MA mA')
    where
      aux : _ → ⟨ Endo |A'| ⟩
      aux (yes (mA , eq)) = {!!}
      aux (no ¬p) = PrePtbId

  interp .snd = {!!}

  A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'
  A' = mkValType |A'| MA' {!interp!}
     


module _
  {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  (inj-A : PRel (ValType→Predomain A) (ValType→Predomain A') ℓ)
  (emb-MA : MonoidHom (PtbV (A .snd)) (PtbV (A' .snd)))
  (emb-A : PMor (ValType→Predomain A) (ValType→Predomain A'))
  (agree : ∀ (mA : ⟨ PtbV (A .snd) ⟩) →
    emb-A ∘p (ι (A .snd) mA) ≡ (ι (A' .snd) (emb-MA .fst mA)) ∘p emb-A)
  (dec : ∀ (y : ⟨ A' ⟩) → Dec (Σ[ x ∈ ⟨ A ⟩ ] emb-A .PMor.f x ≡ y)) where

  private
    iA = ι (A .snd)
    iA' = ι (A' .snd)
  open PMor

  inj : VRelPP A A' ℓ

  -- Relation
  inj .fst = inj-A

  -- Push
  inj .snd .fst = corecVFact1 A A' (fst inj) emb-MA
    (λ mA x y xRy → aux mA x y (dec y) xRy)
    where
      aux : ∀ mA x y →
        Dec _ →
        inj-A .PRel.R x y →
        inj-A .PRel.R (iA mA .f x ) (iA' (emb-MA .fst mA) .f y)
      aux mA x y (yes (x' , eq)) xRy = {!!}
      aux mA x y (no ¬p) xRy = {!!}
    -- NTS: Sq inj-A inj-A (iA mA x) (iA' (emb-MA mA) y)

  -- Pull
  inj .snd .snd = {!!}
-}

