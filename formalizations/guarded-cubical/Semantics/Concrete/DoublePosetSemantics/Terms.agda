{-# OPTIONS --cubical --rewriting --guarded  #-}

{-# OPTIONS --lossy-unification #-}

{-# OPTIONS --profile=constraints #-}


open import Common.Later


module Semantics.Concrete.DoublePosetSemantics.Terms (k : Clock) where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Nat renaming ( ℕ to Nat )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Univalence


open import Cubical.Data.Sigma


open import Cubical.Data.Empty as ⊥

open import Common.Common

open import Syntax.Types
-- open import Syntax.Terms
-- open import Semantics.Abstract.TermModel.Convenient
-- open import Semantics.Abstract.TermModel.Convenient.Computations

open import Syntax.IntensionalTerms hiding (π2)


open import Cubical.Foundations.Structure

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Convenience
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
  hiding (S) renaming (Comp to Compose)
open import Semantics.Lift k renaming (θ to θL ; ret to Return)
open import Semantics.Concrete.DoublePoset.DblDyn k
open import Semantics.Concrete.DoublePoset.LockStepErrorBisim k
-- open import Semantics.RepresentationSemantics k

-- open import Semantics.Concrete.RepresentableRelation k
open LiftDoublePoset
open ClockedCombinators k renaming (Δ to Del)

private
  variable
    ℓ ℓ' : Level
-- todo: doubleposet

open TyPrec

private
 variable
   R R' S S' T T' : Ty
   Γ Γ' Δ Δ' : Ctx
   γ γ' : Subst Δ Γ
   -- γ' : Subst Δ' Γ'
   V V' : Val Γ S
   E F   : EvCtx Γ S T
   E' F' : EvCtx Γ' S' T'

   M N : Comp Γ S
   M' N' : Comp Γ' S'

   C : Δ ⊑ctx Δ'
   D : Γ ⊑ctx Γ'

   c : S ⊑ S'
   d : T ⊑ T'

module _ {ℓo : Level} where

  {-# NON_COVERING #-}
  ⟦_⟧ty : Ty → DoublePoset ℓ-zero ℓ-zero ℓ-zero
  ⟦ nat ⟧ty = ℕ
  ⟦ dyn ⟧ty = DynP
  ⟦ S ⇀ T ⟧ty = ⟦ S ⟧ty ==> 𝕃 (⟦ T ⟧ty)

  -- Typing context interpretation
  {-# NON_COVERING #-}
  ⟦_⟧ctx : Ctx -> DoublePoset ℓ-zero ℓ-zero ℓ-zero -- Ctx → 𝓜.cat .ob
  ⟦ [] ⟧ctx = UnitDP -- 𝓜.𝟙
  ⟦ A ∷ Γ ⟧ctx = ⟦ Γ ⟧ctx ×dp ⟦ A ⟧ty -- ⟦ Γ ⟧ctx 𝓜.× ⟦ A ⟧ty

  {-# NON_COVERING #-}
  ⟦_⟧S : Subst Δ Γ   → DPMor ⟦ Δ ⟧ctx ⟦ Γ ⟧ctx -- 𝓜.cat [ ⟦ Δ ⟧ctx , ⟦ Γ ⟧ctx ]

  {-# NON_COVERING #-}
  ⟦_⟧V : Val Γ S     → DPMor ⟦ Γ ⟧ctx ⟦ S ⟧ty  -- 𝓜.cat [ ⟦ Γ ⟧ctx , ⟦ S ⟧ty ]

  {-# NON_COVERING #-}
  ⟦_⟧E : EvCtx Γ R S → DPMor (⟦ Γ ⟧ctx ×dp ⟦ R ⟧ty) (𝕃 ⟦ S ⟧ty) -- ???
    -- 𝓜.Linear ⟦ Γ ⟧ctx [ ⟦ R ⟧ty  , ⟦ S ⟧ty ]

  {-# NON_COVERING #-}
  ⟦_⟧C : Comp Γ S    → DPMor ⟦ Γ ⟧ctx (𝕃 ⟦ S ⟧ty) -- 𝓜.ClLinear [ ⟦ Γ ⟧ctx , ⟦ S ⟧ty ]

    -- Substitutions
  ⟦ ids ⟧S = MonId -- 𝓜.cat .id
  ⟦ γ ∘s δ ⟧S = mCompU ⟦ γ ⟧S ⟦ δ ⟧S -- ⟦ γ ⟧S ∘⟨ 𝓜.cat ⟩ ⟦ δ ⟧S
  ⟦ ∘IdL {γ = γ} i ⟧S = eqDPMor (mCompU MonId ⟦ γ ⟧S) ⟦ γ ⟧S refl i -- eqDPMor (mCompU MonId ⟦ γ ⟧S) ⟦ γ ⟧S refl i -- 𝓜.cat .⋆IdR ⟦ γ ⟧S i
  ⟦ ∘IdR {γ = γ} i ⟧S = eqDPMor (mCompU ⟦ γ ⟧S MonId) ⟦ γ ⟧S refl i -- eqDPMor (mCompU ⟦ γ ⟧S MonId) ⟦ γ ⟧S refl i -- 𝓜.cat .⋆IdL ⟦ γ ⟧S i
  ⟦ ∘Assoc {γ = γ}{δ = δ}{θ = θ} i ⟧S =
    eqDPMor (mCompU ⟦ γ ⟧S (mCompU ⟦ δ ⟧S ⟦ θ ⟧S)) (mCompU (mCompU ⟦ γ ⟧S ⟦ δ ⟧S) ⟦ θ ⟧S) refl i
     -- 𝓜.cat .⋆Assoc ⟦ θ ⟧S ⟦ δ ⟧S ⟦ γ ⟧S i
  ⟦ !s ⟧S = UnitDP! -- 𝓜.!t
  ⟦ []η {γ = γ} i ⟧S = eqDPMor ⟦ γ ⟧S UnitDP! refl i -- 𝓜.𝟙η ⟦ γ ⟧S i
  ⟦ γ ,s V ⟧S = PairFun ⟦ γ ⟧S ⟦ V ⟧V -- ⟦ γ ⟧S 𝓜.,p ⟦ V ⟧V
  ⟦ wk ⟧S = π1 -- 𝓜.π₁
  ⟦ wkβ {δ = γ}{V = V} i ⟧S =
    eqDPMor (mCompU π1 (PairFun ⟦ γ ⟧S ⟦ V ⟧V)) ⟦ γ ⟧S refl i  -- -- 𝓜.×β₁ {f = ⟦ γ ⟧S}{g = ⟦ V ⟧V} i
  ⟦ ,sη {δ = γ} i ⟧S =
    eqDPMor ⟦ γ ⟧S (PairFun (mCompU π1 ⟦ γ ⟧S) (mCompU π2 ⟦ γ ⟧S)) refl i --  -- 𝓜.×η {f = ⟦ γ ⟧S} i
  ⟦ isSetSubst γ γ' p q i j ⟧S =
    DPMorIsSet ⟦ γ ⟧S ⟦ γ' ⟧S (cong ⟦_⟧S p) (cong ⟦_⟧S q) i j -- follows because MonFun is a set


  -- Values
  ⟦ V [ γ ]v ⟧V = mCompU ⟦ V ⟧V ⟦ γ ⟧S
  ⟦ substId {V = V} i ⟧V =
    eqDPMor (mCompU ⟦ V ⟧V MonId) ⟦ V ⟧V refl i
  ⟦ substAssoc {V = V}{δ = δ}{γ = γ} i ⟧V =
    eqDPMor (mCompU ⟦ V ⟧V (mCompU ⟦ δ ⟧S ⟦ γ ⟧S))
          (mCompU (mCompU ⟦ V ⟧V ⟦ δ ⟧S) ⟦ γ ⟧S)
          refl i
  ⟦ var ⟧V = π2
  ⟦ varβ {δ = γ}{V = V} i ⟧V =
    eqDPMor (mCompU π2 ⟦ γ ,s V ⟧S) ⟦ V ⟧V refl i
  ⟦ zro ⟧V = Zero
  ⟦ suc ⟧V = Suc
  ⟦ lda M ⟧V = Curry ⟦ M ⟧C
  ⟦ fun-η {V = V} i ⟧V = eqDPMor
    ⟦ V ⟧V
    (Curry (mCompU (mCompU (mCompU App π2) PairAssocLR)
                   (PairFun (PairFun UnitDP! (mCompU ⟦ V ⟧V π1)) π2)))
    (funExt (λ ⟦Γ⟧ -> eqDPMor _ _ refl)) i
  ⟦ isSetVal V V' p q i j ⟧V =
    DPMorIsSet ⟦ V ⟧V ⟦ V' ⟧V (cong ⟦_⟧V p) (cong ⟦_⟧V q) i j
 

  -- Evaluation Contexts
  ⟦ ∙E {Γ = Γ} ⟧E = mCompU mRet π2 -- mCompU mRet π2
  ⟦ E ∘E F ⟧E = mExt' _ ⟦ E ⟧E ∘m ⟦ F ⟧E
  ⟦ ∘IdL {E = E} i ⟧E =
    eqDPMor (mExt' _ (mCompU mRet π2) ∘m ⟦ E ⟧E) ⟦ E ⟧E (funExt (λ x → monad-unit-r (DPMor.f ⟦ E ⟧E x))) i 
  ⟦ ∘IdR {E = E} i ⟧E =
    eqDPMor (mExt' _ ⟦ E ⟧E ∘m mCompU mRet π2) ⟦ E ⟧E (funExt (λ x → monad-unit-l _ _)) i
  ⟦ ∘Assoc {E = E}{F = F}{F' = F'} i ⟧E =
    eqDPMor (mExt' _ ⟦ E ⟧E ∘m (mExt' _ ⟦ F ⟧E ∘m ⟦ F' ⟧E))
          (mExt' _ (mExt' _ ⟦ E ⟧E ∘m ⟦ F ⟧E) ∘m ⟦ F' ⟧E)
          (funExt (λ x → monad-assoc _ _ _)) i 
  ⟦ E [ γ ]e ⟧E = mCompU ⟦ E ⟧E (PairFun (mCompU ⟦ γ ⟧S π1) π2)
  ⟦ substId {E = E} i ⟧E = eqDPMor (mCompU ⟦ E ⟧E (PairFun (mCompU MonId π1) π2)) ⟦ E ⟧E refl i
  ⟦ substAssoc {E = E}{γ = γ}{δ = δ} i ⟧E =
    eqDPMor (mCompU ⟦ E ⟧E (PairFun (mCompU (mCompU ⟦ γ ⟧S ⟦ δ ⟧S) π1) π2))
          (mCompU (mCompU ⟦ E ⟧E (PairFun (mCompU ⟦ γ ⟧S π1) π2)) (PairFun (mCompU ⟦ δ ⟧S π1) π2))
          refl i
  -- For some reason, using refl, or even funExt with refl, in the third argument
  -- to eqDPMor below leads to an error when lossy unification is turned on.
  -- This seems to be fixed by using congS η refl
  ⟦ ∙substDist {γ = γ} i ⟧E = eqDPMor
    (mCompU (mCompU mRet π2)
    (PairFun (mCompU ⟦ γ ⟧S π1) π2)) (mCompU mRet π2)
    (funExt (λ {(⟦Γ⟧ , ⟦R⟧) -> congS η refl})) i
  ⟦ ∘substDist {E = E}{F = F}{γ = γ} i ⟧E =
    eqDPMor (mCompU (mExt' _ ⟦ E ⟧E ∘m ⟦ F ⟧E) (PairFun (mCompU ⟦ γ ⟧S π1) π2))
          (mExt' _ (mCompU ⟦ E ⟧E (PairFun (mCompU ⟦ γ ⟧S π1) π2)) ∘m mCompU ⟦ F ⟧E (PairFun (mCompU ⟦ γ ⟧S π1) π2))
          refl i
  -- (E ∘E F) [ γ ]e ≡ (E [ γ ]e) ∘E (F [ γ ]e)
  ⟦ bind M ⟧E = ⟦ M ⟧C

  -- E ≡ bind (E [ wk ]e [ retP [ !s ,s var ]cP ]∙P)
  ⟦ ret-η {Γ}{R}{S}{E} i ⟧E = 
         eqDPMor ⟦ E ⟧E (Bind (⟦ Γ ⟧ctx ×dp ⟦ R ⟧ty)
         (mCompU (mCompU mRet π2) (PairFun UnitDP! π2))
         (mCompU ⟦ E ⟧E (PairFun (mCompU π1 π1) π2)))
         (funExt (λ x → sym (ext-eta _ _))) i
    {-- explicit i where
      explicit : ⟦ E ⟧E
                 ≡ 𝓜.bindP (𝓜.pull 𝓜.π₁ ⟪ ⟦ E ⟧E ⟫) ∘⟨ 𝓜.cat ⟩ (𝓜.cat .id 𝓜.,p (𝓜.retP ∘⟨ 𝓜.cat ⟩ (𝓜.!t 𝓜.,p 𝓜.π₂)))
      explicit = sym (cong₂ (comp' 𝓜.cat) (sym 𝓜.bind-natural) refl
        ∙  sym (𝓜.cat .⋆Assoc _ _ _)
        ∙ cong₂ (comp' 𝓜.cat) refl (𝓜.,p-natural ∙ cong₂ 𝓜._,p_ (sym (𝓜.cat .⋆Assoc _ _ _) ∙ cong₂ (comp' 𝓜.cat) refl 𝓜.×β₁ ∙ 𝓜.cat .⋆IdL _)
          (𝓜.×β₂ ∙ cong₂ (comp' 𝓜.cat) refl (cong₂ 𝓜._,p_ 𝓜.𝟙η' refl) ∙ 𝓜.η-natural {γ = 𝓜.!t}))
        ∙ 𝓜.bindP-l) --}
  --⟦ dn S⊑T ⟧E = {!!} -- ⟦ S⊑T .ty-prec ⟧p ∘⟨ 𝓜.cat ⟩ 𝓜.π₂
  ⟦ isSetEvCtx E F p q i j ⟧E =  DPMorIsSet ⟦ E ⟧E ⟦ F ⟧E (cong ⟦_⟧E p) (cong ⟦_⟧E q) i j  -- 𝓜.cat .isSetHom ⟦ E ⟧E ⟦ F ⟧E (cong ⟦_⟧E p) (cong ⟦_⟧E q) i j


  matchNat-helper : {ℓX ℓ'X ℓ''X ℓY ℓ'Y ℓ''Y : Level} {X : DoublePoset ℓX ℓ'X ℓ''X} {Y : DoublePoset ℓY ℓ'Y ℓ''Y} ->
    DPMor X Y -> DPMor (X ×dp ℕ) Y -> DPMor (X ×dp ℕ) Y
  matchNat-helper fZ fS =
    record { f = λ { (Γ , zero) → DPMor.f fZ Γ ;
                     (Γ , suc n) → DPMor.f fS (Γ , n) } ;
             isMon = λ { {Γ1 , zero} {Γ2 , zero} (Γ1≤Γ2 , n1≤n2) → DPMor.isMon fZ Γ1≤Γ2 ;
                         {Γ1 , zero} {Γ2 , suc n2} (Γ1≤Γ2 , n1≤n2) → rec (znots n1≤n2) ;
                         {Γ1 , suc n1} {Γ2 , zero} (Γ1≤Γ2 , n1≤n2) → rec (snotz n1≤n2) ;
                         {Γ1 , suc n1} {Γ2 , suc n2} (Γ1≤Γ2 , n1≤n2) → DPMor.isMon fS (Γ1≤Γ2 , injSuc n1≤n2)} ;
             pres≈ = λ { {Γ1 , zero} {Γ2 , zero} (Γ1≈Γ2 , n1≈n2) → DPMor.pres≈ fZ Γ1≈Γ2 ;
                         {Γ1 , zero} {Γ2 , suc n2} (Γ1≈Γ2 , n1≈n2) → rec (znots n1≈n2) ;
                         {Γ1 , suc n1} {Γ2 , zero} (Γ1≈Γ2 , n1≈n2) → rec (snotz n1≈n2) ;
                         {Γ1 , suc n1} {Γ2 , suc n2} (Γ1≈Γ2 , n1≈n2) → DPMor.pres≈ fS (Γ1≈Γ2 , injSuc n1≈n2) }
                         }


  -- Computations
  ⟦ _[_]∙ {Γ = Γ} E M ⟧C = Bind ⟦ Γ ⟧ctx ⟦ M ⟧C ⟦ E ⟧E
  ⟦ plugId {M = M} i ⟧C =
    eqDPMor (Bind _ ⟦ M ⟧C (mCompU mRet π2)) ⟦ M ⟧C (funExt (λ x → monad-unit-r (U ⟦ M ⟧C x))) i
  ⟦ plugAssoc {F = F}{E = E}{M = M} i ⟧C =
    eqDPMor (Bind _ ⟦ M ⟧C (mExt' _ ⟦ F ⟧E ∘m ⟦ E ⟧E))
          (Bind _ (Bind _ ⟦ M ⟧C ⟦ E ⟧E) ⟦ F ⟧E)
          (funExt (λ ⟦Γ⟧ → sym (monad-assoc
            (λ z → DPMor.f ⟦ E ⟧E (⟦Γ⟧ , z))
            (DPMor.f (π2 .DPMor.f (⟦Γ⟧ , U (Curry ⟦ F ⟧E) ⟦Γ⟧)))
            (DPMor.f ⟦ M ⟧C ⟦Γ⟧))))
          i  
  ⟦ M [ γ ]c ⟧C = mCompU ⟦ M ⟧C ⟦ γ ⟧S  -- ⟦ M ⟧C ∘⟨ 𝓜.cat ⟩ ⟦ γ ⟧S
  ⟦ substId {M = M} i ⟧C =
    eqDPMor (mCompU ⟦ M ⟧C MonId) ⟦ M ⟧C refl i  -- 𝓜.cat .⋆IdL ⟦ M ⟧C i
  ⟦ substAssoc {M = M}{δ = δ}{γ = γ} i ⟧C =
    eqDPMor (mCompU ⟦ M ⟧C (mCompU ⟦ δ ⟧S ⟦ γ ⟧S))
          (mCompU (mCompU ⟦ M ⟧C ⟦ δ ⟧S) ⟦ γ ⟧S)
          refl i -- 𝓜.cat .⋆Assoc ⟦ γ ⟧S ⟦ δ ⟧S ⟦ M ⟧C i
  ⟦ substPlugDist {E = E}{M = M}{γ = γ} i ⟧C =
    eqDPMor (mCompU (Bind _ ⟦ M ⟧C ⟦ E ⟧E) ⟦ γ ⟧S) (Bind _ (mCompU ⟦ M ⟧C ⟦ γ ⟧S)
          (mCompU ⟦ E ⟧E (PairFun (mCompU ⟦ γ ⟧S π1) π2)))
          refl i
  ⟦ err {S = S} ⟧C = K _ ℧ -- mCompU mRet {!!}  -- 𝓜.err
  ⟦ strictness {E = E} i ⟧C =
    eqDPMor (Bind _ (mCompU (K UnitDP ℧) UnitDP!) ⟦ E ⟧E)
          (mCompU (K UnitDP ℧) UnitDP!)
          (funExt (λ _ -> ext-err _)) i -- 𝓜.℧-homo ⟦ E ⟧E i
  -- i = i0 ⊢ Bind ⟦ Γ ⟧ctx (mCompU (K UnitP ℧) UnitP!) ⟦ E ⟧E
  -- i = i1 ⊢ mCompU (K UnitP ℧) UnitP!
  ⟦ ret ⟧C = mCompU mRet π2
  ⟦ ret-β {S}{T}{Γ}{M = M} i ⟧C = eqDPMor (Bind (⟦ Γ ⟧ctx ×dp ⟦ T ⟧ty)
         (mCompU (mCompU mRet π2) (PairFun UnitDP! π2))
         (mCompU ⟦ M ⟧C (PairFun (mCompU π1 π1) π2))) ⟦ M ⟧C (funExt (λ x → monad-unit-l _ _)) i
  ⟦ app ⟧C = mCompU (mCompU App π2) PairAssocLR
  ⟦ fun-β {M = M} i ⟧C =
    eqDPMor (mCompU (mCompU (mCompU App π2) PairAssocLR)
          (PairFun (PairFun UnitDP! (mCompU (Curry ⟦ M ⟧C) π1)) π2))
          ⟦ M ⟧C refl i
  ⟦ matchNat Mz Ms ⟧C = matchNat-helper ⟦ Mz ⟧C ⟦ Ms ⟧C
  ⟦ matchNatβz Mz Ms i ⟧C = eqDPMor
    (mCompU (matchNat-helper ⟦ Mz ⟧C ⟦ Ms ⟧C)
            (PairFun MonId (mCompU Zero UnitDP!)))
    ⟦ Mz ⟧C
    refl i
  ⟦ matchNatβs Mz Ms i ⟧C = eqDPMor
    (mCompU (matchNat-helper ⟦ Mz ⟧C ⟦ Ms ⟧C)
         (PairFun π1 (mCompU Suc (PairFun UnitDP! π2))))
    ⟦ Ms ⟧C refl i
  ⟦ matchNatη {M = M} i ⟧C = eqDPMor
    ⟦ M ⟧C
    (matchNat-helper
       (mCompU ⟦ M ⟧C (PairFun MonId (mCompU Zero UnitDP!)))
       (mCompU ⟦ M ⟧C (PairFun π1 (mCompU Suc (PairFun UnitDP! π2)))))
    (funExt (λ { (⟦Γ⟧ , zero) → refl ;
                 (⟦Γ⟧ , suc n) → refl}))
    i
  ⟦ isSetComp M N p q i j ⟧C = DPMorIsSet ⟦ M ⟧C ⟦ N ⟧C (cong ⟦_⟧C p) (cong ⟦_⟧C q) i j  -- 𝓜.cat .isSetHom ⟦ M ⟧C ⟦ N ⟧C (cong ⟦_⟧C p) (cong ⟦_⟧C q) i j

