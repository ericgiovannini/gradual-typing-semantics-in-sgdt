{-# OPTIONS --cubical --rewriting --guarded  #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Later


module Semantics.Concrete.PosetSemantics (k : Clock) where

-- A convenient model of the term language is
-- 1. A bicartesian closed category
-- 2. Equipped with a strong monad
-- 3. An object modeling the numbers with models of the con/dtors
-- 4. An object modeling the dynamic type with models of the inj casts

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Comonad.Instances.Environment
open import Cubical.Categories.Exponentials
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Nat renaming ( ℕ to Nat )

open import Cubical.Data.Empty as ⊥

open import Common.Common

open import Syntax.Types
-- open import Syntax.Terms
-- open import Semantics.Abstract.TermModel.Convenient
-- open import Semantics.Abstract.TermModel.Convenient.Computations

open import Syntax.Intensional


open import Cubical.Foundations.Structure

open import Cubical.Relation.Binary.Poset
open import Common.Poset.Convenience
open import Common.Poset.Monotone
open import Common.Poset.Constructions
open import Common.Poset.MonotoneRelation
open import Semantics.MonotoneCombinators
  hiding (S) renaming (Comp to Compose)
open import Semantics.Lift k renaming (θ to θL ; ret to Return)
open import Semantics.Concrete.Dyn k
open import Semantics.LockStepErrorOrdering k
-- open import Semantics.RepresentationSemantics k
open import Semantics.Concrete.RepresentableRelation k

open LiftPoset
open ClockedCombinators k renaming (Δ to Del)

private
  variable
    ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open BinCoproduct
open BinProduct
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
  
  -- ⇒F = ExponentialF 𝓜.cat 𝓜.binProd 𝓜.exponentials
  {-
  2Cell :
    {ℓA ℓ'A ℓB ℓ'B ℓC ℓ'C ℓD ℓ'D ℓR ℓS : Level} ->
    {A : Poset ℓA ℓ'A} {B : Poset ℓB ℓ'B} {C : Poset ℓC ℓ'C} {D : Poset ℓD ℓ'D} ->
    (R : MonRel A B ℓR) ->
    (S : MonRel C D ℓS)
    (f : MonFun A C) ->
    (g : MonFun B D) ->
    Type {!!}
  2Cell R S f g = {!!}
  -}

  -- Type interpretation
  ⟦_⟧ty : Ty → Poset ℓ-zero ℓ-zero
  ⟦ nat ⟧ty = ℕ
  ⟦ dyn ⟧ty = DynP
  ⟦ S ⇀ T ⟧ty = ⟦ S ⟧ty ==> 𝕃 (⟦ T ⟧ty)

  -- Typing context interpretation
  ⟦_⟧ctx : Ctx -> Poset ℓ-zero ℓ-zero -- Ctx → 𝓜.cat .ob
  ⟦ [] ⟧ctx = UnitP -- 𝓜.𝟙
  ⟦ A ∷ Γ ⟧ctx = ⟦ Γ ⟧ctx ×p ⟦ A ⟧ty -- ⟦ Γ ⟧ctx 𝓜.× ⟦ A ⟧ty

  -- Interpetations for substitutions, values, ev ctxs, and computations
  -- (signatures only; definitions are below)
  ⟦_⟧S : Subst Δ Γ   → MonFun ⟦ Δ ⟧ctx ⟦ Γ ⟧ctx -- 𝓜.cat [ ⟦ Δ ⟧ctx , ⟦ Γ ⟧ctx ]
  ⟦_⟧V : Val Γ S     → MonFun ⟦ Γ ⟧ctx ⟦ S ⟧ty  -- 𝓜.cat [ ⟦ Γ ⟧ctx , ⟦ S ⟧ty ]
  ⟦_⟧E : EvCtx Γ R S → MonFun (⟦ Γ ⟧ctx ×p ⟦ R ⟧ty) (𝕃 ⟦ S ⟧ty) -- ???
    -- 𝓜.Linear ⟦ Γ ⟧ctx [ ⟦ R ⟧ty  , ⟦ S ⟧ty ]
  ⟦_⟧C : Comp Γ S    → MonFun ⟦ Γ ⟧ctx (𝕃 ⟦ S ⟧ty) -- 𝓜.ClLinear [ ⟦ Γ ⟧ctx , ⟦ S ⟧ty ]




  -- Substitutions
  ⟦ ids ⟧S = MonId -- 𝓜.cat .id
  ⟦ γ ∘s δ ⟧S = mCompU ⟦ γ ⟧S ⟦ δ ⟧S -- ⟦ γ ⟧S ∘⟨ 𝓜.cat ⟩ ⟦ δ ⟧S
  ⟦ ∘IdL {γ = γ} i ⟧S = eqMon (mCompU MonId ⟦ γ ⟧S) ⟦ γ ⟧S refl i -- eqMon (mCompU MonId ⟦ γ ⟧S) ⟦ γ ⟧S refl i -- 𝓜.cat .⋆IdR ⟦ γ ⟧S i
  ⟦ ∘IdR {γ = γ} i ⟧S = eqMon (mCompU ⟦ γ ⟧S MonId) ⟦ γ ⟧S refl i -- eqMon (mCompU ⟦ γ ⟧S MonId) ⟦ γ ⟧S refl i -- 𝓜.cat .⋆IdL ⟦ γ ⟧S i
  ⟦ ∘Assoc {γ = γ}{δ = δ}{θ = θ} i ⟧S =
    eqMon (mCompU ⟦ γ ⟧S (mCompU ⟦ δ ⟧S ⟦ θ ⟧S)) (mCompU (mCompU ⟦ γ ⟧S ⟦ δ ⟧S) ⟦ θ ⟧S) refl i
     -- 𝓜.cat .⋆Assoc ⟦ θ ⟧S ⟦ δ ⟧S ⟦ γ ⟧S i
  ⟦ !s ⟧S = UnitP! -- 𝓜.!t
  ⟦ []η {γ = γ} i ⟧S = eqMon ⟦ γ ⟧S UnitP! refl i -- 𝓜.𝟙η ⟦ γ ⟧S i
  ⟦ γ ,s V ⟧S = PairFun ⟦ γ ⟧S ⟦ V ⟧V -- ⟦ γ ⟧S 𝓜.,p ⟦ V ⟧V
  ⟦ wk ⟧S = π1 -- 𝓜.π₁
  ⟦ wkβ {δ = γ}{V = V} i ⟧S =
    eqMon (mCompU π1 (PairFun ⟦ γ ⟧S ⟦ V ⟧V)) ⟦ γ ⟧S refl i  -- -- 𝓜.×β₁ {f = ⟦ γ ⟧S}{g = ⟦ V ⟧V} i
  ⟦ ,sη {δ = γ} i ⟧S =
    eqMon ⟦ γ ⟧S (PairFun (mCompU π1 ⟦ γ ⟧S) (mCompU π2 ⟦ γ ⟧S)) refl i --  -- 𝓜.×η {f = ⟦ γ ⟧S} i
  ⟦ isSetSubst γ γ' p q i j ⟧S =
    MonFunIsSet ⟦ γ ⟧S ⟦ γ' ⟧S (cong ⟦_⟧S p) (cong ⟦_⟧S q) i j -- follows because MonFun is a set
  ⟦ isPosetSubst {γ = γ} {γ' = γ'} x x₁ i ⟧S = {!!}


  
  -- Values
  ⟦ V [ γ ]v ⟧V = mCompU ⟦ V ⟧V ⟦ γ ⟧S
  ⟦ substId {V = V} i ⟧V =
    eqMon (mCompU ⟦ V ⟧V MonId) ⟦ V ⟧V refl i
  ⟦ substAssoc {V = V}{δ = δ}{γ = γ} i ⟧V =
    eqMon (mCompU ⟦ V ⟧V (mCompU ⟦ δ ⟧S ⟦ γ ⟧S))
          (mCompU (mCompU ⟦ V ⟧V ⟦ δ ⟧S) ⟦ γ ⟧S)
          refl i
  ⟦ var ⟧V = π2
  ⟦ varβ {δ = γ}{V = V} i ⟧V =
    eqMon (mCompU π2 ⟦ γ ,s V ⟧S) ⟦ V ⟧V refl i
  ⟦ zro ⟧V = Zero
  ⟦ suc ⟧V = Suc
  ⟦ lda M ⟧V = Curry ⟦ M ⟧C
  ⟦ fun-η {V = V} i ⟧V = eqMon
    ⟦ V ⟧V
    (Curry (mCompU (mCompU (mCompU App π2) PairAssocLR)
                   (PairFun (PairFun UnitP! (mCompU ⟦ V ⟧V π1)) π2)))
    (funExt (λ ⟦Γ⟧ -> eqMon _ _ refl)) i
      -- eqMon ⟦ V ⟧V (Curry
      --   (mCompU (mCompU (mCompU App π2) PairAssocLR)
      --   (PairFun (PairFun UnitP! (mCompU ⟦ V ⟧V π1)) π2))) (funExt λ x → eqMon _ _ refl) i
    -- eqMon  ⟦ V ⟧V (Curry ⟦ appP [ !s ,s (V [ wk ]v) ,s var ]cP ⟧C) {!!} i
    -- V ≡ lda (appP [ (!s ,s (V [ wk ]v)) ,s var ]cP)
  ⟦ up S⊑T ⟧V = {!!}
  ⟦ δl S⊑T ⟧V = π2
  ⟦ δr S⊑T ⟧V = π2
  ⟦ isSetVal V V' p q i j ⟧V =
    MonFunIsSet ⟦ V ⟧V ⟦ V' ⟧V (cong ⟦_⟧V p) (cong ⟦_⟧V q) i j
  ⟦ isPosetVal x x₁ i ⟧V = {!!}


  -- Evaluation Contexts
  ⟦ ∙E {Γ = Γ} ⟧E = mCompU mRet π2 -- mCompU mRet π2
  ⟦ E ∘E F ⟧E = mExt' _ ⟦ E ⟧E ∘m ⟦ F ⟧E
  ⟦ ∘IdL {E = E} i ⟧E =
    eqMon (mExt' _ (mCompU mRet π2) ∘m ⟦ E ⟧E) ⟦ E ⟧E (funExt (λ x → monad-unit-r (MonFun.f ⟦ E ⟧E x))) i 
  ⟦ ∘IdR {E = E} i ⟧E =
    eqMon (mExt' _ ⟦ E ⟧E ∘m mCompU mRet π2) ⟦ E ⟧E (funExt (λ x → monad-unit-l _ _)) i
  ⟦ ∘Assoc {E = E}{F = F}{F' = F'} i ⟧E =
    eqMon (mExt' _ ⟦ E ⟧E ∘m (mExt' _ ⟦ F ⟧E ∘m ⟦ F' ⟧E))
          (mExt' _ (mExt' _ ⟦ E ⟧E ∘m ⟦ F ⟧E) ∘m ⟦ F' ⟧E)
          (funExt (λ x → monad-assoc _ _ _)) i 
  ⟦ E [ γ ]e ⟧E = mCompU ⟦ E ⟧E (PairFun (mCompU ⟦ γ ⟧S π1) π2)
  ⟦ substId {E = E} i ⟧E = eqMon (mCompU ⟦ E ⟧E (PairFun (mCompU MonId π1) π2)) ⟦ E ⟧E refl i
  ⟦ substAssoc {E = E}{γ = γ}{δ = δ} i ⟧E =
    eqMon (mCompU ⟦ E ⟧E (PairFun (mCompU (mCompU ⟦ γ ⟧S ⟦ δ ⟧S) π1) π2))
          (mCompU (mCompU ⟦ E ⟧E (PairFun (mCompU ⟦ γ ⟧S π1) π2)) (PairFun (mCompU ⟦ δ ⟧S π1) π2))
          refl i
  -- For some reason, using refl, or even funExt with refl, in the third argument
  -- to eqMon below leads to an error when lossy unification is turned on.
  -- This seems to be fixed by using congS η refl
  ⟦ ∙substDist {γ = γ} i ⟧E = eqMon
    (mCompU (mCompU mRet π2)
    (PairFun (mCompU ⟦ γ ⟧S π1) π2)) (mCompU mRet π2)
    (funExt (λ {(⟦Γ⟧ , ⟦R⟧) -> congS η refl})) i
  ⟦ ∘substDist {E = E}{F = F}{γ = γ} i ⟧E =
    eqMon (mCompU (mExt' _ ⟦ E ⟧E ∘m ⟦ F ⟧E) (PairFun (mCompU ⟦ γ ⟧S π1) π2))
          (mExt' _ (mCompU ⟦ E ⟧E (PairFun (mCompU ⟦ γ ⟧S π1) π2)) ∘m mCompU ⟦ F ⟧E (PairFun (mCompU ⟦ γ ⟧S π1) π2))
          refl i
  -- (E ∘E F) [ γ ]e ≡ (E [ γ ]e) ∘E (F [ γ ]e)
  ⟦ bind M ⟧E = ⟦ M ⟧C

  -- E ≡ bind (E [ wk ]e [ retP [ !s ,s var ]cP ]∙P)
  ⟦ ret-η {Γ}{R}{S}{E} i ⟧E = 
         eqMon ⟦ E ⟧E (Bind (⟦ Γ ⟧ctx ×p ⟦ R ⟧ty)
         (mCompU (mCompU mRet π2) (PairFun UnitP! π2))
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
  ⟦ dn S⊑T ⟧E = {!!} -- ⟦ S⊑T .ty-prec ⟧p ∘⟨ 𝓜.cat ⟩ 𝓜.π₂
  ⟦ isSetEvCtx E F p q i j ⟧E =  MonFunIsSet ⟦ E ⟧E ⟦ F ⟧E (cong ⟦_⟧E p) (cong ⟦_⟧E q) i j  -- 𝓜.cat .isSetHom ⟦ E ⟧E ⟦ F ⟧E (cong ⟦_⟧E p) (cong ⟦_⟧E q) i j
  ⟦ δl S⊑T ⟧E = mCompU mRet π2  
  ⟦ δr S⊑T ⟧E = mCompU mRet π2  
  ⟦ isPosetEvCtx x x₁ i ⟧E =  {!eqMon ?!}


  matchNat-helper : {ℓX ℓ'X ℓY ℓ'Y : Level} {X : Poset ℓX ℓ'X} {Y : Poset ℓY ℓ'Y} ->
    MonFun X Y -> MonFun (X ×p ℕ) Y -> MonFun (X ×p ℕ) Y
  matchNat-helper fZ fS =
    record { f = λ { (Γ , zero) → MonFun.f fZ Γ ;
                     (Γ , suc n) → MonFun.f fS (Γ , n) } ;
             isMon = λ { {Γ1 , zero} {Γ2 , zero} (Γ1≤Γ2 , n1≤n2) → MonFun.isMon fZ Γ1≤Γ2 ;
                         {Γ1 , zero} {Γ2 , suc n2} (Γ1≤Γ2 , n1≤n2) → rec (znots n1≤n2) ;
                         {Γ1 , suc n1} {Γ2 , zero} (Γ1≤Γ2 , n1≤n2) → rec (snotz n1≤n2) ;
                         {Γ1 , suc n1} {Γ2 , suc n2} (Γ1≤Γ2 , n1≤n2) → MonFun.isMon fS (Γ1≤Γ2 , injSuc n1≤n2)} }


  -- Computations
  ⟦ _[_]∙ {Γ = Γ} E M ⟧C = Bind ⟦ Γ ⟧ctx ⟦ M ⟧C ⟦ E ⟧E
  ⟦ plugId {M = M} i ⟧C =
    eqMon (Bind _ ⟦ M ⟧C (mCompU mRet π2)) ⟦ M ⟧C (funExt (λ x → monad-unit-r (U ⟦ M ⟧C x))) i
  ⟦ plugAssoc {F = F}{E = E}{M = M} i ⟧C =
    eqMon (Bind _ ⟦ M ⟧C (mExt' _ ⟦ F ⟧E ∘m ⟦ E ⟧E))
          (Bind _ (Bind _ ⟦ M ⟧C ⟦ E ⟧E) ⟦ F ⟧E)
          (funExt (λ ⟦Γ⟧ → sym (monad-assoc
            (λ z → MonFun.f ⟦ E ⟧E (⟦Γ⟧ , z))
            (MonFun.f (π2 .MonFun.f (⟦Γ⟧ , U (Curry ⟦ F ⟧E) ⟦Γ⟧)))
            (MonFun.f ⟦ M ⟧C ⟦Γ⟧))))
          i  
  ⟦ M [ γ ]c ⟧C = mCompU ⟦ M ⟧C ⟦ γ ⟧S  -- ⟦ M ⟧C ∘⟨ 𝓜.cat ⟩ ⟦ γ ⟧S
  ⟦ substId {M = M} i ⟧C =
    eqMon (mCompU ⟦ M ⟧C MonId) ⟦ M ⟧C refl i  -- 𝓜.cat .⋆IdL ⟦ M ⟧C i
  ⟦ substAssoc {M = M}{δ = δ}{γ = γ} i ⟧C =
    eqMon (mCompU ⟦ M ⟧C (mCompU ⟦ δ ⟧S ⟦ γ ⟧S))
          (mCompU (mCompU ⟦ M ⟧C ⟦ δ ⟧S) ⟦ γ ⟧S)
          refl i -- 𝓜.cat .⋆Assoc ⟦ γ ⟧S ⟦ δ ⟧S ⟦ M ⟧C i
  ⟦ substPlugDist {E = E}{M = M}{γ = γ} i ⟧C =
    eqMon (mCompU (Bind _ ⟦ M ⟧C ⟦ E ⟧E) ⟦ γ ⟧S) (Bind _ (mCompU ⟦ M ⟧C ⟦ γ ⟧S)
          (mCompU ⟦ E ⟧E (PairFun (mCompU ⟦ γ ⟧S π1) π2)))
          refl i
  ⟦ err {S = S} ⟧C = K _ ℧ -- mCompU mRet {!!}  -- 𝓜.err
  ⟦ strictness {E = E} i ⟧C =
    eqMon (Bind _ (mCompU (K UnitP ℧) UnitP!) ⟦ E ⟧E)
          (mCompU (K UnitP ℧) UnitP!)
          (funExt (λ _ -> ext-err _)) i -- 𝓜.℧-homo ⟦ E ⟧E i
  -- i = i0 ⊢ Bind ⟦ Γ ⟧ctx (mCompU (K UnitP ℧) UnitP!) ⟦ E ⟧E
  -- i = i1 ⊢ mCompU (K UnitP ℧) UnitP!
  ⟦ ret ⟧C = mCompU mRet π2
  ⟦ ret-β {S}{T}{Γ}{M = M} i ⟧C = eqMon (Bind (⟦ Γ ⟧ctx ×p ⟦ T ⟧ty)
         (mCompU (mCompU mRet π2) (PairFun UnitP! π2))
         (mCompU ⟦ M ⟧C (PairFun (mCompU π1 π1) π2))) ⟦ M ⟧C (funExt (λ x → monad-unit-l _ _)) i
  ⟦ app ⟧C = mCompU (mCompU App π2) PairAssocLR
  ⟦ fun-β {M = M} i ⟧C =
    eqMon (mCompU (mCompU (mCompU App π2) PairAssocLR)
          (PairFun (PairFun UnitP! (mCompU (Curry ⟦ M ⟧C) π1)) π2))
          ⟦ M ⟧C refl i
  ⟦ matchNat Mz Ms ⟧C = matchNat-helper ⟦ Mz ⟧C ⟦ Ms ⟧C
             -- record { f = λ { (Γ , zero) → MonFun.f ⟦ Mz ⟧C Γ ;
             --                             (Γ , suc n) → MonFun.f ⟦ Ms ⟧C (Γ , n) } ;
             -- isMon = λ { {Γ1 , zero} {Γ2 , zero} (Γ1≤Γ2 , n1≤n2) → MonFun.isMon ⟦ Mz ⟧C Γ1≤Γ2 ;
             --             {Γ1 , zero} {Γ2 , suc n2} (Γ1≤Γ2 , n1≤n2) → rec (znots n1≤n2) ;
             --             {Γ1 , suc n1} {Γ2 , zero} (Γ1≤Γ2 , n1≤n2) → rec (snotz n1≤n2) ;
             --             {Γ1 , suc n1} {Γ2 , suc n2} (Γ1≤Γ2 , n1≤n2) → MonFun.isMon ⟦ Ms ⟧C (Γ1≤Γ2 , injSuc n1≤n2)} }
  ⟦ matchNatβz Mz Ms i ⟧C = eqMon
    (mCompU (matchNat-helper ⟦ Mz ⟧C ⟦ Ms ⟧C)
            (PairFun MonId (mCompU Zero UnitP!)))
    ⟦ Mz ⟧C
    refl i
  ⟦ matchNatβs Mz Ms V i ⟧C = eqMon
    (mCompU (matchNat-helper ⟦ Mz ⟧C ⟦ Ms ⟧C)
            (PairFun MonId (mCompU Suc (PairFun UnitP! ⟦ V ⟧V))))
    (mCompU ⟦ Ms ⟧C (PairFun MonId ⟦ V ⟧V))
    refl i
  ⟦ matchNatη {M = M} i ⟧C = eqMon
    ⟦ M ⟧C
    (matchNat-helper
       (mCompU ⟦ M ⟧C (PairFun MonId (mCompU Zero UnitP!)))
       (mCompU ⟦ M ⟧C (PairFun π1 (mCompU Suc (PairFun UnitP! π2)))))
    (funExt (λ { (⟦Γ⟧ , zero) → refl ;
                 (⟦Γ⟧ , suc n) → refl}))
    i
  ⟦ isSetComp M N p q i j ⟧C = MonFunIsSet ⟦ M ⟧C ⟦ N ⟧C (cong ⟦_⟧C p) (cong ⟦_⟧C q) i j  -- 𝓜.cat .isSetHom ⟦ M ⟧C ⟦ N ⟧C (cong ⟦_⟧C p) (cong ⟦_⟧C q) i j
  ⟦ isPosetComp x x₁ i ⟧C = {!!}


  

  -- Logic semantics

{-
  ⟦_⟧e : S ⊑ R → MonFun ⟦ S ⟧ty ⟦ R ⟧ty
  ⟦_⟧p : S ⊑ R → MonFun ⟦ R ⟧ty (𝕃 ⟦ S ⟧ty)
  ⟦_⟧p' : S ⊑ R → MonFun (𝕃 ⟦ R ⟧ty) (𝕃 ⟦ S ⟧ty)


  ⟦ nat ⟧e = MonId
  ⟦ dyn ⟧e = MonId
  -- The most annoying one because it's not from bifunctoriality, more like separate functoriality
  -- λ f . λ x . x'  <- p x;
  --             y'  <- app(f,x');
  --             η (e y')
  ⟦ c ⇀ d ⟧e     = {!!}
  ⟦ inj-nat ⟧e   = InjNat -- 𝓜.inj ∘⟨ 𝓜.cat ⟩ 𝓜.σ1
  ⟦ inj-arr c ⟧e = mCompU InjArr ⟦ c ⟧e -- 𝓜.inj ∘⟨ 𝓜.cat ⟩ 𝓜.σ2 ∘⟨ 𝓜.cat ⟩ ⟦ c ⟧e


  ⟦ nat ⟧p = mRet
  ⟦ dyn ⟧p = mRet
  -- = η ∘ (⟦ c ⟧e ⇒ ⟦ d ⟧p')
  ⟦ c ⇀ d ⟧p     = mCompU (mCompU mRet {!!}) (Bind _ {!⟦ c ⇀ d ⟧e !} {!!}) -- 𝓜.ClLinear .id ∘⟨ 𝓜.cat ⟩ ⇒F ⟪ ⟦ c ⟧e , ⟦ d ⟧p' ⟫
  ⟦ inj-nat ⟧p   = {!!} -- (𝓜.ClLinear .id 𝓜.|| 𝓜.℧) ∘⟨ 𝓜.ClLinear ⟩ 𝓜.prj
  ⟦ inj-arr c ⟧p = {!!} -- (𝓜.℧ 𝓜.|| ⟦ c ⟧p) ∘⟨ 𝓜.ClLinear ⟩ 𝓜.prj


  ⟦ c ⟧p' = {!!} -- 𝓜.clBind ⟦ c ⟧p



  -- Weak bisimilarity relation
  Bisim : (S : Ty) -> MonRel ⟦ S ⟧ty ⟦ S ⟧ty ℓ
  Bisim nat = {!!}
  Bisim dyn = {!!}
  Bisim (S ⇀ T) = {!!}
-}






  {-

  -- The term syntax
  -- substitutions, values, ev ctxts, terms

  ⟦_⟧S : Subst Δ Γ   → 𝓜.cat [ ⟦ Δ ⟧ctx , ⟦ Γ ⟧ctx ]
  ⟦_⟧V : Val Γ S     → 𝓜.cat [ ⟦ Γ ⟧ctx , ⟦ S ⟧ty ]
  ⟦_⟧E : EvCtx Γ R S → 𝓜.Linear ⟦ Γ ⟧ctx [ ⟦ R ⟧ty  , ⟦ S ⟧ty ]
  ⟦_⟧C : Comp Γ S    → 𝓜.ClLinear        [ ⟦ Γ ⟧ctx , ⟦ S ⟧ty ]

  ⟦ ids ⟧S = 𝓜.cat .id
  ⟦ γ ∘s δ ⟧S = ⟦ γ ⟧S ∘⟨ 𝓜.cat ⟩ ⟦ δ ⟧S
  ⟦ ∘IdL {γ = γ} i ⟧S = 𝓜.cat .⋆IdR ⟦ γ ⟧S i
  ⟦ ∘IdR {γ = γ} i ⟧S = 𝓜.cat .⋆IdL ⟦ γ ⟧S i
  ⟦ ∘Assoc {γ = γ}{δ = δ}{θ = θ} i ⟧S = 𝓜.cat .⋆Assoc ⟦ θ ⟧S ⟦ δ ⟧S ⟦ γ ⟧S i
  ⟦ !s ⟧S = 𝓜.!t
  ⟦ []η {γ = γ} i ⟧S = 𝓜.𝟙η ⟦ γ ⟧S i
  ⟦ γ ,s V ⟧S = ⟦ γ ⟧S 𝓜.,p ⟦ V ⟧V
  ⟦ wk ⟧S = 𝓜.π₁
  ⟦ wkβ {δ = γ}{V = V} i ⟧S = 𝓜.×β₁ {f = ⟦ γ ⟧S}{g = ⟦ V ⟧V} i
  ⟦ ,sη {δ = γ} i ⟧S = 𝓜.×η {f = ⟦ γ ⟧S} i
  ⟦ isSetSubst γ γ' p q i j ⟧S = 𝓜.cat .isSetHom ⟦ γ ⟧S ⟦ γ' ⟧S (cong ⟦_⟧S p) (cong ⟦_⟧S q) i j

  ⟦ V [ γ ]v ⟧V = ⟦ V ⟧V ∘⟨ 𝓜.cat ⟩ ⟦ γ ⟧S
  ⟦ substId {V = V} i ⟧V = 𝓜.cat .⋆IdL ⟦ V ⟧V i
  ⟦ substAssoc {V = V}{δ = δ}{γ = γ} i ⟧V = 𝓜.cat .⋆Assoc ⟦ γ ⟧S ⟦ δ ⟧S ⟦ V ⟧V i
  ⟦ var ⟧V = 𝓜.π₂
  ⟦ varβ {δ = γ}{V = V} i ⟧V = 𝓜.×β₂ {f = ⟦ γ ⟧S}{g = ⟦ V ⟧V} i
  ⟦ zro ⟧V = 𝓜.nat-fp .fst ∘⟨ 𝓜.cat ⟩ 𝓜.σ1 ∘⟨ 𝓜.cat ⟩ 𝓜.!t
  ⟦ suc ⟧V = 𝓜.nat-fp .fst ∘⟨ 𝓜.cat ⟩ 𝓜.σ2 ∘⟨ 𝓜.cat ⟩ 𝓜.π₂
  ⟦ lda M ⟧V = 𝓜.lda ⟦ M ⟧C
  ⟦ fun-η i ⟧V = {!!}
  ⟦ up S⊑T ⟧V = ⟦ S⊑T .ty-prec  ⟧e ∘⟨ 𝓜.cat ⟩ 𝓜.π₂
  ⟦ isSetVal V V' p q i j ⟧V = 𝓜.cat .isSetHom ⟦ V ⟧V ⟦ V' ⟧V (cong ⟦_⟧V p) (cong ⟦_⟧V q) i j

  ⟦ ∙E ⟧E = 𝓜.Linear _ .id
  ⟦ E ∘E F ⟧E = ⟦ E ⟧E ∘⟨ 𝓜.Linear _ ⟩ ⟦ F ⟧E
  ⟦ ∘IdL {E = E} i ⟧E = 𝓜.Linear _ .⋆IdR ⟦ E ⟧E i
  ⟦ ∘IdR {E = E} i ⟧E = 𝓜.Linear _ .⋆IdL ⟦ E ⟧E i
  ⟦ ∘Assoc {E = E}{F = F}{F' = F'} i ⟧E = 𝓜.Linear _ .⋆Assoc ⟦ F' ⟧E ⟦ F ⟧E ⟦ E ⟧E i
  ⟦ E [ γ ]e ⟧E = (𝓜.pull ⟦ γ ⟧S) ⟪ ⟦ E ⟧E ⟫
  ⟦ substId {E = E} i ⟧E = 𝓜.id^* i ⟪ ⟦ E ⟧E ⟫
  ⟦ substAssoc {E = E}{γ = γ}{δ = δ} i ⟧E = 𝓜.comp^* ⟦ γ ⟧S ⟦ δ ⟧S i ⟪ ⟦ E ⟧E ⟫
  ⟦ ∙substDist {γ = γ} i ⟧E = (𝓜.pull ⟦ γ ⟧S) .F-id i
    
  ⟦ ∘substDist {E = E}{F = F}{γ = γ} i ⟧E = 𝓜.pull ⟦ γ ⟧S .F-seq ⟦ F ⟧E ⟦ E ⟧E i
  ⟦ bind M ⟧E = ⟦ M ⟧C
  -- E ≡
  -- bind (E [ wk ]e [ retP [ !s ,s var ]c ]∙)
  ⟦ ret-η {Γ}{R}{S}{E} i ⟧E = explicit i where
    explicit : ⟦ E ⟧E
               ≡ 𝓜.bindP (𝓜.pull 𝓜.π₁ ⟪ ⟦ E ⟧E ⟫) ∘⟨ 𝓜.cat ⟩ (𝓜.cat .id 𝓜.,p (𝓜.retP ∘⟨ 𝓜.cat ⟩ (𝓜.!t 𝓜.,p 𝓜.π₂)))
    explicit = sym (cong₂ (comp' 𝓜.cat) (sym 𝓜.bind-natural) refl
      ∙  sym (𝓜.cat .⋆Assoc _ _ _)
      ∙ cong₂ (comp' 𝓜.cat) refl (𝓜.,p-natural ∙ cong₂ 𝓜._,p_ (sym (𝓜.cat .⋆Assoc _ _ _) ∙ cong₂ (comp' 𝓜.cat) refl 𝓜.×β₁ ∙ 𝓜.cat .⋆IdL _)
        (𝓜.×β₂ ∙ cong₂ (comp' 𝓜.cat) refl (cong₂ 𝓜._,p_ 𝓜.𝟙η' refl) ∙ 𝓜.η-natural {γ = 𝓜.!t}))
      ∙ 𝓜.bindP-l)
  ⟦ dn S⊑T ⟧E = ⟦ S⊑T .ty-prec ⟧p ∘⟨ 𝓜.cat ⟩ 𝓜.π₂
  ⟦ isSetEvCtx E F p q i j ⟧E = 𝓜.cat .isSetHom ⟦ E ⟧E ⟦ F ⟧E (cong ⟦_⟧E p) (cong ⟦_⟧E q) i j

  ⟦ E [ M ]∙ ⟧C = (COMP _ 𝓜 ⟪ ⟦ E ⟧E ⟫) ⟦ M ⟧C
  ⟦ plugId {M = M} i ⟧C = (COMP _ 𝓜 .F-id i) ⟦ M ⟧C
  ⟦ plugAssoc {F = F}{E = E}{M = M} i ⟧C = (COMP _ 𝓜 .F-seq ⟦ E ⟧E ⟦ F ⟧E i) ⟦ M ⟧C

  ⟦ M [ γ ]c ⟧C = ⟦ M ⟧C ∘⟨ 𝓜.cat ⟩ ⟦ γ ⟧S
  ⟦ substId {M = M} i ⟧C = 𝓜.cat .⋆IdL ⟦ M ⟧C i
  ⟦ substAssoc {M = M}{δ = δ}{γ = γ} i ⟧C = 𝓜.cat .⋆Assoc ⟦ γ ⟧S ⟦ δ ⟧S ⟦ M ⟧C i
  ⟦ substPlugDist {E = E}{M = M}{γ = γ} i ⟧C = COMP-Enriched 𝓜 ⟦ γ ⟧S ⟦ M ⟧C ⟦ E ⟧E i
  ⟦ err ⟧C = 𝓜.err
  ⟦ strictness {E = E} i ⟧C = 𝓜.℧-homo ⟦ E ⟧E i

  ⟦ ret ⟧C = 𝓜.retP
  -- (bind M [ wk ]e [ ret [ !s ,s var ]c ]∙)
  -- ≡ bind (π₂ ^* M) ∘ (id , ret [ !s ,s var ]c)
  -- ≡ bind (π₂ ^* M) ∘ (id , id ∘ (! , π₂))
  -- ≡ π₂ ^* bind M ∘ (id , (! , π₂))
  -- ≡ M
  ⟦ ret-β {S}{T}{Γ}{M = M} i ⟧C = explicit i where
    explicit :
    -- pull γ ⟪ f ⟫ = f ∘ ((γ ∘⟨ C ⟩ π₁) ,p π₂)
    -- pull π₁ ⟪ f ⟫ = f ∘ ((π₁ ∘⟨ C ⟩ π₁) ,p π₂)
      𝓜.bindP ((𝓜.pull 𝓜.π₁) ⟪ ⟦ M ⟧C ⟫)
        ∘⟨ 𝓜.cat ⟩ (𝓜.cat .id 𝓜.,p (𝓜.retP ∘⟨ 𝓜.cat ⟩ (𝓜.!t 𝓜.,p 𝓜.π₂)))
      ≡ ⟦ M ⟧C
    explicit =
      cong₂ (comp' 𝓜.cat) (sym 𝓜.bind-natural) refl
      ∙ (sym (𝓜.cat .⋆Assoc _ _ _)
      -- (π₁ ∘ π₁ ,p π₂) ∘ ((𝓜.cat .id) ,p (η ∘ !t , π₂))
      -- (π₁ ∘ π₁ ,p π₂) ∘ ((𝓜.cat .id) ,p (η ∘ !t , π₂))
      ∙ cong₂ (comp' 𝓜.cat) refl (𝓜.,p-natural ∙ cong₂ 𝓜._,p_ (sym (𝓜.cat .⋆Assoc _ _ _) ∙ cong₂ (comp' 𝓜.cat) refl 𝓜.×β₁ ∙ 𝓜.cat .⋆IdL _) 𝓜.×β₂))
      -- ret ∘ (!t , π₂)
      -- ≡ ret ∘ (π₁ ∘ !t , π₂)
      ∙ cong₂ (comp' (𝓜.With ⟦ Γ ⟧ctx)) refl (cong₂ (comp' 𝓜.cat) refl (cong₂ 𝓜._,p_ 𝓜.𝟙η' refl) ∙ 𝓜.η-natural {γ = 𝓜.!t})
      ∙ 𝓜.bindP-l

  ⟦ app ⟧C = {!!}
  ⟦ fun-β i ⟧C = {!!}

  ⟦ matchNat Mz Ms ⟧C = {!!}
  ⟦ matchNatβz Mz Ms i ⟧C = {!!}
  ⟦ matchNatβs Mz Ms V i ⟧C = {!!}
  ⟦ matchNatη i ⟧C = {!!}

  ⟦ isSetComp M N p q i j ⟧C = 𝓜.cat .isSetHom ⟦ M ⟧C ⟦ N ⟧C (cong ⟦_⟧C p) (cong ⟦_⟧C q) i j

-}
