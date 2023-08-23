{-# OPTIONS --cubical --rewriting --guarded #-}
 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Common
open import Common.Later

module Semantics.RepresentationSemantics (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.CommMonoid.Base
open import Cubical.Algebra.Monoid.More

open import Syntax.Types
open import Syntax.Terms
open import Syntax.Logic

open import Cubical.Relation.Binary.Poset
open import Common.Poset.Convenience
open import Common.Poset.Constructions
open import Common.Poset.Monotone
open import Common.Poset.MonotoneRelation

open import Semantics.Lift k
open import Semantics.Concrete.MonotonicityProofs
open import Semantics.MonotoneCombinators
open import Semantics.LockStepErrorOrdering k
-- open import Semantics.Concrete.DynNew k

open import Semantics.Concrete.PosetWithPtbs.Base k
open import Semantics.Concrete.PosetWithPtbs.Constructions k
open import Semantics.Concrete.PosetWithPtbs.DynPWP k




open LiftPoset
open ClockedProofs k
open ClockedCombinators k

open PosetWithPtb

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓR : Level

----------------------------------
-- Left pseudo-representation
----------------------------------
record LeftRep (X Y : PosetWithPtb ℓ ℓ' ℓ'') (R : MonRel (X .P) (Y .P) ℓR) :
  Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓR))) where
  𝕏 = X .P
  𝕐 = Y .P

  field
    e : MonFun 𝕏 𝕐
    δX : ⟨ X .Perturbᴱ ⟩
    δY : ⟨ Y .Perturbᴱ ⟩

    --  UpL:                   UpR:
    --
    --        R                   ⊑X
    --   X o----* Y           X o----* X
    --   |        |           |        |
    -- e |        | δY    δX  |        | e
    --   v        v           v        v
    --   Y o----* Y           X o----* Y
    --       ⊑Y                   R
    
    UpL : TwoCell (MonRel.R R) (rel 𝕐) (MonFun.f e) (MonFun.f (ptb-funᴱ Y δY))
    UpR : TwoCell (rel 𝕏) (MonRel.R R) (MonFun.f (ptb-funᴱ X δX)) (MonFun.f e)



----------------------------------
-- Right pseudo-representation
----------------------------------
record RightRep (X Y : PosetWithPtb ℓ ℓ' ℓ'') (R : MonRel (X .P) (Y .P) ℓR) :
  Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓR))) where
  𝕏 = X .P
  𝕐 = Y .P

  LR = LiftMonRel.ℝ 𝕏 𝕐 R
  field
    p  : MonFun (𝕃 𝕐) (𝕃 𝕏)

    δX : ⟨ 𝕃PWP X .Perturbᴾ ⟩
    δY : ⟨ 𝕃PWP Y .Perturbᴾ ⟩

    dnR : TwoCell (MonRel.R LR) (rel (𝕃 𝕏)) (MonFun.f (ptb-funᴾ (𝕃PWP X) δX)) (MonFun.f p)
    dnL : TwoCell (rel (𝕃 𝕐)) (MonRel.R LR) (MonFun.f p) (MonFun.f (ptb-funᴾ (𝕃PWP Y) δY))

    --  DnR:                      DnL:
    --
    --          L R                         ⊑LY
    --    L X o----* L Y              L Y o----* L Y
    --     |          |                 |        |
    -- δX  |          |  p           p  |        | δY
    --     v          v                 v        v
    --    L X o----* L X              L X o----* L Y
    --          ⊑LX                         L R

-----------------------------------------------------------------
-- A *(psuedo) representable relation* c between posets-with-
-- perturbations X and Y consists of:
--
--   - A monotone relation R between the underlying posets
--   - A left representation of R
--   - A right representation of R
--   - The existence of fillers of squares by perturbations
--
----------------------------------------------------------------
record RepresentableRel (X Y : PosetWithPtb ℓ ℓ' ℓ'') (ℓo : Level) :
  Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' (ℓ-suc ℓo)))) where
  open PosetWithPtb
  field
    R : MonRel (X .P) (Y .P) ℓo
    leftRep  : LeftRep  {ℓR = ℓo} X Y R
    rightRep : RightRep {ℓR = ℓo} X Y R
    fillers  : FillersFor X Y R

unquoteDecl RepRelIsoΣ = declareRecordIsoΣ RepRelIsoΣ (quote (RepresentableRel))

isSetRepRel : ∀ {ℓ ℓ' ℓ'' ℓo} {X Y : PosetWithPtb ℓ ℓ' ℓ''} -> isSet (RepresentableRel X Y ℓo)
isSetRepRel = isSetRetract (Iso.fun RepRelIsoΣ) (Iso.inv RepRelIsoΣ)
  (λ R -> Iso.leftInv RepRelIsoΣ R)
  (isSetΣ isSetMonRel (λ R -> isSet× {!!} {!!}))


---------------------------------------------------------
-- Constructions Involving Pseudo-Representable Relations
---------------------------------------------------------

open LeftRep
open RightRep
open RepresentableRel
open FillersFor

--
-- Pseudo-representation of the identity relation on a poset X
--
IdRepRel : {ℓo : Level} -> (X : PosetWithPtb ℓ ℓ' ℓ'') -> RepresentableRel X X (ℓ-max ℓo ℓ')
IdRepRel {ℓo = ℓo} X .R = poset-monrel {ℓo = ℓo} (X .P)
IdRepRel X .leftRep = record {
  e = MonId ;
  δX = monoidId (CommMonoid→Monoid (X .Perturbᴱ)) ;
  δY = monoidId (CommMonoid→Monoid (X .Perturbᴱ)) ;
  UpL = λ _ _ p -> {!!} ;
  UpR = λ _ _ p -> {!!} }
IdRepRel X .rightRep = record {
  p = MonId ;
  δX = commMonoidId (𝕃PWP X .Perturbᴾ) ;
  δY = commMonoidId (𝕃PWP X .Perturbᴾ) ;
  dnR = λ lx ly lx≤ly → {!!} ;
  dnL = λ lx ly lx≤ly → {!!} }
IdRepRel X .fillers .fillerL-e δᴮ = δᴮ , {!!}
IdRepRel X .fillers .fillerL-p = {!!}
IdRepRel X .fillers .fillerR-e = {!!}
IdRepRel X .fillers .fillerR-p = {!!}





--
-- Lifting pseudo-representable relations to a pseudo-representable
-- relation between functions into Lift
--
open MonRel
RepFun : {Ai Ao Bi Bo : PosetWithPtb ℓ ℓ' ℓ''} ->
  RepresentableRel Ai Bi ℓR ->
  RepresentableRel Ao Bo ℓR ->
  RepresentableRel (Ai ==>L  Ao) (Bi ==>L Bo) (ℓ-max ℓ ℓR)
RepFun {Ao = Ao} {Bo = Bo} ci co .R =
  (ci .R) ==>monrel (LiftMonRel.ℝ (Ao .P) (Bo .P) (co .R)) 
RepFun {Ai = Ai} {Ao = Ao} {Bi = Bi} {Bo = Bo} ci co .leftRep = 
 record {
  e = Curry (
    mMap' (With2nd (co .leftRep .e))        ∘m  -- With2nd (U mMap (co .leftRep .e)) ∘m
    Uncurry mExt                            ∘m
    With2nd (mCompU (ci .rightRep .p) mRet) ∘m
    --With2nd (ci .rightRep .p) ∘m
    --With2nd mRet ∘m
    π2) ;

  δX = (ci .rightRep .δX) , (co .leftRep .δX) ;
  δY = (ci .rightRep .δY) , (co .leftRep .δY) ;

  UpL = λ f g f≤g bi ->
    mapL-monotone-het _ _
    (MonFun.f (co .leftRep .e))
    (MonFun.f (ptb-funᴱ Bo (co .leftRep .δY)))
    (co .leftRep .UpL) _ _
    (ext-monotone-het _ _ (MonFun.f f) (MonFun.f g) f≤g _ _ (ci .rightRep .dnL _ _ {!!})) ;

  UpR = λ f g f≤g ai bi ai≤bi ->
    mapL-monotone-het
      (rel (Ao .P))
      (co .R .R)
      (MonFun.f (ptb-funᴱ Ao (co .leftRep .δX)))
      (MonFun.f (co .leftRep .e))
      (co .leftRep .UpR)
      _ _ (bind-monotone (MonFun.f f) (MonFun.f g)
        (ci .rightRep .dnR _ _ (ret-monotone-het _ ai bi ai≤bi)) (≤mon→≤mon-het f g f≤g))
  }


RepFun ci co .rightRep = {!!}

RepFun {Ai = Ai} {Ao = Ao} {Bi = Bi} {Bo = Bo}
       ci co .fillers .fillerL-e (δ-LBi , δ-Bo) =
  (filler-left-in .fst , filler-left-out .fst) ,
  λ f g f≤g ai bi ai≤bi →
    mapL-monotone-het _ _
      (MonFun.f (ptb-funᴱ Ao (filler-left-out .fst)))
      (MonFun.f (ptb-funᴱ Bo δ-Bo))
      (filler-left-out .snd) _ _
      (ext-monotone-het _ _ (MonFun.f f) (MonFun.f g) f≤g _ _
      (filler-left-in .snd _ _ (ret-monotone-het (R ci .R) ai bi ai≤bi)))
  where
    filler-left-in  = ci .fillers .fillerL-p δ-LBi -- filler for domain
    filler-left-out = co .fillers .fillerL-e δ-Bo  -- filler for codomain
   
RepFun ci co .fillers .fillerL-p = {!!}
RepFun ci co .fillers .fillerR-e = {!!}
RepFun ci co .fillers .fillerR-p = {!!}


--
-- Pseudo-representable relations involving Dyn
--

-- inj-nat
{-
injℕ : RepresentableRel ℕ DynPWP ℓR
injℕ .R = functionalRel InjNat Id (poset-monrel DynP)
injℕ .leftRep = record {
  e = InjNat ;
  δX = Id ;
  δY = Id ;
  UpL = λ n d H → lower H ;
  UpR = λ n m n≡m → lift (MonFun.isMon InjNat n≡m) }
injℕ .rightRep = record {
  p = U mExt ProjNat ;
  δX = U mExt mRet ;
  δY = U mExt mRet ;
  dnR = λ ln ld ln≤ld → ext-monotone-het
    (injℕ .R .R) (rel ℕ) _ _
    (λ n d n≤d → {!!})
    ln ld ln≤ld ;
  dnL = {!!} }


-- inj-arrow
injArr : RepresentableRel (DynP ==> 𝕃 DynP) DynP ℓR
injArr .R = functionalRel InjArr Id (poset-monrel DynP)
injArr .leftRep = record {
  e = InjArr ;
  δX = Id ;
  δY = Id ;
  UpL = λ f d H → lower H ;
  UpR = λ f g f≤g → lift (MonFun.isMon InjArr f≤g) }
injArr .rightRep = {!!}
-}



--
-- Composing pseudo-representable relations
--

{-
composeRep : {A B C : PosetWithPtb ℓ ℓ' ℓ''} ->
  (c : RepresentableRel A B ℓR) ->
  (d : RepresentableRel B C ℓR) ->
  -- (c-left : Σ[ f ∈ (MonFun A A) ]
  --   TwoCell (c .R .R) (c .R .R) (MonFun.f f) (MonFun.f (d .leftRep .δX))) ->
  -- (d-right : Σ[ f ∈ (MonFun C C) ]
  --   TwoCell (d .R .R) (d .R .R) (MonFun.f (c .leftRep .δY)) (MonFun.f f)) ->
  RepresentableRel A C (ℓ-max ℓ ℓR)
  
composeRep c d .R = CompMonRel (c .R) (d .R)
composeRep {C = C} c d .leftRep = record {
  e = mCompU (d .leftRep .e) (c .leftRep .e) ;
  δX = mCompU {!!} (c .leftRep .δX) ;
  δY = mCompU (d .leftRep .δY) {!!} ;

  UpL = λ x z x≤z -> elim
    (λ _ -> isPropValued-poset (C .P) _ _)
    (λ { (y , x≤y , y≤z) -> d .leftRep .UpL _ _
      (is-antitone (d .R) (c .leftRep .UpL x y x≤y) {!!}) })
    x≤z ;

  {-
  UpL = λ x z (y , x≤y , y≤z) →
    d .leftRep .UpL _ _
      (is-antitone (d .R) (c .leftRep .UpL x y x≤y) (d-r .snd y z y≤z)) ;
  -}
      
  UpR = {!!} }
composeRep c d .rightRep = record {
  p = mCompU (c .rightRep .p) (d .rightRep .p) ;
  δX = {!!} ;
  δY = {!!} ;
  dnR = {!!} ;
  dnL = {!!} }

-}






-- Every syntactic type precision c : A ⊑ B denotes:
-- 1. ⟦c⟧ : ⟦A⟧ o-* ⟦B⟧
-- 2. A left-representation of ⟦c⟧
-- 3. A right-representation of ⟦c⟧

{-
⟦_⟧ty : Ty -> Poset ℓ-zero ℓ-zero
⟦ nat ⟧ty = ℕ
⟦ dyn ⟧ty = {!!}
⟦ A ⇀ B ⟧ty = ⟦ A ⟧ty ==> ⟦ B ⟧ty

rep : (A B : Ty) -> A ⊑ B -> RepresentableRel ⟦ A ⟧ty ⟦ B ⟧ty
rep .nat .nat nat = IdRepRel ℕ
rep .dyn .dyn dyn = IdRepRel DynP
rep (Ai ⇀ Ao) (Bi ⇀ Bo) (ci ⇀ co) = RepFun (rep _ _ ci) (rep _ _ co)
rep .nat .dyn inj-nat = {!!}
rep A .dyn (inj-arr c) = {!!}
-}



