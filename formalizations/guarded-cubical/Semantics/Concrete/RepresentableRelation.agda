{-# OPTIONS --cubical --rewriting --guarded #-}
 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.RepresentableRelation (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.HITs.PropositionalTruncation

--open import Syntax.Types
--open import Syntax.Terms
--open import Syntax.Logic

open import Common.Common
open import Cubical.Relation.Binary.Poset
open import Common.Poset.Convenience
open import Common.Poset.Constructions
open import Common.Poset.Monotone
open import Common.Poset.MonotoneRelation
open import Semantics.MonotoneCombinators

open import Semantics.Lift k
open import Semantics.Concrete.MonotonicityProofs
open import Semantics.LockStepErrorOrdering k
open import Semantics.Concrete.DynNew k


open LiftPoset
open ClockedCombinators k
open ClockedProofs k

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓ'X ℓY ℓ'Y : Level
    ℓX' ℓ'X' ℓY' ℓ'Y' : Level
    ℓR ℓR' : Level

----------------------------------
-- Left pseudo-representation
----------------------------------
record LeftRep (X : Poset ℓX ℓ'X) (Y : Poset ℓY ℓ'Y) (R : MonRel X Y ℓR) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) (ℓ-suc ℓR)) where
  field
    e : MonFun X Y
    δX : MonFun X X
    δY : MonFun Y Y

    --  UpL:                   UpR:
    --
    --        R                   ⊑X
    --   X o----* Y           X o----* X
    --   |        |           |        |
    -- e |        | δY    δX  |        | e
    --   v        v           v        v
    --   Y o----* Y           X o----* Y
    --       ⊑Y                   R
    
    UpL : TwoCell (MonRel.R R) (rel Y) (MonFun.f e) (MonFun.f δY)
    UpR : TwoCell (rel X) (MonRel.R R) (MonFun.f δX) (MonFun.f e)


----------------------------------
-- Right pseudo-representation
----------------------------------
record RightRep (X : Poset ℓX ℓ'X) (Y : Poset ℓY ℓ'Y) (R : MonRel X Y ℓR) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) (ℓ-suc ℓR)) where

  LR = LiftMonRel.ℝ X Y R
  field
    p  : MonFun (𝕃 Y) (𝕃 X)

    δX : MonFun (𝕃 X) (𝕃 X)
    δY : MonFun (𝕃 Y) (𝕃 Y)

    dnR : TwoCell (MonRel.R LR) (rel (𝕃 X)) (MonFun.f δX) (MonFun.f p)
    dnL : TwoCell (rel (𝕃 Y)) (MonRel.R LR) (MonFun.f p) (MonFun.f δY)

    --  DnR:                      DnL:
    --
    --          L R                         ⊑LY
    --    L X o----* L Y              L Y o----* L Y
    --     |          |                 |        |
    -- δX  |          |  p           p  |        | δY
    --     v          v                 v        v
    --    L X o----* L X              L X o----* L Y
    --          ⊑LX                         L R



record RepresentableRel (X : Poset ℓX ℓ'X) (Y : Poset ℓY ℓ'Y) (ℓo : Level) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) (ℓ-suc ℓo)) where
  field
    R : MonRel X Y ℓo
    leftRep  : LeftRep  {ℓR = ℓo} X Y R
    rightRep : RightRep {ℓR = ℓo} X Y R


---------------------------------------------------------
-- Constructions Involving Pseudo-Representable Relations
---------------------------------------------------------

open LeftRep
open RightRep
open RepresentableRel

--
-- Pseudo-representation of the identity relation on a poset X
--
IdRepRel : {ℓo : Level} -> (X : Poset ℓ ℓ') ->
  RepresentableRel X X (ℓ-max ℓo ℓ')
IdRepRel {ℓo = ℓo} X .R = poset-monrel {ℓo = ℓo} X
IdRepRel X .leftRep = record {
  e = MonId ;
  δX = MonId ;
  δY = MonId ;
  UpL = λ _ _ p -> lower p ;
  UpR = λ _ _ p -> lift p }
IdRepRel X .rightRep = record {
  p = MonId ;
  δX = MonId ;
  δY = MonId ;
  dnR = λ lx ly lx≤ly → {!!} ;
  dnL = λ lx ly lx≤ly → {!!} }


-- "Product" of pseudo-representable relations
RepRel× : {X : Poset ℓX ℓ'X} {X' : Poset ℓX' ℓ'X'}
          {Y : Poset ℓY ℓ'Y} {Y' : Poset ℓY' ℓ'Y'} ->
  RepresentableRel X X' ℓR ->
  RepresentableRel Y Y' ℓR' ->
  RepresentableRel (X ×p Y) (X' ×p Y') (ℓ-max ℓR ℓR')
RepRel× c d .R = c .R ×monrel d .R
RepRel× c d .leftRep = record {
  e = {!!} ;
  δX = {!!} ;
  δY = {!!} ;
  UpL = {!!} ;
  UpR = {!!} }
RepRel× c d .rightRep = record {
  p = {!!} ;
  δX = {!!} ;
  δY = {!!} ;
  dnR = {!!} ;
  dnL = {!!} }


--
-- Lifting pseudo-representable relations to a pseudo-representable relation
-- between functions into Lift
--
open MonRel
RepFun : {Ai Ao Bi Bo : Poset ℓ ℓ'} ->
  RepresentableRel Ai Bi ℓR ->
  RepresentableRel Ao Bo ℓR ->
  RepresentableRel (Ai ==> 𝕃 Ao) (Bi ==> 𝕃 Bo) (ℓ-max ℓ ℓR)
RepFun {Ao = Ao} {Bo = Bo} ci co .R =
  (ci .R) ==>monrel (LiftMonRel.ℝ Ao Bo (co .R)) 
RepFun {Ai = Ai} {Ao = Ao} {Bi = Bi} {Bo = Bo} ci co .leftRep = 

 record {
  e = Curry (
    mMap' (With2nd (co .leftRep .e)) ∘m  -- With2nd (U mMap (co .leftRep .e)) ∘m
    (Uncurry mExt) ∘m
    With2nd (mCompU (ci .rightRep .p) mRet) ∘m
    --With2nd (ci .rightRep .p) ∘m
    --With2nd mRet ∘m
    π2) ;
    
  δX = Curry (
    mMap' (With2nd (co .leftRep .δX)) ∘m
    (Uncurry mExt) ∘m
    With2nd (mCompU (ci .rightRep .δX) mRet) ∘m
    π2) ;

  δY = Curry (
    mMap' (With2nd (co .leftRep .δY)) ∘m
    (Uncurry mExt) ∘m
    With2nd (mCompU (ci .rightRep .δY) mRet) ∘m
    π2) ;
  
  UpL = λ f g f≤g bi ->
    mapL-monotone-het _ _
    (MonFun.f (co .leftRep .e))
    (MonFun.f (co .leftRep .δY))
    (co .leftRep .UpL) _ _
    (ext-monotone-het _ _ (MonFun.f f) (MonFun.f g) f≤g _ _ (ci .rightRep .dnL _ _ {!!})) ;
  
  UpR = λ f g f≤g ai bi ai≤bi ->
    mapL-monotone-het
      (rel (Ao))
      (co .R .R)
      (MonFun.f (co .leftRep .δX))
      (MonFun.f (co .leftRep .e))
      (co .leftRep .UpR)
      _ _ (bind-monotone (MonFun.f f) (MonFun.f g)
        (ci .rightRep .dnR _ _ (ret-monotone-het _ ai bi ai≤bi)) (≤mon→≤mon-het f g f≤g)) }

RepFun ci co .rightRep = record {
  p = U mMap {!!} ;
  δX = {!!} ;
  δY = {!!} ;
  dnR = {!!} ;
  dnL = {!!} }

--
-- Pseudo-representable relations involving Dyn
--


injℕ : RepresentableRel ℕ DynP ℓR
injℕ .R = functionalRel InjNat Id (poset-monrel DynP)
injℕ .leftRep = record {
  e = InjNat ;
  δX = Id ;
  δY = Id ;
  UpL = λ n d n≤d → lower n≤d ;

  -- Know: n is related to m (i.e. n = m)
  -- NTS:  InjNat n is related to InjNat m
  UpR = λ n m n≡m → lift (MonFun.isMon InjNat n≡m) }
  
injℕ .rightRep = record {
  p = U mExt ProjNat ;
  δX = U mExt mRet ; -- ext ret (which equals id)
  δY = U mExt mRet ;
  dnR = λ ln ld ln≤ld →
    ext-monotone-het {!!} (rel ℕ) ret (MonFun.f ProjNat)
    (λ n d n≤d → {!!}) ln ld ln≤ld ;
  dnL = {!!} }


injArr : RepresentableRel (DynP ==> 𝕃 DynP) DynP ℓR
injArr .R = functionalRel InjArr Id (poset-monrel DynP)
injArr .leftRep = record {
  e = InjArr ;
  δX = Id ;
  δY = Id ;
  UpL = λ f d f≤d → lower f≤d ;
  UpR = λ f g f≤g → lift (MonFun.isMon InjArr f≤g) }
  
injArr .rightRep = record { p = ? ; δX = ? ; δY = ? ; dnR = ? ; dnL = ? }


--
-- Composing pseudo-representable relations
-- Note: It is not in general possible to compose arbitrary pseudo-rep
-- relations. But the relations corresponding to our syntactic type
-- precision *do* satisfy the needed conditions for composition.
--

composeRep : {A B C : Poset ℓ ℓ'} ->
  (c : RepresentableRel A B ℓR) ->
  (d : RepresentableRel B C ℓR) ->
  (c-filler-left : Σ[ f ∈ (MonFun A A) ]
    TwoCell (c .R .R) (c .R .R) (MonFun.f f) (MonFun.f (d .leftRep .δX))) ->
  (d-filler-right : Σ[ f ∈ (MonFun C C) ]
    TwoCell (d .R .R) (d .R .R) (MonFun.f (c .leftRep .δY)) (MonFun.f f)) ->
  RepresentableRel A C (ℓ-max ℓ ℓR)
composeRep c d c-filler-l d-filler-r .R = CompMonRel (c .R) (d .R)
composeRep {C = C} c d c-filler-l d-filler-r .leftRep = record {
  e = mCompU (d .leftRep .e) (c .leftRep .e) ;
  δX = {!!} ;
  δY = {!!} ;
  UpL =  λ x z x≤z -> elim
    (λ _ -> isPropValued-poset C _ _)
    (λ { (y , x≤y , y≤z) -> d .leftRep .UpL _ _
      (is-antitone (d .R) (c .leftRep .UpL x y x≤y) {!!}) })
    x≤z  ;
  UpR = {!!} }
composeRep c d c-filler-l d-filler-r .rightRep = record {
  p = {!!} ;
  δX = {!!} ;
  δY = {!!} ;
  dnR = {!!} ;
  dnL = {!!} }




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
