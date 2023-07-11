{-# OPTIONS --cubical --rewriting --guarded #-}
 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.RepresentationSemantics (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Syntax.Types
open import Syntax.Terms
open import Syntax.Logic

open import Common.Common
open import Cubical.Relation.Binary.Poset
open import Common.Poset.Convenience
open import Common.Poset.Constructions
open import Common.Poset.Monotone
open import Common.Poset.MonotoneRelation
open import Semantics.MonotoneCombinators

open import Semantics.Lift k
open import Semantics.Concrete.MonotonicityProofs k
open import Semantics.LockStepErrorOrdering k
open import Semantics.Concrete.Dyn k


open LiftPoset
open Clocked k

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓR : Level

----------------------------------
-- Left pseudo-representation
----------------------------------
record LeftRep (X Y : Poset ℓ ℓ') (R : MonRel X Y {ℓR}) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓR)) where
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
record RightRep (X Y : Poset ℓ ℓ') (R : MonRel X Y {ℓR}) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓR)) where

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



record RepresentableRel (X Y : Poset ℓ ℓ') (ℓo : Level) : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-suc ℓo))) where
  field
    R : MonRel X Y {ℓo}
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
IdRepRel : {ℓo : Level} -> (X : Poset ℓ ℓ') -> RepresentableRel X X (ℓ-max ℓo ℓ')
IdRepRel X .R = poset-monrel X
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
{-
record {
  e = record { f = λ f ->
                 record { f = λ b -> mapL (MonFun.f (co .leftRep .e)) (ext (MonFun.f f) (MonFun.f (ci .rightRep .p) (η b))) ;
               isMon = {!!} } ; isMon = {!!} } ;
  δX = record { f = λ f ->
                 record { f = λ a -> mapL (MonFun.f (co .leftRep .δX)) (ext (MonFun.f f) (MonFun.f (ci .rightRep .δX) (η a))) ;
               isMon = {!!} } ; isMon = {!!} } ;
  δY = {!!} ;
  UpL = {!!} ;
  UpR = λ f g f≤g ai bi ai≤bi → mapL-monotone-het {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} }
-}


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
  δY = {!!} ;
  UpL = {!!} ;
  UpR = λ f g f≤g ai bi ai≤bi →
    mapL-monotone-het (rel Ao) (co .R .R) (MonFun.f (co .leftRep .δX)) (MonFun.f (co .leftRep .e)) (co .leftRep .UpR) {!!} {!!}
      {!!} }

RepFun ci co .rightRep = {!!}

--
-- Pseudo-representable relations involving Dyn
--


injℕ : RepresentableRel ℕ DynP ℓR
injℕ .R = functionalRel InjNat Id (poset-monrel DynP)
injℕ .leftRep = record {
  e = {!!} ;
  δX = {!!} ;
  δY = {!!} ;
  UpL = {!!} ;
  UpR = {!!} }
injℕ .rightRep = {!!}


injArr : RepresentableRel (DynP ==> 𝕃 DynP) DynP ℓR
injArr .R = {!!}
injArr .leftRep = {!!}
injArr .rightRep = {!!}


--
-- Composing pseudo-representable relations
-- Note: It is not in general possible to compose arbitrary pseudo-rep
-- relations. But the relations corresponding to our syntactic type
-- precision *do* satisfy the needed conditions for composition.
--

composeRep : {A B C : Poset ℓ ℓ'} ->
  (c : RepresentableRel A B ℓR) ->
  (d : RepresentableRel B C ℓR) ->
  RepresentableRel A C (ℓ-max ℓ ℓR)
composeRep c d .R = CompMonRel (c .R) (d .R)
composeRep c d .leftRep = record {
  e = mCompU (d .leftRep .e) (c .leftRep .e) ;
  δX = {!!} ;
  δY = {!!} ;
  UpL = {!!} ;
  UpR = {!!} }
composeRep c d .rightRep = record {
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
