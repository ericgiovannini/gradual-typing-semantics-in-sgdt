{-# OPTIONS --cubical --rewriting --guarded #-}
 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.RepresentableRelation (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (elim)

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


open LiftPoset using (𝕃)
open ClockedCombinators k
open ClockedProofs k

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓ'X ℓY ℓ'Y : Level
    ℓX' ℓ'X' ℓY' ℓ'Y' : Level
    ℓR ℓR' : Level

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

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
  dnR = λ lx lx' lx≤lx' → {!!};
  dnL = λ lx lx' lx≤lx' → {!MonRel.R !} }
  -- How to construct a relation?


-- "Product" of pseudo-representable relations
RepRel× : {X : Poset ℓX ℓ'X} {X' : Poset ℓX' ℓ'X'}
          {Y : Poset ℓY ℓ'Y} {Y' : Poset ℓY' ℓ'Y'} ->
  RepresentableRel X X' ℓR ->
  RepresentableRel Y Y' ℓR' ->
  RepresentableRel (X ×p Y) (X' ×p Y') (ℓ-max ℓR ℓR')
RepRel× c d .R = c .R ×monrel d .R
RepRel× {X = X} {X' = X'} {Y = Y} {Y' = Y'} c d .leftRep = record {
  e = PairFun (With1st (c .leftRep .e)) (With2nd (d .leftRep .e)) ;
  δX = PairFun (With1st (c .leftRep .δX)) (With2nd (d .leftRep .δX)) ;
  δY = PairFun (With1st (c .leftRep .δY)) (With2nd (d .leftRep .δY)) ;
  UpL = λ (x , y) (x' , y') (p1 , p2) → c .leftRep .UpL x x' p1 , d .leftRep .UpL y y' p2 ;
  UpR = λ (x , y) (x' , y') (p1 , p2) → c .leftRep .UpR x x' p1 , d .leftRep .UpR y y' p2 }
{- (X' .snd PosetStr.≤
       MonFun.f (With1st (c .leftRep .e)) .patternInTele0) x'-}
RepRel× {X = X} {X' = X'} {Y = Y} {Y' = Y'} c d .rightRep = record {
  p = mCompU (mCompU (mLift×p' X Y)
             (PairFun (With1st (c .rightRep .p)) (With2nd (d .rightRep .p))))
             (mLift×p X' Y') ;
  δX = mCompU (mCompU (mLift×p' X Y)
              (PairFun (With1st (c .rightRep .δX)) (With2nd (d .rightRep .δX))))
              (mLift×p X Y) ;
  δY = mCompU (mCompU (mLift×p' X' Y')
              (PairFun (With1st (c .rightRep .δY)) (With2nd (d .rightRep .δY))))
              (mLift×p X' Y') ;
  dnR = λ l l' l≤l' → lift×-inv-monotone _ _
    ((c .rightRep .dnR _ _
      (lift×-monotone-het _ _ l l'
      l≤l' .fst))
    , (d .rightRep .dnR _ _
        (lift×-monotone-het _ _ l l'
        l≤l' .snd))) ;
  dnL = λ l l' l≤l' → lift×-inv-monotone-het _ _ _ _ 
    (c .rightRep .dnL _ _
      (lift×-monotone l l' l≤l' .fst)
    , d .rightRep .dnL _ _
      (lift×-monotone l l' l≤l' .snd)) }

{-
(LX' × LY' → LX)  ->  (LX' × LY' → LY) -> 
-}

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
  
  UpL = λ f g f≤g bi -> mapL-monotone-het _ _
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

RepFun {Ai = Ai} {Ao = Ao} {Bi = Bi} {Bo = Bo} ci co .rightRep = record {
  p = U mMap (Curry (With2nd (co .rightRep .p) ∘m App ∘m With2nd (ci .leftRep .e))) ;
  δX = U mMap (Curry (With2nd (co .rightRep .δX) ∘m App ∘m With2nd (ci .leftRep .δX))) ;
  δY = U mMap (Curry (With2nd (co .rightRep .δY) ∘m App ∘m With2nd (ci .leftRep .δY))) ;
  dnR = λ lf lg lf≤lg → mapL-monotone-het _ _
    (MonFun.f (Curry (With2nd (co .rightRep .δX) ∘m App ∘m With2nd (ci .leftRep .δX))))
    (MonFun.f (Curry (With2nd (co .rightRep .p) ∘m App ∘m With2nd (ci .leftRep .e))))
    (λ f g f≤g ai → co .rightRep .dnR _ _ {!!}) lf lg lf≤lg ; --todo ℓ' != ℓR of type Level
  dnL = λ lg lg' lg≤lg' → mapL-monotone-het _ _
    (MonFun.f (Curry (With2nd (co .rightRep .p) ∘m App ∘m With2nd (ci .leftRep .e))))
    (MonFun.f (Curry (With2nd (co .rightRep .δY) ∘m App ∘m With2nd (ci .leftRep .δY))))
    (λ g g' g≤g' ai bi ai≤bi → co .rightRep .dnL _ _
      (≤mon→≤mon-het g g' g≤g' {!!} {!!} {!!}) --(≤mon→≤mon-het g g' g≤g' _ _ (ci .leftRep .UpL ai bi ai≤bi))
      )
    lg lg' lg≤lg' }


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
    ext-monotone-het (R (injℕ .R)) (rel ℕ) ret (MonFun.f ProjNat)
    (λ n d n≤d → {!R!}) ln ld ln≤ld ;
  dnL = λ ld ld' ld≤ld' →
    ext-monotone-het (rel DynP) (R (injℕ .R)) (MonFun.f ProjNat) ret
    (λ d d' d≤d' → {!!}) ld ld' ld≤ld' }


Rel : ∀ ℓ -> _
Rel ℓ = functionalRel InjArr Id (poset-monrel {ℓo = ℓ} DynP)

Rel-lem : ∀ f d ℓ -> R (Rel ℓ) f d ->
  Σ[ g~ ∈ ⟨ ▹' k ((DynP ==> 𝕃 DynP)) ⟩ ]
    (transport  ⟨DynP⟩-Sum d ≡ inr g~) × (▸ (λ t -> f ≤mon g~ t))
Rel-lem f d ℓ injA = (transport {!!} {!!}) , ({!!} , {!!})
--  (λ t → f) , (λ i → {!!}) , (λ t x → reflexive _ d)o

injArr : RepresentableRel (DynP ==> 𝕃 DynP) DynP ℓR
injArr {ℓR = ℓR} .R = Rel ℓR
injArr .leftRep = record {
  e = InjArr ;
  δX = Id ;
  δY = Id ;
  UpL = λ f d f≤d → lower f≤d ;
  UpR = λ f g f≤g → lift (MonFun.isMon InjArr f≤g) }
  
injArr {ℓR = ℓR} .rightRep = record {
  p = mExtU ProjArr ;
  δX = mExtU (mCompU Δ mRet) ; --@not sure
  δY = mExtU (mCompU Δ mRet) ;
  dnR = λ lf ld lf≤ld → ext-monotone-het _ _
    (MonFun.f (mCompU Δ mRet))
    (MonFun.f ProjArr)
    (λ f d f≤d -> aux f d f≤d (Rel-lem f d ℓR f≤d)) lf ld lf≤ld ;
  dnL = λ ld ld' ld≤ld' → ext-monotone-het _ _
    (MonFun.f ProjArr)
    (MonFun.f (mCompU Δ mRet))
    (λ d d' d≤d' → {!!})
    ld ld' ld≤ld' }

    where
      open LiftRelation.Properties
      aux : ∀ f d f≤d sigma -> 
       LiftRelation._≾_ ⟨ DynP ==> 𝕃 DynP ⟩ ⟨ DynP ==> 𝕃 DynP ⟩ (rel (DynP ==> 𝕃 DynP))
        (δ (ret f)) (MonFun.f ProjArr d)
      aux f d f≤d (g~ , eq-inr , f≤g~) = let eq = ProjArr-fun d g~ eq-inr in
        transport ((λ i -> LiftRelation._≾_ _ _ (rel (DynP ==> 𝕃 DynP)) (δ (ret f)) (sym eq i)))
             (ord-θ-monotone ⟨ DynP ==> 𝕃 DynP ⟩ ⟨ DynP ==> 𝕃 DynP ⟩ (rel (DynP ==> 𝕃 DynP))
                λ t -> ord-η-monotone ⟨ DynP ==> 𝕃 DynP ⟩ ⟨ DynP ==> 𝕃 DynP ⟩ (rel (DynP ==> 𝕃 DynP)) (f≤g~ t))
     
-- (λ i -> LiftRelation._≾_ _ _ _ (δ (ret f)) (eq i))
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
  δX = c .leftRep .δX;
  δY = d .leftRep .δY ;
  UpL =  λ x z x≤z -> elim
    (λ _ -> isPropValued-poset C _ _)
    (λ { (y , x≤y , y≤z) -> d .leftRep .UpL _ _
      (is-antitone (d .R) (c .leftRep .UpL x y x≤y) {!d-filler-r!}) })
    x≤z ;
  UpR = λ a a' a≤a' → elim (λ _ -> isPropValued-poset {!!} _ _) {!!} {!!} }
composeRep c d c-filler-l d-filler-r .rightRep = record {
  p = mCompU (c .rightRep .p) (d .rightRep .p) ;
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
