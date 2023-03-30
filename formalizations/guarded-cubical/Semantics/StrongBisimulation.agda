{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
open import Semantics.Monotone.Base

module Semantics.StrongBisimulation(k : Clock) where

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Data.Nat hiding (_^_) renaming (ℕ to Nat)
open import Cubical.Data.Bool.Base
open import Cubical.Data.Bool.Properties hiding (_≤_)
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary

open import Cubical.Data.Unit.Properties

open import Agda.Primitive

open import Common.Common
open import Semantics.Predomains
open import Semantics.Lift k
open import Semantics.ErrorDomains

private
  variable
    l : Level
    A B : Set l
    ℓ ℓ' : Level
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A





-- Flat predomain from a set

flat : hSet ℓ-zero -> Predomain
flat h = ⟨ h ⟩ ,
         (posetstr _≡_ (isposet (str h) (str h)
           (λ _ → refl)
           (λ a b c a≡b b≡c → a ≡⟨ a≡b ⟩ b ≡⟨ b≡c ⟩ c ∎)
           λ a b a≡b _ → a≡b))

𝔹 : Predomain
𝔹 = flat (Bool , isSetBool)

ℕ : Predomain
ℕ = flat (Nat , isSetℕ)

UnitP : Predomain
UnitP = flat (Unit , isSetUnit)



-- Predomains from arrows (need to ensure monotonicity)

-- Ordering on functions between predomains. This does not require that the
-- functions are monotone.
fun-order-het : (P1 P1' P2 P2' : Predomain) ->
  (⟨ P1 ⟩ -> ⟨ P1' ⟩ -> Type) ->
  (⟨ P2 ⟩ -> ⟨ P2' ⟩ -> Type) ->
  (⟨ P1 ⟩ -> ⟨ P2 ⟩) -> (⟨ P1' ⟩ -> ⟨ P2' ⟩) -> Type ℓ-zero
fun-order-het P1 P1' P2 P2' rel-P1P1' rel-P2P2' fP1P2 fP1'P2' =
  (p : ⟨ P1 ⟩) -> (p' : ⟨ P1' ⟩) ->
  rel-P1P1' p p' ->
  rel-P2P2' (fP1P2 p) (fP1'P2' p')


-- TODO can define this in terms of fun-order-het
fun-order : (P1 P2 : Predomain) -> (⟨ P1 ⟩ -> ⟨ P2 ⟩) -> (⟨ P1 ⟩ -> ⟨ P2 ⟩) -> Type ℓ-zero
fun-order P1 P2 f1 f2 =
  (x y : ⟨ P1 ⟩) -> x ≤P1 y -> (f1 x) ≤P2 (f2 y)
  where
    module P1 = PosetStr (P1 .snd)
    module P2 = PosetStr (P2 .snd)
    _≤P1_ = P1._≤_
    _≤P2_ = P2._≤_

{-
mon-fun-order-refl : {P1 P2 : Predomain} ->
  (f : ⟨ P1 ⟩ -> ⟨ P2 ⟩) ->
  ({x y : ⟨ P1 ⟩} -> rel P1 x y -> rel P2 (f x) (f y)) ->
  fun-order P1 P2 f f
mon-fun-order-refl {P1} {P2} f f-mon = λ x y x≤y → f-mon x≤y
-}
  

fun-order-trans : {P1 P2 : Predomain} ->
  (f g h : ⟨ P1 ⟩ -> ⟨ P2 ⟩) ->
  fun-order P1 P2 f g ->
  fun-order P1 P2 g h ->
  fun-order P1 P2 f h
fun-order-trans {P1} {P2} f g h f≤g g≤h =
  λ x y x≤y ->
    P2.is-trans (f x) (g x) (h y)
    (f≤g x x (reflexive P1 x))
    (g≤h x y x≤y)
   where
     module P1 = PosetStr (P1 .snd)
     module P2 = PosetStr (P2 .snd)



mon-fun-order : (P1 P2 : Predomain) -> MonFun P1 P2 → MonFun P1 P2 → Type ℓ-zero
mon-fun-order P1 P2 mon-f1 mon-f2 =
  fun-order P1 P2 (MonFun.f mon-f1) (MonFun.f mon-f2)
   where
     module P1 = PosetStr (P1 .snd)
     module P2 = PosetStr (P2 .snd)
     _≤P1_ = P1._≤_
     _≤P2_ = P2._≤_


mon-fun-order-refl : {P1 P2 : Predomain} ->
  (f : MonFun P1 P2) ->
  fun-order P1 P2 (MonFun.f f) (MonFun.f f)
mon-fun-order-refl f = λ x y x≤y -> MonFun.isMon f x≤y

mon-fun-order-trans : {P1 P2 : Predomain} ->
  (f g h : MonFun P1 P2) ->
  mon-fun-order P1 P2 f g ->
  mon-fun-order P1 P2 g h ->
  mon-fun-order P1 P2 f h
mon-fun-order-trans {P1} {P2} f g h f≤g g≤h =
  fun-order-trans {P1} {P2} (MonFun.f f) (MonFun.f g) (MonFun.f h) f≤g g≤h


-- Predomain of monotone functions between two predomains
arr' : Predomain -> Predomain -> Predomain
arr' P1 P2 =
  MonFun P1 P2 ,
  -- (⟨ P1 ⟩ -> ⟨ P2 ⟩) ,
  (posetstr
    (mon-fun-order P1 P2)
    (isposet {!!} {!!}
      mon-fun-order-refl
      
      -- TODO can use fun-order-trans
      (λ f1 f2 f3 Hf1-f2 Hf2-f3 x y H≤xy ->
      -- Goal: f1 .f x ≤P2 f3 .f y
       P2.is-trans (f1 .f x) (f2 .f x) (f3 .f y)
         (Hf1-f2 x x (IsPoset.is-refl (P1.isPoset) x))
         (Hf2-f3 x y H≤xy))
      {!!}))
  where
    open MonFun
    module P1 = PosetStr (P1 .snd)
    module P2 = PosetStr (P2 .snd)


_==>_ : Predomain -> Predomain -> Predomain
A ==> B = arr' A B

infixr 20 _==>_



-- TODO show that this is a monotone relation

-- TODO define version where the arguments are all monotone relations
-- instead of arbitrary relations

FunRel : {A A' B B' : Predomain} ->
  MonRel {ℓ-zero} A A' ->
  MonRel {ℓ-zero} B B' ->
  MonRel {ℓ-zero} (A ==> B) (A' ==> B')
FunRel {A} {A'} {B} {B'} RAA' RBB' =
  record {
    R = λ f f' → fun-order-het A A' B B'
                   (MonRel.R RAA') (MonRel.R RBB')
                   (MonFun.f f) (MonFun.f f') ;
    isAntitone = {!!} ;
    isMonotone = λ {f} {f'} {g'} f≤f' f'≤g' a a' a≤a' →
      MonRel.isMonotone RBB' (f≤f' a a' a≤a') {!!} } -- (f'≤g' a' a' (reflexive A' a')) }



 
-- Lifting a heterogeneous relation between A and B to a
-- relation between L A and L B
-- (We may be able to reuse this logic to define the homogeneous ordering on 𝕃 below)

module LiftRelation
  (A B : Predomain)
  (RAB : ⟨ A ⟩ -> ⟨ B ⟩ -> Type)
  where

  module A = PosetStr (A .snd)
  module B = PosetStr (B .snd)

  open A renaming (_≤_ to _≤A_)
  open B renaming (_≤_ to _≤B_)

  module Inductive
    (rec : ▹ ( L℧ ⟨ A ⟩ → L℧ ⟨ B ⟩ → Type)) where

    _≾'_ : L℧ ⟨ A ⟩ → L℧ ⟨ B ⟩ → Type
    (η a) ≾' (η b) = RAB a b
    ℧ ≾' lb = Unit
    (θ la~) ≾' (θ lb~) = ▸ (λ t → rec t (la~ t) (lb~ t))
    _ ≾' _ = ⊥

  _≾_ : L℧ ⟨ A ⟩ -> L℧ ⟨ B ⟩ -> Type
  _≾_ = fix _≾'_
    where open Inductive

  unfold-≾ : _≾_ ≡ Inductive._≾'_ (next _≾_)
  unfold-≾ = fix-eq Inductive._≾'_

  module Properties where
     open Inductive (next _≾_)

     ≾->≾' : {la : L℧ ⟨ A ⟩} {lb : L℧ ⟨ B ⟩} ->
       la ≾ lb -> la ≾' lb
     ≾->≾' {la} {lb} la≾lb = transport (λ i → unfold-≾ i la lb) la≾lb

     ≾'->≾ : {la : L℧ ⟨ A ⟩} {lb : L℧ ⟨ B ⟩} ->
       la ≾' lb -> la ≾ lb
     ≾'->≾ {la} {lb} la≾'lb = transport (sym (λ i → unfold-≾ i la lb)) la≾'lb

     ord-η-monotone : {a : ⟨ A ⟩} -> {b : ⟨ B ⟩} -> RAB a b -> (η a) ≾ (η b)
     ord-η-monotone {a} {b} a≤b = transport (sym (λ i → unfold-≾ i (η a) (η b))) a≤b

     ord-bot : (lb : L℧ ⟨ B ⟩) -> ℧ ≾ lb
     ord-bot lb = transport (sym (λ i → unfold-≾ i ℧ lb)) tt


-- Predomain to lift predomain
module LiftPredomain (p : Predomain) where

  module X = PosetStr (p .snd)
  open X using (_≤_)


  -- Open the more general definitions from the heterogeneous
  -- lifting module, specializing the types for the current
  -- (homogeneous) situation, and re-export the definitions for
  -- clients of this module to use at these specialized types.
  open LiftRelation p p _≤_ public

  -- could also say: open LiftRelation.Inductive p p _≤_ (next _≾_)
  open Inductive (next _≾_) public
  open Properties public


  -- TODO move to heterogeneous lifting module
  ord-δ-monotone : {lx ly : L℧ ⟨ p ⟩} -> lx ≾ ly -> (δ lx) ≾ (δ ly)
  ord-δ-monotone {lx} {ly} lx≤ly =
    transport (sym (λ i → unfold-≾ i (δ lx) (δ ly))) (ord-δ-monotone' lx≤ly)
    where
      ord-δ-monotone' : {lx ly : L℧ ⟨ p ⟩} ->
        lx ≾ ly ->
        Inductive._≾'_ (next _≾_) (δ lx) (δ ly)
      ord-δ-monotone' {lx} {ly} lx≤ly = λ t → lx≤ly


  ord-refl-ind : ▹ ((a : L℧ ⟨ p ⟩) -> a ≾ a) ->
                    (a : L℧ ⟨ p ⟩) -> a ≾ a

  ord-refl-ind IH (η x) =
    transport (sym (λ i -> unfold-≾ i (η x) (η x))) (IsPoset.is-refl X.isPoset x)
  ord-refl-ind IH ℧ =
    transport (sym (λ i -> unfold-≾ i ℧ ℧)) tt
  ord-refl-ind IH (θ x) =
    transport (sym (λ i -> unfold-≾ i (θ x) (θ x))) λ t → IH t (x t)

  ord-refl : (a : L℧ ⟨ p ⟩) -> a ≾ a
  ord-refl = fix ord-refl-ind


  𝕃 : Predomain
  𝕃 =
    (L℧ ⟨ p ⟩) ,
    (posetstr _≾_ (isposet {!!} {!!} ord-refl ord-trans {!!}))
    where
      
      ord-trans-ind :
        ▹ ((a b c : L℧ ⟨ p ⟩) ->
           a ≾' b ->
           b ≾' c ->
           a ≾' c) ->
        (a b c : L℧ ⟨ p ⟩) ->
         a ≾' b ->
         b ≾' c ->
         a ≾' c
      ord-trans-ind IH (η x) (η y) (η z) ord-ab ord-bc =
        IsPoset.is-trans X.isPoset x y z ord-ab ord-bc
        -- x ≡⟨ ord-ab ⟩ y ≡⟨ ord-bc ⟩ z ∎
      ord-trans-ind IH (η x) (η y) ℧ ord-ab ord-bc = ord-bc
      ord-trans-ind IH (η x) (θ y) ℧ contra ord-bc = contra
      ord-trans-ind IH (η x) (η y) (θ z) ord-ab contra = contra
      ord-trans-ind IH (η x) ℧ (θ y) ord-ab ord-bc = ord-ab
      ord-trans-ind IH (η x) (θ y) (θ z) ord-ab ord-bc = ord-ab
      ord-trans-ind IH ℧ b c ord-ab ord-bc = tt
      ord-trans-ind IH (θ lx~) (θ ly~) (θ lz~) ord-ab ord-bc =
        λ t -> transport (sym λ i → unfold-≾ i (lx~ t) (lz~ t))
          (IH t (lx~ t) (ly~ t) (lz~ t)
          (transport (λ i -> unfold-≾ i (lx~ t) (ly~ t)) (ord-ab t))
          (transport (λ i -> unfold-≾ i (ly~ t) (lz~ t)) (ord-bc t)))

      ord-trans : (a b c : L℧ ⟨ p ⟩) -> a ≾ b -> b ≾ c -> a ≾ c
      ord-trans = fix (transport (sym (λ i ->
         (▹ ((a b c : L℧ ⟨ p ⟩) →
            unfold-≾ i a b → unfold-≾ i b c → unfold-≾ i a c) →
             (a b c : L℧ ⟨ p ⟩) →
            unfold-≾ i a b → unfold-≾ i b c → unfold-≾ i a c))) ord-trans-ind)




module LiftRelMon
  (A B : Predomain)
  (RAB : MonRel A B) where

  -- Bring the heterogeneous relation between 𝕃 A and 𝕃 B into scope
  open LiftRelation A B (MonRel.R RAB)
    using (_≾_ ; module Inductive ; module Properties) -- brings _≾_ into scope
  open Inductive (next _≾_)  -- brings _≾'_ into scope
  open Properties -- brings conversion between _≾_ and _≾'_ into scope

  -- Bring the homogeneous lifted relations on A and B into scope 
  -- open LiftPredomain renaming (_≾_ to _≾h_ ; _≾'_ to _≾h'_)
  open LiftPredomain using (𝕃)

  _≾LA_ = LiftPredomain._≾_ A
  _≾LB_ = LiftPredomain._≾_ B
  -- Could also say:
  -- open LiftPredomain A using () renaming (_≾_ to _≾LA_)

  _≾'LA_ = LiftPredomain._≾'_ A
  _≾'LB_ = LiftPredomain._≾'_ B

  R : MonRel (𝕃 A) (𝕃 B)
  R = record {
    R = _≾_ ;
    isAntitone = λ {la} {la'} {lb} la≤lb la'≤la -> {!!} ;
    isMonotone = {!!} }
    where
      antitone' :
        ▹ ({la la' : L℧ ⟨ A ⟩} -> {lb : L℧ ⟨ B ⟩} ->
            la ≾' lb -> la' ≾'LA la -> la' ≾' lb) ->
           {la la' : L℧ ⟨ A ⟩} -> {lb : L℧ ⟨ B ⟩} ->
            la ≾' lb -> la' ≾'LA la -> la' ≾' lb
      antitone' IH {η a2} {η a1} {η a3} la≤lb la'≤la =
        MonRel.isAntitone RAB la≤lb la'≤la
      antitone' IH {la} {℧} {lb} la≤lb la'≤la = tt
      antitone' IH {θ la2~} {θ la1~} {θ lb~} la≤lb la'≤la =
        λ t → ≾'->≾ (IH t {!!} {!!})

      monotone : {!!}
      monotone = {!!}

 -- isAntitone : ∀ {x x' y} -> R x y -> x' ≤X x -> R x' y
 -- isMonotone : ∀ {x y y'} -> R x y -> y ≤Y y' -> R x y'




-- Product of predomains


-- We can't use Cubical.Data.Prod.Base for products, because this version of _×_
-- is not a subtype of the degenerate sigma type Σ A (λ _ → B), and this is needed
-- when we define the lookup function.
-- So we instead use Cubical.Data.Sigma.

-- These aren't included in Cubical.Data.Sigma, so we copy the
-- definitions from Cubical.Data.Prod.Base.
proj₁ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → A × B → A
proj₁ (x , _) = x

proj₂ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → A × B → B
proj₂ (_ , x) = x


infixl 21 _×d_
_×d_  : Predomain -> Predomain -> Predomain
A ×d B =
  (⟨ A ⟩ × ⟨ B ⟩) ,
  (posetstr order {!!})
  where
    module A = PosetStr (A .snd)
    module B = PosetStr (B .snd)
   

    prod-eq : {a1 a2 : ⟨ A ⟩} -> {b1 b2 : ⟨ B ⟩} ->
      (a1 , b1) ≡ (a2 , b2) -> (a1 ≡ a2) × (b1 ≡ b2)
    prod-eq p = (λ i → proj₁ (p i)) , λ i -> proj₂ (p i)

    isSet-prod : isSet (⟨ A ⟩ × ⟨ B ⟩)
    isSet-prod (a1 , b1) (a2 , b2) p1 p2 =
      let (p-a1≡a2 , p-b1≡b2) = prod-eq p1 in
      let (p'-a1≡a2 , p'-b1≡b2) = prod-eq p2 in
      {!!}

    order : ⟨ A ⟩ × ⟨ B ⟩ -> ⟨ A ⟩ × ⟨ B ⟩ -> Type ℓ-zero
    order (a1 , b1) (a2 , b2) = (a1 A.≤ a2) × (b1 B.≤ b2)

    order-refl : BinaryRelation.isRefl order
    order-refl = λ (a , b) → reflexive A a , reflexive B b

    order-trans : BinaryRelation.isTrans order
    order-trans (a1 , b1) (a2 , b2) (a3 , b3) (a1≤a2 , b1≤b2) (a2≤a3 , b2≤b3) =
      (IsPoset.is-trans A.isPoset a1 a2 a3 a1≤a2 a2≤a3) ,
       IsPoset.is-trans B.isPoset b1 b2 b3 b1≤b2 b2≤b3
    

    is-poset : IsPoset order
    is-poset = isposet
      isSet-prod
      {!!}
      order-refl
      order-trans
      {!!}



π1 : {A B : Predomain} -> ⟨ (A ×d B) ==> A ⟩
π1 {A} {B} = record {
  f = g;
  isMon = g-mon }
  where
    g : ⟨ A ×d B ⟩ -> ⟨ A ⟩
    g (a , b) = a

    g-mon  : {p1 p2 : ⟨ A ×d B ⟩} → rel (A ×d B) p1 p2 → rel A (g p1) (g p2)
    g-mon {γ1 , a1} {γ2 , a2} (a1≤a2 , b1≤b2) = a1≤a2


π2 : {A B : Predomain} -> ⟨ (A ×d B) ==> B ⟩
π2 {A} {B} = record {
  f = g;
  isMon = g-mon }
  where
    g : ⟨ A ×d B ⟩ -> ⟨ B ⟩
    g (a , b) = b

    g-mon  : {p1 p2 : ⟨ A ×d B ⟩} → rel (A ×d B) p1 p2 → rel B (g p1) (g p2)
    g-mon {γ1 , a1} {γ2 , a2} (a1≤a2 , b1≤b2) = b1≤b2



Pair : {A B : Predomain} -> ⟨ A ==> B ==> (A ×d B) ⟩
Pair {A} = record {
  f = λ a →
    record {
      f = λ b -> a , b ;
      isMon = λ b1≤b2 → (reflexive A a) , b1≤b2 } ;
  isMon = λ {a1} {a2} a1≤a2 b1 b2 b1≤b2 → a1≤a2 , b1≤b2 }





-- Induced equivalence relation on a Predomain
equivRel : (d : Predomain) -> EquivRel ⟨ d ⟩ ℓ-zero
equivRel d =
  (λ x y → (x ≤ y) × (y ≤ x)) ,
  BinaryRelation.equivRel
    (λ x → (reflexive d x) , (reflexive d x))
    (λ x y (x≤y , y≤x) → y≤x , x≤y)
    λ x y z (x≤y , y≤x) (y≤z , z≤y) →
      (transitive d x y z x≤y y≤z) , (transitive d z y x z≤y y≤x)
  where
    module D = PosetStr (d .snd)
    _≤_ = D._≤_


congruence : {X : Type} -> (_R_ : L℧ X -> L℧ X -> Type) -> Type
congruence {X} _R_ = {lx ly : ▹ (L℧ X)} -> ▸ (λ t → (lx t) R (ly t)) -> (θ lx) R (θ ly)

congruence' : {X : Type} -> (_R_ : L℧ X -> L℧ X -> Type) -> Type
congruence' {X} _R_ = {lx ly : L℧ X} -> ▹ (lx R ly) -> (θ (next lx)) R (θ (next ly))

cong→cong' : ∀ {X}{_R_ : L℧ X -> L℧ X -> Type} → congruence _R_ → congruence' _R_
cong→cong' cong ▹R = cong ▹R

trivialize : {X : Type} (_R_ : L℧ X -> L℧ X -> Type) ->
  BinaryRelation.isTrans _R_ ->
  congruence _R_ ->
  ((x : L℧ X) -> x R (θ (next x))) ->
  ((x : L℧ X) -> x R (fix θ))
trivialize {X} _R_ hTrans hCong hθR = fix trivialize'
  where
   trivialize' :
    ▹ ((x : L℧ X) -> x R (fix θ)) → (x : L℧ X) -> x R (fix θ)
   trivialize' IH lx =
     subst (λ y → lx R y) (sym (fix-eq θ))
       (hTrans _ _ _
         (hθR lx)
         (hCong (λ t → IH t lx)))



-- Weak bisimulation relaion

module Bisimilarity (d : Predomain) where

  module D = PosetStr (d .snd)
  private
    _==_ = fst (equivRel d) -- the equivalence relation induced by d
    isEqRel = snd (equivRel d)

  -- make this a module so we can avoid having to make the IH
  -- a parameter of the comparison function
  module Inductive (IH : ▹ (L℧ ⟨ d ⟩ -> L℧ ⟨ d ⟩ -> Type)) where

    _≈'_ : L℧ (⟨ d ⟩) -> L℧ (⟨ d ⟩) -> Type
    ℧ ≈' ℧ = Unit
      
    η x ≈' η y = x == y
    
    θ lx ≈' θ ly = ▸ (λ t -> IH t (lx t) (ly t))
    -- or equivalently: θ lx ≾' θ ly = ▸ ((IH ⊛ lx) ⊛ ly)

    θ x~ ≈' ℧ = Σ Nat λ n -> θ x~ ≡ (δ ^ n) ℧

    θ x~ ≈' η y = Σ Nat λ n -> Σ ⟨ d ⟩ λ x -> (θ x~ ≡ (δ ^ n) (η x)) × (x == y)

    ℧ ≈' θ y~ = Σ Nat λ n -> θ y~ ≡ (δ ^ n) ℧

    η x ≈' θ y~ = Σ Nat λ n -> Σ ⟨ d ⟩ λ y -> (θ y~ ≡ (δ ^ n) (η y)) × (x == y)

    _ ≈' _ = ⊥


  _≈_ : L℧ (⟨ d ⟩) -> L℧ (⟨ d ⟩) -> Type
  _≈_ = fix _≈'_
    where open Inductive

  unfold-≈ : _≈_ ≡ Inductive._≈'_ (next _≈_)
  unfold-≈ = fix-eq Inductive._≈'_

  
  

  module Properties where
    open Inductive (next _≈_)
    open BinaryRelation (_==_)

    ≈->≈' : {lx ly : L℧ ⟨ d ⟩} ->
     lx ≈ ly -> lx ≈' ly
    ≈->≈' {lx} {ly} lx≈ly = transport (λ i → unfold-≈ i lx ly) lx≈ly

    ≈'->≈ : {lx ly : L℧ ⟨ d ⟩} ->
     lx ≈' ly -> lx ≈ ly
    ≈'->≈ {lx} {ly} lx≈'ly = transport (sym (λ i → unfold-≈ i lx ly)) lx≈'ly
    
    ≈-℧ : (lx : L℧ ⟨ d ⟩) ->
     lx ≈' ℧ -> (Σ Nat λ n -> lx ≡ (δ ^ n) ℧)
    ≈-℧ ℧ H = zero , refl
    ≈-℧ (θ x) H = H


    symmetric' :
      ▹ ((lx ly : L℧ ⟨ d ⟩) -> lx ≈' ly -> ly ≈' lx) ->
         (lx ly : L℧ ⟨ d ⟩) -> lx ≈' ly -> ly ≈' lx
    symmetric' _ ℧ ℧ _ = tt
    symmetric' _ (η x) (η y) (x≤y , y≤x) = y≤x , x≤y -- symmetry of the underlying relation
    symmetric' IH (θ lx~) (θ ly~) lx≈'ly =
      λ t → ≈'->≈  (IH t (lx~ t) (ly~ t) (≈->≈' (lx≈'ly t)))
    symmetric' _ (θ lx~) ℧ (n , H-eq) = n , H-eq
    symmetric' _ (θ lx~) (η y) (n , x , H-eq , H-rel) =
      n , x , H-eq , (isEquivRel.symmetric isEqRel x y H-rel)
    symmetric' _ ℧ (θ ly~) (n , H-eq) = n , H-eq
    symmetric' _ (η x) (θ ly~) (n , y , H-eq , H-rel) =
      n , y , H-eq , (isEquivRel.symmetric isEqRel x y H-rel)

    symmetric : (lx ly : L℧ ⟨ d ⟩) -> lx ≈ ly -> ly ≈ lx
    symmetric = {!!} -- fix {k} (subst {!!} {!!}) 

   {-
        ord-trans = fix (transport (sym (λ i ->
         (▹ ((a b c : L℧ ⟨ p ⟩) →
            unfold-ord i a b → unfold-ord i b c → unfold-ord i a c) →
             (a b c : L℧ ⟨ p ⟩) →
            unfold-ord i a b → unfold-ord i b c → unfold-ord i a c))) ord-trans-ind)
  -}

    θ-cong : congruence _≈_
    θ-cong {lx~} {ly~} H-later = ≈'->≈ H-later
    -- Goal: θ lx ≈ θ ly
    -- i.e. (θ lx) (≈' (next ≈)) (θ ly)
    -- i.e. ▸ (λ t → (lx t) ((next ≈) t) (ly t))
    -- i.e. ▸ (λ t → (lx t) ≈ (ly t))

    x≈'δx : ▹ ((lx : L℧ ⟨ d ⟩) -> lx ≈' (δ lx)) ->
               (lx : L℧ ⟨ d ⟩) -> lx ≈' (δ lx)
    x≈'δx _ (η x) = 1 , x , refl , (isEquivRel.reflexive isEqRel x)
    x≈'δx _ ℧ = 1 , refl
    x≈'δx IH (θ lx~) =

      -- Alternate solution:
      -- λ t → ≈'->≈
      --  (transport (λ i → (lx~ t) ≈' θ (next-Mt≡M lx~ t i)) (IH t (lx~ t)))

       transport
         (λ i -> ▸ (λ t -> unfold-≈ (~ i) (lx~ t) (θ (next-Mt≡M lx~ t i))))
         λ t → IH t (lx~ t)

    -- Goal: θ lx~ ≈' δ (θ lx~)
    -- i.e.  θ lx~ ≈' θ (next (θ lx~))
    -- i.e. ▸ λ t -> (lx~ t) ((next ≈) t) ((next (θ lx~)) t)
    -- i.e. ▸ λ t -> (lx~ t) ≈ (θ lx~)
    -- The IH says: ▸ λ t -> (lx~ t) ≈' (θ (next (lx~ t)))
    -- So we just need to change ≈' to ≈ and change
    -- (θ (next (lx~ t))) to (θ lx~). The below term does this.
   
    -- (λ i -> ▸ (λ t -> unfold-≈ (~ i) (lx~ t) (θ (next-Mt≡M lx~ t i)))) :
    --
    --   ▸ λ t -> (lx~ t) ≈' (θ (next (lx~ t))) ≡
    --   ▸ λ t -> (lx~ t) ≈  (θ lx~)

    -- Informally:
  
    -- By IH, we know:
    --   (lx~ t) ≈' (δ (lx~ t))

    -- Also Know:
    --   lx~ ≡ next (lx~ t) (using later-extensionality + tick irrelevance)

    -- So STS:
    --         (lx~ t) ≈ θ (next (lx~ t))
    -- which holds by IH.

    x≈δx : (lx : L℧ ⟨ d ⟩) -> lx ≈ (δ lx)
    x≈δx = transport
      (sym (λ i → (lx : L℧ ⟨ d ⟩) -> unfold-≈ i lx (δ lx)))
      (fix x≈'δx)


    contradiction : {A : Type} -> A -> ¬ A -> ⊥
    contradiction HA ¬A = ¬A HA

    contrapositive : {A : Type} -> (A -> B) -> (¬ B -> ¬ A)
    contrapositive A→B ¬B HA = ¬B (A→B HA)

    non-trivial→not-transitive :
      (Σ ⟨ d ⟩ λ x -> Σ ⟨ d ⟩ λ y -> (¬ (x == y))) ->
      ¬ (BinaryRelation.isTrans _≈_)
    non-trivial→not-transitive (x , y , x≠y) H-trans =
      let fixθ-top = trivialize _≈_ H-trans θ-cong x≈δx in
      let ηx≈ηy = H-trans (η x) (fix θ) (η y)
                        (fixθ-top (η x))
                        (symmetric _ _ (fixθ-top (η y))) in
      let not-ηx≈ηy = contrapositive (λ H -> ≈->≈' H) x≠y in
      contradiction ηx≈ηy not-ηx≈ηy


    inj-δ : {X : Set} -> (lx ly : L℧ X) -> δ lx ≡ δ ly -> lx ≡ ly
    inj-δ lx ly δlx≡δly = let tmp = inj-θ (next lx) (next ly) δlx≡δly in
      {!!}


    fixθ-lem1 : (n : Nat) ->
      (▹ (¬ (θ {Nat} (next (fix θ)) ≡ (δ ^ n) ℧))) ->
          ¬ (θ {Nat} (next (fix θ)) ≡ (δ ^ n) ℧)
    fixθ-lem1 zero    _  H-eq =  θ≠℧ H-eq
    fixθ-lem1 (suc n) IH H-eq =
       let tmp = inj-θ (next (fix θ)) (next ((δ ^ n) ℧)) H-eq in {!!}
     

    ℧-fixθ : ¬ (℧ ≈' θ (next (fix θ)))
    ℧-fixθ (n , H-eq) = {!!}
    
