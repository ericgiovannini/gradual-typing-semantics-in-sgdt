{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.LockStepErrorOrdering (k : Clock) where

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
open import Common.Poset.Convenience
open import Common.Poset.MonotoneRelation
open import Semantics.Lift k
open import Semantics.PredomainInternalHom

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B : Set ℓ
private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

 
-- Lifting a heterogeneous relation between A and B to a relation
-- between L A and L B.
module LiftRelation
  (A B : Type ℓ)
  (R : A -> B -> Type ℓ')
  where

  module Inductive
    (rec : ▹ ( L℧ A  → L℧ B → Type ℓ')) where

    _≾'_ : L℧ A → L℧ B → Type ℓ'
    (η a) ≾' (η b) = R a b
    ℧ ≾' lb = Unit*
    (θ la~) ≾' (θ lb~) = ▸ (λ t → rec t (la~ t) (lb~ t))
    _ ≾' _ = ⊥*

  _≾_ : L℧ A -> L℧ B -> Type ℓ'
  _≾_ = fix _≾'_
    where open Inductive

  unfold-≾ : _≾_ ≡ Inductive._≾'_ (next _≾_)
  unfold-≾ = fix-eq Inductive._≾'_

  module Properties where
     open Inductive (next _≾_)

     ≾->≾' : {la : L℧ A} {lb : L℧ B} ->
       la ≾ lb -> la ≾' lb
     ≾->≾' {la} {lb} la≾lb = transport (λ i → unfold-≾ i la lb) la≾lb

     ≾'->≾ : {la : L℧ A} {lb : L℧ B} ->
       la ≾' lb -> la ≾ lb
     ≾'->≾ {la} {lb} la≾'lb = transport (sym (λ i → unfold-≾ i la lb)) la≾'lb

     ord-η-monotone : {a : A} -> {b : B} -> R a b -> (η a) ≾ (η b)
     ord-η-monotone {a} {b} a≤b = transport (sym (λ i → unfold-≾ i (η a) (η b))) a≤b

     ord-bot : (lb : L℧ B) -> ℧ ≾ lb
     ord-bot lb = transport (sym (λ i → unfold-≾ i ℧ lb)) tt*

     ord-θ-monotone : {la~ : ▹ L℧ A} -> {lb~ : ▹ L℧ B} ->
       ▸ (λ t -> la~ t ≾ lb~ t) -> θ la~ ≾ θ lb~
     ord-θ-monotone H = ≾'->≾ H

     ord-δ-monotone : {la : L℧ A} {lb : L℧ B} -> la ≾ lb -> (δ la) ≾ (δ lb)
     ord-δ-monotone {la} {lb} la≤lb =
       transport (sym (λ i → unfold-≾ i (δ la) (δ lb))) (ord-δ-monotone' la≤lb)
      where
      ord-δ-monotone' : {la : L℧ A} {lb : L℧ B} ->
        la ≾ lb ->
        Inductive._≾'_ (next _≾_) (δ la) (δ lb)
      ord-δ-monotone' {la} {lb} la≤lb = λ t → la≤lb

module LiftComp
  (A B C : Type ℓ)
  (R : A -> B -> Type ℓ')
  (S : B -> C -> Type ℓ') where

  module R-LALB = LiftRelation A B R
  module R-LBLC = LiftRelation B C S
  module R-LALC = LiftRelation A C (compRel R S)

  _≾AB_ = R-LALB._≾_
  _≾BC_ = R-LBLC._≾_
  _≾AC_ = R-LALC._≾_

  open R-LALB.Inductive (next R-LALB._≾_) renaming (_≾'_ to _≾'AB_)
  open R-LBLC.Inductive (next R-LBLC._≾_) renaming (_≾'_ to _≾'BC_)
  open R-LALC.Inductive (next R-LALC._≾_) renaming (_≾'_ to _≾'AC_)
  

  -- If la L(R ∘ S) lc, then la (LR ∘ LS) lc
  liftComp→compLift' :
    ▹ ((la : L℧ A) (lc : L℧ C) -> la ≾'AC lc -> compRel _≾'AB_ _≾'BC_ la lc) ->
       (la : L℧ A) (lc : L℧ C) -> la ≾'AC lc -> compRel _≾'AB_ _≾'BC_ la lc
  liftComp→compLift' _ (η a) (η c) (b , aRb , bSc) = (η b) , (aRb , bSc)
  liftComp→compLift' _ ℧ lc _ = ℧ , (tt* , tt*)
  liftComp→compLift' IH (θ la~) (θ lc~) la≤lc =
    (θ (λ t -> fst (IH t (la~ t) (lc~ t) (LiftRelation.Properties.≾->≾' _ _ _ (la≤lc t))))) ,
    ((λ t → LiftRelation.Properties.≾'->≾ _ _ _
      (fst (snd (IH t (la~ t) (lc~ t) (LiftRelation.Properties.≾->≾' _ _ _ (la≤lc t)))))) ,
     (λ t → LiftRelation.Properties.≾'->≾ _ _ _
      (snd (snd (IH t (la~ t) (lc~ t) (LiftRelation.Properties.≾->≾' _ _ _ (la≤lc t)))))))



-- If we have monotone relations R between A and B, and
-- S between B and C, and if la ≤ lb and lb ≤ lc,
-- then la ≤ lc in the lift of the composition of R and S.
--
-- We formulate this result at this level of generality since we can
-- easily prove two corollaries:
--   (1) the monotone and antitone
--   properties of the relation obtained by lifting a heterogeneous
--   relation between A and B to a relation between Lift A and Lift B.
--   (2) The transitivity of the relation obtained by lifting a homogeneous
--   relation on A to a relation on Lift A
module LiftRelTransHet
  (A B C : Poset ℓ ℓ')
  -- {ℓ'' : Level}
  (R : MonRel A B ℓ'')
  (S : MonRel B C ℓ'') where

  module R-LALB = LiftRelation ⟨ A ⟩ ⟨ B ⟩ (MonRel.R R)
  module R-LBLC = LiftRelation ⟨ B ⟩ ⟨ C ⟩ (MonRel.R S)
  module R-LALC = LiftRelation ⟨ A ⟩ ⟨ C ⟩ (compRel (MonRel.R R) (MonRel.R S))

  _≾AB_ = R-LALB._≾_
  _≾BC_ = R-LBLC._≾_
  _≾AC_ = R-LALC._≾_

  open R-LALB.Inductive (next R-LALB._≾_) renaming (_≾'_ to _≾'AB_)
  open R-LBLC.Inductive (next R-LBLC._≾_) renaming (_≾'_ to _≾'BC_)
  open R-LALC.Inductive (next R-LALC._≾_) renaming (_≾'_ to _≾'AC_)


  R-trans-het' :
    ▹  ((la : L℧ ⟨ A ⟩) (lb : L℧ ⟨ B ⟩) (lc : L℧ ⟨ C ⟩) ->
         la ≾'AB lb -> lb ≾'BC lc -> la ≾'AC lc) ->
        (la : L℧ ⟨ A ⟩) (lb : L℧ ⟨ B ⟩) (lc : L℧ ⟨ C ⟩) ->
         la ≾'AB lb -> lb ≾'BC lc -> la ≾'AC lc
  R-trans-het' IH ℧ lb lc la≤lb lb≤lc = tt*
  R-trans-het' IH (η a) (η b) (η c) a≤b b≤c = b , (a≤b , b≤c)
  R-trans-het' IH (θ la~) (θ lb~) (θ lc~) la≤lb lb≤lc =
    λ t -> LiftRelation.Properties.≾'->≾ _ _ _
      (IH t (la~ t) (lb~ t) (lc~ t)
        (LiftRelation.Properties.≾->≾' _ _ _ (la≤lb t))
        (LiftRelation.Properties.≾->≾' _ _ _ (lb≤lc t)))

  R-trans-het :
    (la : L℧ ⟨ A ⟩) (lb : L℧ ⟨ B ⟩) (lc : L℧ ⟨ C ⟩) ->
     la ≾AB lb -> lb ≾BC lc -> la ≾AC lc
  R-trans-het = fix {!!}

  compLift→liftComp :
     (la : L℧ ⟨ A ⟩) (lc : L℧ ⟨ C ⟩) -> compRel _≾AB_ _≾BC_ la lc -> la ≾AC lc
  compLift→liftComp la lc (lb , la≤lb , lb≤lc) = R-trans-het la lb lc la≤lb lb≤lc



-- Lift poset
module LiftPoset (A : Poset ℓ ℓ') where

  module X = PosetStr (A .snd)
  open X using (_≤_)

  -- Open the more general definitions from the heterogeneous
  -- lifting module, specializing the types for the current
  -- (homogeneous) situation, and re-export the definitions for
  -- clients of this module to use at these specialized types.
  open LiftRelation ⟨ A ⟩ ⟨ A ⟩ _≤_ public

  -- could also say: open LiftRelation.Inductive p p _≤_ (next _≾_)
  open Inductive (next _≾_) public
  open Properties public

  -- Specialize the heterogeneous transitivity result to the homogeneous
  -- setting.
  open LiftRelTransHet A A A (poset-monrel A) (poset-monrel A)

  ord-prop' : ▹ (BinaryRelation.isPropValued _≾'_) -> BinaryRelation.isPropValued _≾'_
  ord-prop' IH (η a) (η b) p q = IsPoset.is-prop-valued X.isPoset a b p q
  ord-prop' IH ℧ lb (lift tt) (lift tt) = refl
  ord-prop' IH (θ la~) (θ lb~) p q =
    lem-p p q (λ i t -> IH t (la~ t) (lb~ t) (≾->≾' (p t)) (≾->≾' (q t)) i)
    where
      unfold : (r : ▸ λ t -> la~ t ≾ lb~ t) -> (▸ λ t -> la~ t ≾' lb~ t)
      unfold r t = transport (λ i → unfold-≾ i (la~ t) (lb~ t)) (r t) -- or:  ≾->≾' (r t)
      -- or: unfold r = transport (λ i → ▸ λ t -> unfold-≾ i (la~ t) (lb~ t)) r

      fold : (r : ▸ λ t -> la~ t ≾' lb~ t) -> (▸ λ t -> la~ t ≾ lb~ t)
      fold r t = transport (sym (λ i → unfold-≾ i (la~ t) (lb~ t))) (r t) -- or:  ≾'->≾ (r t)
      -- or : fold r = transport (sym (λ i → ▸ λ t -> unfold-≾ i (la~ t) (lb~ t))) r

      fold-unfold : (r : ▸ λ t -> la~ t ≾ lb~ t) -> fold (unfold r) ≡ r
      fold-unfold r = transport⁻Transport (λ i -> ▸ λ t -> unfold-≾ i (la~ t) (lb~ t)) r

      lem-p : (p q : ▸ λ t -> (la~ t) ≾ (lb~ t)) -> unfold p ≡ unfold q -> p ≡ q
      lem-p p q eq = sym (fold-unfold p) ∙ cong fold eq ∙ fold-unfold q


  -- Have : p, q : θ la~ ≾' θ lb~
  -- i.e.   p, q : (t : Tick) -> la~ t ≾ lb~ t 
  -- We need to provide a path between p and q
  -- By IH we have
  -- ▹ (∀ a b . ∀ (p₁ q₁ : a ≾' b) . p₁ ≡ q₁)

  ord-prop : BinaryRelation.isPropValued _≾_
  ord-prop = prop-≾'→prop-≾ (fix ord-prop')
    where
      prop-≾'→prop-≾ : BinaryRelation.isPropValued _≾'_ -> BinaryRelation.isPropValued _≾_
      prop-≾'→prop-≾ = transport (λ i -> BinaryRelation.isPropValued (sym unfold-≾ i))

  ord-refl-ind : ▹ ((a : L℧ ⟨ A ⟩) -> a ≾ a) ->
                    (a : L℧ ⟨ A ⟩) -> a ≾ a
  ord-refl-ind IH (η x) =
    transport (sym (λ i -> unfold-≾ i (η x) (η x))) (IsPoset.is-refl X.isPoset x)
  ord-refl-ind IH ℧ =
    transport (sym (λ i -> unfold-≾ i ℧ ℧)) tt*
  ord-refl-ind IH (θ x) =
    transport (sym (λ i -> unfold-≾ i (θ x) (θ x))) λ t → IH t (x t)

  ord-refl : (a : L℧ ⟨ A ⟩) -> a ≾ a
  ord-refl = fix ord-refl-ind

  ord-antisym' : ▹ ((la lb : L℧ ⟨ A ⟩) -> la ≾' lb -> lb ≾' la -> la ≡ lb) ->
                    (la lb : L℧ ⟨ A ⟩) -> la ≾' lb -> lb ≾' la -> la ≡ lb
  ord-antisym' IH (η a) (η b) a≤b b≤a i = η (IsPoset.is-antisym X.isPoset a b a≤b b≤a i)
  ord-antisym' IH ℧ ℧ _ _ = refl
  ord-antisym' IH (θ la~) (θ lb~) la≤lb lb≤la i =
    θ λ t -> IH t (la~ t) (lb~ t) (≾->≾' (la≤lb t)) (≾->≾' (lb≤la t)) i


  compRel-lem : {a c : ⟨ A ⟩} -> compRel (rel A) (rel A) a c -> (rel A a c)
  compRel-lem (b , a≤b , b≤c) = IsPoset.is-trans X.isPoset _ _ _ a≤b b≤c

  ord-trans : BinaryRelation.isTrans _≾_
  ord-trans = {!R-trans-het!}

  ord-antisym : BinaryRelation.isAntisym _≾_
  ord-antisym = {!!}


 

  𝕃 : Poset ℓ ℓ'
  𝕃 =
    (L℧ ⟨ A ⟩) ,
    (posetstr _≾_ (isposet (isSetL℧ (IsPoset.is-set X.isPoset))
      ord-prop ord-refl ord-trans ord-antisym))


{-
      ord-trans-ind :
        ▹ ((a b c : L℧ ⟨ A ⟩) ->
           a ≾' b ->
           b ≾' c ->
           a ≾' c) ->
        (a b c : L℧ ⟨ A ⟩) ->
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
      ord-trans-ind IH ℧ b c ord-ab ord-bc = tt*
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

-}


module LiftMonRel (A B : Poset ℓ ℓ') (R : MonRel A B ℓ'') where
  module LR = LiftRelation ⟨ A ⟩ ⟨ B ⟩ (MonRel.R R)
  open LiftPoset
  open MonRel
  
  ℝ : MonRel (𝕃 A) (𝕃 B) ℓ''
  ℝ = record {
    R = LR._≾_ ;
    is-prop-valued = {!!} ;
    is-antitone = {!!} ;
    is-monotone = {!!} }


{-
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
        λ t → ≾'->≾ {!!}

      monotone : {!!}
      monotone = {!!}

 -- isAntitone : ∀ {x x' y} -> R x y -> x' ≤X x -> R x' y
 -- isMonotone : ∀ {x y y'} -> R x y -> y ≤Y y' -> R x y'

-}
