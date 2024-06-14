{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.DoublePoset.LockStepErrorBisim (k : Clock) where

open import Cubical.Relation.Binary

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
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset

open import Cubical.Data.Unit.Properties

open import Agda.Primitive

open import Common.Common
open import Semantics.Lift k
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Convenience
open import Semantics.Concrete.DoublePoset.Constructions
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.LockStepErrorOrdering k
open import Semantics.WeakBisimilarity k


open BinaryRelation
open PosetBisimStr hiding (_≤_)

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓA ℓ'A ℓ''A ℓB ℓ'B ℓ''B ℓC ℓ'C ℓ''C : Level
    ℓX ℓ'X ℓY ℓ'Y : Level
    ℓR ℓR1 ℓR2 : Level
    A B : Set ℓ
private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

module LiftPosetBisim (A : PosetBisim ℓ ℓ' ℓ'') where
  module A = PosetBisimStr (A .snd)
  open import Common.Poset.MonotoneRelation
  open A using (_≤_)
  open LiftRelation ⟨ A ⟩ ⟨ A ⟩ _≤_ public

  A⊎1 : PosetBisim ℓ (ℓ-max ℓ' ℓ-zero) (ℓ-max ℓ'' ℓ-zero)
  A⊎1 = A ⊎p UnitPB

  Bisim-⊎ : ⟨ A ⟩ ⊎ Unit → ⟨ A ⟩ ⊎ Unit → Type ℓ''
  Bisim-⊎ = A⊎1 .snd ._≈_
  -- Bisim-⊎ (inl a) (inl a') = a A.≈ a'
  -- Bisim-⊎ (inr tt) (inr tt) = Unit*
  -- Bisim-⊎ _ _ = ⊥*
 

  module LiftBisim = Bisim (⟨ A ⟩ ⊎ Unit) Bisim-⊎

  -- temporarily placed here
  module FunctionalRel {X' : Type ℓ'X} {X : Type ℓX} {Y' : Type ℓ'Y} {Y : Type ℓY}
     (f : X' -> X) (g : Y' -> Y) (R : X -> Y -> Type ℓR) where
    functionalRelation :  (X' -> Y' -> Type ℓR)
    functionalRelation = λ x' y' → R (f x') (g y')

  module _ {X' : Type ℓ'X} {X : Type ℓX} (f : X' -> X) (R : X -> X -> Type ℓR) (isReflR : isRefl R) where
    open FunctionalRel f f R
    functionalRel-refl : isRefl functionalRelation
    functionalRel-refl = λ x' -> isReflR (f x')

  module _ {X' : Type ℓ'X} {X : Type ℓX} (f : X' -> X) (R : X -> X -> Type ℓR) (isSymR : isSym R) where
    open FunctionalRel f f R
    functionalRel-sym : isSym functionalRelation
    functionalRel-sym x' y' funRelxy = isSymR (f x') (f y') funRelxy

  module _ {X' : Type ℓ'X} {X : Type ℓX} {Y' : Type ℓ'Y} {Y : Type ℓY}
     (f : X' -> X) (g : Y' -> Y) (R : X -> Y -> Type ℓR)
     (isPropValuedR : ∀ x y -> isProp (R x y)) where
     open FunctionalRel f g R
     functionalRel-propValued : ∀ x' y' -> isProp (functionalRelation x' y')
     functionalRel-propValued x' y' p q = isPropValuedR (f x') (g y') p q




  L℧A→LA⊎Unit' : ▹ (L℧ ⟨ A ⟩ → L (⟨ A ⟩ ⊎ Unit)) -> L℧ ⟨ A ⟩ → L (⟨ A ⟩ ⊎ Unit)
  L℧A→LA⊎Unit' IH (η a) = η (inl a)
  L℧A→LA⊎Unit' IH ℧ = η (inr tt)
  L℧A→LA⊎Unit' IH (θ la~) = θ (λ t → IH t (la~ t))
  
  L℧A→LA⊎Unit : L℧ ⟨ A ⟩ → L (⟨ A ⟩ ⊎ Unit)
  L℧A→LA⊎Unit = fix L℧A→LA⊎Unit'

  LA⊎Unit→L℧A' : ▹ (L (⟨ A ⟩ ⊎ Unit) → L℧ ⟨ A ⟩) -> L (⟨ A ⟩ ⊎ Unit) → L℧ ⟨ A ⟩
  LA⊎Unit→L℧A' IH (η (inl a)) = η a
  LA⊎Unit→L℧A' IH (η (inr tt)) = ℧
  LA⊎Unit→L℧A' IH (θ la~) = θ (λ t → IH t (la~ t))

  LA⊎Unit→L℧A : L (⟨ A ⟩ ⊎ Unit) → L℧ ⟨ A ⟩
  LA⊎Unit→L℧A = fix LA⊎Unit→L℧A'

  unfold-L→L℧ : LA⊎Unit→L℧A ≡ LA⊎Unit→L℧A' (next LA⊎Unit→L℧A)
  unfold-L→L℧ = fix-eq LA⊎Unit→L℧A'

  unfold-L℧→L : L℧A→LA⊎Unit ≡ L℧A→LA⊎Unit' (next L℧A→LA⊎Unit)
  unfold-L℧→L = fix-eq L℧A→LA⊎Unit'

  L℧ALA⊎Unit-iso : Iso (L℧ ⟨ A ⟩) (L (⟨ A ⟩ ⊎ Unit))
  L℧ALA⊎Unit-iso =
    iso to inv sec is-retract
    where
      to' = L℧A→LA⊎Unit'
      to = L℧A→LA⊎Unit 
      inv' = LA⊎Unit→L℧A'
      inv = LA⊎Unit→L℧A
      
      P' = (section (to' (next to)) (inv' (next inv)))
      P = section to inv

      P'→P : P' → P
      P'→P H x = (λ i -> fix-eq to' i (fix-eq inv' i x)) ∙ H x

      sec' : ▹ (section (to' (next to)) (inv' (next inv))) -> section (to' (next to)) (inv' (next inv))
      sec' IH (η (inl b)) = refl
      sec' IH (η (inr t)) = refl
      sec' IH (θ la~) = λ i -> θ λ t -> P'→P (IH t) (la~ t) i
      
      sec : section L℧A→LA⊎Unit LA⊎Unit→L℧A
      sec = transport (λ i → section (fix-eq to' (~ i)) (fix-eq inv' (~ i))) (fix sec')

      Q'→Q : retract (to' (next to)) (inv' (next inv)) → retract to inv
      Q'→Q H x = (λ i → fix-eq inv' i (fix-eq to' i x)) ∙ H x

      is-retract' : ▹ retract (to' (next to)) (inv' (next inv)) -> retract (to' (next to)) (inv' (next inv))
      is-retract' IH (η a) = refl
      is-retract' IH ℧ = refl
      is-retract' IH (θ la~) = λ i → θ (λ t → Q'→Q (IH t) (la~ t) i)
      
      is-retract : retract L℧A→LA⊎Unit LA⊎Unit→L℧A
      is-retract = transport (λ i → retract (fix-eq to' (~ i)) (fix-eq inv' (~ i))) (fix is-retract')

  open FunctionalRel

  _∽_ : L℧ ⟨ A ⟩ → L℧ ⟨ A ⟩ → Type (ℓ-max ℓ ℓ'')
  _∽_ = functionalRelation L℧A→LA⊎Unit L℧A→LA⊎Unit LiftBisim._≈_
  -- L℧ X ≡ Lift (X + 1)

  open Inductive (next _≾_) public
  open Properties public

  prop-≾'→prop-≾ : BinaryRelation.isPropValued _≾'_ -> BinaryRelation.isPropValued _≾_
  prop-≾'→prop-≾ = transport (λ i -> BinaryRelation.isPropValued (sym unfold-≾ i))

  ord-prop' : ▹ (BinaryRelation.isPropValued _≾'_) -> BinaryRelation.isPropValued _≾'_
  ord-prop' IH (η a) (η b) p q = A.is-prop-valued a b p q
  ord-prop' IH ℧ lb (lift tt) (lift tt) = refl
  ord-prop' IH (θ la~) (θ lb~) p q =
    λ i t → prop-≾'→prop-≾ (IH t) (la~ t) (lb~ t) (p t) (q t) i

  ord-prop : BinaryRelation.isPropValued _≾_
  ord-prop = prop-≾'→prop-≾ (fix ord-prop')

  ord-refl' : ▹ ((a : L℧ ⟨ A ⟩) -> a ≾ a) ->
                    (a : L℧ ⟨ A ⟩) -> a ≾ a
  ord-refl' IH (η x) =
    transport (sym (λ i -> unfold-≾ i (η x) (η x))) (A.is-refl x)
  ord-refl' IH ℧ =
    transport (sym (λ i -> unfold-≾ i ℧ ℧)) tt*
  ord-refl' IH (θ x) =
    transport (sym (λ i -> unfold-≾ i (θ x) (θ x))) λ t → IH t (x t)

  ord-refl : (a : L℧ ⟨ A ⟩) -> a ≾ a
  ord-refl = fix ord-refl'

  ord-antisym' : ▹ ((la lb : L℧ ⟨ A ⟩) -> la ≾' lb -> lb ≾' la -> la ≡ lb) ->
                    (la lb : L℧ ⟨ A ⟩) -> la ≾' lb -> lb ≾' la -> la ≡ lb
  ord-antisym' IH (η a) (η b) a≤b b≤a i = η (A.is-antisym a b a≤b b≤a i)
  ord-antisym' IH ℧ ℧ _ _ = refl
  ord-antisym' IH (θ la~) (θ lb~) la≤lb lb≤la i =
    θ λ t -> IH t (la~ t) (lb~ t) (≾->≾' (la≤lb t)) (≾->≾' (lb≤la t)) i

  ord-antisym : BinaryRelation.isAntisym _≾_ -- (a b : A) → R a b → R b a → a ≡ b
  ord-antisym = transport {!!} (fix ord-antisym')

  ord-trans : BinaryRelation.isTrans _≾_
  ord-trans = {!!}

 {-

  prop-≈→prop-≃ : BinaryRelation.isPropValued LiftBisim._≈_ -> BinaryRelation.isPropValued _≃_
  prop-≈→prop-≃ = transport (λ i → BinaryRelation.isPropValued (sym {!!} i))

  bisim-prop : BinaryRelation.isPropValued _≃_
  bisim-prop = {!!} -}
      

  𝕃 : PosetBisim ℓ ℓ' (ℓ-max ℓ ℓ'')
  𝕃 = L℧ ⟨ A ⟩ ,
    (posetbisimstr (isSetL℧ A.is-set)
      _≾_
      (isorderingrelation ord-prop ord-refl ord-trans ord-antisym)
      _∽_
      (isbisim (functionalRel-refl L℧A→LA⊎Unit LiftBisim._≈_ (LiftBisim.Reflexive.≈-refl (A⊎1 .snd .is-refl-Bisim)))
             (functionalRel-sym L℧A→LA⊎Unit LiftBisim._≈_ (LiftBisim.Symmetric.symmetric (A⊎1 .snd .is-sym)))
             (functionalRel-propValued L℧A→LA⊎Unit L℧A→LA⊎Unit LiftBisim._≈_ (LiftBisim.PropValued.prop (A⊎1 .snd .is-prop-valued-Bisim)))))


module LiftDPMorRel (A : PosetBisim ℓA ℓ'A ℓ''A) (B : PosetBisim ℓB ℓ'B ℓ''B) (R : PBRel A B ℓ'') where
  module LR = LiftRelation ⟨ A ⟩ ⟨ B ⟩ (PBRel.R R)
  open LiftPosetBisim
  open PBRel
  
  ℝ : PBRel (𝕃 A) (𝕃 B) ℓ''
  ℝ = record {
    R = LR._≾_ ;
    is-prop-valued = {!!} ;
    is-antitone = {!!} ;
    is-monotone = {!!} }
