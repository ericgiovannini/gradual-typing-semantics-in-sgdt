{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.GuardedResults.NoGoTheorem (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary

open import Semantics.Concrete.GuardedLift k

private
  variable
    ℓ ℓ' : Level

    X : Type ℓ
private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A



-- General no-go theorem about a step-indexed relation on the guarded Lift monad

congruence : {X : Type ℓ} → (_R_ : L X -> L X -> Type ℓ') -> Type (ℓ-max ℓ ℓ')
congruence {X = X} _R_ = {lx ly : ▹ (L X)} -> ▸ (λ t → (lx t) R (ly t)) -> (θ lx) R (θ ly)

congruence' : {X : Type ℓ} → (_R_ : L X -> L X -> Type ℓ') -> Type (ℓ-max ℓ ℓ')
congruence' {X = X} _R_ = {lx ly : L X} -> ▹ (lx R ly) -> (θ (next lx)) R (θ (next ly))

cong→cong' : ∀ {_R_ : L X -> L X -> Type ℓ'} → congruence _R_ → congruence' _R_
cong→cong' cong ▹R = cong ▹R



relThmR : (_R_ : L X -> L X -> Type ℓ') ->
  BinaryRelation.isTrans _R_ ->
  congruence _R_ ->
  ((x : L X) -> x R (θ (next x))) ->
  ((x : L X) -> x R (fix θ))
relThmR {X = X} _R_ hTrans hCong hθR = fix lem
  where
   lem :
    ▹ ((x : L X) -> x R (fix θ)) → (x : L X) -> x R (fix θ)
   lem IH lx =
     subst (λ y → lx R y) (sym (fix-eq θ))
       (hTrans _ _ _
         (hθR lx)
         (hCong (λ t → IH t lx)))


relThmL : (_R_ : L X -> L X -> Type ℓ') ->
  BinaryRelation.isTrans _R_ ->
  congruence _R_ ->
  ((x : L X) -> (θ (next x)) R x) ->
  ((x : L X) -> (fix θ) R x)
relThmL {X = X} _R_ hTrans hCong hθR = fix lem
  where
    lem :
      ▹ ((x : L X) -> (fix θ) R x) → (x : L X) -> (fix θ) R x
    lem IH lx = subst
      (λ y -> y R lx) (sym (fix-eq θ))
      (hTrans _ _ _ (hCong (λ t -> IH t lx)) (hθR lx))

no-go :
  (_R_ : L X -> L X -> Type ℓ') ->
  BinaryRelation.isTrans _R_ ->
  congruence _R_ ->
  ((x : L X) -> (θ (next x)) R x) ->
  ((x : L X) -> x R (θ (next x))) ->
  ∀ x y → x R y
no-go _R_ hTrans hCong hδ-Left hδ-Right x y =
  hTrans x (fix θ) y (relThmR _ hTrans hCong hδ-Right x) (relThmL _ hTrans hCong hδ-Left y)
