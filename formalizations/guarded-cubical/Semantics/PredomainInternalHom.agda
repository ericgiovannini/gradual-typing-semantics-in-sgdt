{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.PredomainInternalHom where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Relation.Binary.Order.Poset


open import Semantics.Predomains
open import Semantics.Monotone.Base

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
