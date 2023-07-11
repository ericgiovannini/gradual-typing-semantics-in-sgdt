{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.MonotonicityProofs (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_^_)

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.Foundations.Function

-- open import Semantics.Predomains
open import Semantics.Lift k
-- open import Semantics.Monotone.Base
-- open import Semantics.StrongBisimulation k
-- open import Semantics.PredomainInternalHom

open import Common.Common

open import Cubical.Relation.Binary.Poset
open import Common.Poset.Convenience
open import Common.Poset.Monotone
open import Common.Poset.Constructions

open import Semantics.LockStepErrorOrdering k

private
  variable
    ℓ ℓ' : Level
    ℓR1 ℓR2 : Level
    ℓA ℓ'A ℓA' ℓ'A' ℓB ℓ'B ℓB' ℓ'B' : Level
    A :  Poset ℓA ℓ'A
    A' : Poset ℓA' ℓ'A'
    B :  Poset ℓB ℓ'B
    B' : Poset ℓB' ℓ'B'
private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

open LiftPoset


-- If A ≡ B, then we can translate knowledge about a relation on A
-- to its image in B obtained by transporting the related elements of A
-- along the equality of the underlying sets of A and B
rel-transport :
  {A B : Poset ℓ ℓ'} ->
  (eq : A ≡ B) ->
  {a1 a2 : ⟨ A ⟩} ->
  rel A a1 a2 ->
  rel B
    (transport (λ i -> ⟨ eq i ⟩) a1)
    (transport (λ i -> ⟨ eq i ⟩) a2)
rel-transport {A} {B} eq {a1} {a2} a1≤a2 =
  transport (λ i -> rel (eq i)
    (transport-filler (λ j -> ⟨ eq j ⟩) a1 i)
    (transport-filler (λ j -> ⟨ eq j ⟩) a2 i))
  a1≤a2

rel-transport-sym : {A B : Poset ℓ ℓ'} ->
  (eq : A ≡ B) ->
  {b1 b2 : ⟨ B ⟩} ->
  rel B b1 b2 ->
  rel A
    (transport (λ i → ⟨ sym eq i ⟩) b1)
    (transport (λ i → ⟨ sym eq i ⟩) b2)
rel-transport-sym eq {b1} {b2} b1≤b2 = rel-transport (sym eq) b1≤b2


mTransport : {A B : Poset ℓ ℓ'} -> (eq : A ≡ B) -> ⟨ A ==> B ⟩
mTransport {A} {B} eq = record {
  f = λ b → transport (λ i -> ⟨ eq i ⟩) b ;
  isMon = λ {b1} {b2} b1≤b2 → rel-transport eq b1≤b2 }


mTransportSym : {A B : Poset ℓ ℓ'} -> (eq : A ≡ B) -> ⟨ B ==> A ⟩
mTransportSym {A} {B} eq = record {
  f = λ b → transport (λ i -> ⟨ sym eq i ⟩) b ;
  isMon = λ {b1} {b2} b1≤b2 → rel-transport (sym eq) b1≤b2 }


-- Transporting the domain of a monotone function preserves monotonicity
mon-transport-domain : {A B C : Poset ℓ ℓ'} ->
  (eq : A ≡ B) ->
  (f : MonFun A C) ->
  {b1 b2 : ⟨ B ⟩} ->
  (rel B b1 b2) ->
  rel C
    (MonFun.f f (transport (λ i → ⟨ sym eq i ⟩ ) b1))
    (MonFun.f f (transport (λ i → ⟨ sym eq i ⟩ ) b2))
mon-transport-domain eq f {b1} {b2} b1≤b2 =
  MonFun.isMon f (rel-transport (sym eq) b1≤b2)

mTransportDomain : {A B C : Poset ℓ ℓ'} ->
  (eq : A ≡ B) ->
  MonFun A C ->
  MonFun B C
mTransportDomain {A} {B} {C} eq f = record {
  f = g eq f;
  isMon = mon-transport-domain eq f }
  where
    g : {A B C : Poset ℓ ℓ'} ->
      (eq : A ≡ B) ->
      MonFun A C ->
      ⟨ B ⟩ -> ⟨ C ⟩
    g eq f b = MonFun.f f (transport (λ i → ⟨ sym eq i ⟩ ) b)




-- ext respects monotonicity, in a general, heterogeneous sense
ext-monotone-het : {A A' : Poset ℓA ℓ'A} {B B' : Poset ℓB ℓ'B}
  (rAA' : ⟨ A ⟩ -> ⟨ A' ⟩ -> Type ℓR1) ->
  (rBB' : ⟨ B ⟩ -> ⟨ B' ⟩ -> Type ℓR2) ->
  (f :  ⟨ A ⟩  -> ⟨ (𝕃 B) ⟩) ->
  (f' : ⟨ A' ⟩ -> ⟨ (𝕃 B') ⟩) ->
  TwoCell rAA' (LiftRelation._≾_ _ _ rBB') f f' ->
  (la : ⟨ 𝕃 A ⟩) -> (la' : ⟨ 𝕃 A' ⟩) ->
  (LiftRelation._≾_ _ _ rAA' la la') ->
  LiftRelation._≾_ _ _ rBB' (ext f la) (ext f' la')
ext-monotone-het {A = A} {A' = A'} {B = B} {B' = B'} rAA' rBB' f f' f≤f' la la' la≤la' =
  let fixed = fix (monotone-ext') in
  transport
    (sym (λ i -> LiftBB'.unfold-≾ i (unfold-ext f i la) (unfold-ext f' i la')))
    (fixed la la' (transport (λ i → LiftAA'.unfold-≾ i la la') la≤la'))
  where

    -- Note that these four have already been
    -- passed (next _≾_) as a parameter (this happened in
    -- the defintion of the module 𝕃, where we said
    -- open Inductive (next _≾_) public)
    _≾'LA_  = LiftPoset._≾'_ A
    _≾'LA'_ = LiftPoset._≾'_ A'
    _≾'LB_  = LiftPoset._≾'_ B
    _≾'LB'_ = LiftPoset._≾'_ B'

    module LiftAA' = LiftRelation ⟨ A ⟩ ⟨ A' ⟩ rAA'
    module LiftBB' = LiftRelation ⟨ B ⟩ ⟨ B' ⟩ rBB'

    -- The heterogeneous lifted relations
    _≾'LALA'_ = LiftAA'.Inductive._≾'_ (next LiftAA'._≾_)
    _≾'LBLB'_ = LiftBB'.Inductive._≾'_ (next LiftBB'._≾_)
    

    monotone-ext' :
      ▹ (
          (la : ⟨ 𝕃 A ⟩) -> (la' : ⟨ 𝕃 A' ⟩)  ->
          (la ≾'LALA' la') ->
          (ext' f  (next (ext f))  la) ≾'LBLB'
          (ext' f' (next (ext f')) la')) ->
        (la : ⟨ 𝕃 A ⟩) -> (la' : ⟨ 𝕃 A' ⟩)  ->
        (la ≾'LALA' la') ->
        (ext' f  (next (ext f))  la) ≾'LBLB'
        (ext' f' (next (ext f')) la')
    monotone-ext' IH (η x) (η y) x≤y =
      transport
      (λ i → LiftBB'.unfold-≾ i (f x) (f' y))
      (f≤f' x y x≤y)
    monotone-ext' IH ℧ la' la≤la' = tt*
    monotone-ext' IH (θ lx~) (θ ly~) la≤la' = λ t ->
      transport
        (λ i → (sym (LiftBB'.unfold-≾)) i
          (sym (unfold-ext f) i (lx~ t))
          (sym (unfold-ext f') i (ly~ t)))
        (IH t (lx~ t) (ly~ t)
          (transport (λ i -> LiftAA'.unfold-≾ i (lx~ t) (ly~ t)) (la≤la' t)))



-- ext respects monotonicity (in the usual homogeneous sense)
-- This can be rewritten to reuse the above result!
ext-monotone :
  (f f' : ⟨ A ⟩ -> ⟨ (𝕃 B) ⟩) ->
  TwoCell (rel A) (rel (𝕃 B)) f f' ->
  (la la' : ⟨ 𝕃 A ⟩) ->
  rel (𝕃 A) la la' ->
  rel (𝕃 B) (ext f la) (ext f' la')
ext-monotone {A} {B} f f' f≤f' la la' la≤la' = {!!}
 

bind-monotone :
  {la la' : ⟨ 𝕃 A ⟩} ->
  (f f' : ⟨ A ⟩ -> ⟨ (𝕃 B) ⟩) ->
  rel (𝕃 A) la la' ->
  TwoCell (rel A) (rel (𝕃 B)) f f' ->
  rel (𝕃 B) (bind la f) (bind la' f')
bind-monotone {A = A} {B = B} {la = la} {la' = la'} f f' la≤la' f≤f' =
  ext-monotone {A = A} {B = B} f f' f≤f' la la' la≤la'
   

mapL-monotone-het : {A A' : Poset ℓA ℓ'A} {B B' : Poset ℓB' ℓ'B'} ->
  (rAA' : ⟨ A ⟩ -> ⟨ A' ⟩ -> Type ℓR1) ->
  (rBB' : ⟨ B ⟩ -> ⟨ B' ⟩ -> Type ℓR2) ->
  (f : ⟨ A ⟩ -> ⟨ B ⟩) ->
  (f' : ⟨ A' ⟩ -> ⟨ B' ⟩) ->
  TwoCell rAA' rBB' f f' ->
  (la : ⟨ 𝕃 A ⟩) -> (la' : ⟨ 𝕃 A' ⟩) ->
  (LiftRelation._≾_ _ _ rAA' la la') ->
   LiftRelation._≾_ _ _ rBB' (mapL f la) (mapL f' la')
mapL-monotone-het {A = A} {A' = A'} {B = B} {B' = B'} rAA' rBB' f f' f≤f' la la' la≤la' =
  ext-monotone-het {A = A} {A' = A'} {B = B} {B' = B'} rAA' rBB' (ret ∘ f) (ret ∘ f')
    (λ a a' a≤a' → LiftRelation.Properties.ord-η-monotone _ _ rBB' (f≤f' a a' a≤a'))
    la la' la≤la'


-- This is a special case of the above
mapL-monotone : {A B : Poset ℓ ℓ'} ->
  {la la' : ⟨ 𝕃 A ⟩} ->
  (f f' : ⟨ A ⟩ -> ⟨ B ⟩) ->
  rel (𝕃 A) la la' ->
  TwoCell (rel A) (rel B) f f' ->
  rel (𝕃 B) (mapL f la) (mapL f' la')
mapL-monotone {A = A} {B = B} {la = la} {la' = la'} f f' la≤la' f≤f' =
  bind-monotone (ret ∘ f) (ret ∘ f') la≤la'
    (λ a1 a2 a1≤a2 → ord-η-monotone B (f≤f' a1 a2 a1≤a2))


-- As a corollary/special case, we can consider the case of a single
-- monotone function.
monotone-bind-mon :
  {la la' : ⟨ 𝕃 A ⟩} ->
  (f : MonFun A (𝕃 B)) ->
  (rel (𝕃 A) la la') ->
  rel (𝕃 B) (bind la (MonFun.f f)) (bind la' (MonFun.f f))
monotone-bind-mon f la≤la' =
  bind-monotone (MonFun.f f) (MonFun.f f) la≤la' (≤mon-refl {!!})

