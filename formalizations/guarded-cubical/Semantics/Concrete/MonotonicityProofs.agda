{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.MonotonicityProofs where

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



open import Common.Common

open import Cubical.Relation.Binary.Poset
open import Common.Poset.Convenience
open import Common.Poset.Monotone
open import Common.Poset.Constructions



private
  variable
    ℓ ℓ' : Level
    ℓR ℓR1 ℓR2 : Level
    ℓA ℓ'A ℓA' ℓ'A' ℓB ℓ'B ℓB' ℓ'B' : Level
    A :  Poset ℓA ℓ'A
    A' : Poset ℓA' ℓ'A'
    B :  Poset ℓB ℓ'B
    B' : Poset ℓB' ℓ'B'




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




module ClockedProofs (k : Clock) where
  open import Semantics.Lift k
  open import Semantics.LockStepErrorOrdering k
  open LiftPoset

  private
    ▹_ : Type ℓ → Type ℓ
    ▹_ A = ▹_,_ k A


  ret-monotone-het : {A A' : Poset ℓA ℓ'A} ->
    (rAA' : ⟨ A ⟩ -> ⟨ A' ⟩ -> Type ℓR1) ->
    TwoCell rAA' (LiftRelation._≾_ _ _ rAA') ret ret
  ret-monotone-het {A = A} {A' = A'} rAA' = λ a a' a≤a' →
    LiftRelation.Properties.ord-η-monotone ⟨ A ⟩ ⟨ A' ⟩ rAA' a≤a'

  ret-monotone : {A : Poset ℓA ℓ'A} ->
    (a a' : ⟨ A ⟩) ->
    rel A a a' ->
    rel (𝕃 A) (ret a) (ret a')
  ret-monotone {A = A} = λ a a' a≤a' →
    LiftRelation.Properties.ord-η-monotone ⟨ A ⟩ ⟨ A ⟩ _ a≤a'

  _×rel_ : {A : Type ℓA} {A' : Type ℓA'} {B : Type ℓB} {B' : Type ℓB'} ->
    (R : A -> A' -> Type ℓR1) -> (S : B -> B' -> Type ℓR2) ->
    (p : A × B) -> (p' : A' × B') -> Type (ℓ-max ℓR1 ℓR2)
  (R ×rel S) (a , b) (a' , b') = R a a' × S b b'

  lift×-monotone-het : {A : Poset ℓA ℓ'A} {A' : Poset ℓA' ℓ'A'}
    {B : Poset ℓB ℓ'B} {B' : Poset ℓB' ℓ'B'} ->
    (R : ⟨ A ⟩ -> ⟨ A' ⟩ -> Type ℓR1) ->
    (S : ⟨ B ⟩ -> ⟨ B' ⟩ -> Type ℓR2) ->
    (lab : ⟨ 𝕃 (A ×p B) ⟩) -> (la'b' : ⟨ 𝕃 (A' ×p B') ⟩) ->
    (_ LiftRelation.≾ _) (R ×rel S) lab la'b' ->
    ((_ LiftRelation.≾ _) R ×rel (_ LiftRelation.≾ _) S) (lift× lab) (lift× la'b')
  lift×-monotone-het {A = A} {A' = A'} {B = B} {B' = B'} R S lab la'b' lab≤la'b' =
    let fixed = fix monotone-lift×' in
    -- transport⁻Transport
    transport (sym (λ i → LiftP'.unfold-≾ {!i!} {!!} {!!}))
      (fixed lab la'b' (transport (λ i → LiftP'.unfold-≾ i lab la'b') lab≤la'b'))
--(sym λ i → LiftP'.unfold-≾ {!!} {!unfold-lift×-inv i!} {!!})
{-
(LiftP1'._≾_ ×rel LiftP2'._≾_) (lift× lab) (lift× la'b') ≡
      Σ
      (lift×' (next lift×) lab .fst ≾'P1' lift×' (next lift×) la'b' .fst)
      (λ _ →
         lift×' (next lift×) lab .snd ≾'P2' lift×' (next lift×) la'b' .snd)
-}
    where
      _≾'LA_  = LiftPoset._≾'_ A
      _≾'LA'_ = LiftPoset._≾'_ A'
      _≾'LB_  = LiftPoset._≾'_ B
      _≾'LB'_ = LiftPoset._≾'_ B'

      module LiftP' = LiftRelation (⟨ A ⟩ × ⟨ B ⟩) (⟨ A' ⟩ × ⟨ B' ⟩) (R ×rel S)
      module LiftP1' = LiftRelation ⟨ A ⟩ ⟨ A' ⟩ R
      module LiftP2' = LiftRelation ⟨ B ⟩ ⟨ B' ⟩ S

      _≾'P'_ = LiftP'.Inductive._≾'_ (next LiftP'._≾_)
      _≾'P1'_ = LiftP1'.Inductive._≾'_ (next LiftP1'._≾_)
      _≾'P2'_ = LiftP2'.Inductive._≾'_ (next LiftP2'._≾_)

      monotone-lift×' :
        ▹ ((lab : ⟨ 𝕃 (A ×p B) ⟩) -> (la'b' : ⟨ 𝕃 (A' ×p B') ⟩) ->
          lab ≾'P' la'b' ->
          (lift×' (next lift×) lab .fst ≾'P1' lift×' (next lift×) la'b' .fst)
          × (lift×' (next lift×) lab .snd ≾'P2' lift×' (next lift×) la'b' .snd)) ->
        (lab : ⟨ 𝕃 (A ×p B) ⟩) -> (la'b' : ⟨ 𝕃 (A' ×p B') ⟩) ->
          lab ≾'P' la'b' ->
          (lift×' (next lift×) lab .fst ≾'P1' lift×' (next lift×) la'b' .fst)
          × (lift×' (next lift×) lab .snd ≾'P2' lift×' (next lift×) la'b' .snd)
      monotone-lift×' IH (η (a , b)) (η (a' , b')) (x , y) =
       transport (λ i → LiftP1'.unfold-≾ i (η a) (η a')) (LiftP1'.Properties.ord-η-monotone x)
        , transport (λ i → LiftP2'.unfold-≾ i (η b) (η b')) (LiftP2'.Properties.ord-η-monotone y)
      monotone-lift×' IH ℧ l' l≤l' = tt* , tt*
      monotone-lift×' IH (θ p) (θ p') l≤l' =
        (λ t → transport
          (λ i → (sym LiftP1'.unfold-≾) i
            ((sym unfold-lift×) i (p t) .fst)
            ((sym unfold-lift×) i (p' t) .fst))
          (IH t (p t) (p' t)
            (transport (λ i → LiftP'.unfold-≾ i (p t) (p' t)) (l≤l' t)) .fst))
        , λ t → transport
          (λ i → (sym LiftP2'.unfold-≾) i
            ((sym unfold-lift×) i (p t) .snd)
            ((sym unfold-lift×) i (p' t) .snd))
          (IH t (p t) (p' t)
            (transport (λ i → LiftP'.unfold-≾ i (p t) (p' t)) (l≤l' t)) .snd)

--todo: follow ext-monotone-het
  lift×-inv-monotone-het : {A : Poset ℓA ℓ'A} {A' : Poset ℓA' ℓ'A'}
    {B : Poset ℓB ℓ'B} {B' : Poset ℓB' ℓ'B'} ->
    (R : ⟨ A ⟩ -> ⟨ A' ⟩ -> Type ℓR1) ->
    (S : ⟨ B ⟩ -> ⟨ B' ⟩ -> Type ℓR2) ->
    (lalb : ⟨ 𝕃 A ×p 𝕃 B ⟩) -> (la'lb' : ⟨ 𝕃 A' ×p 𝕃 B' ⟩) ->
    ((_ LiftRelation.≾ _) R ×rel (_ LiftRelation.≾ _) S) lalb la'lb' ->
    (_ LiftRelation.≾ _) (R ×rel S) (lift×-inv lalb) (lift×-inv la'lb')
  lift×-inv-monotone-het {A = A} {A' = A'} {B = B} {B' = B'} R S p p' (la≤la' , lb≤lb') =
    let fixed = fix monotone-lift×-inv' in
    transport
      (sym (λ i -> LiftP'.unfold-≾ i (unfold-lift×-inv i p) (unfold-lift×-inv i p')))
      (fixed p p' ((transport (λ i → LiftP1'.unfold-≾ i (p .fst) (p' .fst)) la≤la')
                  , transport (λ i → LiftP2'.unfold-≾ i (p .snd) (p' .snd)) lb≤lb'))
    where
      _≾'LA_  = LiftPoset._≾'_ A
      _≾'LA'_ = LiftPoset._≾'_ A'
      _≾'LB_  = LiftPoset._≾'_ B
      _≾'LB'_ = LiftPoset._≾'_ B'

      module LiftP' = LiftRelation (⟨ A ⟩ × ⟨ B ⟩) (⟨ A' ⟩ × ⟨ B' ⟩) (R ×rel S)
      module LiftP1' = LiftRelation ⟨ A ⟩ ⟨ A' ⟩ R
      module LiftP2' = LiftRelation ⟨ B ⟩ ⟨ B' ⟩ S

      _≾'P'_ = LiftP'.Inductive._≾'_ (next LiftP'._≾_)
      _≾'P1'_ = LiftP1'.Inductive._≾'_ (next LiftP1'._≾_)
      _≾'P2'_ = LiftP2'.Inductive._≾'_ (next LiftP2'._≾_)
      monotone-lift×-inv' :
        ▹ ((p : ⟨ 𝕃 A ×p 𝕃 B ⟩) -> (p' : ⟨ 𝕃 A' ×p 𝕃 B' ⟩) ->
          ((p .fst ≾'P1' p' .fst) × (p .snd ≾'P2' p' .snd)) ->
          lift×-inv' (next lift×-inv) p ≾'P' lift×-inv' (next lift×-inv) p') ->
        (p : ⟨ 𝕃 A ×p 𝕃 B ⟩) -> (p' : ⟨ 𝕃 A' ×p 𝕃 B' ⟩) ->
          ((p .fst ≾'P1' p' .fst) × (p .snd ≾'P2' p' .snd)) ->
          lift×-inv' (next lift×-inv) p ≾'P' lift×-inv' (next lift×-inv) p'
      monotone-lift×-inv' IH (η a1 , η b1) (η a2 , η b2) (a1≤a2 , b1≤b2) =
        transport
          (λ i → LiftP'.unfold-≾ {!i!} (lift×-inv (η a1 , η b1)) (lift×-inv (η a2 , η b2)))
          {!!}
        {-
        lift×-inv' (next lift×-inv) (η a1 , η b1) ≾'P'
        lift×-inv' (next lift×-inv) (η a2 , η b2)
        -}
      monotone-lift×-inv' IH ((η a) , (θ lb~)) ((η a') , (θ lb'~)) (la≤la' , lb≤lb') = {!!}
      monotone-lift×-inv' IH (℧ , _) (℧ , _) (la≤la' , lb≤lb') = {!!}
      monotone-lift×-inv' IH (_ , ℧) (_ , ℧) (la≤la' , lb≤lb') = {!!}
      monotone-lift×-inv' IH ((θ la~) , lb) (la' , lb') (la≤la' , lb≤lb') = {!!}
      monotone-lift×-inv' IH p p' p≤p' = {!!}
 
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
        ▹ ((la : ⟨ 𝕃 A ⟩) -> (la' : ⟨ 𝕃 A' ⟩)  ->
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
  ext-monotone {A = A} {B = B} f f' f≤f' la la' la≤la' =
    ext-monotone-het {A = A} {A' = A} {B = B} {B' = B} (rel A) (rel B) f f' f≤f' la la' la≤la'

  lift×-monotone : {A : Poset ℓA ℓ'A} {B : Poset ℓB ℓ'B} ->
    (l l' : ⟨ 𝕃 (A ×p B) ⟩) ->
    rel (𝕃 (A ×p B)) l l' ->
    rel (𝕃 A ×p 𝕃 B) (lift× l) (lift× l')
  lift×-monotone = {!!}

  lift×-inv-monotone : {A : Poset ℓA ℓ'A} {B : Poset ℓB ℓ'B} ->
    (l l' : ⟨ 𝕃 A ×p 𝕃 B ⟩) ->
    rel (𝕃 A ×p 𝕃 B) l l' ->
    rel (𝕃 (A ×p B)) (lift×-inv l) (lift×-inv l')
  lift×-inv-monotone = {!!}
  
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

