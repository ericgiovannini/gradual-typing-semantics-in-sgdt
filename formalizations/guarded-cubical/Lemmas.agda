{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Later

module Lemmas (k : Clock) where

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

open import StrongBisimulation k
open import GradualSTLC
open import SyntacticTermPrecision k

private
  variable
    l : Level
    A B : Set l
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A

open 𝕃

{-
test : (A B : Type) -> (eq : A ≡ B) -> (x : A) -> (T : (A : Type) -> A -> Type) ->
 (T A x) -> (T B (transport eq x))
test A B eq x T Tx = transport (λ i -> T (eq i) (transport-filler eq x i)) Tx

-- transport (λ i -> T (eq i) ?) Tx
-- Goal : eq i
-- Constraints:
-- x = ?8 (i = i0) : A
-- ?8 (i = i1) = transp (λ i₁ → eq i₁) i0 x : B


-- transport-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x : A)
--                   → PathP (λ i → p i) x (transport p x)
                   

test' : (A B : Predomain) -> (S : Type) ->
 (eq : A ≡ B)  ->
 (x : ⟨ A ⟩) ->
 (T : (A : Predomain) -> ⟨ A ⟩ -> Type) ->
 (T A x) -> T B (transport (λ i -> ⟨ eq i ⟩) x)
test' A B S eq x T Tx = transport
  (λ i -> T (eq i) (transport-filler (λ j → ⟨ eq j ⟩) x i))
  Tx
-}


-- If A ≡ B, then we can translate knowledge about a relation on A
-- to its image in B obtained by transporting the related elements of A
-- along the equality of the underlying sets of A and B
rel-transport :
  {A B : Predomain} ->
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

rel-transport-sym : {A B : Predomain} ->
  (eq : A ≡ B) ->
  {b1 b2 : ⟨ B ⟩} ->
  rel B b1 b2 ->
  rel A
    (transport (λ i → ⟨ sym eq i ⟩) b1)
    (transport (λ i → ⟨ sym eq i ⟩) b2)
rel-transport-sym eq {b1} {b2} b1≤b2 = rel-transport (sym eq) b1≤b2


mTransport : {A B : Predomain} -> (eq : A ≡ B) -> ⟨ A ==> B ⟩
mTransport {A} {B} eq = record {
  f = λ b → transport (λ i -> ⟨ eq i ⟩) b ;
  isMon = λ {b1} {b2} b1≤b2 → rel-transport eq b1≤b2 }


mTransportSym : {A B : Predomain} -> (eq : A ≡ B) -> ⟨ B ==> A ⟩
mTransportSym {A} {B} eq = record {
  f = λ b → transport (λ i -> ⟨ sym eq i ⟩) b ;
  isMon = λ {b1} {b2} b1≤b2 → rel-transport (sym eq) b1≤b2 }


-- Transporting the domain of a monotone function preserves monotonicity
mon-transport-domain : {A B C : Predomain} ->
  (eq : A ≡ B) ->
  (f : MonFun A C) ->
  {b1 b2 : ⟨ B ⟩} ->
  (rel B b1 b2) ->
  rel C
    (MonFun.f f (transport (λ i → ⟨ sym eq i ⟩ ) b1))
    (MonFun.f f (transport (λ i → ⟨ sym eq i ⟩ ) b2))
mon-transport-domain eq f {b1} {b2} b1≤b2 =
  MonFun.isMon f (rel-transport (sym eq) b1≤b2)

mTransportDomain : {A B C : Predomain} ->
  (eq : A ≡ B) ->
  MonFun A C ->
  MonFun B C
mTransportDomain {A} {B} {C} eq f = record {
  f = g eq f;
  isMon = mon-transport-domain eq f }
  where
    g : {A B C : Predomain} ->
      (eq : A ≡ B) ->
      MonFun A C ->
      ⟨ B ⟩ -> ⟨ C ⟩
    g eq f b = MonFun.f f (transport (λ i → ⟨ sym eq i ⟩ ) b)






-- rel (𝕃 B) (ext f la) (ext f' la') ≡ _A_1119
-- ord (ext f la) (ext f' la') ≡ 
-- ord' (next ord) (ext' f (next (ext f)) la) (ext' f (next (ext f)) la')


-- ext respects monotonicity 
ext-monotone : {A B : Predomain} ->
  (f f' : ⟨ A ⟩ -> ⟨ (𝕃 B) ⟩) ->
  fun-order A (𝕃 B) f f' ->
  (la la' : ⟨ 𝕃 A ⟩) ->
  rel (𝕃 A) la la' ->
  rel (𝕃 B) (ext f la) (ext f' la')
ext-monotone {A} {B} f f' f≤f' la la' la≤la' =
  let fixed = fix (monotone-ext' f f' f≤f') in
  transport
    (sym (λ i -> unfold-ord B i (unfold-ext f i la) (unfold-ext f' i la')))
    (fixed la la' (transport (λ i → unfold-ord A i la la') la≤la'))
  where
    monotone-ext' :
      (f f' : ⟨ A ⟩ -> ⟨ (𝕃 B) ⟩) ->
      (fun-order A (𝕃 B) f f') ->
      ▹ (
        (la la' : ⟨ 𝕃 A ⟩) ->
         ord' A (next (ord A)) la la' ->
         ord' B (next (ord B))
          (ext' f  (next (ext f))  la)
          (ext' f' (next (ext f')) la')) ->
     (la la' : ⟨ 𝕃 A ⟩) ->
       ord' A (next (ord A)) la la' ->
       ord' B (next (ord B))
        (ext' f  (next (ext f))  la)
        (ext' f' (next (ext f')) la')
    monotone-ext' f f' f≤f' IH (η x) (η y) x≤y =
      transport
      (λ i → unfold-ord B i (f x) (f' y))
      (f≤f' x y x≤y)
    monotone-ext' f f' f≤f' IH ℧ la' la≤la' = tt
    monotone-ext' f f' f≤f' IH (θ lx~) (θ ly~) la≤la' = λ t ->
      transport
        (λ i → (sym (unfold-ord B)) i
          (sym (unfold-ext f) i (lx~ t))
          (sym (unfold-ext f') i (ly~ t)))
        (IH t (lx~ t) (ly~ t)
          (transport (λ i -> unfold-ord A i (lx~ t) (ly~ t)) (la≤la' t)))



{-
ext-monotone' : {A B : Predomain} ->
  {la la' : ⟨ 𝕃 A ⟩} ->
  (f f' : ⟨ A ⟩ -> ⟨ (𝕃 B) ⟩) ->
  rel (𝕃 A) la la' ->
  fun-order A (𝕃 B) f f' ->
  rel (𝕃 B) (ext f la) (ext f' la')
ext-monotone' {A} {B} {la} {la'} f f' la≤la' f≤f' =
  let fixed = fix (monotone-ext' f f' f≤f') in
  --transport
    --(sym (λ i -> ord B (unfold-ext f i la) (unfold-ext f' i la')))
    (fixed la la' (transport (λ i → unfold-ord A i la la') la≤la'))
  where
    monotone-ext' :
      (f f' : ⟨ A ⟩ -> ⟨ (𝕃 B) ⟩) ->
      (fun-order A (𝕃 B) f f') ->
      ▹ (
        (la la' : ⟨ 𝕃 A ⟩) ->
         ord' A (next (ord A)) la la' ->
         ord B
          (ext f  la)
          (ext f' la')) ->
     (la la' : ⟨ 𝕃 A ⟩) ->
       ord' A (next (ord A)) la la' ->
       ord B
        (ext f  la)
        (ext f' la')
    monotone-ext' f f' f≤f' IH (η x) (η y) x≤y = {!!} -- (f≤f' x y x≤y)
    monotone-ext' f f' f≤f' IH ℧ la' la≤la' = transport (sym (λ i -> unfold-ord B i (ext f ℧) (ext f' la'))) {!!}
      -- transport (sym (λ i → unfold-ord B i (ext' f (next (ext f)) ℧) (ext' f' (next (ext f')) la'))) tt
    monotone-ext' f f' f≤f' IH (θ lx~) (θ ly~) la≤la' = {!!} -- λ t -> ?
-}


bind-monotone : {A B : Predomain} ->
  {la la' : ⟨ 𝕃 A ⟩} ->
  (f f' : ⟨ A ⟩ -> ⟨ (𝕃 B) ⟩) ->
  rel (𝕃 A) la la' ->
  fun-order A (𝕃 B) f f' ->
  rel (𝕃 B) (bind la f) (bind la' f')
bind-monotone {A} {B} {la} {la'} f f' la≤la' f≤f' =
  ext-monotone f f' f≤f' la la' la≤la'
   

mapL-monotone : {A B : Predomain} ->
  {la la' : ⟨ 𝕃 A ⟩} ->
  (f f' : ⟨ A ⟩ -> ⟨ B ⟩) ->
  rel (𝕃 A) la la' ->
  fun-order A B f f' ->
  rel (𝕃 B) (mapL f la) (mapL f' la')
mapL-monotone {A} {B} {la} {la'} f f' la≤la' f≤f' =
  bind-monotone (ret ∘ f) (ret ∘ f') la≤la'
    (λ a1 a2 a1≤a2 → ord-η-monotone B (f≤f' a1 a2 a1≤a2))

-- As a corollary/special case, we can consider the case of a single
-- monotone function.
monotone-bind-mon : {A B : Predomain} ->
  {la la' : ⟨ 𝕃 A ⟩} ->
  (f : MonFun A (𝕃 B)) ->
  (rel (𝕃 A) la la') ->
  rel (𝕃 B) (bind la (MonFun.f f)) (bind la' (MonFun.f f))
monotone-bind-mon f la≤la' =
  bind-monotone (MonFun.f f) (MonFun.f f) la≤la' (mon-fun-order-refl f)

{-
-- bind respects monotonicity

monotone-bind : {A B : Predomain} ->
  {la la' : ⟨ 𝕃 A ⟩} ->
  (f f' : MonFun A (𝕃 B)) ->
  rel (𝕃 A) la la' ->
  rel (arr' A (𝕃 B)) f f' ->
  rel (𝕃 B) (bind la (MonFun.f f)) (bind la' (MonFun.f f'))
monotone-bind {A} {B} {la} {la'} f f' la≤la' f≤f' =
  {!!}

  where
    
    monotone-ext' :
     
      (f f' : MonFun A (𝕃 B)) ->
      (rel (arr' A (𝕃 B)) f f') ->
      ▹ (
        (la la' : ⟨ 𝕃 A ⟩) ->
         ord' A (next (ord A)) la la' ->
         ord' B (next (ord B))
          (ext' (MonFun.f f)  (next (ext (MonFun.f f)))  la)
          (ext' (MonFun.f f') (next (ext (MonFun.f f'))) la')) ->
     (la la' : ⟨ 𝕃 A ⟩) ->
       ord' A (next (ord A)) la la' ->
       ord' B (next (ord B))
        (ext' (MonFun.f f)  (next (ext (MonFun.f f)))  la)
        (ext' (MonFun.f f') (next (ext (MonFun.f f'))) la')
    monotone-ext' f f' f≤f' IH (η x) (η y) x≤y =
      transport
      (λ i → unfold-ord B i (MonFun.f f x) (MonFun.f f' y))
      (f≤f' x y x≤y)
    monotone-ext' f f' f≤f' IH ℧ la' la≤la' = tt
    monotone-ext' f f' f≤f' IH (θ lx~) (θ ly~) la≤la' = λ t ->
      transport
        (λ i → (sym (unfold-ord B)) i
          (sym (unfold-ext (MonFun.f f)) i (lx~ t))
          (sym (unfold-ext (MonFun.f f')) i (ly~ t)))
          --(ext (MonFun.f f) (lx~ t))
          --(ext (MonFun.f f') (ly~ t)))
        (IH t (lx~ t) (ly~ t)
          (transport (λ i -> unfold-ord A i (lx~ t) (ly~ t)) (la≤la' t)))
       --  (IH t (θ lx~) {!θ ly~!} la≤la')
-}
--  unfold-ord : ord ≡ ord' (next ord)



-- For the η case:
--  Goal:
--      ord' B (λ _ → fix (ord' B)) (MonFun.f f x) (MonFun.f f' y)

-- Know: (x₁ y₁ : fst A) →
--      rel A x₁ y₁ →
--      fix (ord' B) (MonFun.f f x₁) (MonFun.f f' y₁)


-- For the θ case:
-- Goal:
--  ord B
--      ext (MonFun.f f)) (lx~ t)
--      ext (MonFun.f f')) (ly~ t)

-- Know: IH : ...
-- la≤la'   : (t₁ : Tick k) → fix (ord' A) (lx~ t₁) (ly~ t₁)

-- The IH is in terms of ord' (i.e., ord' A (next (ord A)) la la')
-- but the assumption la ≤ la' in the θ case is equivalent to
-- (t₁ : Tick k) → fix (ord' A) (lx~ t₁) (ly~ t₁)


