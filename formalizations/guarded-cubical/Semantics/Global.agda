{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Later

module Semantics.Global where



open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_ ; _^_)
open import Cubical.Data.Nat.Order
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty.Base renaming (rec to exFalso)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Foundations.Function

open import Agda.Builtin.Equality renaming (_≡_ to _≣_) hiding (refl)
open import Agda.Builtin.Equality.Rewrite

import Semantics.StrongBisimulation
import Semantics.Monotone.Base
-- import Syntax.GradualSTLC

open import Common.Common
open import Semantics.Predomains
open import Semantics.Lift

-- TODO move definition of Predomain to a module that
-- isn't parameterized by a clock!

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ

-- Lift monad
open Semantics.StrongBisimulation
-- open StrongBisimulation.LiftPredomain

-- "Global" definitions
-- TODO in the general setting, X should have type Clock -> Type
-- and L℧F X should be equal to ∀ k -> L℧ k (X k)
L℧F : (X : Type ℓ) -> Type ℓ
L℧F X = ∀ (k : Clock) -> L℧ k X

□ : Type -> Type
□ X = ∀ (k : Clock) -> X

ηF : {X : Type} -> □ X -> L℧F X
ηF {X} x = λ k → η (x k)

℧F : {X : Type} -> L℧F X
℧F = λ k -> ℧

θF : {X : Type} -> L℧F X -> L℧F X
θF lx = λ k → θ (λ t → lx k)

δ-gl : {X : Type} -> L℧F X -> L℧F X
δ-gl lx = λ k → δ k (lx k)

δ-gl^n : {X : Type} (lxF : L℧F X) -> (n : Nat) -> (k : Clock) ->
      ((δ-gl) ^ n) lxF k ≡ ((δ k) ^ n) (lxF k)
δ-gl^n lxF zero k = refl
δ-gl^n lxF (suc n') k = cong (δ k) (δ-gl^n lxF n' k)



{- Iso definitions used in this file:

 _Iso⟨_⟩_  : {ℓ ℓ' ℓ'' : Level} {B : Type ℓ'} {C : Type ℓ''}
              (X : Type ℓ) →
              Iso X B → Iso B C → Iso X C
  _∎Iso     : {ℓ : Level} (A : Type ℓ) → Iso A A


   Σ-Π-Iso   : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : A → Type ℓ'}
              {C : (a : A) → B a → Type ℓ''} →
              Iso ((a : A) → Σ-syntax (B a) (C a))
                  (Σ-syntax ((a : A) → B a) (λ f → (a : A) → C a (f a)))

   codomainIsoDep
            : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : A → Type ℓ'}
              {C : A → Type ℓ''} →
              ((a : A) → Iso (B a) (C a)) → Iso ((a : A) → B a) ((a : A) → C a)

   ⊎Iso      : {A.ℓa : Level} {A : Type A.ℓa} {C.ℓc : Level}
              {C : Type C.ℓc} {B.ℓb : Level} {B : Type B.ℓb} {D.ℓd : Level}
              {D : Type D.ℓd} →
              Iso A C → Iso B D → Iso (A ⊎ B) (C ⊎ D)

  Σ-cong-iso-fst
            : {A.ℓ : Level} {A : Type A.ℓ} {B..1 : Level} {A' : Type B..1}
              {B.ℓ : Level} {B : A' → Type B.ℓ} (isom : Iso A A') →
              Iso (Σ A (B ∘ Iso.fun isom)) (Σ A' B)

  Σ-cong-iso-snd
            : {B'..1 : Level} {A : Type B'..1} {B.ℓ : Level} {B : A → Type B.ℓ}
              {B'.ℓ : Level} {B' : A → Type B'.ℓ} →
              ((x : A) → Iso (B x) (B' x)) → Iso (Σ A B) (Σ A B')

-}



Unit-clock-irrel : clock-irrel Unit
Unit-clock-irrel M k k' with M k | M k'
...  | tt | tt = refl

∀kL℧-▹-Iso : {X : Type} -> Iso
  ((k : Clock) -> ▹_,_ k (L℧ k X))
  ((k : Clock) -> L℧ k X) 
∀kL℧-▹-Iso = force-iso


bool2ty : Type ℓ -> Type ℓ -> Bool -> Type ℓ
bool2ty A B true = A
bool2ty A B false = B

bool2ty-eq : {X : Type ℓ} {A B : X -> Type ℓ'} ->
  (b : Bool) ->
  (∀ (x : X) -> bool2ty (A x) (B x) b) ≡
  bool2ty (∀ x -> A x) (∀ x -> B x) b
bool2ty-eq {X} {A} {B} true = refl
bool2ty-eq {X} {A} {B} false = refl



Iso-⊎-ΣBool : {A B : Type ℓ} -> Iso (A ⊎ B) (Σ Bool (λ b -> bool2ty A B b))
Iso-⊎-ΣBool {A = A} {B = B} = iso to inv sec retr
  where
    to : A ⊎ B → Σ Bool (λ b -> bool2ty A B b)
    to (inl a) = true , a
    to (inr b) = false , b

    inv : Σ Bool (bool2ty A B) → A ⊎ B
    inv (true , a) = inl a
    inv (false , b) = inr b

    sec : section to inv
    sec (true , a) = refl
    sec (false , b) = refl

    retr : retract to inv
    retr (inl a) = refl
    retr (inr b) = refl



∀clock-Σ : {A : Type} -> {B : A -> Clock -> Type} ->
    clock-irrel A ->
    (∀ (k : Clock) -> Σ A (λ a -> B a k)) ->
    Σ A (λ a -> ∀ (k : Clock) -> B a k)
∀clock-Σ {A} {B} H-clk-irrel p =
    let a = fst (p k0) in
      a , (λ k -> transport
                   (λ i → B (H-clk-irrel (fst ∘ p) k k0 i) k)
                   (snd (p k)))
  -- NTS:  B (fst (p k)) k ≡ B (fst (p k0)) k
  -- i.e. essentially need to show that fst (p k) ≡ fst (p k0)
  -- This follows from clock irrelevance for A, with M = fst ∘ p of type Clock -> A




MLTT-choice : {S : Type} -> {A : S -> Type} -> {B : (s : S) -> A s -> Type} ->
  Iso (∀ (s : S) -> (Σ[ x ∈ A s ] B s x))
      (Σ[ x ∈ (∀ s -> A s) ] ( ∀ s -> B s (x s) ))
MLTT-choice = Σ-Π-Iso

Eq-Iso : {A B : Type ℓ} ->
  A ≡ B -> Iso A B
Eq-Iso {A = A} {B = B} H-eq = subst (Iso A) H-eq idIso
-- same as: transport (cong (Iso A) H-eq) idIso



Iso-∀clock-Σ : {A : Type ℓ} -> {B : A -> Clock -> Type ℓ'} ->
  clock-irrel A ->
  Iso
    (∀ (k : Clock) -> Σ A (λ a -> B a k))
    (Σ A (λ a -> ∀ (k : Clock) -> B a k))
Iso-∀clock-Σ {A = A} {B = B} H-clk-irrel =
  (∀ (k : Clock) -> Σ A (λ a -> B a k))
     Iso⟨ Σ-Π-Iso {A = Clock} {B = λ _ -> A} {C = λ k a -> B a k} ⟩
     
  (Σ ((k : Clock) → A) (λ f → (k : Clock) → B (f k) k))
     Iso⟨ ( Σ-cong-iso-snd (λ f → codomainIsoDep (λ k → Eq-Iso (λ i → B (H-clk-irrel f k k0 i) k)))) ⟩

  (Σ ((k : Clock) → A) (λ f → (k : Clock) → B (f k0) k))
     Iso⟨ Σ-cong-iso-fst {B = λ a -> ∀ k' -> B a k'} (Iso-∀kA-A H-clk-irrel) ⟩
     
  (Σ A (λ a -> ∀ (k : Clock) -> B a k)) ∎Iso

-- Action of the above isomorphism
Iso-∀clock-Σ-fun : {A : Type ℓ} {B : A -> Clock -> Type ℓ'} ->
  (H : clock-irrel A) ->
  (f : (k : Clock) -> Σ A (λ a -> B a k)) ->
  Iso.fun (Iso-∀clock-Σ {A = A} {B = B} H) f ≡ (fst (f k0) , {!!})
Iso-∀clock-Σ-fun {A} {B} H f = {!!}

{- Note:
          Σ-cong-iso-fst
            : {A.ℓ : Level} {A : Type A.ℓ} {B..1 : Level} {A' : Type B..1}
              {B.ℓ : Level} {B : A' → Type B.ℓ} (isom : Iso A A') →
              Iso (Σ A (B ∘ Iso.fun isom)) (Σ A' B)

    In this case, the isomorphism function associated with Iso-∀kA-A
    takes f : (∀ (k : Clock) -> A) to A by applying f to k0.
    This is why we need the intermediate step of transforming B (f k) k
    into B (f k0) k.

-}



Iso-Π-⊎-clk : {A B : Clock -> Type ℓ} ->
  Iso
    ((k : Clock) -> (A k ⊎ B k))
    (((k : Clock) -> A k) ⊎ ((k : Clock) -> B k))
Iso-Π-⊎-clk {A = A} {B = B} =
  (∀ (k : Clock) -> (A k ⊎ B k))
    Iso⟨ codomainIsoDep (λ k -> Iso-⊎-ΣBool) ⟩
  (∀ (k : Clock) -> Σ[ b ∈ Bool ] bool2ty (A k) (B k) b )
    Iso⟨ Iso-∀clock-Σ bool-clock-irrel ⟩
  (Σ[ b ∈ Bool ] ∀ k -> bool2ty (A k) (B k) b)
    Iso⟨ Σ-cong-iso-snd (λ b → Eq-Iso (bool2ty-eq b)) ⟩
    --  (cong (Iso ((x : Clock) → bool2ty (A x) (B x) b)) (bool2ty-eq b))
  (Σ[ b ∈ Bool ] bool2ty (∀ k -> A k) (∀ k -> B k) b)
    Iso⟨ invIso Iso-⊎-ΣBool ⟩
  (∀ k -> A k) ⊎ (∀ k -> B k) ∎Iso

-- Action of the above isomorphism
Iso-Π-⊎-clk-fun : {A B : Clock -> Type} -> {f : (k : Clock) -> (A k ⊎ B k) } ->
  Iso.fun Iso-Π-⊎-clk f ≡ {!!}
Iso-Π-⊎-clk-fun {A} {B} {f} = {!!}






L℧F-iso : {X : Type} -> Iso (L℧F X) (((□ X) ⊎ ⊤) ⊎ (L℧F X))
L℧F-iso {X} =
  (∀ k -> L℧ k X)

          Iso⟨ codomainIsoDep (λ k -> L℧-iso k ) ⟩
  
  (∀ k -> (X ⊎ ⊤) ⊎ (▹_,_ k (L℧ k X)))

          Iso⟨ Iso-Π-⊎-clk ⟩

  (∀ (k : Clock) -> (X ⊎ ⊤)) ⊎ (∀ k -> ▹_,_ k (L℧ k X))
 
          Iso⟨ ⊎Iso Iso-Π-⊎-clk idIso ⟩
  
  ((∀ (k : Clock) -> X) ⊎ (∀ (k : Clock) -> ⊤)) ⊎
       (∀ k -> ▹_,_ k (L℧ k X))
       
          Iso⟨ ⊎Iso
                (⊎Iso idIso (Iso-∀kA-A Unit-clock-irrel))
                force-iso ⟩
                    
  ((□ X) ⊎ ⊤) ⊎ (L℧F X) ∎Iso

-- Characterizing the behavior of the isomorphism on specific inputs.
rule-tru : {k k' : Clock} -> {i : I} ->
  bool-clock-irrel (λ x → true) k k' i ≣ true
rule-tru = {!!}

rule-fls : {k k' : Clock} -> {i : I} ->
  bool-clock-irrel (λ x → false) k k' i ≣ false
rule-fls = {!!}

{-# REWRITE rule-tru rule-fls #-}





lem-iso : {A B : Type} -> (iAB : Iso A B) -> (a : A) -> (b : B) ->
  Iso.fun iAB a ≡ b -> Iso.inv iAB b ≡ a
lem-iso iAB a b H =
  Iso.inv iAB b                ≡⟨ sym (λ i -> Iso.inv iAB (H i) ) ⟩
  Iso.inv iAB (Iso.fun iAB a)  ≡⟨ Iso.leftInv iAB a ⟩
  a ∎

L℧F-iso-η : {X : Type} -> (x : □ X) ->
  Iso.fun L℧F-iso (ηF x) ≡ (inl (inl x))
L℧F-iso-η x = cong inl (cong inl (clock-ext (λ k -> {!!})))

L℧F-iso-℧ : {X : Type} ->
  Iso.fun (L℧F-iso {X}) ℧F ≡ inl (inr tt)
L℧F-iso-℧ = cong inl refl

L℧F-iso-θ : {X : Type} -> (l : L℧F X) ->
  Iso.fun (L℧F-iso {X}) (λ k -> θ (next (l k))) ≡ inr l
L℧F-iso-θ l = cong inr (clock-ext (λ k -> {!!}))

L℧F-iso-η-inv : {X : Type} ->
  (l : L℧F X) -> (x : □ X) -> Iso.fun L℧F-iso l ≡ (inl (inl x)) ->
  l ≡ (ηF x)
L℧F-iso-η-inv l x H = isoFunInjective L℧F-iso l (ηF x)
  (Iso.fun L℧F-iso l ≡⟨ H ⟩
  inl (inl x)        ≡⟨ sym (L℧F-iso-η x) ⟩
  Iso.fun L℧F-iso (ηF x) ∎)




-- In the special case where X is clock-irrelevant, we can simplify the
-- above isomorphism further by replacing □ X with X.
L℧F-iso-irrel : {X : Type} -> clock-irrel X -> Iso (L℧F X) ((X ⊎ ⊤) ⊎ (L℧F X))
L℧F-iso-irrel {X} H-irrel =
  L℧F X                     Iso⟨ L℧F-iso ⟩
  ((□ X) ⊎ ⊤) ⊎ (L℧F X)     Iso⟨ ⊎Iso (⊎Iso (Iso-∀kA-A H-irrel) idIso) idIso ⟩
  (X ⊎ ⊤) ⊎ (L℧F X) ∎Iso


unfold-L℧F : {X : Type} -> clock-irrel X -> (L℧F X) ≡ ((X ⊎ ⊤) ⊎ (L℧F X))
unfold-L℧F H = ua (isoToEquiv (L℧F-iso-irrel H))
