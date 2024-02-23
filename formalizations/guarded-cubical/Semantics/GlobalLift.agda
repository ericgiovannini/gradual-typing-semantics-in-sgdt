{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.GlobalLift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_ ; _^_)
open import Cubical.Data.Empty.Base renaming (rec to exFalso)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Nat
open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.List as List

open import Agda.Builtin.Equality renaming (_≡_ to _≣_) hiding (refl)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion hiding (Iso ; funExt)

open import Common.Later
open import Common.Common
open import Common.ClockProperties
open import Semantics.Lift

private
  variable
    ℓ ℓ' : Level


-- Definition of global Lift.
L^gl : (X : Type ℓ) -> Type ℓ
L^gl X = ∀ (k : Clock) -> L k X


-- Global η
ηL^gl : {X : Type ℓ} → X → L^gl X
ηL^gl x = (λ k → η x)

-- Global δ
δL^gl : {X : Type ℓ} -> L^gl X -> L^gl X
δL^gl l = λ k -> δL k (l k)

delay-n : {X : Type ℓ} → L^gl X → ℕ → L^gl X
delay-n l zero = l
delay-n l (suc n) = δL^gl (delay-n l n)


-- Global Lift satisfies an "unfolding" equation.
L^gl-iso : {X : Type ℓ} ->
  clock-irrel X ->
  Iso (L^gl X) ((X ⊎ (L^gl X)))
L^gl-iso {X = X} H-irrel =
  (∀ k -> L k X)
    Iso⟨ codomainIsoDep (λ k -> Iso-L k) ⟩
  (∀ k -> (X ⊎ (▹ k , L k X)))
    Iso⟨ Iso-Π-⊎-clk ⟩
  ((∀ (k : Clock) -> X) ⊎ (∀ k -> ▹ k , L k X))
    Iso⟨ ⊎Iso ((Iso-∀kA-A H-irrel)) force-iso ⟩
  X ⊎ L^gl X ∎Iso


-- Describing the behavior of the above isomorphism:



-- Rewriting axioms used in the proofs:


{-# REWRITE rewrite-transp #-}




iso-inv-inl : {X : Type ℓ} (H : clock-irrel X) (x : X) ->
  Iso.inv (L^gl-iso H) (inl x) ≡ λ k -> η x
iso-inv-inl H x = refl


-- The below statement, which is equivalent to the above one, is provable if
-- we have that rewrite-clock-irrel-bool-2 is true, hence the rewrite above.
-- We could prove this without the automatic rewrite, but then we would need
-- to do the rewriting manually in the proof.
iso-fun-η : {X : Type ℓ} (H : clock-irrel X) (x : X) ->
  Iso.fun (L^gl-iso H) (λ k -> η x) ≡ inl x
iso-fun-η {X = X} H x =
  congS inl (transportRefl _ ∙ transportRefl _ ∙ lem)
  where
    lem-transp : (transp (λ j → Clock) i0 (transp (λ j → Clock) i0 k0)) ≡ k0
    lem-transp = transportRefl _ ∙ transportRefl _
   
    lem : _
    lem = (λ i -> transp (λ j -> bool2ty X (▹ lem-transp i , L (lem-transp i) X) (bool-clock-irrel (λ _ -> true) (lem-transp i) k0 j)) i0 (transportRefl x i)) ∙
          transportRefl x


iso-fun-θ : {X : Type ℓ} (H : clock-irrel X) (l : L^gl X) ->
  Iso.fun (L^gl-iso H) (δL^gl l) ≡ inr l
iso-fun-θ {X = X} H l = congS inr lem
  where
    var : _
    var = (λ k → transp
            (λ j → bool2ty X (Tick k → L k X) (bool-clock-irrel (λ x → false) k k0 j))
            i0
            (transp (λ j → Tick k → L k X) i0 (λ _ → l k)))

    transpVar : _
    transpVar = (transp (λ j → (k : Clock) → Tick k → L k X) i0 var)

    lem :
      force' (transp (λ i → (x : Clock) → Tick x → L x X) i0 transpVar) ≡ l
    lem = (λ i -> force' (transportRefl transpVar i)) ∙
          (λ i -> force' (transportRefl var i)) ∙
          (λ i -> force' (λ k -> transp (λ j -> bool2ty X (▹ k , L k X) (path-clock-irrel-bool-1 {k = k} {k' = k0} false i j)) i0 (transportRefl (next (l k)) i))) ∙
          (λ i -> force' (λ k -> transportRefl (next (l k)) i)) ∙
          force'-beta l

{-
    lem = (λ i -> force' (transportRefl transpVar i)) ∙
          (λ i -> force'
            (transportRefl (λ k -> transp
                                     (λ j -> bool2ty X (▹ k , L k X) (bool-clock-irrel (λ _ -> false) k k0 j))
                                     i0 (transportRefl (λ _ -> l k) i))
                           i)) ∙
          (λ i -> force' (λ k -> transp (λ j -> bool2ty X (▹ k , L k X) (path-clock-irrel-bool-1 {k = k} {k' = k0} false i j)) i0 (next (l k)))) ∙
          (λ i -> force' (λ k -> transportRefl (next (l k)) i)) ∙
          force'-beta l
-}


{-
force'
      (λ k →
         transp
         (λ i' →
            bool2ty X (▹ k , L k X) (bool-clock-irrel (λ _ → false) k k0 i'))
         i0 (λ _ → l k))
      ≡ force' (λ k → next (l k))

-}


{-
force'
      (transp (λ i → (x : Clock) → Tick x → L x X) i0
       (transp (λ j → (k : Clock) → Tick k → L k X) i0
        (λ a →
           transp
           (λ i →
              bool2ty X (Tick a → L a X) (bool-clock-irrel (λ x → false) a k0 i))
           i0 (transp (λ j → Tick a → L a X) i0 (λ _ → l a)))))
      ≡ l

-}

iso-fun-eq-inl : {X : Type ℓ} (H : clock-irrel X) (l : L^gl X) (x : X) ->
  Iso.fun (L^gl-iso H) l ≡ inl x ->
  l ≡ (λ k -> η x)
iso-fun-eq-inl H l x eq =
  isoFunInjective (L^gl-iso H) l (λ k → η x) (eq ∙ sym (iso-fun-η H x))

iso-fun-eq-inr : {X : Type ℓ} (H : clock-irrel X) (l l' : L^gl X) ->
  Iso.fun (L^gl-iso H) l ≡ inr l' ->
  l ≡ δL^gl l'
iso-fun-eq-inr H l l' eq =
  isoFunInjective (L^gl-iso H) l (δL^gl l') (eq ∙ sym (iso-fun-θ H l'))


-- Converting a global lift to a function on ℕ defined at most once
module _ {X : Type ℓ} (H : clock-irrel X) where

  toFun : L^gl X -> ℕ -> X ⊎ ⊤
  toFun l n with Iso.fun (L^gl-iso H) l
  toFun l zero    | inl x  = inl x
  toFun l (suc n) | inl l' = inr tt
  toFun l zero    | inr x  = inr tt
  toFun l (suc n) | inr l' = toFun l' n
  -- Using a fold over an inductive type where
  -- the observed value is coinductive


  fromFun'' : (k : Clock) ->
    (▹ k , ((ℕ -> X ⊎ ⊤) -> L k X)) ->
           ((ℕ -> X ⊎ ⊤) -> L k X)
  fromFun'' k rec f with f zero
  ... | inl x = η x
  ... | inr tt = θ (λ t -> rec t (f ∘ suc))

  fromFun' : (k : Clock) -> (ℕ -> X ⊎ ⊤) -> L k X
  fromFun' k = fix (fromFun'' k)

  fromFun : (ℕ -> X ⊎ ⊤) -> L^gl X
  fromFun f k  = fromFun' k f

  unfold-ff' : ∀ f k -> fromFun' k f ≡ fromFun'' k (next (fromFun' k)) f
  unfold-ff' f k = λ i -> fix-eq (fromFun'' k) i f

  ff''→ff' : ∀ f k z -> fromFun'' k (next (fromFun' k)) f ≡ z -> fromFun' k f ≡ z
  ff''→ff' f k z H = unfold-ff' f k ∙ H

  -- We need to make the L^gl value part of the inductive hypothesis.
  -- This may seem odd, since it's a global value and hence we don't
  -- pass a tick to it.
  lemma : (k : Clock) ->
    (▹ k , ((l : L^gl X) -> fromFun'' k (next (fromFun' k)) (toFun l) ≡ l k)) ->
            (l : L^gl X) -> fromFun'' k (next (fromFun' k)) (toFun l) ≡ l k
  lemma k IH l with Iso.fun (L^gl-iso H) l in eq
  ... | inl x = sym (funExt⁻ lem k)
    where
      lem : l ≡ λ k -> η x
      lem = iso-fun-eq-inl H l x (eqToPath eq)

  ... | inr l' = (λ i -> θ (λ t -> ff''→ff' _ k (l' k) (IH t l') i)) ∙ sym (funExt⁻ lem k)     
    where
      lem : l ≡ δL^gl l'
      lem = iso-fun-eq-inr H l l' (eqToPath eq)
   --
   -- Explanation of proof for the inr case:
   -- 
   -- NTS:
   -- θ_t (fromFun' k (toFun l')) ≡ l k
   --
   -- Know:
   -- (1) l ≡ δL^gl l'
   -- (2) IH : ▸_t (∀ (l'' : L^gl X) -> ff'' k (next (ff' k)) (toFun l'') ≡ l'' k)
   --
   -- We have
   --
   --    θ_t (fromFun' k (toFun l'))
   --  = θ_t (ff'' k (next (ff' k)) (toFun l'))  [ by lemma relating ff' and ff'' ]
   --  = θ_t (l' k)    [ by IH ]
   --  = δL (l' k)     [ by defn ]
   --  = (δ^gl l') k   [ by defn ]
   --  = l k           [ by (1) ]
   --
  

{-

 θ
      (λ t →
         fix (λ rec₁ f → fromFun'' H k rec₁ f | f 0) (λ x → toFun l' x))
      ≡ δL^gl l' k

-}


module Test where

  -- The global lift element that delays for two steps and then returns 50.
  lift1 : L^gl ℕ
  lift1 = delay-n (ηL^gl 50) 2 -- i.e.  δL^gl (δL^gl (ηL^gl 50))

  fun1 : ℕ → ℕ ⊎ ⊤
  fun1 = toFun nat-clock-irrel lift1

  _ : fun1 0 ≡ inr tt
  _ = refl

  _ : fun1 2 ≡ inl 50
  _ = refl

  fun1-0 : ℕ ⊎ ⊤
  fun1-0 = fun1 0

  fun1-1 : ℕ ⊎ ⊤
  fun1-1 = fun1 1

  test-1 : List (ℕ ⊎ ⊤)
  test-1 = List.map fun1 (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
  

open Test

