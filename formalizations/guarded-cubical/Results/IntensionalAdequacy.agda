{-# OPTIONS --cubical --rewriting --guarded #-}
{-# OPTIONS --guardedness #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Later


module Results.IntensionalAdequacy where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_ ; _^_)
open import Cubical.Data.Nat.Order
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty.Base renaming (rec to exFalso)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Foundations.Function

import Semantics.StrongBisimulation
import Semantics.Monotone.Base
import Syntax.GradualSTLC

open import Common.Common
open import Semantics.Predomains
open import Semantics.Lift

-- TODO move definition of Predomain to a module that
-- isn't parameterized by a clock!

private
  variable
    l : Level
    X : Type l

-- Lift monad
open Semantics.StrongBisimulation
-- open StrongBisimulation.LiftPredomain


-- "Global" definitions
L℧F : (X : Type) -> Type
L℧F X = ∀ (k : Clock) -> L℧ k X

ηF : {X : Type} -> X -> L℧F X
ηF {X} x = λ k → η x

℧F : {X : Type} -> L℧F X
℧F = λ k -> ℧

θF : {X : Type} -> L℧F X -> L℧F X
θF lx = λ k → θ (λ t → lx k)

δ-gl : {X : Type} -> L℧F X -> L℧F X
δ-gl lx = λ k → δ k (lx k)

δ-gl^n : (lxF : L℧F Nat) -> (n : Nat) -> (k : Clock) ->
      ((δ-gl) ^ n) lxF k ≡ ((δ k) ^ n) (lxF k)
δ-gl^n lxF zero k = refl
δ-gl^n lxF (suc n') k = cong (δ k) (δ-gl^n lxF n' k)


{-
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
-}

Unit-clock-irrel : clock-irrel Unit
Unit-clock-irrel M k k' with M k | M k'
...  | tt | tt = refl

∀kL℧-▹-Iso : {X : Type} -> Iso ((k : Clock) -> ▹_,_ k (L℧ k X)) ((k : Clock) -> L℧ k X) 
∀kL℧-▹-Iso = force-iso

∀clock-Σ : {A : Type} -> {B : A -> Clock -> Type} ->
    -- (∀ a k -> clock-irrel (B a k)) ->
    clock-irrel A ->
    (∀ (k : Clock) -> Σ A (λ a -> B a k)) ->
    Σ A (λ a -> ∀ (k : Clock) -> B a k)
∀clock-Σ {A} {B} H-clk-irrel H =
    let a = fst (H k0) in
      a , (λ k -> transport
                   (λ i → B (H-clk-irrel (fst ∘ H) k k0 i) k)
                   (snd (H k)))
  -- NTS:  B (fst (H k)) k ≡ B (fst (H k0)) k
  -- i.e. essentially need to show that fst (H k) ≡ fst (H k0)
  -- This follows from clock irrelevance for A, with M = fst ∘ H of type Clock -> A



Iso-Π-⊎ : {A B : Clock -> Type} ->
  Iso ((k : Clock) -> (A k ⊎ B k)) (((k : Clock) -> A k) ⊎ ((k : Clock) -> B k))
Iso-Π-⊎ {A} {B} = iso to inv sec retr
  where
    to : ((k : Clock) → A k ⊎ B k) → ((k : Clock) → A k) ⊎ ((k : Clock) → B k)
    to f with f k0
    ... | inl a = inl (λ k → transport (type-clock-irrel A k0 k) a)
    ... | inr b = inr (λ k → transport (type-clock-irrel B k0 k) b)

    inv : ((k : Clock) → A k) ⊎ ((k : Clock) → B k) -> ((k : Clock) → A k ⊎ B k)
    inv (inl f) k = inl (f k)
    inv (inr f) k = inr (f k)

    sec : section to inv
    sec (inl f) = cong inl (clock-ext λ k -> {!!})
    sec (inr f) = cong inr (clock-ext (λ k -> {!!}))

    retr : retract to inv
    retr f with (f k0)
    ... | inl a = clock-ext (λ k → {!!})
    ... | inr b = {!!}

  {-
  transport-filler
            : {ℓ : Level} {A B : Type ℓ} (p : A ≡ B) (x : A) →
              PathP (λ i → p i) x (transport p x)
  -}              

L℧-iso : {k : Clock} -> {X : Type} -> Iso (L℧ k X) ((X ⊎ ⊤) ⊎ (▹_,_ k (L℧ k X)))
L℧-iso {k} {X} = iso f g sec retr
  where
    f : L℧ k X → (X ⊎ ⊤) ⊎ (▹ k , L℧ k X)
    f (η x) = inl (inl x)
    f ℧ = inl (inr tt)
    f (θ lx~) = inr lx~

    g : (X ⊎ ⊤) ⊎ (▹ k , L℧ k X) -> L℧ k X
    g (inl (inl x)) = η x
    g (inl (inr tt)) = ℧
    g (inr lx~) = θ lx~

    sec : section f g
    sec (inl (inl x)) = refl
    sec (inl (inr tt)) = refl
    sec (inr lx~) = refl

    retr : retract f g
    retr (η x) = refl
    retr ℧ = refl
    retr (θ x) = refl


L℧F-iso : {X : Type} -> clock-irrel X -> Iso (L℧F X) ((X ⊎ ⊤) ⊎ (L℧F X))
L℧F-iso {X} H-irrel-X =
  (∀ k -> L℧ k X)

          Iso⟨ codomainIsoDep (λ k -> L℧-iso) ⟩
  
  (∀ k -> (X ⊎ ⊤) ⊎ (▹_,_ k (L℧ k X)))

          Iso⟨ Iso-Π-⊎ ⟩

  (∀ (k : Clock) -> (X ⊎ ⊤)) ⊎ (∀ k -> ▹_,_ k (L℧ k X))

          Iso⟨ ⊎Iso Iso-Π-⊎ idIso ⟩
  
  ((∀ (k : Clock) -> X) ⊎ (∀ (k : Clock) -> ⊤)) ⊎
       (∀ k -> ▹_,_ k (L℧ k X))
       
          Iso⟨ ⊎Iso (⊎Iso (Iso-∀kA-A H-irrel-X) (Iso-∀kA-A Unit-clock-irrel)) force-iso ⟩
                    
  (X ⊎ ⊤) ⊎ (L℧F X) ∎Iso


unfold-L℧F : {X : Type} -> clock-irrel X -> (L℧F X) ≡ ((X ⊎ ⊤) ⊎ (L℧F X))
unfold-L℧F H = ua (isoToEquiv (L℧F-iso H))

   

-- Adequacy of lock-step relation
module AdequacyLockstep

  where

  open Semantics.StrongBisimulation
  open Semantics.StrongBisimulation.LiftPredomain

  _≾-gl_ : {p : Predomain} -> (L℧F ⟨ p ⟩) -> (L℧F ⟨ p ⟩) -> Type
  _≾-gl_ {p} lx ly = ∀ (k : Clock) -> _≾_ k p (lx k) (ly k)

  -- _≾'_ : {k : Clock} -> L℧ k Nat → L℧ k Nat → Type
  -- _≾'_ {k} = {!!}


  -- These should probably be moved to the module where _≾'_ is defined.
  ≾'-℧ : {k : Clock} -> (lx : L℧ k Nat) ->
    _≾'_ k (ℕ k0) lx ℧ -> lx ≡ ℧
  ≾'-℧ (η x) ()
  ≾'-℧ ℧ _ = refl
  ≾'-℧ (θ x) ()

  ≾'-θ : {k : Clock} -> (lx : L℧ k Nat) -> (ly~ : ▹_,_ k (L℧ k Nat)) ->
    _≾'_ k (ℕ k0) lx (θ ly~) ->
    Σ (▹_,_ k (L℧ k Nat)) (λ lx~ -> lx ≡ θ lx~)
  ≾'-θ (θ lz~) ly~ H = lz~ , refl
  ≾'-θ ℧ ly~ x = {!!}


  L℧F-▹alg : ((k : Clock) -> ▹_,_ k (L℧ k Nat)) -> L℧F Nat
  L℧F-▹alg = λ lx~ → λ k → θ (lx~ k)

  L℧F-▹alg' : ((k : Clock) -> ▹_,_ k (L℧ k Nat)) -> L℧F Nat
  L℧F-▹alg' = λ lx~ → λ k → θ (λ t → lx~ k t)


  helper : {X : Type} -> {k : Clock} -> (M~ : ▹_,_ k X) ->
    next (M~ ◇) ≡ M~
  helper M~ = next-Mt≡M M~ ◇


  adequate-err' :
    (m : Nat) ->
    (lxF : L℧F Nat) ->
    (H-lx : _≾-gl_ {ℕ k0} lxF ((δ-gl ^ m) ℧F)) ->
    (Σ (Nat) λ n -> (n ≤ m) × ((lxF ≡ (δ-gl ^ n) ℧F)))
  adequate-err' zero lxF H-lx with (Iso.fun (L℧F-iso nat-clock-irrel) lxF)
  ... | inl (inl x) = zero , {!!}
  ... | _ = {!!}
  adequate-err' (suc m) = {!!}

  adequate-err :
    (m : Nat) ->
    (lxF : L℧F Nat) ->
    (H-lx : _≾-gl_ {ℕ k0} lxF ((δ-gl ^ m) ℧F)) ->
    (Σ (Nat) λ n -> (n ≤ m) × ((lxF ≡ (δ-gl ^ n) ℧F)))
  adequate-err zero lxF H-lxF =
    let H' = transport (λ i -> ∀ k -> unfold-≾ k (ℕ k0) i (lxF k) (℧F k)) H-lxF in
        zero , ≤-refl , clock-ext λ k → ≾'-℧ (lxF k) (H' k)
           -- H' says that for all k, (lxF k) ≾' (℧F k) i.e.
           -- for all k, (lxF k) ≾' ℧, which means, by definition of ≾',
           -- for all k, (lxF k) = ℧, which means, by clock extensionality,
           -- that lxF = ℧F.
  adequate-err (suc m') lxF H-lxF =
    let IH = adequate-err m' (λ k → fst (fst (aux k)) ◇) (λ k → snd (aux k))
    in {!!}
      where
        aux : (k : Clock) -> (Σ (▹ k , L℧ k Nat) (λ lx~ → lxF k ≡ θ lx~)) × _
        aux k =  let RHS = (((δ-gl ^ m') ℧F) k) in
                 let RHS' = (δ k RHS) in
                 let H1 = transport (λ i -> unfold-≾ k (ℕ k0) i (lxF k) RHS') (H-lxF k) in
                 let pair = ≾'-θ (lxF k) (next RHS) H1 in 
                 let H2 = transport (λ i → _≾'_ k (ℕ k0) (snd pair i) RHS') H1 in
                 let H3 = transport ((λ i -> (t : Tick k) -> _≾_ k (ℕ k0) (tick-irrelevance (fst pair) t ◇ i) RHS)) H2 in
                 pair , (H3 ◇)
       


    {-
    let H' = transport
               (λ i -> ∀ k -> unfold-≾ k (ℕ k0) i (lxF k) ((δ-gl ((δ-gl ^ n) ℧F)) k)) H-lxF in
    let H'' = transport (λ i -> ∀ k -> _≾'_ k (ℕ k0) (snd (≾'-θ (lxF k) (next ((δ-gl ^ n) ℧F k)) (H' k)) i) (δ k (((δ-gl ^ n) ℧F) k)) ) H' in
               
    let IH = adequate-err n lxF {!!} in {!!}
    -}
      -- H-lxF says that lx ≾-gl (δ-gl ((δ-gl ^ n) ℧F))
      -- H' says that for all k, (lxF k) ≾' (δ-gl ((δ-gl ^ n) ℧F)) k
      -- i.e. for all k, (lxF k) ≾' δ k (((δ-gl ^ n) ℧F) k)
      -- By inversion on ≾', this means that
      -- for all k, there exists lx~ : ▹k (L℧ k Nat)
      -- such that (lxF k) ≡ θ lx~, and
      -- ▸k ( λ t -> lx~ t ≾ (next (((δ-gl ^ n) ℧F) k)) t )
      -- ▸k ( λ t -> lx~ t ≾ (((δ-gl ^ n) ℧F) k) )






module AdequacyBisim where

  open Semantics.StrongBisimulation
  open Semantics.StrongBisimulation.Bisimilarity
  open Inductive
  open Bisimilarity.Properties


  -- Some properties of the global bisimilarity relation
  module GlobalBisim (p : Predomain) where

    _≈-gl_ : (L℧F ⟨ p ⟩) -> (L℧F ⟨ p ⟩) -> Type
    _≈-gl_ lx ly = ∀ (k : Clock) -> _≈_ k p (lx k) (ly k)
  
    ≈-gl-δ-elim : (lx ly : L℧F ⟨ p ⟩) ->
      _≈-gl_ (δ-gl lx) (δ-gl ly) ->
      _≈-gl_ lx ly
    ≈-gl-δ-elim lx ly H = force' H'
      where
        H' : ∀ k -> ▹_,_ k (_≈_ k p (lx k) (ly k))
        H' = transport (λ i → ∀ k -> unfold-≈ k p i (δ k (lx k)) (δ k (ly k))) H
   -- H  :   (δ-gl lx) ≈-gl (δ-gl ly)
   -- i.e.   ∀ k . (δ k (lx k)) ≈ (δ k (ly k))
   -- i.e.   ∀ k . (δ k (lx k)) ≈' (δ k (ly k))
   -- i.e.   ∀ k . ▸ (λ t -> (next (lx k) t) ≈ (next (ly k) t))
   -- i.e.   ∀ k . ▸ (λ t -> (lx k) ≈ (ly k))
   -- i.e.   ∀ k . ▹ ((lx k) ≈ (ly k))
   -- By force we then have: ∀ k . lx k ≈ ly k
   
   

    ≈-gl-δ : (lx ly : L℧F ⟨ p ⟩) ->
      _≈-gl_ (δ-gl lx) ly -> _≈-gl_ lx ly
    ≈-gl-δ lx ly H = {!!}
      where
        H' : {!!}
        H' = {!!}
    

  open GlobalBisim (ℕ k0)




  adequate-err :
    (m : Nat) ->
    (lxF : L℧F Nat) ->
    (H-lx : _≈-gl_ lxF ((δ-gl ^ m) ℧F)) ->
    (Σ (Nat) λ n -> ((lxF ≡ (δ-gl ^ n) ℧F)))
  adequate-err zero lxF H-lx = (fst H3) , clock-ext (snd H4)
    where
      H1 : (k : Clock) -> _≈'_ k (ℕ k0) (next (_≈_ k (ℕ k0))) (lxF k) (℧F k)
      H1 = transport (λ i → ∀ k -> unfold-≈ k (ℕ k0) i (lxF k) (℧F k)) H-lx

      H2 : (k : Clock) -> Σ Nat (λ n → lxF k ≡ (δ k ^ n) ℧)
      H2 k = ≈-℧ k (ℕ k0) (lxF k) (H1 k)

      H3 : Σ Nat (λ n -> ∀ (k : Clock) -> lxF k ≡ (δ k ^ n) ℧)
      H3 = ∀clock-Σ nat-clock-irrel H2

      --δ-gl^n : (lxF : L℧F Nat) -> (n : Nat) -> (k : Clock) ->
      --  ((δ-gl) ^ n) lxF k ≡ ((δ k) ^ n) (lxF k)

      H4 : Σ Nat (λ n -> ∀ (k : Clock) -> lxF k ≡ (δ-gl ^ n) ℧F k)
      H4 = (fst H3) , (λ k → lxF k ≡⟨ snd H3 k ⟩ (sym (δ-gl^n ℧F (fst H3) k)))
     -- NTS: lxF k ≡ (δ-gl ^ fst H3) ℧F k
     
  adequate-err (suc m') lxF H-lx = {!!}

