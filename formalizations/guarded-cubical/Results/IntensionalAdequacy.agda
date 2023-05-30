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
open import Semantics.Global


-- TODO move definition of Predomain to a module that
-- isn't parameterized by a clock!

private
  variable
    l : Level
    X : Type l

-- Lift monad
open Semantics.StrongBisimulation
-- open StrongBisimulation.LiftPredomain

   

-- Adequacy of lock-step relation
module AdequacyLockstep

  where

  open Semantics.StrongBisimulation
  open Semantics.StrongBisimulation.LiftPredomain

  _≾-gl_ : {p : Predomain} -> (L℧F ⟨ p ⟩) -> (L℧F ⟨ p ⟩) -> Type
  _≾-gl_ {p} lx ly = ∀ (k : Clock) -> _≾_ k p (lx k) (ly k)

  -- These should probably be moved to the module where _≾'_ is defined.
  ≾'-℧ : {k : Clock} -> (lx : L℧ k Nat) ->
    _≾'_ k ℕ lx ℧ -> lx ≡ ℧
  ≾'-℧ (η x) ()
  ≾'-℧ ℧ _ = refl
  ≾'-℧ (θ x) ()

  ≾'-θ : {k : Clock} -> (lx : L℧ k Nat) -> (ly~ : ▹_,_ k (L℧ k Nat)) ->
    _≾'_ k ℕ lx (θ ly~) ->
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
    (H-lx : _≾-gl_ {ℕ} lxF ((δ-gl ^ m) ℧F)) ->
    (Σ (Nat) λ n -> (n ≤ m) × ((lxF ≡ (δ-gl ^ n) ℧F)))
  adequate-err' zero lxF H-lx with (Iso.fun (L℧F-iso-irrel nat-clock-irrel) lxF)
  ... | inl (inl x) = zero , {!!}
  ... | _ = {!!}
  adequate-err' (suc m) = {!!}

  adequate-err :
    (m : Nat) ->
    (lxF : L℧F Nat) ->
    (H-lx : _≾-gl_ {ℕ} lxF ((δ-gl ^ m) ℧F)) ->
    (Σ (Nat) λ n -> (n ≤ m) × ((lxF ≡ (δ-gl ^ n) ℧F)))
  adequate-err zero lxF H-lxF =
    let H' = transport (λ i -> ∀ k -> unfold-≾ k (ℕ) i (lxF k) (℧F k)) H-lxF in
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
                 let H1 = transport (λ i -> unfold-≾ k (ℕ) i (lxF k) RHS') (H-lxF k) in
                 let pair = ≾'-θ (lxF k) (next RHS) H1 in 
                 let H2 = transport (λ i → _≾'_ k (ℕ) (snd pair i) RHS') H1 in
                 let H3 = transport ((λ i -> (t : Tick k) -> _≾_ k (ℕ) (tick-irrelevance (fst pair) t ◇ i) RHS)) H2 in
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
    

  open GlobalBisim (ℕ)




  adequate-err :
    (m : Nat) ->
    (lxF : L℧F Nat) ->
    (H-lx : _≈-gl_ lxF ((δ-gl ^ m) ℧F)) ->
    (Σ (Nat) λ n -> ((lxF ≡ (δ-gl ^ n) ℧F)))
  adequate-err zero lxF H-lx = (fst H3) , clock-ext (snd H4)
    where
      H1 : (k : Clock) -> _≈'_ k (ℕ) (next (_≈_ k (ℕ))) (lxF k) (℧F k)
      H1 = transport (λ i → ∀ k -> unfold-≈ k (ℕ) i (lxF k) (℧F k)) H-lx

      H2 : (k : Clock) -> Σ Nat (λ n → lxF k ≡ (δ k ^ n) ℧)
      H2 k = ≈-℧ k (ℕ) (lxF k) (H1 k)

      H3 : Σ Nat (λ n -> ∀ (k : Clock) -> lxF k ≡ (δ k ^ n) ℧)
      H3 = ∀clock-Σ nat-clock-irrel H2

      --δ-gl^n : (lxF : L℧F Nat) -> (n : Nat) -> (k : Clock) ->
      --  ((δ-gl) ^ n) lxF k ≡ ((δ k) ^ n) (lxF k)

      H4 : Σ Nat (λ n -> ∀ (k : Clock) -> lxF k ≡ (δ-gl ^ n) ℧F k)
      H4 = (fst H3) , (λ k → lxF k ≡⟨ snd H3 k ⟩ (sym (δ-gl^n ℧F (fst H3) k)))
     -- NTS: lxF k ≡ (δ-gl ^ fst H3) ℧F k
     
  adequate-err (suc m') lxF H-lx = {!!}



module DynExp where

  open import Semantics.SemanticsNew
  open import Semantics.PredomainInternalHom
  open import Semantics.StrongBisimulation
  open LiftPredomain
  open import Semantics.Monotone.Base
  open import Semantics.Monotone.MonFunCombinators
  open import Cubical.Relation.Binary.Poset
  open import Semantics.Predomains


  DynUnfold : Iso
    (∀ k -> ⟨ DynP k ⟩)
    (Nat ⊎ (∀ k -> ⟨ DynP k ==> 𝕃 k (DynP k) ⟩))
  DynUnfold = {!!}


  dyn-clk : (k k' : Clock) -> ⟨ DynP k ==> DynP k' ⟩
  dyn-clk = {!!}


  𝔽𝕃 : (Clock -> Predomain) -> Predomain
  𝔽𝕃 f = 𝔽 (λ k → 𝕃 k (f k))

  dyn-eqn : Iso
    ⟨ (ℕ ⊎d (𝔽 (λ k -> DynP k ==> 𝕃 k (DynP k) ))) ⟩
    ⟨ (ℕ ⊎d (𝔽 DynP)) ==> 𝔽𝕃 DynP ⟩
  dyn-eqn = {!!}
    

