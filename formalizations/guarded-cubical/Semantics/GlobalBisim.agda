{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.GlobalBisim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sum

open import Cubical.Data.Empty as ⊥

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Poset

open import Cubical.HITs.PropositionalTruncation renaming (elim to PTelim ; rec to PTrec)

open import Common.Common
open import Common.Later
open import Common.LaterProperties
open import Common.ClockProperties
open import Semantics.Lift 
open import Semantics.WeakBisimilarity
open import Semantics.GlobalLift


private
  variable
    ℓ ℓ' ℓR : Level


-- module WBSum {ℓ ℓR : Level} (X : Type ℓ) (R : X -> X -> Type ℓR) (k : Clock) = BisimSum k X R

module GlobalBisimSum  (X : Type ℓ) (R : X -> X -> Type ℓR) where
  -- open WBSum X R
  --open module WBSum = BisimSum X R -- enaming (_≈_ to _≈S_)

  --_≈[_]_ : {!L k X → (k : Clock) → L k X!}
  --l ≈[ k ] l' = {!_≈_ k l l'!}

  ≈S : (k : Clock) → L k X → L k X → Type (ℓ-max ℓ ℓR)
  ≈S k = BisimSum._≈_ k X R
  syntax ≈S k x y = x ≈[ k ] y

  _≈g_ : L^gl X -> L^gl X -> Type (ℓ-max ℓ ℓR)
  l1 ≈g l2 = ∀ k → (l1 k) ≈[ k ] (l2 k)

  case1 : (l l' : L^gl X) -> Type (ℓ-max ℓ ℓR)
  case1 l l' = Σ[ x ∈ X ] Σ[ y ∈ X ] (l ≡ ηL^gl x) × (l' ≡ ηL^gl y) × R x y

  case2 : (l l' : L^gl X) -> Type (ℓ-max ℓ ℓR)
  case2 l l' =
    Σ[ x ∈ X ] ((l  ≡ ηL^gl x)
      × ∥ Σ[ n ∈ ℕ ] Σ[ y ∈ X ] ((l' ≡ (δL^gl ^ n) (ηL^gl y)) × R x y) ∥₁)

  case3 : (l l' : L^gl X) -> Type (ℓ-max ℓ ℓR)
  case3 l l' =
    Σ[ y ∈ X ] ((l' ≡ ηL^gl y)
      × ∥ Σ[ n ∈ ℕ ] Σ[ x ∈ X ] ((l  ≡ (δL^gl ^ n) (ηL^gl x)) × R x y) ∥₁)

  case4 : (l l' : L^gl X) -> Type (ℓ-max ℓ ℓR)
  case4 l l' = Σ[ lx~ ∈ (∀ k -> ▹ k , L k X) ] Σ[ ly~ ∈ (∀ k -> ▹ k , (L^gl X)) ]
    (l ≡ λ k → lx~ k {!!}) × (l' ≡ {!!}) × (▸ (λ t -> {!!}))

  _≈g'_ : {!!}
  l1 ≈g' l2 = {!!}

  L^gl-R-iso : clock-irrel X -> (l l' : L^gl X) ->
    Iso (l ≈g l') (case1 l l' ⊎ (case2 l l' ⊎ (case3 l l' ⊎ case4 l l'))) 
  L^gl-R-iso X-irrel l l' =
    (l ≈g l')
      Iso⟨ {!!} ⟩
      {!!} Iso⟨ {!!} ⟩ {!!}
    (case1 l l' ⊎ (case2 l l' ⊎ (case3 l l' ⊎ case4 l l'))) ∎Iso
  
      
  
      
