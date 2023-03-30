
{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.ErrorDomains (k : Clock) where

open import Cubical.Relation.Binary.Poset
open import Cubical.Foundations.Structure

open import Semantics.Predomains
open import Cubical.Data.Sigma


open import Semantics.Monotone.Base

-- Error domains

record ErrorDomain : Set₁ where
  field
    X : Predomain
  module X = PosetStr (X .snd)
  _≤_ = X._≤_
  field
    ℧ : X .fst
    ℧⊥ : ∀ x → ℧ ≤ x
    θ : MonFun (▸''_ k X) X


-- Underlying predomain of an error domain

𝕌 : ErrorDomain -> Predomain
𝕌 d = ErrorDomain.X d

{-
arr : Predomain -> ErrorDomain -> ErrorDomain
arr dom cod =
  record {
    X = arr' dom (𝕌 cod) ;
    ℧ = const-err ;
    ℧⊥ = const-err-bot ;
    θ = {!!} }
    where
       -- open LiftOrder
       const-err : ⟨ arr' dom (𝕌 cod) ⟩
       const-err = record {
         f = λ _ -> ErrorDomain.℧ cod ;
         isMon = λ _ -> reflexive (𝕌 cod) (ErrorDomain.℧ cod) }

       const-err-bot : (f : ⟨ arr' dom (𝕌 cod) ⟩) -> rel (arr' dom (𝕌 cod)) const-err f
       const-err-bot f = λ x y x≤y → ErrorDomain.℧⊥ cod (MonFun.f f y)
-}


{-
-- Predomain to lift Error Domain

𝕃℧ : Predomain → ErrorDomain
𝕃℧ X = record {
  X = 𝕃 X ; ℧ = ℧ ; ℧⊥ = ord-bot X ;
  θ = record { f = θ ; isMon = λ t -> {!!} } }
  where
    -- module X = PosetStr (X .snd)
    -- open Relation X
    open LiftPredomain
-}
