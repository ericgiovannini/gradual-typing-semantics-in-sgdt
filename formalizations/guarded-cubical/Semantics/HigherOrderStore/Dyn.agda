{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.HigherOrderStore.Dyn (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Properties
open import Cubical.Categories.NaturalTransformation

-- open import Semantics.Concrete.Predomain.SimpleErrorDomain k
open import Semantics.HigherOrderStore.SimpleErrorDomain k
open import Semantics.HigherOrderStore.WorldTag k

private
  variable
    ℓ ℓ' : Level
    A : hSet ℓ-zero

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


ValPsh : Type (ℓ-suc ℓ-zero)
ValPsh = Functor 𝕎 (SET ℓ-zero)

CompPsh : Type (ℓ-suc ℓ-zero)
CompPsh = Functor (𝕎 ^op) (SIMPED ℓ-zero)




-- Given a category 𝓥 and a category 𝓒 and functors
-- F : 𝓥 → 𝓒 and U : 𝓒 → 𝓥 with F ⊣ U, we define
-- a type dyn

