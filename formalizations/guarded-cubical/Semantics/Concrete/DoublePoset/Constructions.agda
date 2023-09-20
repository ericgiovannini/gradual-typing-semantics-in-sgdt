{-# OPTIONS --guarded --rewriting #-}


module Semantics.Concrete.DoublePoset.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure


open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism

open import Common.Later

private
  variable
    ℓ ℓ' : Level
    ℓX ℓ'X ℓ''X : Level
    ℓY ℓ'Y ℓ''Y : Level

    X : DoublePoset ℓX ℓ'X ℓ''X
    Y : DoublePoset ℓY ℓ'Y ℓ''Y


-- Constructions not involving later


-- Contructions involving later
module ClockedConstructions (k : Clock) where

  private
    ▹_ : Type ℓ -> Type ℓ
    ▹ A = ▹_,_ k A

    -- Theta for double posets
    --DP▸ : ?
    --DP▸ = ?

 
