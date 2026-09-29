{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Experiments.Perturbations2.Types (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid

open import Cubical.Data.Empty
open import Cubical.Relation.Nullary

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.FreeErrorDomainOpaque k
open import Semantics.Concrete.Perturbation.Semantic k


private
  variable
    ℓ ℓ' : Level
    ℓ≤ ℓ≈ : Level
    ℓM : Level


private
  ▹_ : Set ℓ → Set ℓ
  ▹_ A = ▹_,_ k A


record ValType (ℓ ℓ≤ ℓ≈ ℓM : Level) : Type {!!} where

  field
    pre  : Predomain ℓ ℓ≤ ℓ≈
    Ptb  : Monoid ℓM
    Ptbᴷ : Monoid ℓM

    -- interp : MonoidHom Ptb (Endo pre)
    interp : MonoidHom Ptb (Endo pre)
