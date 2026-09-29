{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.ExtProofs (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Relation.Binary.Base


open import Common.Common
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k

open import Semantics.Concrete.DoublePoset.FreeErrorDomain k -- CBPV version of ext

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.DPMorRelation

open import Semantics.Concrete.DoublePoset.ErrorDomain k

open CBPVMonad

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓR ℓS : Level
    ℓX ℓY ℓZ : Level
    ℓ≤X ℓ≤Y : Level

    ℓA  ℓ≤A  ℓ≈A : Level
    ℓA' ℓ≤A' ℓ≈A' : Level
    ℓB  ℓ≤B  ℓ≈B : Level
    ℓB' ℓ≤B' ℓ≈B' : Level

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


module _ (A : PosetBisim ℓA ℓ≤A ℓ≈A) (B : ErrorDomain ℓB ℓ≤B ℓ≈B) where

  test : (f g : PBMor A (U-ob B)) → f ≤mon g → {!ext!}

