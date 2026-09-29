{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.Instances.Predomain (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.HLevels
import Cubical.Data.Sigma as Data
open import Cubical.Foundations.Structure
open import Cubical.Data.List

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions
  using (LiftPredomain ; ℕ ; UnitP ; _×dp_ ; _⊎p_ ; π1 ; π2)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Combinators hiding (S ; U)
open import Semantics.Concrete.Predomain.SquareOpaque
  renaming (CompSqV to CompPSqV ; CompSqH to CompPSqH)
open import Semantics.Concrete.Predomain.SquareCombinators

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k


private
  variable
    ℓ : Level

open ThinDoubleCat

module _ (ℓ : Level) where

  PREDOM : ThinDoubleCat (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ ℓ
  PREDOM .ob = Predomain ℓ ℓ ℓ
  PREDOM .vhom[_,_] Aᵢ Aₒ = PMor Aᵢ Aₒ
  PREDOM .hhom[_,_] A A' = PRel A A' ℓ
  PREDOM .sq cᵢ cₒ f g = PSq cᵢ cₒ f g
  
  PREDOM .idV = Id
  PREDOM ._⋆V_ f g = g ∘p f
  PREDOM .idLV f = CompPD-IdR f
  PREDOM .idRV f = CompPD-IdL f
  PREDOM .assocV f g h = CompPD-Assoc f g h
  
  PREDOM .idH = idPRel _
  PREDOM ._⋆H_ c c' = c ⊙ c'
  PREDOM .idLH = {!!}
  PREDOM .idRH = {!!}
  PREDOM .assocH = {!!}
  
  PREDOM .idSqV = Predom-IdSqV
  PREDOM .idSqH = Predom-IdSqH
  PREDOM ._⋆SqV_ = CompPSqV
  PREDOM ._⋆SqH_ = CompPSqH
  
  PREDOM .isSetVMor = PMorIsSet
  PREDOM .isSetHMor = {!!}
  PREDOM .isPropSq = isPropPSq
  
  PREDOM ._≈vhom_ f g = f ≈mon g
  PREDOM .isBisim≈ = isbisim ≈mon-refl ≈mon-sym ≈mon-prop
  PREDOM .comp≈ f f' g g' = ≈mon-comp {f = f} {g = f'} {f' = g} {g' = g'}
