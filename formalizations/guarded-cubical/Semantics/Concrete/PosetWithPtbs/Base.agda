{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}




open import Common.Later

module Semantics.Concrete.PosetWithPtbs.Base (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Reflection.RecordEquiv
open import Cubical.Relation.Binary.Poset
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.Function

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.CommMonoid.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_ ; _^_)


open import Common.Common

open import Semantics.Lift k
open import Semantics.LockStepErrorOrdering k
open import Common.Poset.Convenience
open import Common.Poset.Constructions
open import Common.Poset.Monotone
--open import Common.Poset.MonotoneRelation
open import Semantics.MonotoneCombinators

-- open import Cubical.Algebra.Monoid.FreeProduct
--   renaming (ε to empty ; _·_ to _·free_ ; _⋆_ to _⋆M_)


-- open import Semantics.Abstract.Model.Model


-- open Model

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓA ℓ'A ℓB ℓ'B ℓC ℓ'C : Level

  ▹_ : Type ℓ -> Type ℓ
  ▹ A = ▹_,_ k A


-- Monoid of all monotone endofunctions on a poset
EndoMonFun : (X : Poset ℓ ℓ') -> Monoid (ℓ-max ℓ ℓ')
EndoMonFun X = makeMonoid {M = MonFun X X} Id mCompU MonFunIsSet
  (λ f g h -> eqMon _ _ refl) (λ f -> eqMon _ _ refl) (λ f -> eqMon _ _ refl)


-- We define this separately for the sake of isolation.
-- Writing EndoMonFun (𝕃 X) causes Agda to take an extremely long time to type-check
-- So, we make it a separate definition.
-- The isSet proof for some reason slows down the typechecking massively,
-- so we omit it for now.
EndoMonFunLift : {ℓ ℓ' : Level} -> (X : Poset ℓ ℓ') -> Monoid (ℓ-max ℓ ℓ')
EndoMonFunLift {ℓ = ℓ} {ℓ' = ℓ'} X = makeMonoid {M = MonFun (𝕃 X) (𝕃 X)} Id mCompU {!!}
  (λ f g h -> eqMon (mCompU f (mCompU g h)) {!!} refl)
  (λ f -> eqMon (mCompU f Id) f refl)
  (λ f -> eqMon (mCompU Id f) f refl)
  where open LiftPoset


--
-- A poset along with a monoid of monotone perturbation functions
--
record PosetWithPtb (ℓ ℓ' ℓ'' : Level) :
  Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓ''))) where
  open LiftPoset

  field
    P       : Poset ℓ ℓ'
    Perturbᴱ : CommMonoid ℓ''
    Perturbᴾ : CommMonoid ℓ''
    perturbᴱ : MonoidHom (CommMonoid→Monoid Perturbᴱ) (EndoMonFun P)
    perturbᴾ : MonoidHom (CommMonoid→Monoid Perturbᴾ) (EndoMonFun P)
    -- perturbᴾ : MonoidHom (CommMonoid→Monoid Perturbᴾ) (EndoMonFunLift P)
    --TODO: needs to be injective map
    -- Perturb : ⟨ EndoMonFun P ⟩

  ptb-funᴱ : ⟨ Perturbᴱ ⟩ -> ⟨ EndoMonFun P ⟩
  ptb-funᴱ = perturbᴱ .fst

  ptb-funᴾ : ⟨ Perturbᴾ ⟩ -> ⟨ EndoMonFun P ⟩
  -- ptb-funᴾ : ⟨ Perturbᴾ ⟩ -> ⟨ EndoMonFunLift P ⟩

  ptb-funᴾ = perturbᴾ .fst
  

open PosetWithPtb

