{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.SemPtbLater (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum


open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Sigma


open import Common.Common
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions renaming (ℕ to NatP)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.Combinators
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.Monad k
open import Semantics.Concrete.Predomain.MonadRelationalResults k
open import Semantics.Concrete.Predomain.MonadCombinators k
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Predomain.Kleisli k


open import Cubical.Algebra.Monoid.PointedMonoid
open import Semantics.Concrete.LaterMonoid k
open import Semantics.Concrete.Perturbation.Semantic k

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓA₃ ℓ≤A₃ ℓ≈A₃ : Level

private
  ▹_ : Type ℓ -> Type ℓ
  ▹ A = ▹_,_ k A


postulate
  δ̂ : ∀ {B : ErrorDomain ℓB ℓ≤B ℓ≈B} → CSemPtb B

delay-endo : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  (⟨ CEndo B ⟩ → ⟨ CEndo B ⟩)
delay-endo {B = B} = {!!}

EndoBAsPointed : (B : ErrorDomain ℓB ℓ≤B ℓ≈B) → PointedMonoidDelay (ℓ-max (ℓ-max ℓB ℓ≤B) ℓ≈B)
EndoBAsPointed B = PointedMonoid→PointedMonoidDelay (Monoid→PointedMonoid (CEndo B) {!!}) {!!}



