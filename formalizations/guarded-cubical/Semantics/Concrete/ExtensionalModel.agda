{-

  Extensional notion of 2-cell/square that combines bisimulation with
  the strict ordering.

-}

{-# OPTIONS --rewriting #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Common.Later

module Semantics.Concrete.ExtensionalModel (k : Clock) where

open import Common.Common
open import Common.LaterProperties

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function hiding (_$_)

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct

open import Cubical.Data.Sigma


open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions hiding (𝔹)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.Combinators

open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Dyn.DynInstantiated k

open import Semantics.Concrete.Perturbation.Semantic k
-- open import Semantics.Concrete.Predomains.Perturbations k
-- open import Semantics.Concrete.Predomains.QuasiRepresentation k
-- open import Semantics.Concrete.ConcreteIntensionalModel k as Intensional
open import Semantics.Concrete.Types k as Types
  using (ValType ; ValMor ; CompType ; CompMor)
open import Semantics.Concrete.Relations k as Rel using (ValRel ; CompRel)

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓc ℓd : Level

    ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  ℓMAᵢ  : Level
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' ℓMAᵢ' : Level
    ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  ℓMAₒ  : Level
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' ℓMAₒ' : Level
    ℓcᵢ ℓcₒ                : Level

    ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ  ℓMBᵢ  : Level
    ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ' ℓMBᵢ' : Level
    ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ  ℓMBₒ  : Level
    ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ' ℓMBₒ' : Level
    ℓdᵢ ℓdₒ                : Level

    ℓX ℓY ℓR : Level

open PMor

module _
  {Aᵢ  : ValType ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  ℓMAᵢ}
  {Aᵢ' : ValType ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' ℓMAᵢ'}
  {Aₒ  : ValType ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  ℓMAₒ}
  {Aₒ' : ValType ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' ℓMAₒ'}
  (cᵢ  : ValRel Aᵢ Aᵢ' ℓcᵢ)
  (cₒ  : ValRel Aₒ Aₒ' ℓcₒ)
  (f   : ValMor Aᵢ  Aₒ)
  (g   : ValMor Aᵢ' Aₒ')
  where
  ValTypeSq : Type _
  ValTypeSq =
    Σ[ f' ∈ ValMor Aᵢ Aₒ ] (f ≈mon f')
    × (Σ[ g' ∈ ValMor Aᵢ' Aₒ' ] (g ≈mon g')
    × PSq (cᵢ .fst .fst) (cₒ .fst .fst) f' g')

module _
  {Bᵢ  : CompType ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ  ℓMBᵢ}
  {Bᵢ' : CompType ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ' ℓMBᵢ'}
  {Bₒ  : CompType ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ  ℓMBₒ}
  {Bₒ' : CompType ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ' ℓMBₒ'}
  (dᵢ  : CompRel Bᵢ Bᵢ' ℓcᵢ)
  (dₒ  : CompRel Bₒ Bₒ' ℓcₒ)
  (ϕ   : CompMor Bᵢ  Bₒ)
  (ψ   : CompMor Bᵢ' Bₒ')
  where
  open ErrorDomMor
  CompTypeSq : Type _
  CompTypeSq =
    Σ[ ϕ' ∈ CompMor Bᵢ Bₒ ] (ϕ .f ≈mon ϕ' .f)
    × (Σ[ ψ' ∈ CompMor Bᵢ' Bₒ' ] (ψ .f ≈mon ψ' .f)
    × ErrorDomSq (dᵢ .fst .fst) (dₒ .fst .fst) ϕ' ψ')
