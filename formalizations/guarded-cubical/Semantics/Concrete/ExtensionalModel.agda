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


open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions hiding (𝔹)
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.DblPosetCombinators

open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.Dyn k

open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Predomains.Perturbations k
open import Semantics.Concrete.Predomains.QuasiRepresentation k

open import Semantics.Concrete.ConcreteIntensionalModel k as Intensional

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

open PBMor

module _
  {Aᵢ  : ValType ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  ℓMAᵢ}
  {Aᵢ' : ValType ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' ℓMAᵢ'}
  {Aₒ  : ValType ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  ℓMAₒ}
  {Aₒ' : ValType ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' ℓMAₒ'}
  (cᵢ  : ValTypeRel Aᵢ Aᵢ' ℓcᵢ)
  (cₒ  : ValTypeRel Aₒ Aₒ' ℓcₒ)
  (f   : ValTypeMor Aᵢ  Aₒ)
  (g   : ValTypeMor Aᵢ' Aₒ')
  where
  ValTypeSq : Type _
  ValTypeSq =
    Σ[ f' ∈ ValTypeMor Aᵢ Aₒ ] (f ≈mon f')
    × (Σ[ g' ∈ ValTypeMor Aᵢ' Aₒ' ] (g ≈mon g')
    × PBSq (cᵢ .fst) (cₒ .fst) f' g')

module _
  {Bᵢ  : CompType ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ  ℓMBᵢ}
  {Bᵢ' : CompType ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ' ℓMBᵢ'}
  {Bₒ  : CompType ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ  ℓMBₒ}
  {Bₒ' : CompType ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ' ℓMBₒ'}
  (dᵢ  : CompTypeRel Bᵢ Bᵢ' ℓcᵢ)
  (dₒ  : CompTypeRel Bₒ Bₒ' ℓcₒ)
  (ϕ   : CompTypeMor Bᵢ  Bₒ)
  (ψ   : CompTypeMor Bᵢ' Bₒ')
  where
  open ErrorDomMor
  CompTypeSq : Type _
  CompTypeSq =
    Σ[ ϕ' ∈ CompTypeMor Bᵢ Bₒ ] (ϕ .f ≈mon ϕ' .f)
    × (Σ[ ψ' ∈ CompTypeMor Bᵢ' Bₒ' ] (ψ .f ≈mon ψ' .f)
    × ErrorDomSq (dᵢ .fst) (dₒ .fst) ϕ' ψ')
