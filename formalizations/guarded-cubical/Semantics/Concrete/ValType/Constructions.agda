{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.ValType.Constructions (k : Clock) where

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
open import Cubical.Algebra.Monoid.Instances.Trivial as Trivial

open import Cubical.Data.Sigma hiding (_×_)
import Cubical.Data.Unit as Unit
import Cubical.Data.Nat as Nat

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions
  renaming (ℕ to ∣ℕ∣; flat to flatDP)
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
  renaming (U to ∣U∣)

open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.Dyn k
open import Semantics.Concrete.DynPerturb k as PtbD

open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Predomains.Perturbations k
open import Semantics.Concrete.Predomains.QuasiRepresentation k
open import Semantics.Concrete.ConcreteIntensionalModel k

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓ≤' ℓ≈' ℓM' : Level
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

open ValTypeStr

flat : hSet ℓ → ValType ℓ ℓ ℓ ℓ-zero
flat X = mkValType (flatDP X) TrivialMonoid Trivial.rec

ℕ : ValType _ _ _ _
ℕ = flat (Nat.ℕ , Nat.isSetℕ)

U : CompType ℓ ℓ≤ ℓ≈ ℓM → ValType ℓ ℓ≤ ℓ≈ ℓM
U B = mkValType (U-ob (CompType→ErrorDomain B)) M-UB iUB where
  open U-Ptb _ (B .snd .snd .snd)

Unit : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
Unit = flat (Unit.Unit , Unit.isSetUnit)

_×_ : ValType ℓ ℓ≤ ℓ≈ ℓM
    → ValType ℓ' ℓ≤' ℓ≈' ℓM'
    → ValType _ _ _ _
A × A' = mkValType (ValType→Predomain A ×dp ValType→Predomain A')
  M-×
  i× where
  open ×-Ptb _ (A .snd .interpV) _ (A' .snd .interpV)

dyn : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
dyn = mkValType Dyn PtbD ι-dyn where
  open DynDef
