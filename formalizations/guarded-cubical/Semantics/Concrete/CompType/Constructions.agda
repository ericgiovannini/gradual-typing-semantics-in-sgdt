{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.CompType.Constructions (k : Clock) where

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
open import Cubical.Algebra.Monoid.Instances.Trivial

open import Cubical.Data.Sigma


open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions
  renaming (ℕ to ∣ℕ∣)
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
  renaming (U to ∣U∣)

open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.Dyn k

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

F : ValType ℓ ℓ≤ ℓ≈ ℓM → CompType ℓ (ℓ-max ℓ ℓ≤) (ℓ-max ℓ ℓ≈) ℓM
F A = mkCompType (F-ob (ValType→Predomain A)) M-FA iFA where
  open F-ob
  open ValTypeStr
  open F-Ptb (A .snd .PtbV) (A .snd .interpV )

_⟶_ : ValType ℓ ℓ≤ ℓ≈ ℓM
      → CompType ℓ' ℓ≤' ℓ≈' ℓM'
      → CompType
          (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈) ℓ') ℓ≤') ℓ≈')
          (ℓ-max ℓ ℓ≤')
          (ℓ-max (ℓ-max ℓ ℓ≈) ℓ≈')
          (ℓ-max ℓM ℓM')
A ⟶ B = mkCompType (ValType→Predomain A ⟶ob CompType→ErrorDomain B)
  M-Arrow
  i-Arrow
  where
  open Arrow-Ptb _ (A .snd .interpV) _ (B .snd .snd .snd)
