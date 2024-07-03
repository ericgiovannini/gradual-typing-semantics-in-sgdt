{-

  Defines our final notion of value and computation relation, which are
  predomains/domains relations respectively that are additionally equipped with
  1. pushpull structure
  2. quasi-representability structure

  Additionally defines squares thereof as squares of the
  underlying relations

-}

{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Common.Later

module Semantics.Concrete.Relations.Constructions (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Monoid.Base
open import Cubical.Data.Sigma

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Perturbation.Relation k as Relation hiding (F)
open import Semantics.Concrete.Perturbation.QuasiRepresentation k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k


open import Semantics.Concrete.Types k as Types hiding (_×_; F)
open import Semantics.Concrete.Relations.Base k

---------------------------------------------------------------
-- Value Type Relations
---------------------------------------------------------------
private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓ≤' ℓ≈' ℓM' : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓc ℓc' ℓd ℓd' : Level
    ℓcᵢ ℓcᵢ' ℓdᵢ ℓdᵢ' : Level
    ℓcₒ ℓcₒ' ℓdₒ ℓdₒ' : Level

    ℓA₁   ℓ≤A₁   ℓ≈A₁   : Level
    ℓA₁'  ℓ≤A₁'  ℓ≈A₁'  : Level
    ℓA₂   ℓ≤A₂   ℓ≈A₂   : Level
    ℓA₂'  ℓ≤A₂'  ℓ≈A₂'  : Level
    ℓA₃   ℓ≤A₃   ℓ≈A₃   : Level
    ℓA₃'  ℓ≤A₃'  ℓ≈A₃'  : Level

    ℓB₁   ℓ≤B₁   ℓ≈B₁   : Level
    ℓB₁'  ℓ≤B₁'  ℓ≈B₁'  : Level
    ℓB₂   ℓ≤B₂   ℓ≈B₂   : Level
    ℓB₂'  ℓ≤B₂'  ℓ≈B₂'  : Level
    ℓB₃   ℓ≤B₃   ℓ≈B₃   : Level
    ℓB₃'  ℓ≤B₃'  ℓ≈B₃'  : Level

    ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ : Level
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' : Level
    ℓAₒ ℓ≤Aₒ ℓ≈Aₒ : Level
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' : Level
    ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ : Level
    ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ' : Level
    ℓBₒ ℓ≤Bₒ ℓ≈Bₒ : Level
    ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ' : Level

    ℓc₁ ℓc₂ ℓc₃  : Level

    ℓMA₁ ℓMA₂ ℓMA₃ : Level
    ℓMA₁' ℓMA₂' ℓMA₃' : Level
    ℓMB₁ ℓMB₂ ℓMB₃ : Level
    ℓMAᵢ ℓMAₒ ℓMBᵢ ℓMBₒ : Level
    ℓMAᵢ' ℓMAₒ' ℓMBᵢ' ℓMBₒ' : Level

module _ {A  : ValType ℓA  ℓ≤A  ℓ≈A ℓMA} {A'  : ValType ℓA'  ℓ≤A'  ℓ≈A' ℓMA'} where
  F : ValRel A A' ℓc → CompRel (Types.F A) (Types.F A') _
  F c .fst = Relation.F (c .fst)
  F c .snd .fst = {!!}
  F c .snd .snd = {!!}
