{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.CompRel.Constructions (k : Clock) where

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
import Semantics.Concrete.CompType.Constructions k as CompType

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

F : ∀ {A : ValType ℓ ℓ≤ ℓ≈ ℓM}{A' : ValType ℓ' ℓ≤' ℓ≈' ℓM'}
  → ValTypeRel A A' ℓc
  → CompTypeRel (CompType.F A) (CompType.F A') _
F c .fst = F-rel (c .fst) where open F-rel
F c .snd .fst = F-PushPull (c .fst) (c .snd .fst) where open F-PushPull
F c .snd .snd = {!!}

_⟶_ : ∀ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA}{A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
      {B : CompType ℓB ℓ≤B ℓ≈B ℓMB}{B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
    → ValTypeRel A A' ℓc
    → CompTypeRel B B' ℓd
    → CompTypeRel (A CompType.⟶ B) (A' CompType.⟶ B') _
(c ⟶ d) .fst = Arr-rel (c .fst) (d .fst)
(c ⟶ d) .snd .fst = ⟶PP (c .fst) (c .snd .fst) (d .fst) (d .snd .fst)
  where open ⟶PushPull
(c ⟶ d) .snd .snd = {!!}
