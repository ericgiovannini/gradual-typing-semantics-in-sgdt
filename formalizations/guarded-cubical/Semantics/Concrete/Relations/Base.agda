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

module Semantics.Concrete.Relations.Base (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Monoid.Base
open import Cubical.Data.Sigma

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Perturbation.Semantic k
--open import Semantics.Concrete.Perturbation.Relation k as Relation
open import Semantics.Concrete.Perturbation.Relation.Alt k as Relation
open import Semantics.Concrete.Perturbation.QuasiRepresentation k
open import Semantics.Concrete.Types k as Types hiding (_×_)
open import Semantics.Concrete.Predomain.FreeErrorDomain k
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

module _ (A  : ValType ℓA  ℓ≤A  ℓ≈A ℓMA) (A'  : ValType ℓA'  ℓ≤A'  ℓ≈A' ℓMA') where
  ValRel : ∀ (ℓc : Level) → Type _
  ValRel ℓc =
    Σ[ c ∈ VRelPP A A' ℓc ]
    LeftRepV A A' (c .fst)
    × RightRepC (Types.F A) (Types.F A') (F-rel (c .fst))
    where open F-rel

module _ {A  : ValType ℓA  ℓ≤A  ℓ≈A ℓMA} {A'  : ValType ℓA'  ℓ≤A'  ℓ≈A' ℓMA'} where
  -- If two relations are (quasi)-represented by the same embedding, then they are quasi-equivalent.
  ValRel≈ : (c : ValRel A A' ℓc) (c' : ValRel A A' ℓc') → Type _
  ValRel≈ c c' = c .snd .fst .fst ≡ c' .snd .fst .fst

module _ (B  : CompType ℓB  ℓ≤B  ℓ≈B ℓMB) (B'  : CompType ℓB'  ℓ≤B'  ℓ≈B' ℓMB') where
  CompRel : ∀ (ℓd : Level) → Type _
  CompRel ℓd =
    Σ[ d ∈ CRelPP B B' ℓd ]
    RightRepC B B' (d .fst)
    × LeftRepV (Types.U B) (Types.U B') (U-rel (d .fst))

module _ {B  : CompType ℓB  ℓ≤B  ℓ≈B ℓMB} {B'  : CompType ℓB'  ℓ≤B'  ℓ≈B' ℓMB'} where
  -- If two relations are (quasi)-represented by the same embedding, then they are quasi-equivalent.
  CompRel≈ : (d : CompRel B B' ℓd) (d' : CompRel B B' ℓd') → Type _
  CompRel≈ d d' = d .snd .fst .fst ≡ d' .snd .fst .fst


module _ {Aᵢ  : ValType ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ ℓMAᵢ} {Aᵢ'  : ValType ℓAᵢ'  ℓ≤Aᵢ'  ℓ≈Aᵢ' ℓMAᵢ'}
         {Aₒ  : ValType ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ ℓMAₒ} {Aₒ'  : ValType ℓAₒ'  ℓ≤Aₒ'  ℓ≈Aₒ' ℓMAₒ'}
         (cᵢ : ValRel Aᵢ Aᵢ' ℓcᵢ)
         (cₒ : ValRel Aₒ Aₒ' ℓcₒ)
         (f : ValTypeMor Aᵢ Aₒ)
         (f' : ValTypeMor Aᵢ' Aₒ')
         where
  ValSq : Type _
  ValSq = PSq (cᵢ .fst .fst) (cₒ .fst .fst) f f'

module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
         {B : CompType ℓB ℓ≤B ℓ≈B ℓMB} {B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
         (c : ValRel A A' ℓc)
         (d : CompRel B B' ℓd)
         where
  ObliqueSq : ∀ (M : ObliqueMor A B) (M' : ObliqueMor A' B') → Type _
  ObliqueSq M M' = PSq (c .fst .fst) (U-rel (d .fst .fst)) M M'

  ObliqueExtSq : ∀ (M : ObliqueMor A B) (M' : ObliqueMor A' B') → Type _
  ObliqueExtSq M M' =
    Σ[ N ∈ ObliqueMor A B ] M ≈mon N
    × (Σ[ N' ∈ ObliqueMor A' B' ] N' ≈mon M'
    × ObliqueSq N N')

module _ {Bᵢ  : CompType ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ ℓMBᵢ} {Bᵢ'  : CompType ℓBᵢ'  ℓ≤Bᵢ'  ℓ≈Bᵢ' ℓMBᵢ'}
         {Bₒ  : CompType ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ ℓMBₒ} {Bₒ'  : CompType ℓBₒ'  ℓ≤Bₒ'  ℓ≈Bₒ' ℓMBₒ'}
         (dᵢ : CompRel Bᵢ Bᵢ' ℓdᵢ)
         (dₒ : CompRel Bₒ Bₒ' ℓdₒ)
         (f : CompTypeMor Bᵢ Bₒ)
         (f' : CompTypeMor Bᵢ' Bₒ')
         where
  CompSq : Type _
  CompSq = ErrorDomSq (dᵢ .fst .fst) (dₒ .fst .fst) f f'
