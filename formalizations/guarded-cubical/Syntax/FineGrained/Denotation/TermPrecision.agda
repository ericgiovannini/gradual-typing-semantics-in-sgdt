{-

  Denotational semantics of term precision, i.e., graduality
  
-}
{-# OPTIONS --rewriting --lossy-unification --allow-unsolved-metas #-}
open import Common.Later
module Syntax.FineGrained.Denotation.TermPrecision (k : Clock) where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Foundations.Structure
open import Cubical.Data.List

open import Syntax.Types
open import Syntax.FineGrained.Terms
open import Syntax.FineGrained.Order
open import Syntax.FineGrained.Denotation.Types k
open import Syntax.FineGrained.Denotation.TypePrecision k
open import Syntax.FineGrained.Denotation.Terms k

open import Semantics.Concrete.ExtensionalModel k
open import Semantics.Concrete.ConcreteIntensionalModel k
open import Semantics.Concrete.ValType.Constructions k
open import Semantics.Concrete.CompType.Constructions k
import Semantics.Concrete.ValRel.Constructions k as ValRel
import Semantics.Concrete.CompRel.Constructions k as CompRel

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T R' S' T' : Ty
   B B' C C' D D' : Γ ⊑ctx Γ'
   b b' c c' d d' : S ⊑ S'
   γ γ' γ'' : Subst Δ Γ
   δ δ' δ'' : Subst Θ Δ
   θ θ' θ'' : Subst Z Θ
   V V' V'' : Val Γ S
   M M' M'' N N' : Comp Γ S
   E E' E'' : EvCtx Γ S T


⟦_⟧S⊑ : Subst⊑ C D γ γ' → ValTypeSq ⟦ C ⟧ctx⊑ ⟦ D ⟧ctx⊑ ⟦ γ ⟧S ⟦ γ' ⟧S
⟦_⟧V⊑ : Val⊑ C c V V' →  ValTypeSq ⟦ C ⟧ctx⊑ ⟦ c ⟧ty⊑ ⟦ V ⟧V ⟦ V' ⟧V
⟦_⟧C⊑ : Comp⊑ C c M M'
  → ValTypeSq ⟦ C ⟧ctx⊑ (ValRel.U (CompRel.F ⟦ c ⟧ty⊑)) ⟦ M ⟧C ⟦ M' ⟧C

⟦_⟧E⊑ : EvCtx⊑ C c d E E'
  → CompTypeSq (CompRel.F ⟦ c ⟧ty⊑)
               (⟦ C ⟧ctx⊑ CompRel.⟶ CompRel.F ⟦ d ⟧ty⊑)
               ⟦ E ⟧E
               ⟦ E' ⟧E

⟦_⟧S⊑ = {!!}
⟦_⟧V⊑ = {!!}
⟦_⟧C⊑ = ?
⟦_⟧E⊑ = {!!}
