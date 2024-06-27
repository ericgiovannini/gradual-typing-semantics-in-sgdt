{-
  Denotational semantics of gradual types as error predomains
-}
{-# OPTIONS --rewriting #-}
open import Common.Later
module Syntax.FineGrained.Denotation.Types (k : Clock) where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Foundations.Structure
open import Cubical.Data.List
open import Syntax.Types
open import Semantics.Concrete.ConcreteIntensionalModel k
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Constructions
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.Dyn k

open DynDef {ℓ = ℓ-zero}

⟦_⟧ty-pre : Ty → PosetBisim ℓ-zero ℓ-zero ℓ-zero
⟦ nat ⟧ty-pre = ℕ
⟦ dyn ⟧ty-pre = Dyn
⟦ A ⇀ B ⟧ty-pre = U-ob (⟦ A ⟧ty-pre ⟶ob F-ob ⟦ B ⟧ty-pre) where
  open F-ob

-- TODO: need to define the perturbations of all of these first
⟦_⟧ty : Ty → ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero
⟦ nat ⟧ty = {!!}
⟦ dyn ⟧ty = {!!}
⟦ A ⇀ B ⟧ty = ⟨ ⟦ A ⇀ B ⟧ty-pre ⟩ , valtypestr {!!} {!!} {!!} where
  open ValTypeStr
  -- open U-PushBull ....
