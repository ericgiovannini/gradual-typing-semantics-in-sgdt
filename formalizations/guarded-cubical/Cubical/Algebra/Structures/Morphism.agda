{-# OPTIONS --polarity #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Cubical.Algebra.Structures.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Cubical.Algebra.Structures.Base
open import Cubical.Algebra.Structures.AlgebraicTheory

private
  variable
    ℓ ℓ' ℓ'' : Level


module _ {ℓX ℓar : Level}
  (Σ : Sig ℓX ℓar)
  where

  open Signature Σ
  open Sig Σ

  module _ (M : PreStructure ℓ) (N : PreStructure ℓ') where

    private
      module M = PreStructureStr (M .snd)
      module N = PreStructureStr (N .snd)

    record PreStructHom : Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓ ℓ')) where
      field
        f : ⟨ M ⟩ → ⟨ N ⟩
        is-hom : ∀ {x} (vars : (ar x) → ⟨ M ⟩)
          → f (M.op x vars) ≡ N.op x (f ∘ vars)

  open PreStructHom

  module _ (M : PreStructure ℓ) where

    idHom : PreStructHom M M
    idHom .f x = x
    idHom .is-hom vars = refl


  module _
    (M : PreStructure ℓ)
    (N : PreStructure ℓ')
    (P : PreStructure ℓ'')
    (ϕ : PreStructHom N P)
    (ψ : PreStructHom M N)
    where

   private
     module M = PreStructureStr (M .snd)
     module N = PreStructureStr (N .snd)
     module P = PreStructureStr (P .snd)
     module ϕ = PreStructHom ϕ
     module ψ = PreStructHom ψ

   _∘hom_ : PreStructHom M P
   (_∘hom_) .f = ϕ.f ∘ ψ.f
   (_∘hom_) .is-hom vars = cong ϕ.f (ψ.is-hom vars) ∙ ({!!})



module _ {ℓX ℓar ℓE ℓq : Level} (T : AlgTheory ℓX ℓar ℓE ℓq) where

  open AlgTheory T using (σ ; eqns ; module σ ; module eqns)
  -- private module eqns = Eqns eqns

  open Signature σ


  -- Homomorphisms of structures
  module _ (M : Structure eqns ℓ) (N : Structure eqns ℓ') where

    private
      module M = StructureStr (M .snd)
      module N = StructureStr (N .snd)

    StructHom : Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓ ℓ'))
    StructHom = PreStructHom σ (Structure→PreStructure M) (Structure→PreStructure N)

  module _ {M : Structure eqns ℓ} {N : Structure eqns ℓ'}
    (ϕ : StructHom M N)
    where

    module StructHom→module = PreStructHom ϕ






{-
    module _ (M : Structure eqns ℓ) where

      idHom : PreStructHom M M
      idHom .f x = x
      idHom .is-hom vars = refl


    module _
      (M : Structure eqns ℓ)
      (N : Structure eqns ℓ')
      (P : Structure eqns ℓ'')
      (ϕ : StructHom N P)
      (ψ : StructHom M N)
      where

     private
       module M = StructureStr (M .snd)
       module N = StructureStr (N .snd)
       module P = StructureStr (P .snd)
       module ϕ = PreStructHom ϕ
       module ψ = PreStructHom ψ

     _∘hom_ : StructHom M P
     (_∘hom_) .f = ϕ.f ∘ ψ.f
     (_∘hom_) .is-hom vars = cong ϕ.f (ψ.is-hom vars) ∙ ({!!})
-}
