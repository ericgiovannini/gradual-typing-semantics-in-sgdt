{-# OPTIONS --polarity #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Cubical.Algebra.Structures.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet

open import Cubical.Algebra.Structures.Base
open import Cubical.Algebra.Structures.Morphism
open import Cubical.Algebra.Structures.AlgebraicTheory


private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓᴰ ℓᴰ' : Level
    ℓM ℓN ℓP : Level
    ℓMᴰ ℓNᴰ ℓPᴰ : Level


module _ {ℓX ℓar : Level}
  (Σ : Sig ℓX ℓar)
  where

  open Signature Σ
  open Sig Σ


  -- Displayed PreStructures
  ---------------------------
  record PreStructureᴰ (M : PreStructure ℓ) ℓᴰ
    : Type (ℓ-max (ℓ-max ℓ (ℓ-suc ℓᴰ)) (ℓ-max ℓX ℓar)) where
    
      open PreStructureStr (M .snd)
      
      field
        eltᴰ : ⟨ M ⟩ → Type ℓᴰ

        -- Given x : X, an `ar x`-indexed collection `vars` of elements of M, and
        -- a family for each z ∈ ar x displayed over the element `vars z` ∈ M,
        -- we get a single element displayed over `op x vars`.
        opᴰ : ∀ (x : X) {vars : ar x → ⟨ M ⟩}
          → (varsᴰ : (z : ar x) → eltᴰ (vars z))
          → eltᴰ (op x vars)

        isSetEltᴰ : ∀ {x} → isSet (eltᴰ x)

      _≡[_]_ : ∀ {x y} → eltᴰ x → x ≡ y → eltᴰ y → Type _
      xᴰ ≡[ p ] yᴰ = PathP (λ i → eltᴰ (p i)) xᴰ yᴰ

      reind : ∀ {x y} (p : x ≡ y) → eltᴰ x → eltᴰ y
      reind = subst eltᴰ

      reind-filler : ∀ {x y}(p : x ≡ y)
        → (xᴰ : eltᴰ x)
        → xᴰ ≡[ p ] reind p xᴰ
      reind-filler = subst-filler eltᴰ

      rectify :
        ∀ {x y} {xᴰ yᴰ}
        → {p q : x ≡ y}
        → xᴰ ≡[ p ] yᴰ → xᴰ ≡[ q ] yᴰ
      rectify {xᴰ = xᴰ}{yᴰ = yᴰ} = subst (xᴰ ≡[_] yᴰ)
        (is-set _ _ _ _)

      _∙ᴰ_ :
        ∀ {x y z} {xᴰ yᴰ zᴰ}
        → {p : x ≡ y}{q : y ≡ z}
        → xᴰ ≡[ p ] yᴰ → yᴰ ≡[ q ] zᴰ
        → xᴰ ≡[ p ∙ q ] zᴰ
      _∙ᴰ_ {xᴰ = xᴰ}{zᴰ = zᴰ}{p}{q} pᴰ qᴰ =
        subst (λ p → PathP (λ i → p i) xᴰ zᴰ)
          (sym (congFunct eltᴰ p q))
          (compPathP pᴰ qᴰ)


  module _ {ℓY : Level} (Y : Type ℓY) where

    module _ {ℓ ℓᴰ : Level} (s : PreStructure ℓ) (sᴰ : PreStructureᴰ s ℓᴰ) where
      open PreStructureᴰ sᴰ

      -- Interpreting a term AST (with variables in Y) in a displayed
      -- PreStructure.
      interpᴰ : (f : (Y → ⟨ s ⟩)) (fᴰ : (y : Y) → eltᴰ (f y))
        → (t : Term Y)
        → eltᴰ (interp Y ⟨ s ⟩ (s .snd) f t)
      interpᴰ f fᴰ (var y) = fᴰ y
      interpᴰ f fᴰ (oper x vars) = opᴰ x (λ z → interpᴰ f fᴰ (vars z))


      -- Interpreting an equation in a displayed PreStructure.
      interp-eqnᴰ : (eqn : Equation Y)
        → (eqn-holds : interp-eqn (s .snd) Y eqn)
        → Type (ℓ-max (ℓ-max ℓY ℓ) ℓᴰ)
      interp-eqnᴰ eqn eqn-holds = {gamma : Y → ⟨ s ⟩}
        → (gammaᴰ : (z : Y) → eltᴰ (gamma z))
        → interpᴰ gamma gammaᴰ (eqn .fst)
                ≡[ eqn-holds gamma ]
          interpᴰ gamma gammaᴰ (eqn .snd)



  -- Local sections
  ------------------
  module _ {M : PreStructure ℓ} {N : PreStructure ℓ'}
    (ϕ : PreStructHom _ M N)
    (Nᴰ : PreStructureᴰ N ℓNᴰ)
    where

    private
      module M = PreStructureStr (M .snd)
      module N = PreStructureStr (N .snd)
      module Nᴰ = PreStructureᴰ Nᴰ
      module ϕ = PreStructHom ϕ

    record LocalSectionᴾ : Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓ ℓNᴰ)) where
      field
        f : ∀ (z : ⟨ M ⟩) → Nᴰ.eltᴰ (ϕ.f z)
        ls : ∀ (x : X) (vars : (ar x) → ⟨ M ⟩)
          → (f (M.op x vars)) Nᴰ.≡[ ϕ.is-hom vars ] (Nᴰ.opᴰ x (f ∘ vars))


  -- Global sections
  -------------------
  module _ {M : PreStructure ℓ} (Mᴰ : PreStructureᴰ M ℓMᴰ) where
    GlobalSectionᴾ : Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓ) ℓMᴰ)
    GlobalSectionᴾ = LocalSectionᴾ (idHom Σ M) Mᴰ


  -- Weakening
  -------------
  module _ (M : PreStructure ℓ) (N : PreStructure ℓ') where

    private
      module M = PreStructureStr (M .snd)
      module N = PreStructureStr (N .snd)

    wkn-pre : PreStructureᴰ M ℓ'
    wkn-pre .PreStructureᴰ.eltᴰ _ = ⟨ N ⟩
    wkn-pre .PreStructureᴰ.opᴰ x {vars} varsᴰ = N.op x varsᴰ
    wkn-pre .PreStructureᴰ.isSetEltᴰ = N.is-set


  -- Displayed homomorphisms
  ---------------------------
  module _ {M : PreStructure ℓ} {N : PreStructure ℓ'}
    (ϕ : PreStructHom _ M N)
    (Mᴰ : PreStructureᴰ M ℓMᴰ) (Nᴰ : PreStructureᴰ N ℓNᴰ)
    where

    private
      module M = PreStructureStr (M .snd)
      module N = PreStructureStr (N .snd)
      module ϕ = PreStructHom ϕ
      module Mᴰ = PreStructureᴰ Mᴰ
      module Nᴰ = PreStructureᴰ Nᴰ

    record PreStructHomᴰ : Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓ (ℓ-max ℓMᴰ ℓNᴰ))) where
      field
        fᴰ : ∀ {x : ⟨ M ⟩} → Mᴰ.eltᴰ x → Nᴰ.eltᴰ (ϕ.f x)
        is-homᴰ : ∀ {x : X} {vars : ar x → ⟨ M ⟩}
          → (varsᴰ : (z : ar x) → Mᴰ.eltᴰ (vars z))
          → fᴰ (Mᴰ.opᴰ x varsᴰ) Nᴰ.≡[ ϕ.is-hom vars ] Nᴰ.opᴰ x (fᴰ ∘ varsᴰ)



module _ {ℓX ℓar ℓE ℓq : Level} (T : AlgTheory ℓX ℓar ℓE ℓq) where

  open AlgTheory T using (σ ; eqns)
  open Sig σ
  open Signature
  -- private module eqns = Eqns eqns

  -- Displayed Structures
  ------------------------
  record Structureᴰ (M : Structure σ eqns ℓ) ℓᴰ
    : Type (ℓ-max (ℓ-max ℓ (ℓ-suc ℓᴰ)) (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓE ℓq))) where

    private module M = StructureStr (M .snd)
    |M| : PreStructure σ ℓ
    |M| = ⟨ M ⟩ , M.s

    field
      -- A family indexed by elements of M
      sᴰ : PreStructureᴰ σ |M| ℓᴰ

    open PreStructureᴰ sᴰ public
    field

      -- For each "syntactic" equation e of the structure M, we have a
      -- semantic equation displayed over the interpretation of e in M.
      eqns-holdᴰ : (e : eqns.E) {gamma : eqns.q e → ⟨ M ⟩}
        → (gammaᴰ : (z : eqns.q e) → eltᴰ (gamma z))
        → interpᴰ σ (eqns.q e) |M| sᴰ gamma gammaᴰ (eqns.lhs e)
            ≡[ M.eqns-hold e gamma ]
          interpᴰ σ (eqns.q e) |M| sᴰ gamma gammaᴰ (eqns.rhs e)

    foo :
      (e : eqns.E)
      → (g : eqns.q e → ⟨ M ⟩)
      → (gᴰ : (m : ⟨ M ⟩) → eltᴰ m)
      → gᴰ (interp σ (eqns.q e) ⟨ M ⟩ (M .snd .StructureStr.s) g (eqns.lhs e))
          ≡[ M.eqns-hold e g ]
        gᴰ (interp σ (eqns.q e) ⟨ M ⟩ (M .snd .StructureStr.s) g (eqns.rhs e))
    foo = {!!}


  open Structureᴰ

  -- Local sections
  ------------------
  module _ {M : Structure σ eqns ℓ} {N : Structure σ eqns ℓ'}
    (ϕ : StructHom T M N)
    (Nᴰ : Structureᴰ N ℓNᴰ)
    where

    private
      module M = StructureStr (M .snd)
      module N = StructureStr (N .snd)
      module Nᴰ = Structureᴰ Nᴰ
      module ϕ = PreStructHom ϕ

    LocalSection : Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓ) ℓNᴰ)
    LocalSection = LocalSectionᴾ σ ϕ Nᴰ.sᴰ

{-
    record LocalSection : Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓ ℓNᴰ)) where
      field
        f : ∀ (z : ⟨ M ⟩) → Nᴰ.eltᴰ (ϕ.f z)
        ls : ∀ (x : X) (vars : (ar x) → ⟨ M ⟩)
          → (f (M.op x vars)) Nᴰ.≡[ ϕ.is-hom vars ] (Nᴰ.opᴰ x (f ∘ vars))
-}


  -- Global sections
  -------------------
  module _ {M : Structure σ eqns ℓ} (Mᴰ : Structureᴰ M ℓMᴰ) where
    private module Mᴰ = Structureᴰ Mᴰ
    
    GlobalSection : Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓ) ℓMᴰ)
    GlobalSection = GlobalSectionᴾ σ (Mᴰ.sᴰ)

    -- GlobalSection = LocalSection (idHom Σ eqns M) Mᴰ


{-

  -- Weakening
  -------------
  module _ (M : Structure eqns ℓ) (N : Structure eqns ℓ') where

    private
      module M = StructureStr (M .snd)
      module N = StructureStr (N .snd)

    wkn-p : PreStructureᴰ (Structure→PreStructure M) ℓ'
    wkn-p .PreStructureᴰ.eltᴰ _ = ⟨ N ⟩
    wkn-p .PreStructureᴰ.opᴰ x {vars} varsᴰ = N.op x varsᴰ
    wkn-p .PreStructureᴰ.isSetEltᴰ = N.is-set

    lem : ∀ e gamma gammaᴰ (t : Term (eqns.q e))
      → interpᴰ (eqns.q e) (Structure→PreStructure M) wkn-pre gamma gammaᴰ t
      ≡ interp (eqns.q e) ⟨ N ⟩ N.s gammaᴰ t
    lem e gamma gammaᴰ (var y) = refl
    lem e gamma gammaᴰ (oper x vars) =
      cong₂ N.op refl (funExt (λ z → lem e gamma gammaᴰ (vars z)))

    wkn : Structureᴰ M ℓ'
    wkn .sᴰ = wkn-pre
    wkn .eqns-holdᴰ e {gamma} gammaᴰ =
        lem e gamma gammaᴰ (eqns.lhs e)
      ∙ N.eqns-hold e gammaᴰ
      ∙ {!!}


  -- Displayed homomorphisms
  ---------------------------
  module _ {M : Structure eqns ℓ} {N : Structure eqns ℓ'}
    (ϕ : StructHom _ eqns M N)
    (Mᴰ : Structureᴰ M ℓMᴰ) (Nᴰ : Structureᴰ N ℓNᴰ)
    where

    private
      module M = StructureStr (M .snd)
      module N = StructureStr (N .snd)
      module ϕ = StructHom→module ϕ
      module Mᴰ = Structureᴰ Mᴰ
      module Nᴰ = Structureᴰ Nᴰ

    record StructHomᴰ : Type (ℓ-max (ℓ-max ℓX ℓar) (ℓ-max ℓ (ℓ-max ℓMᴰ ℓNᴰ))) where
      field
        fᴰ : ∀ {x : ⟨ M ⟩} → Mᴰ.eltᴰ x → Nᴰ.eltᴰ (ϕ.f x)
        is-homᴰ : ∀ {x : X} {vars : ar x → ⟨ M ⟩}
          → (varsᴰ : (z : ar x) → Mᴰ.eltᴰ (vars z))
          → fᴰ (Mᴰ.opᴰ x varsᴰ) Nᴰ.≡[ ϕ.is-hom vars ] Nᴰ.opᴰ x (fᴰ ∘ varsᴰ)


-}
