{-# OPTIONS --polarity #-}

module Cubical.Algebra.Structures.Free where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Bool as Bool hiding (elim)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥ hiding (elim)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Structures.Base
open import Cubical.Algebra.Structures.Morphism
open import Cubical.Algebra.Structures.Displayed
open import Cubical.Algebra.Structures.AlgebraicTheory

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓᴰ ℓᴰ' : Level
    ℓM ℓN ℓP : Level
    ℓMᴰ ℓNᴰ ℓPᴰ : Level
    ℓA ℓB : Level


module _ {ℓX ℓar : Level} (σ : Sig ℓX ℓar) where

  open Signature

  module _ {ℓ : Level} (A : Type ℓ) where

    -- Terms form a PreStructure.
    Term-As-Prestructure : PreStructure σ (ℓ-max (ℓ-max ℓX ℓar) ℓ)
    Term-As-Prestructure .fst = Term σ A
    Term-As-Prestructure .snd .PreStructureStr.op = oper
    Term-As-Prestructure .snd .PreStructureStr.is-set = {!!}

    -- Universal property


module _ {ℓX ℓar ℓE ℓq : Level}
  (T : AlgTheory ℓX ℓar ℓE ℓq)
  where

  open AlgTheory T
  open Signature
  open Sig σ




  -- The free structure on a set A, i.e., the left adjoint to the
  -- forgetful functor from the category of structures to sets.
  module _ {ℓ : Level} (A : Type ℓ) where

    data |Free| : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) ℓ)
    Free-P : PreStructureStr σ |Free|
    Free : Structure σ eqns (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq) ℓ)

    data |Free| where

      -- generator
      ⟦_⟧ : A → |Free|

      -- operations
      opFree : (x : X) → (ar x → |Free|) → |Free|

      -- equations
      eqFree : (e : eqns.E)
         → (gamma : eqns.q e → |Free|)
         → interp σ (eqns.q e) |Free| Free-P gamma (eqns.lhs e) ≡
           interp σ (eqns.q e) |Free| Free-P gamma (eqns.rhs e) 

      -- isSet
      trunc : isSet |Free|


    Free-P .PreStructureStr.op = opFree
    Free-P .PreStructureStr.is-set = trunc

    Free .fst = |Free|
    Free .snd .StructureStr.s = Free-P
    Free .snd .StructureStr.eqns-hold = eqFree


  module _ (A : Type ℓ) where

    Term→Free : Term σ A → |Free| A
    Term→Free (var y) = ⟦ y ⟧
    Term→Free (oper x vars) = opFree x (λ z → Term→Free (vars z))


  module _ (A : Type ℓA) (B : ⟨ Free A ⟩ → Type ℓB)
    (⟦_⟧* : (a : A) → B ⟦ a ⟧)
    (op* : {x : X} → {vars : ar x → |Free| A}
      → ((z : ar x) → B (vars z))
      → B (opFree x vars))
    (interp* : {ℓY : Level} {Y : Type ℓY}
        → (f : (Y → ⟨ Free A ⟩))
        → (fᴰ : (y : Y) → B (f y))
        → (t : Term σ Y)
        → B (interp σ Y ⟨ Free A ⟩ (Free-P A) f t))
    (eq* : {e : eqns.E} {vars : eqns.q e → |Free| A}
      → (varsᴰ : (z : eqns.q e) → B (vars z))
      → PathP (λ i → B (eqFree e vars i))
          (interp* vars varsᴰ (eqns.lhs e))
          (interp* vars varsᴰ (eqns.rhs e)))
    (trunc* : ∀ y → isSet (B y))
    where

    elim : (y : ⟨ Free A ⟩) → B y
    elim ⟦ a ⟧ = ⟦ a ⟧*
    elim (opFree x vars) = op* (λ z → elim (vars z))
    elim (eqFree e gamma i) =
      let H = eq* (λ z → elim (gamma z)) in
      (sym (lem (eqns.lhs e)) ◁ H ▷ lem (eqns.rhs e)) i
      where
        lem : ∀ t →
          interp* {Y = eqns.q e} gamma (λ z → elim (gamma z)) t ≡
          elim (interp σ (eqns.q e) ⟨ Free A ⟩ (Free-P A) gamma t)
        lem (var y) = {!!}
        lem (oper x vars) = {!!}
    elim (trunc x y p q i j) = {!!}


  -- Universal property of the free T-Structure.
  module _  (A : Type ℓA) (Mᴰ : Structureᴰ T (Free A) ℓᴰ) where

    private
      module Mᴰ = Structureᴰ Mᴰ
      module Mᴰ-Pre = PreStructureᴰ (Mᴰ.sᴰ)

    module _ (iA : (a : A) → Mᴰ.eltᴰ ⟦ a ⟧) where

      open LocalSectionᴾ

      elimFree : GlobalSection T Mᴰ
      elimFree .f = aux
        where
          aux : ∀ x → Mᴰ.eltᴰ x
          commutes : ∀ e gamma (t : Term σ (eqns.q e)) →
                     interpᴰ _ (eqns.q e) _ Mᴰ.sᴰ gamma (λ z → aux (gamma z)) t
                   ≡ aux (interp _ (eqns.q e) _ (Free-P _) gamma t)
          commutes e gamma (var y) = refl
          commutes e gamma (oper x vars) = {!!} -- (λ j → Mᴰ.opᴰ x (λ z → commutes (vars z) j))

          commutes' : ∀ e gamma (t : Term σ (eqns.q e)) → (f : |Free| A) →
                     (eq : f ≡ (interp _ (eqns.q e) _ (Free-P _) gamma t)) →
                     PathP (λ i → Mᴰ.eltᴰ (eq (~ i)))
                       (interpᴰ _ (eqns.q e) _ Mᴰ.sᴰ gamma (λ z → aux (gamma z)) t)
                       (aux f)
          commutes' e gamma (var x) f eq = {!!}
          commutes' e gamma (oper x vars) f eq = {!!}
          --commutes' e gamma (var y) f eq = refl
          --commutes' e gamma (oper x vars) f eq = {!!} -- (λ j → Mᴰ.opᴰ x (λ z → commutes (vars z) j))
         
          aux ⟦ a ⟧ = iA a
          aux (opFree x vars) = Mᴰ.opᴰ x (λ z → aux (vars z))
          aux (eqFree e gamma i) = let H = Mᴰ.eqns-holdᴰ e (λ z → aux (gamma z)) in
            -- (sym (commutes e (λ z → gamma z) (eqns.lhs e)) ◁ H ▷ commutes e (λ z → gamma z) (eqns.rhs e)) i
              ({!!}  ◁ H ▷ commutes' e gamma (eqns.rhs e)
              ((Free A .snd .StructureStr.eqns-hold e (λ z → gamma z)) i1)
              (λ i₁ → Free A .snd .StructureStr.eqns-hold e (λ z → gamma z) i1))
              i
            where
             
          aux (trunc x y p q i j) =
            isOfHLevel→isOfHLevelDep 2 (λ x → Mᴰ.isSetEltᴰ)
              (aux x) (aux y)
              (cong aux p) (cong aux q)
              (trunc x y p q)
              i j
            
      elimFree .ls = {!!}



  module _ (A : Type ℓA) (Mᴰ : Structureᴰ T (Free A) ℓᴰ) where
    -- To construct a function from the free Structure into a
    -- displayed *Structure*, it is sufficient to construct a function
    -- from the free PreStructure into the underlying displayed
    -- Prestructure, and then show that the map respects the
    -- equations.

    private module Mᴰ = Structureᴰ Mᴰ
   
    module _
      (Pᴰ : PreStructureᴰ σ (Term-As-Prestructure σ A) ℓᴰ')
      (g : GlobalSectionᴾ σ Mᴰ.sᴰ)
      where
      
      private module Pᴰ = PreStructureᴰ Pᴰ
      private module g = LocalSectionᴾ g

      elim-free : (x : ⟨ Free A ⟩) → Mᴰ.eltᴰ x

      lem : ∀ (Y : Type ℓ) (gamma : Y → ⟨ Free A ⟩) (t : Term σ Y)
        → elim-free (interp σ Y ⟨ Free A ⟩ _ gamma t)
        ≡ interpᴰ σ Y _ Mᴰ.sᴰ gamma (λ y → elim-free (gamma y)) t

      elim-free ⟦ a ⟧ = g.f ⟦ a ⟧
      elim-free (opFree x vars) = g.f (opFree x vars)
      elim-free (eqFree e gamma i) =
        let H = Mᴰ.eqns-holdᴰ e (λ z → elim-free (gamma z)) in {!!}
         -- Mᴰ.foo e gamma elim-free i
         -- (lem (eqns.q e) gamma (eqns.lhs e) ◁ H ▷ sym (lem (eqns.q e) gamma (eqns.rhs e))) i
      elim-free (trunc x x₁ x₂ y i i₁) = {!!}


      lem Y gamma (var y) = {!elim-free ⟦ _ ⟧!}
      -- {!(interp σ Y _ _ gamma (var y))!}
      lem Y gamma (oper x vars) = {!!}
      -- {!interp σ Y _ (Free-P A) gamma (oper x vars)!}


      {-
      test : ∀ (x : ⟨ Free A ⟩)
        → elim-free x ≡ g.f x
      test ⟦ x ⟧ = {!refl!}
      test (opFree x x₁) = {!!}
      test (eqFree e gamma i) = {!!}
      test (trunc x x₁ x₂ y i i₁) = {!!}
      -}


  module _ (A : Type ℓA) (Mᴰ : PreStructureᴰ σ (|Free| A , Free-P A) ℓᴰ) where


{-
  -- Universal property of the free T-Structure.
  module _  (A : Type ℓA) (Mᴰ : Structureᴰ T (Free A) ℓᴰ) where

    private
      module Mᴰ = Structureᴰ Mᴰ
      module Mᴰ-Pre = PreStructureᴰ (Mᴰ.sᴰ)

    module _ (iA : (a : A) → Mᴰ.eltᴰ ⟦ a ⟧) where

      open LocalSectionᴾ

      elim : GlobalSection T Mᴰ
      elim .f = aux
        where
          aux : ∀ x → Mᴰ.eltᴰ x
          aux ⟦ a ⟧ = iA a
          aux (opFree x vars) = Mᴰ.opᴰ x (λ z → aux (vars z))
          aux (eqFree e gamma i) = let H = Mᴰ.eqns-holdᴰ e (λ z → aux (gamma z)) in
            (sym (commutes (eqns.lhs e)) ◁ H ▷ commutes (eqns.rhs e)) i           
            where
              commutes : ∀ (t : Term σ (eqns.q e)) →
                         interpᴰ _ (eqns.q e) _ Mᴰ.sᴰ gamma (λ z → aux (gamma z)) t
                       ≡ aux (interp _ (eqns.q e) _ (Free-P _) gamma t)
              commutes (var y) = refl
              commutes (oper x vars) = (λ j → Mᴰ.opᴰ x (λ z → commutes (vars z) j))
          aux (trunc x y p q i j) =
            isOfHLevel→isOfHLevelDep 2 (λ x → Mᴰ.isSetEltᴰ)
              (aux x) (aux y)
              (cong aux p) (cong aux q)
              (trunc x y p q)
              i j
            
      elim .ls = {!!}
-}

