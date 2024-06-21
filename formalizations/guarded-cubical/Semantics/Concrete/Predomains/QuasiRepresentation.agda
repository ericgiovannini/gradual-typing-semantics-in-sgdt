{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomains.QuasiRepresentation (k : Clock) where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid.Base



open import Common.Common
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k

open import Semantics.Concrete.Predomains.Perturbations k

open import Cubical.HigherCategories.ThinDoubleCategory.ThinDoubleCat


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓc ℓc' ℓd ℓd' : Level
  
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
   
    ℓc₁ ℓc₂ ℓc₃  : Level

    ℓMA₁ ℓMA₂ ℓMA₃ : Level


-- To define the horizontal morphisms of value and computation types,
-- we first define the notion of a left-quasi-representation and
-- right-quasi-representation.
--
-- This informally states that the squares necessary for graduality
-- commute, up to the insertions of specified perturbations.
--
-- A quasi-representation for a relation c between predomains A and A'
-- is parameterized by a pair of monoids MA and MA' and monoid
-- homomorphisms iA : MA → Endo A and iA' : MA' → Endo A' (see the
-- Perturbations module for the definition of Endo).
--
-- We additionally require that the relation c has a push-pull
-- structure Πc with respect to (MA, iA, MA', iA') which says
-- intuitively that we may turn perturbations on A into perturbations
-- on A' and vice versa, and that doing so produces a square with left
-- and right edges equal to the original and pushed/pulled perturbation.
--
-- The same requirement holds for computation relations.



-- Left quasi-representation of a predomain relation
----------------------------------------------------
record LeftRepV
  (A  : PosetBisim ℓA  ℓ≤A  ℓ≈A)  (MA  : Monoid ℓMA)  (iA  : MonoidHom MA  (Endo A))
  (A' : PosetBisim ℓA' ℓ≤A' ℓ≈A') (MA' : Monoid ℓMA') (iA' : MonoidHom MA' (Endo A'))
  (c : PBRel A A' ℓc)
  (Πc : PushPullV A MA iA A' MA' iA' c) :
  Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓ≤A ℓ≤A'))
                     (ℓ-max (ℓ-max ℓ≈A ℓ≈A') (ℓ-max ℓMA ℓMA'))) ℓc) where

  field
    e : PBMor A A'
    δl : ⟨ MA ⟩
    δr : ⟨ MA' ⟩

    --  UpL:                   UpR:
    --
    --        c                   ⊑A
    --   A o----* A'          A o----* A
    --   |        |           |        |
    -- e |        | δr    δl  |        | e
    --   v        v           v        v
    --   A' o---* A'          A o----* A'
    --       ⊑A'                  c

    UpL : PBSq c (idPRel A') e (ptbV MA' iA' δr)
    UpR : PBSq (idPRel A) c (ptbV MA iA δl) e


-- Right quasi-representation of an error domain relation
---------------------------------------------------------

record RightRepC
  (B  : ErrorDomain ℓB  ℓ≤B  ℓ≈B)  (MB  : Monoid ℓMB)  (iB  : MonoidHom MB  (CEndo B))
  (B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B') (MB' : Monoid ℓMB') (iB' : MonoidHom MB' (CEndo B'))
  (d : ErrorDomRel B B' ℓd)
  (Πd : PushPullC B MB iB B' MB' iB' d) :
  
  Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓ≤B ℓ≤B')) (ℓ-max (ℓ-max ℓ≈B ℓ≈B') (ℓ-max ℓMB ℓMB'))) ℓd) where


  field
    p : ErrorDomMor B' B
    δl : ⟨ MB ⟩
    δr : ⟨ MB' ⟩

    --  DnR:                   DnL:
    --
    --         d                   ⊑B'
    --    B o----* B'         B' o---* B'
    --    |        |          |        |
    -- δl |        | p      p |        | δr
    --    v        v          v        v
    --    B o----* B          B o----* B'
    --        ⊑B                   d

    DnR : ErrorDomSq d (idEDRel B) (ptbC MB iB δl) p
    DnL : ErrorDomSq (idEDRel B') d p (ptbC MB' iB' δr)


-- We dually define left representations for error domain relations,
-- and right representations for predomain relations:

-- TODO





-- Left quasi-representations compose
module ComposeLeftRepV
  (A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁)
  (A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂)
  (A₃ : PosetBisim ℓA₃ ℓ≤A₃ ℓ≈A₃)
  (MA₁ : Monoid ℓMA₁)  (iA₁ : MonoidHom MA₁ (Endo A₁))
  (MA₂ : Monoid ℓMA₂)  (iA₂ : MonoidHom MA₂ (Endo A₂))
  (MA₃ : Monoid ℓMA₃)  (iA₃ : MonoidHom MA₃ (Endo A₃))
  (c  : PBRel A₁ A₂ ℓc)  (Πc  : PushPullV A₁ MA₁ iA₁ A₂ MA₂ iA₂ c)
  (ρc : LeftRepV A₁ MA₁ iA₁ A₂ MA₂ iA₂ c Πc)
  (c' : PBRel A₂ A₃ ℓc') (Πc' : PushPullV A₂ MA₂ iA₂ A₃ MA₃ iA₃ c')
  (ρc' : LeftRepV A₂ MA₂ iA₂ A₃ MA₃ iA₃ c' Πc')
  where

  Πcc' = PushPullV-Compose.compPPV MA₁ iA₁ MA₂ iA₂ MA₃ iA₃ c Πc c' Πc'

  module ρc  = LeftRepV ρc
  module ρc' = LeftRepV ρc'
  module Πc  = PushPullV Πc
  module Πc' = PushPullV Πc
  module MA₁ = MonoidStr (MA₁ .snd)
  module MA₂ = MonoidStr (MA₂ .snd)
  module MA₃ = MonoidStr (MA₃ .snd)

  open LeftRepV

  compose : LeftRepV A₁ MA₁ iA₁ A₃ MA₃ iA₃ (c ⊙ c') Πcc'
  compose .e = ρc'.e ∘p ρc.e
  compose .δl = {!!}
  compose .δr = ρc'.δr MA₃.· (Πc'.push .fst ρc.δr)
  compose .UpL = {!!}
  compose .UpR = {!!}

  -- ptb (p · q) = ptb p ∘ ptb q



-- Right quasi-representations compose
