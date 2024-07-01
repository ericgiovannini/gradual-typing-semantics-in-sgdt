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

open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Predomains.Perturbations k

--open import Cubical.HigherCategories.ThinDoubleCategory.ThinDoubleCat


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
    ℓMB₁ ℓMB₂ ℓMB₃ : Level


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


-- record HasRightRepC
--   (B  : ErrorDomain ℓB  ℓ≤B  ℓ≈B)  
--   (B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B') 
--   (d : ErrorDomRel B B' ℓd)
  
--   field
--     MB : Monoid
--     MB' : Monoid
--     iB : MonoidHom
--     iB' : MonoidHom 
--     Π : PushPullC B B'


----------------------------------------------------------------
-- We dually define left representations for error domain relations,
-- and right representations for predomain relations:


-- Left quasi-representation of an error domain relation
--------------------------------------------------------
record LeftRepC
  (B  : ErrorDomain ℓB  ℓ≤B  ℓ≈B)  (MB  : Monoid ℓMB)  (iB  : MonoidHom MB  (CEndo B))
  (B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B') (MB' : Monoid ℓMB') (iB' : MonoidHom MB' (CEndo B'))
  (d : ErrorDomRel B B' ℓd)
  (Πd : PushPullC B MB iB B' MB' iB' d) :
  Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓ≤B ℓ≤B'))
                     (ℓ-max (ℓ-max ℓ≈B ℓ≈B') (ℓ-max ℓMB ℓMB'))) ℓd) where

  field
    e : ErrorDomMor B B'
    δl : ⟨ MB ⟩
    δr : ⟨ MB' ⟩
    --  UpL:                   UpR:
    --
    --        d                  ⊑LB
    --   B o----* B'         B o----* B
    --   |        |          |        |
    -- e |        | δr    δl |        | e
    --   v        v          v        v
    --   B' o---* B'         B o----* B'
    --        d                   d
    UpL : ErrorDomSq d (idEDRel B') e (ptbC MB' iB' δr)
    UpR : ErrorDomSq (idEDRel B) d (ptbC MB iB δl) e
    --  UpL:                   UpR:
    --
    --       ⊑LB'                ⊑LB
    --   B' o---* B'         B o----* B'
    --   |        |          |        |
    -- p |        | δr    δl |        | p
    --   v        v          v        v
    --   B o----* B'         B o----* B
    --        d                   d


-- Right quasi-representation of a predomain relation
------------------------------------------------------
record RightRepV
  (A  : PosetBisim ℓA  ℓ≤A  ℓ≈A)  (MA  : Monoid ℓMA)  (iA  : MonoidHom MA  (Endo A))
  (A' : PosetBisim ℓA' ℓ≤A' ℓ≈A') (MA' : Monoid ℓMA') (iA' : MonoidHom MA' (Endo A'))
  (c : PBRel A A' ℓc)
  (Πc : PushPullV A MA iA A' MA' iA' c) :
  Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓ≤A ℓ≤A'))
                     (ℓ-max (ℓ-max ℓ≈A ℓ≈A') (ℓ-max ℓMA ℓMA'))) ℓc) where

  field
    p : PBMor A' A
    δl : ⟨ MA ⟩
    δr : ⟨ MA' ⟩

    --  DnL:                   DnR:
    --
    --       ⊑A'                  c
    --   A' o---* A'          A o----* A'
    --   |        |           |        |
    -- p |        | δr     δl |        | p
    --   v        v           v        v
    --   A o----* A'          A o----* A
    --       c                    ⊑A

    DnL : PBSq (idPRel A') c p (ptbV MA' iA' δr)
    DnR : PBSq c (idPRel A) (ptbV MA iA δl) p



-- Quasi-order equivalence of value relations
-----------------------------------------------

record QuasiOrderEquivV
  (A  : PosetBisim ℓA  ℓ≤A  ℓ≈A)  (MA  : Monoid ℓMA)  (iA  : MonoidHom MA  (Endo A))
  (A' : PosetBisim ℓA' ℓ≤A' ℓ≈A') (MA' : Monoid ℓMA') (iA' : MonoidHom MA' (Endo A'))
  (c : PBRel A A' ℓc) (c' : PBRel A A' ℓc') :
  Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓ≤A ℓ≤A'))
                     (ℓ-max (ℓ-max ℓ≈A ℓ≈A') (ℓ-max ℓMA ℓMA'))) (ℓ-max ℓc ℓc')) 
  where

  field
    δ₁  : ⟨ MA ⟩
    δ₁' : ⟨ MA' ⟩
    sq-c-c' : PBSq c c' (ptbV MA iA δ₁) (ptbV MA' iA' δ₁')

    δ₂  : ⟨ MA ⟩
    δ₂' : ⟨ MA' ⟩
    sq-c'-c : PBSq c' c (ptbV MA iA δ₂) (ptbV MA' iA' δ₂')



-- Quasi-order equivalence of computation relations
----------------------------------------------------

record QuasiOrderEquivC
  (B  : ErrorDomain ℓB  ℓ≤B  ℓ≈B)  (MB  : Monoid ℓMB)  (iB  : MonoidHom MB  (CEndo B))
  (B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B') (MB' : Monoid ℓMB') (iB' : MonoidHom MB' (CEndo B'))
  (d : ErrorDomRel B B' ℓd) (d' : ErrorDomRel B B' ℓd') :
  Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓ≤B ℓ≤B'))
                     (ℓ-max (ℓ-max ℓ≈B ℓ≈B') (ℓ-max ℓMB ℓMB'))) (ℓ-max ℓd ℓd')) 
  where

  field
    δ₁  : ⟨ MB ⟩
    δ₁' : ⟨ MB' ⟩
    sq-d-d' : ErrorDomSq d d' (ptbC MB iB δ₁) (ptbC MB' iB' δ₁')

    δ₂  : ⟨ MB ⟩
    δ₂' : ⟨ MB' ⟩
    sq-d'-d : ErrorDomSq d' d (ptbC MB iB δ₂) (ptbC MB' iB' δ₂')


----------------------------------------------------------------------

-- Important lemma: If two error domain relations d and d' between B
-- and B' are left-representable by the same embedding morphism e,
-- then d is quasi-order-equivalent to d'.

module LeftRepC-Lemma
  (B  : ErrorDomain ℓB  ℓ≤B  ℓ≈B)  (MB  : Monoid ℓMB)  (iB  : MonoidHom MB  (CEndo B))
  (B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B') (MB' : Monoid ℓMB') (iB' : MonoidHom MB' (CEndo B'))
  (d : ErrorDomRel B B' ℓd) (d' : ErrorDomRel B B' ℓd')
  (Πd  : PushPullC B MB iB B' MB' iB' d)
  (Πd' : PushPullC B MB iB B' MB' iB' d')
  (ρd  : LeftRepC B MB iB B' MB' iB' d  Πd)
  (ρd' : LeftRepC B MB iB B' MB' iB' d' Πd')
  (eq : ρd .LeftRepC.e ≡ ρd' .LeftRepC.e) where

    -- The first square is formed by horizontally composing the
    -- following squares, and using the fact that composing with the
    -- homogeneous relations is the identity.
    
    --           ⊑B                    d
    --       B o----* B           B o----* B'
    --       |        |           |        |
    -- d'.δl | d'.UpR | e      e  | d.UpL  | d.δr
    --       v        v           v        v
    --       B o----* B'          B' o---* B'
    --           d'                   ⊑B'

    -- The second square is formed similarly:


    --          ⊑B                    d'
    --      B o----* B           B o----* B'
    --      |        |           |        |
    -- d.δl | d.UpR  | e      e  | d'.UpL | d'.δr
    --      v        v           v        v
    --      B o----* B'          B' o---* B'
    --          d                    ⊑B'
    
    
    open QuasiOrderEquivC
    module MB = MonoidStr (MB .snd)
    module MB' = MonoidStr (MB' .snd)
    module iB = IsMonoidHom (iB .snd)
    module iB' = IsMonoidHom (iB' .snd)
    module ρd = LeftRepC ρd
    module ρd' = LeftRepC ρd'

    equiv-d-d' : QuasiOrderEquivC B MB iB B' MB' iB' d d'
    equiv-d-d' .δ₁ = ρd'.δl
    equiv-d-d' .δ₁' = ρd.δr
    equiv-d-d' .sq-d-d' = composed123
      where
        α1 : ErrorDomSq d (idEDRel B ⊙ed d) IdE IdE
        α1 = sq-d-idB⊙d d

        α2 : ErrorDomSq (idEDRel B ⊙ed d) (d' ⊙ed idEDRel B') (ptbC MB iB ρd'.δl) (ptbC MB' iB' ρd.δr)
        α2 = _∘esqh_ {ϕ₁ =  (ptbC MB iB ρd'.δl)} {ϕ₂ = ρd' .LeftRepC.e} {ϕ₃ = (ptbC MB' iB' ρd.δr)}
               ρd'.UpR
               (transport (λ i → ErrorDomSq d (idEDRel B') (eq i) (ptbC MB' iB' ρd.δr)) ρd.UpL)

        α3 : ErrorDomSq (d' ⊙ed idEDRel B') d' IdE IdE
        α3 = sq-d⊙B'-d d'

        composed12 : ErrorDomSq d (d' ⊙ed idEDRel B') ((ptbC MB iB ρd'.δl) ∘ed IdE) ((ptbC MB' iB' ρd.δr) ∘ed IdE)
        composed12 = ED-CompSqV
          {d₁ = d} {d₂ = (idEDRel B ⊙ed d)} {d₃ = (d' ⊙ed idEDRel B')}
          {ϕ₁ = IdE} {ϕ₁' = IdE} {ϕ₂ = (ptbC MB iB ρd'.δl)} {ϕ₂' = (ptbC MB' iB' ρd.δr)}
          α1 α2

        composed123 : ErrorDomSq d d' (IdE ∘ed (ptbC MB iB ρd'.δl) ∘ed IdE) (IdE ∘ed (ptbC MB' iB' ρd.δr) ∘ed IdE)
        composed123 = ED-CompSqV
          {d₁ = d} {d₂ = (d' ⊙ed idEDRel B')} {d₃ = d'}
          {ϕ₁ = (ptbC MB iB ρd'.δl)} {ϕ₁' = (ptbC MB' iB' ρd.δr)} {ϕ₂ = IdE} {ϕ₂' = IdE}
          composed12 α3
       
    
    equiv-d-d' .δ₂ = ρd.δl
    equiv-d-d' .δ₂' = ρd'.δr
    equiv-d-d' .sq-d'-d = {!!}
      where
        α1 : {!!}
        α1 = {!!}


module Compose (A : PosetBisim ℓA ℓ≤A ℓ≈A) (M : Monoid ℓM) (iA : MonoidHom M (Endo A)) where
  module M = MonoidStr (M .snd)
  module iA = IsMonoidHom (iA .snd)
  lemma : (m₁ m₂ : fst M) → ptbV M iA (m₁ M.· m₂) ≡ ptbV M iA m₁ ∘p ptbV M iA m₂ --  ∘p ptbV M iA m₃  M.· m₃
  lemma m₁ m₂ = eqPBMor {!!} {!!} {!!}

  lemma2 : (m₁ m₂ m₃ : fst M) → ptbV M iA (m₁ M.· m₂ M.· m₃) ≡ ptbV M iA m₁ ∘p ptbV M iA m₂ ∘p ptbV M iA m₃
  lemma2 m₁ m₂ m₃ = lemma (m₁ M.· m₂) m₃ ∙ cong (λ x → x ∘p ptbV M iA m₃) (lemma m₁ m₂)

module ComposeC (B : ErrorDomain ℓB ℓ≤B ℓ≈B) (M : Monoid ℓMB) (iB : MonoidHom M (CEndo B)) where
  module M = MonoidStr (M .snd)
  module iB = IsMonoidHom (iB .snd)
  lemma : (m₁ m₂ : fst M) → ptbC M iB (m₁ M.· m₂) ≡ ptbC M iB m₁ ∘ed ptbC M iB m₂ --  ∘p ptbV M iA m₃  M.· m₃
  lemma m₁ m₂ = {!!}

  lemma2 : (m₁ m₂ m₃ : fst M) → ptbC M iB (m₁ M.· m₂ M.· m₃) ≡ ptbC M iB m₁ ∘ed ptbC M iB m₂ ∘ed ptbC M iB m₃
  lemma2 m₁ m₂ m₃ = lemma (m₁ M.· m₂) m₃ ∙ cong (λ x → x ∘ed ptbC M iB m₃) (lemma m₁ m₂)


module ptbVε≡Id (A : PosetBisim ℓA ℓ≤A ℓ≈A) (M : Monoid ℓM) (iA : MonoidHom M (Endo A)) where
  module M = MonoidStr (M .snd)
  module iA = IsMonoidHom (iA .snd)
  lemma : ptbV M iA M.ε ≡ Id
  lemma = eqPBMor (ptbV M iA M.ε) Id {!!}

module ptbCε≡Id (B : ErrorDomain ℓB ℓ≤B ℓ≈B) (M : Monoid ℓMB) (iB : MonoidHom M (CEndo B)) where
  module M = MonoidStr (M .snd)
  module iB = IsMonoidHom (iB .snd)
  lemma : ptbC M iB M.ε ≡ IdE
  lemma = {!!}
  

--------------------------------------------------------------------

-- Identity quasi-representations

module IdLeftRepV
  (A : PosetBisim ℓA ℓ≤A ℓ≈A) (MA : Monoid ℓMA) (iA : MonoidHom MA (Endo A))
  where

  open PushPullV-Id

  idLeftRepV : LeftRepV A MA iA A MA iA (idPRel A) {!idPPV!}
  idLeftRepV = {!!}
  


--------------------------------------------------------------------

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
  module Πc' = PushPullV Πc'
  module MA₁ = MonoidStr (MA₁ .snd)
  module MA₂ = MonoidStr (MA₂ .snd)
  module MA₃ = MonoidStr (MA₃ .snd)
  module iA₃ = IsMonoidHom (iA₃ .snd)

  open LeftRepV

  -- RHS of the sqaure should be ptbV MA₃ iA₃ (ρc'.δr MA₃.· MA₃.ε MA₃.· Πc'.push .fst ρc.δr)
  -- ≡ iA₃ (ρc'.δr) PrePtb∘ iA₃ (MA₃.ϵ) PrePtb∘ iA₃ ...
  -- use ptbV function to get out a composition of predomain vertical morphisms
  -- This is possible becasue iA₃ is a homomorphism (iA₃ ϵ ≡ Id)
  -- (iA₃ (x · y) ≡ iA₃ x ∘ iA₃ y)

  compose : LeftRepV A₁ MA₁ iA₁ A₃ MA₃ iA₃ (c ⊙ c') Πcc'
  compose .e = ρc'.e ∘p Id  ∘p ρc.e
  compose .δl = Πc.pull .fst ρc'.δl MA₁.· MA₁.ε MA₁.· ρc.δl
  compose .δr = ρc'.δr MA₃.· MA₃.ε MA₃.· Πc'.push .fst ρc.δr
  compose .UpL = transport (cong (λ x → PBSq (c ⊙ c') (idPRel A₃) (ρc'.e ∘p Id ∘p ρc.e) x) (sym foo)) res  -- CompSqV (CompSqH α1 α2) (CompSqV id-sq α3) 
    where
      α1 : PBSq c (idPRel A₂) ρc.e (ptbV MA₂ iA₂ ρc.δr)
      α1 = ρc.UpL

      α2 : PBSq c' c' (ptbV MA₂ iA₂ ρc.δr) (ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr))
      α2 = Πc'.pushSq ρc.δr

      id-sq : PBSq (idPRel A₂ ⊙ c') c' Id Id
      id-sq = sq-idA⊙c-c c'

      α3 : PBSq c' (idPRel A₃) ρc'.e (ptbV MA₃ iA₃ ρc'.δr)
      α3 = ρc'.UpL

      compose-α1α2 : PBSq (c ⊙ c') (idPRel A₂ ⊙ c') ρc.e (ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr))
      compose-α1α2 = CompSqH {cᵢ₁ = c} {cᵢ₂ = c'} {cₒ₁ = (idPRel A₂)} {cₒ₂ = c'} {f = ρc.e} {g = (ptbV MA₂ iA₂ ρc.δr)} {h = (ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr))} α1 α2

      compose-id-α3 : PBSq (idPRel A₂ ⊙ c') (idPRel A₃) (ρc'.e ∘p Id)  (ptbV MA₃ iA₃ ρc'.δr ∘p Id)
      compose-id-α3 = CompSqV {c₁ = (idPRel A₂ ⊙ c')} {c₂ = c'} {c₃ = (idPRel A₃)} {f₁ = Id} {g₁ = Id} {f₂ = ρc'.e} {g₂ = (ptbV MA₃ iA₃ ρc'.δr)} id-sq α3

      res : PBSq (c ⊙ c') (idPRel A₃) (ρc'.e ∘p Id ∘p ρc.e)
             (ptbV MA₃ iA₃ ρc'.δr ∘p Id ∘p ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr))
      res = CompSqV {c₁ = (c ⊙ c')} {c₂ = (idPRel A₂ ⊙ c')} {c₃ = (idPRel A₃)} {f₁ = ρc.e} {g₁ = (ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr))} {f₂ = (ρc'.e ∘p Id)} {g₂ = (ptbV MA₃ iA₃ ρc'.δr ∘p Id)} compose-α1α2 compose-id-α3

      foo : ptbV MA₃ iA₃ (ρc'.δr MA₃.· MA₃.ε MA₃.· Πc'.push .fst ρc.δr) ≡ ptbV MA₃ iA₃ ρc'.δr ∘p Id ∘p ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr)
      foo = C.lemma2 ρc'.δr MA₃.ε (Πc'.push .fst ρc.δr) ∙ cong (λ x → ptbV MA₃ iA₃ ρc'.δr ∘p x ∘p ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr)) id.lemma
        where
          module C = Compose A₃ MA₃ iA₃
          module id = ptbVε≡Id A₃ MA₃ iA₃
      
  compose .UpR = transport (cong (λ x → PBSq (idPRel A₁) (c ⊙ c') x (ρc'.e ∘p Id ∘p ρc.e)) (sym foo)) res
    where
      α1 : PBSq (idPRel A₁) c (ptbV MA₁ iA₁ ρc.δl) ρc.e
      α1 = ρc.UpR

      id-sq : PBSq c (c ⊙ idPRel A₂) Id Id
      id-sq = sq-c-c⊙A' c

      αl : PBSq c c (ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl)) (ptbV MA₂ iA₂ ρc'.δl)
      αl = Πc.pullSq ρc'.δl

      αr : PBSq (idPRel A₂) c' (ptbV MA₂ iA₂ ρc'.δl) ρc'.e
      αr = ρc'.UpR

      compose-αl-αr : PBSq (c ⊙ idPRel A₂) (c ⊙ c')
                      (ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl)) ρc'.e
      compose-αl-αr = CompSqH {cᵢ₁ = c} {cᵢ₂ = (idPRel A₂)} {cₒ₁ = c} {cₒ₂ = c'} {f = (ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl))} {g = (ptbV MA₂ iA₂ ρc'.δl) } {h = ρc'.e} αl αr

      compose-id-αlαr : PBSq c (c ⊙ c')
                       (ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl) ∘p Id) (ρc'.e ∘p Id)
      compose-id-αlαr = CompSqV {c₁ = c} {c₂ = (c ⊙ idPRel A₂)} {c₃ = (c ⊙ c')} {f₁ = Id} {g₁ = Id} {f₂ = (ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl))} {g₂ = ρc'.e} id-sq compose-αl-αr
      
      res : PBSq (idPRel A₁) (c ⊙ c')
             (ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl) ∘p Id ∘p ptbV MA₁ iA₁ ρc.δl)
             (ρc'.e ∘p Id ∘p ρc.e)
      res = CompSqV {c₁ = (idPRel A₁)} {c₂ = c} {c₃ = (c ⊙ c')} {f₁ = (ptbV MA₁ iA₁ ρc.δl)} {g₁ = ρc.e} {f₂ = (ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl) ∘p Id)} {g₂ = (ρc'.e ∘p Id)} α1 compose-id-αlαr

      foo : ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl MA₁.· MA₁.ε MA₁.· ρc.δl) ≡ ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl) ∘p Id ∘p ptbV MA₁ iA₁ ρc.δl
      foo = C.lemma2 (Πc.pull .fst ρc'.δl) MA₁.ε ρc.δl ∙ cong (λ x → ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl) ∘p x ∘p ptbV MA₁ iA₁ ρc.δl) id.lemma
        where
          module C = Compose A₁ MA₁ iA₁
          module id = ptbVε≡Id A₁ MA₁ iA₁


module ComposeLeftRepC
  (B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁)
  (B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂)
  (B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃)
  (MB₁ : Monoid ℓMB₁)  (iB₁ : MonoidHom MB₁ (CEndo B₁))
  (MB₂ : Monoid ℓMB₂)  (iB₂ : MonoidHom MB₂ (CEndo B₂))
  (MB₃ : Monoid ℓMB₃)  (iB₃ : MonoidHom MB₃ (CEndo B₃))
  (d  : ErrorDomRel B₁ B₂ ℓd)  (Πd : PushPullC B₁ MB₁ iB₁ B₂ MB₂ iB₂ d)
  (ρd : LeftRepC B₁ MB₁ iB₁ B₂ MB₂ iB₂ d Πd)
  (d' : ErrorDomRel B₂ B₃ ℓd') (Πd' : PushPullC B₂ MB₂ iB₂ B₃ MB₃ iB₃ d')
  (ρd' : LeftRepC B₂ MB₂ iB₂ B₃ MB₃ iB₃ d' Πd')
  where

  Πdd' = PushPullC-Compose.compPPC MB₁ iB₁ MB₂ iB₂ MB₃ iB₃ d Πd d' Πd'

  module ρd  = LeftRepC ρd
  module ρd' = LeftRepC ρd'
  module Πd  = PushPullC Πd
  module Πd' = PushPullC Πd'
  module MB₁ = MonoidStr (MB₁ .snd)
  module MB₂ = MonoidStr (MB₂ .snd)
  module MB₃ = MonoidStr (MB₃ .snd)

  open LeftRepC

  compose : LeftRepC B₁ MB₁ iB₁ B₃ MB₃ iB₃ (d ⊙ed d') Πdd'
  compose .e = ρd'.e ∘ed IdE ∘ed ρd.e
  compose .δl = Πd.pull .fst ρd'.δl MB₁.· MB₁.ε MB₁.· ρd.δl
  compose .δr = ρd'.δr MB₃.· MB₃.ε MB₃.· Πd'.push .fst ρd.δr
  compose .UpL = transport (cong (λ x → ErrorDomSq (d ⊙ed d') (idEDRel B₃) (ρd'.e ∘ed IdE ∘ed ρd.e) x) (sym foo)) res
    where
      β1 : ErrorDomSq d (idEDRel B₂) ρd.e (ptbC MB₂ iB₂ ρd.δr)
      β1 = ρd.UpL

      β2 : ErrorDomSq d' d' (ptbC MB₂ iB₂ ρd.δr) (ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr))
      β2 = Πd'.pushSq ρd.δr

      id-sq : ErrorDomSq (idEDRel B₂ ⊙ed d') d' IdE IdE
      id-sq = sq-idB⊙d-d d'

      β3 : ErrorDomSq d' (idEDRel B₃) ρd'.e (ptbC MB₃ iB₃ ρd'.δr)
      β3 = ρd'.UpL

      compose-β1β2 : ErrorDomSq (d ⊙ed d') (idEDRel B₂ ⊙ed d') ρd.e (ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr))
      compose-β1β2 = ED-CompSqH {dᵢ₁ = d} {dᵢ₂ = d'} {dₒ₁ = (idEDRel B₂)} {dₒ₂ = d'} {ϕ₁ = ρd.e} {ϕ₂ = (ptbC MB₂ iB₂ ρd.δr)} {ϕ₃ = (ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr))} β1 β2

      compose-id-β3 : ErrorDomSq (idEDRel B₂ ⊙ed d') (idEDRel B₃) (ρd'.e ∘ed IdE)
                       (ptbC MB₃ iB₃ ρd'.δr ∘ed IdE)
      compose-id-β3 = ED-CompSqV {d₁ = (idEDRel B₂ ⊙ed d')} {d₂ = d'} {d₃ = (idEDRel B₃)} {ϕ₁ = IdE} {ϕ₁' = IdE} {ϕ₂ = ρd'.e} {ϕ₂' = (ptbC MB₃ iB₃ ρd'.δr)} id-sq β3

      res : ErrorDomSq (d ⊙ed d') (idEDRel B₃) (ρd'.e ∘ed IdE ∘ed ρd.e)
             (ptbC MB₃ iB₃ ρd'.δr ∘ed IdE ∘ed
              ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr))
      res = ED-CompSqV {d₁ = (d ⊙ed d')} {d₂ = (idEDRel B₂ ⊙ed d')} {d₃ = (idEDRel B₃)} {ϕ₁ = ρd.e} {ϕ₁' = (ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr))} {ϕ₂ = (ρd'.e ∘ed IdE)} {ϕ₂' = (ptbC MB₃ iB₃ ρd'.δr ∘ed IdE)} compose-β1β2 compose-id-β3

      foo : ptbC MB₃ iB₃ (ρd'.δr MB₃.· MB₃.ε MB₃.· Πd'.push .fst ρd.δr) ≡ ptbC MB₃ iB₃ ρd'.δr ∘ed IdE ∘ed ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr)
      foo = C.lemma2 ρd'.δr MB₃.ε (Πd'.push .fst ρd.δr) ∙ cong (λ x → ptbC MB₃ iB₃ ρd'.δr ∘ed x ∘ed ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr)) id.lemma
        where
          module C = ComposeC B₃ MB₃ iB₃
          module id = ptbCε≡Id B₃ MB₃ iB₃


  compose .UpR = transport (cong (λ x → ErrorDomSq (idEDRel B₁) (d ⊙ed d') x (ρd'.e ∘ed IdE ∘ed ρd.e)) (sym foo)) res
    where
      β1 : ErrorDomSq (idEDRel B₁) d (ptbC MB₁ iB₁ ρd.δl) ρd.e
      β1 = ρd.UpR

      id-sq : ErrorDomSq d (d ⊙ed idEDRel B₂) IdE IdE
      id-sq = sq-d-d⊙B' d

      βl : ErrorDomSq d d (ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl)) (ptbC MB₂ iB₂ ρd'.δl)
      βl = Πd.pullSq ρd'.δl

      βr : ErrorDomSq (idEDRel B₂) d' (ptbC MB₂ iB₂ ρd'.δl) ρd'.e
      βr = ρd'.UpR

      compose-βl-βr : ErrorDomSq (d ⊙ed idEDRel B₂) (d ⊙ed d') (ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl)) ρd'.e
      compose-βl-βr = ED-CompSqH {dᵢ₁ = d} {dᵢ₂ = (idEDRel B₂)} {dₒ₁ = d} {dₒ₂ = d'} {ϕ₁ = (ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl))} {ϕ₂ = (ptbC MB₂ iB₂ ρd'.δl)} {ϕ₃ = ρd'.e} βl βr

      compose-id-βlβr : ErrorDomSq d (d ⊙ed d') (ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl) ∘ed IdE) (ρd'.e ∘ed IdE)
      compose-id-βlβr = ED-CompSqV {d₁ = d} {d₂ = (d ⊙ed idEDRel B₂)} {d₃ = (d ⊙ed d')} {ϕ₁ = IdE} {ϕ₁' = IdE} {ϕ₂ = (ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl))} {ϕ₂' = ρd'.e} id-sq compose-βl-βr

      res : ErrorDomSq (idEDRel B₁) (d ⊙ed d')
             (ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl) ∘ed IdE ∘ed ptbC MB₁ iB₁ ρd.δl)
             (ρd'.e ∘ed IdE ∘ed ρd.e)
      res = ED-CompSqV {d₁ = (idEDRel B₁)} {d₂ = d} {d₃ = (d ⊙ed d')} {ϕ₁ = (ptbC MB₁ iB₁ ρd.δl)} {ϕ₁' = ρd.e} {ϕ₂ =(ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl) ∘ed IdE)} {ϕ₂' = (ρd'.e ∘ed IdE)} β1 compose-id-βlβr
      
      foo : ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl MB₁.· MB₁.ε MB₁.· ρd.δl) ≡ ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl) ∘ed IdE ∘ed ptbC MB₁ iB₁ ρd.δl
      foo = C.lemma2 (Πd.pull .fst ρd'.δl) MB₁.ε ρd.δl ∙ cong (λ x → ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl) ∘ed x ∘ed ptbC MB₁ iB₁ ρd.δl) id.lemma
        where
          module C = ComposeC B₁ MB₁ iB₁
          module id = ptbCε≡Id B₁ MB₁ iB₁


-- Right quasi-representations compose

module ComposeRightRepV
  (A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁)
  (A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂)
  (A₃ : PosetBisim ℓA₃ ℓ≤A₃ ℓ≈A₃)
  (MA₁ : Monoid ℓMA₁)  (iA₁ : MonoidHom MA₁ (Endo A₁))
  (MA₂ : Monoid ℓMA₂)  (iA₂ : MonoidHom MA₂ (Endo A₂))
  (MA₃ : Monoid ℓMA₃)  (iA₃ : MonoidHom MA₃ (Endo A₃))
  (c  : PBRel A₁ A₂ ℓc)  (Πc  : PushPullV A₁ MA₁ iA₁ A₂ MA₂ iA₂ c)
  (ρc : RightRepV A₁ MA₁ iA₁ A₂ MA₂ iA₂ c Πc)
  (c' : PBRel A₂ A₃ ℓc') (Πc' : PushPullV A₂ MA₂ iA₂ A₃ MA₃ iA₃ c')
  (ρc' : RightRepV A₂ MA₂ iA₂ A₃ MA₃ iA₃ c' Πc')
  where

  Πcc' = PushPullV-Compose.compPPV MA₁ iA₁ MA₂ iA₂ MA₃ iA₃ c Πc c' Πc'

  module ρc  = RightRepV ρc
  module ρc' = RightRepV ρc'
  module Πc  = PushPullV Πc
  module Πc' = PushPullV Πc'
  module MA₁ = MonoidStr (MA₁ .snd)
  module MA₂ = MonoidStr (MA₂ .snd)
  module MA₃ = MonoidStr (MA₃ .snd)

  open RightRepV

  compose : RightRepV A₁ MA₁ iA₁ A₃ MA₃ iA₃ (c ⊙ c') Πcc'
  compose .p = ρc.p ∘p Id ∘p ρc'.p
  compose .δl = ρc.δl MA₁.· MA₁.ε MA₁.· Πc.pull .fst ρc'.δl
  compose .δr = Πc'.push .fst ρc.δr MA₃.· MA₃.ε MA₃.· ρc'.δr 
  compose .DnL = {!res!}
    where
      β1 : PBSq (idPRel A₃) c' ρc'.p (ptbV MA₃ iA₃ ρc'.δr)
      β1 = ρc'.DnL

      id-sq : PBSq c' (idPRel A₂ ⊙ c') Id Id
      id-sq = sq-c-idA⊙c c'

      β2 : PBSq (idPRel A₂) c ρc.p (ptbV MA₂ iA₂ ρc.δr)
      β2 = ρc.DnL

      β3 : PBSq c' c' (ptbV MA₂ iA₂ ρc.δr)
            (ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr))
      β3 = Πc'.pushSq ρc.δr

      compose-β1-id : PBSq (idPRel A₃) (idPRel A₂ ⊙ c') (Id ∘p ρc'.p) (Id ∘p ptbV MA₃ iA₃ ρc'.δr)
      compose-β1-id = CompSqV {c₁ = (idPRel A₃)} {c₂ = c'} {c₃ = (idPRel A₂ ⊙ c')} {f₁ = ρc'.p} {g₁ = (ptbV MA₃ iA₃ ρc'.δr)} {f₂ = Id} {g₂ = Id} β1 id-sq

      compose-β2-β3 : PBSq (idPRel A₂ ⊙ c') (c ⊙ c') ρc.p (ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr))
      compose-β2-β3 = CompSqH {cᵢ₁ = (idPRel A₂)} {cᵢ₂ = c'} {cₒ₁ = c} {cₒ₂ = c'} {f = ρc.p} {g = (ptbV MA₂ iA₂ ρc.δr)} {h = (ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr))} β2 β3

      res : PBSq (idPRel A₃) (c ⊙ c') (ρc.p ∘p (Id ∘p ρc'.p))
             (ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr) ∘p (Id ∘p ptbV MA₃ iA₃ ρc'.δr))
      res = CompSqV {c₁ = (idPRel A₃)} {c₂ = (idPRel A₂ ⊙ c')} {c₃ = (c ⊙ c')} {f₁ = (Id ∘p ρc'.p)} {g₁ = (Id ∘p ptbV MA₃ iA₃ ρc'.δr)} {f₂ = ρc.p} {g₂ = (ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr))} compose-β1-id compose-β2-β3

      foo : ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr MA₃.· MA₃.ε MA₃.· ρc'.δr) ≡ ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr) ∘p (Id ∘p ptbV MA₃ iA₃ ρc'.δr)
      foo = C.lemma2 (Πc'.push .fst ρc.δr) MA₃.ε ρc'.δr ∙ cong (λ x → ptbV MA₃ iA₃ (Πc'.push .fst ρc.δr) ∘p x ∘p ptbV MA₃ iA₃ ρc'.δr) id.lemma
        where
          module C = Compose A₃ MA₃ iA₃
          module id = ptbVε≡Id A₃ MA₃ iA₃
    
  compose .DnR = transport (cong (λ x → PBSq (c ⊙ c') (idPRel A₁) x (ρc.p ∘p Id ∘p ρc'.p)) (sym foo)) res
    where
      β1 : PBSq c c (ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl)) (ptbV MA₂ iA₂ ρc'.δl)
      β1 = Πc.pullSq ρc'.δl

      β2 : PBSq c' (idPRel A₂) (ptbV MA₂ iA₂ ρc'.δl) ρc'.p
      β2 = ρc'.DnR

      id-sq : PBSq (c ⊙ idPRel A₂) c Id Id
      id-sq = sq-c⊙A'-c c

      β3 : PBSq c (idPRel A₁) (ptbV MA₁ iA₁ ρc.δl) ρc.p
      β3 = ρc.DnR

      compose-β1-β2 : PBSq (c ⊙ c') (c ⊙ idPRel A₂) (ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl)) ρc'.p
      compose-β1-β2 = CompSqH {cᵢ₁ = c} {cᵢ₂ = c'} {cₒ₁ = c} {cₒ₂ = (idPRel A₂)} {f = (ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl))} {g = (ptbV MA₂ iA₂ ρc'.δl)} {h = ρc'.p} β1 β2

      compose-id-β3 : PBSq (c ⊙ idPRel A₂) (idPRel A₁) (ptbV MA₁ iA₁ ρc.δl ∘p Id)
                       (ρc.p ∘p Id)
      compose-id-β3 = CompSqV {c₁ = (c ⊙ idPRel A₂)} {c₂ = c} {c₃ = (idPRel A₁)} {f₁ = Id} {g₁ = Id} {f₂ = (ptbV MA₁ iA₁ ρc.δl)} {g₂ = ρc.p} id-sq β3

      res : PBSq (c ⊙ c') (idPRel A₁)
             (ptbV MA₁ iA₁ ρc.δl ∘p Id ∘p ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl))
             (ρc.p ∘p Id ∘p ρc'.p)
      res = CompSqV {c₁ = (c ⊙ c')} {c₂ = (c ⊙ idPRel A₂)} {c₃ = (idPRel A₁)} {f₁ = (ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl))} {g₁ = ρc'.p} {f₂ = (ptbV MA₁ iA₁ ρc.δl ∘p Id)} {g₂ = (ρc.p ∘p Id)} compose-β1-β2 compose-id-β3

      foo : ptbV MA₁ iA₁ (ρc.δl MA₁.· MA₁.ε MA₁.· Πc.pull .fst ρc'.δl) ≡ ptbV MA₁ iA₁ ρc.δl ∘p Id ∘p ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl)
      foo = C.lemma2 ρc.δl MA₁.ε (Πc.pull .fst ρc'.δl) ∙ cong (λ x → ptbV MA₁ iA₁ ρc.δl ∘p x ∘p ptbV MA₁ iA₁ (Πc.pull .fst ρc'.δl)) id.lemma
        where
          module C = Compose A₁ MA₁ iA₁
          module id = ptbVε≡Id A₁ MA₁ iA₁

module ComposeRightRepC
  (B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁)
  (B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂)
  (B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃)
  (MB₁ : Monoid ℓMB₁)  (iB₁ : MonoidHom MB₁ (CEndo B₁))
  (MB₂ : Monoid ℓMB₂)  (iB₂ : MonoidHom MB₂ (CEndo B₂))
  (MB₃ : Monoid ℓMB₃)  (iB₃ : MonoidHom MB₃ (CEndo B₃))
  (d  : ErrorDomRel B₁ B₂ ℓd)  (Πd : PushPullC B₁ MB₁ iB₁ B₂ MB₂ iB₂ d)
  (ρd : RightRepC B₁ MB₁ iB₁ B₂ MB₂ iB₂ d Πd)
  (d' : ErrorDomRel B₂ B₃ ℓd') (Πd' : PushPullC B₂ MB₂ iB₂ B₃ MB₃ iB₃ d')
  (ρd' : RightRepC B₂ MB₂ iB₂ B₃ MB₃ iB₃ d' Πd')
  where

  Πdd' = PushPullC-Compose.compPPC MB₁ iB₁ MB₂ iB₂ MB₃ iB₃ d Πd d' Πd'

  module ρd  = RightRepC ρd
  module ρd' = RightRepC ρd'
  module Πd  = PushPullC Πd
  module Πd' = PushPullC Πd'
  module MB₁ = MonoidStr (MB₁ .snd)
  module MB₂ = MonoidStr (MB₂ .snd)
  module MB₃ = MonoidStr (MB₃ .snd)

  open RightRepC

  compose : RightRepC B₁ MB₁ iB₁ B₃ MB₃ iB₃ (d ⊙ed d') Πdd'
  compose .p = ρd.p ∘ed IdE ∘ed ρd'.p
  compose .δl = ρd.δl MB₁.· MB₁.ε MB₁.·  Πd.pull .fst ρd'.δl
  compose .δr = Πd'.push .fst ρd.δr MB₃.· MB₃.ε MB₃.· ρd'.δr
  compose .DnL = transport (cong (λ x → ErrorDomSq (idEDRel B₃) (d ⊙ed d') (ρd.p ∘ed (IdE ∘ed ρd'.p)) x) (sym foo)) res
    where
      β1 : ErrorDomSq (idEDRel B₃) d' ρd'.p (ptbC MB₃ iB₃ ρd'.δr)
      β1 = ρd'.DnL

      id-sq : ErrorDomSq d' (idEDRel B₂ ⊙ed d') IdE IdE
      id-sq = sq-d-idB⊙d d'

      β2 : ErrorDomSq (idEDRel B₂) d ρd.p (ptbC MB₂ iB₂ ρd.δr)
      β2 = ρd.DnL

      β3 : ErrorDomSq d' d' (ptbC MB₂ iB₂ ρd.δr) (ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr))
      β3 = Πd'.pushSq ρd.δr

      compose-β1-id : ErrorDomSq (idEDRel B₃) (idEDRel B₂ ⊙ed d') (IdE ∘ed ρd'.p)
                       (IdE ∘ed ptbC MB₃ iB₃ ρd'.δr)
      compose-β1-id = ED-CompSqV {d₁ = (idEDRel B₃)} {d₂ = d'} {d₃ = (idEDRel B₂ ⊙ed d')} {ϕ₁ = ρd'.p} {ϕ₁' = (ptbC MB₃ iB₃ ρd'.δr)} {ϕ₂ = IdE} {ϕ₂' = IdE} β1 id-sq

      compose-β2-β3 : ErrorDomSq (idEDRel B₂ ⊙ed d') (d ⊙ed d') ρd.p
                       (ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr))
      compose-β2-β3 = ED-CompSqH {dᵢ₁ = (idEDRel B₂)} {dᵢ₂ = d'} {dₒ₁ = d} {dₒ₂ = d'} {ϕ₁ = ρd.p} {ϕ₂ = (ptbC MB₂ iB₂ ρd.δr)} {ϕ₃ = (ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr))} β2 β3

      res : ErrorDomSq (idEDRel B₃) (d ⊙ed d') (ρd.p ∘ed (IdE ∘ed ρd'.p))
             (ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr) ∘ed
              (IdE ∘ed ptbC MB₃ iB₃ ρd'.δr))
      res = ED-CompSqV {d₁ = (idEDRel B₃)} {d₂ = (idEDRel B₂ ⊙ed d')} {d₃ = (d ⊙ed d')} {ϕ₁ = (IdE ∘ed ρd'.p)} {ϕ₁' = (IdE ∘ed ptbC MB₃ iB₃ ρd'.δr)} {ϕ₂ = ρd.p} {ϕ₂' = (ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr))} compose-β1-id compose-β2-β3

      foo : ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr MB₃.· MB₃.ε MB₃.· ρd'.δr) ≡ ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr) ∘ed IdE ∘ed ptbC MB₃ iB₃ ρd'.δr
      foo = C.lemma2 (Πd'.push .fst ρd.δr) MB₃.ε ρd'.δr ∙ cong (λ x → ptbC MB₃ iB₃ (Πd'.push .fst ρd.δr) ∘ed x ∘ed (ptbC MB₃ iB₃ ρd'.δr)) id.lemma
        where
          module C = ComposeC B₃ MB₃ iB₃
          module id = ptbCε≡Id B₃ MB₃ iB₃
  compose .DnR = transport (cong (λ x → ErrorDomSq (d ⊙ed d') (idEDRel B₁) x (ρd.p ∘ed IdE ∘ed ρd'.p)) (sym foo)) res
    where
      β1 : ErrorDomSq d d (ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl)) (ptbC MB₂ iB₂ ρd'.δl)
      β1 = Πd.pullSq ρd'.δl

      β2 : ErrorDomSq d' (idEDRel B₂) (ptbC MB₂ iB₂ ρd'.δl) ρd'.p
      β2 = ρd'.DnR

      id-sq : ErrorDomSq (d ⊙ed idEDRel B₂) d IdE IdE
      id-sq = sq-d⊙B'-d d

      β3 : ErrorDomSq d (idEDRel B₁) (ptbC MB₁ iB₁ ρd.δl) ρd.p
      β3 = ρd.DnR

      compose-β1-β2 : ErrorDomSq (d ⊙ed d') (d ⊙ed idEDRel B₂) (ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl)) ρd'.p
      compose-β1-β2 = ED-CompSqH {dᵢ₁ = d} {dᵢ₂ = d'} {dₒ₁ = d} {dₒ₂ = (idEDRel B₂)} {ϕ₁ = (ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl))} {ϕ₂ = (ptbC MB₂ iB₂ ρd'.δl)} {ϕ₃ = ρd'.p} β1 β2

      compose-id-β3 : ErrorDomSq (d ⊙ed idEDRel B₂) (idEDRel B₁)
                       (ptbC MB₁ iB₁ ρd.δl ∘ed IdE) (ρd.p ∘ed IdE)
      compose-id-β3 = ED-CompSqV {d₁ = (d ⊙ed idEDRel B₂)} {d₂ = d} {d₃ = (idEDRel B₁)} {ϕ₁ = IdE} {ϕ₁' = IdE} {ϕ₂ = (ptbC MB₁ iB₁ ρd.δl)} {ϕ₂' = ρd.p} id-sq β3

      res : ErrorDomSq (d ⊙ed d') (idEDRel B₁) (ptbC MB₁ iB₁ ρd.δl ∘ed IdE ∘ed ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl)) (ρd.p ∘ed IdE ∘ed ρd'.p)
      res = ED-CompSqV {d₁ = (d ⊙ed d')} {d₂ = (d ⊙ed idEDRel B₂)} {d₃ = (idEDRel B₁)} {ϕ₁ = (ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl))} {ϕ₁' = ρd'.p} {ϕ₂ = (ptbC MB₁ iB₁ ρd.δl ∘ed IdE)} {ϕ₂' = (ρd.p ∘ed IdE)} compose-β1-β2 compose-id-β3

      foo : ptbC MB₁ iB₁ (ρd.δl MB₁.· MB₁.ε MB₁.· Πd.pull .fst ρd'.δl) ≡ ptbC MB₁ iB₁ ρd.δl ∘ed IdE ∘ed ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl)
      foo = C.lemma2 ρd.δl MB₁.ε (Πd.pull .fst ρd'.δl) ∙ cong (λ x → ptbC MB₁ iB₁ ρd.δl ∘ed x ∘ed ptbC MB₁ iB₁ (Πd.pull .fst ρd'.δl)) id.lemma
        where
          module C = ComposeC B₁ MB₁ iB₁
          module id = ptbCε≡Id B₁ MB₁ iB₁



-- If c is left-representable, then F c is left representable

-- If c has push pull, then Fc has push pull (Perturbations.agda)

-- 1. 4 composition lemmas (LeftRepV, LeftRepC, RightRepV, RightRepC)
--       Each lemma involves two squares

-- 2. Lemmas about U(d ⊙ed d') and F(c ⊙ c')
--    a. If c and c' are left representable, then F(c ⊙ c') is right representable
--    b. If d and d' are right representable, then U(d ⊙ed d') is left representable

module LeftRepC-Fc
  (A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁)
  (A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂)
  (MA₁ : Monoid ℓMA₁)  (iA₁ : MonoidHom MA₁ (Endo A₁))
  (MA₂ : Monoid ℓMA₂)  (iA₂ : MonoidHom MA₂ (Endo A₂))
  (c  : PBRel A₁ A₂ ℓc)  (Πc  : PushPullV A₁ MA₁ iA₁ A₂ MA₂ iA₂ c)
  (ρc : LeftRepV A₁ MA₁ iA₁ A₂ MA₂ iA₂ c Πc)
  where
  module B₁ = F-ob A₁
  module B₂ = F-ob A₂
  module d = F-rel c
  module push-pull-c = F-PushPull c Πc

  B₁ = B₁.F-ob
  B₂ = B₂.F-ob
  d = d.F-rel
  Πd = push-pull-c.F-PushPull
  
  open LeftRepC
  module ρc = LeftRepV ρc
  
  
  Fc : LeftRepC B₁ push-pull-c.M-FA push-pull-c.iFA B₂ push-pull-c.M-FA' push-pull-c.iFA' d Πd
  Fc .e = d-mor.F-mor ρc.e
    where
      module d-mor = F-mor {Aᵢ = A₁} {Aₒ = A₂}
  Fc .δl = {!!}
  Fc .δr = {!!}
  Fc .UpL = {!!}
  Fc .UpR = {!!}

module Fc⊙c'
  (A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁)
  (A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂)
  (A₃ : PosetBisim ℓA₃ ℓ≤A₃ ℓ≈A₃)
  (MA₁ : Monoid ℓMA₁)  (iA₁ : MonoidHom MA₁ (Endo A₁))
  (MA₂ : Monoid ℓMA₂)  (iA₂ : MonoidHom MA₂ (Endo A₂))
  (MA₃ : Monoid ℓMA₃)  (iA₃ : MonoidHom MA₃ (Endo A₃))
  (c  : PBRel A₁ A₂ ℓc)  (Πc  : PushPullV A₁ MA₁ iA₁ A₂ MA₂ iA₂ c)
  (c' : PBRel A₂ A₃ ℓc') (Πc' : PushPullV A₂ MA₂ iA₂ A₃ MA₃ iA₃ c')
  (ρc : LeftRepV A₁ MA₁ iA₁ A₂ MA₂ iA₂ c Πc) (ρc' : LeftRepV A₂ MA₂ iA₂ A₃ MA₃ iA₃ c' Πc')
  where
  module B₁ = F-ob A₁
  module pp-A₁ = F-PushPull c Πc
  module B₂ = F-ob A₂
  module B₃ = F-ob A₃
  module d = F-rel c
  module d' = F-rel c'
  module rel⊙ = F-rel (c ⊙ c')
  module push-pull-c = F-PushPull c Πc
  module push-pull-c' = F-PushPull c' Πc'
  module push-pull-composed-v = PushPullV-Compose MA₁ iA₁ MA₂ iA₂ MA₃ iA₃ c Πc c' Πc'
  module push-pull-compose-c = F-PushPull (c ⊙ c') push-pull-composed-v.compPPV
  module ρd-m = LeftRepC-Fc A₁ A₂ MA₁ iA₁ MA₂ iA₂ c Πc ρc
  module ρd'-m = LeftRepC-Fc A₂ A₃ MA₂ iA₂ MA₃ iA₃ c' Πc' ρc'
  

  open RightRepC

  B₁ = B₁.F-ob
  B₂ = B₂.F-ob
  B₃ = B₃.F-ob
  MB = push-pull-compose-c.M-FA
  MB' = push-pull-c'.M-FA
  MB'' = push-pull-compose-c.M-FA'
  iB = push-pull-compose-c.iFA
  iB' = push-pull-c'.iFA
  iB'' = push-pull-compose-c.iFA'
  d = d.F-rel
  d' = d'.F-rel
  d⊙d' = rel⊙.F-rel
  Πd = push-pull-c.F-PushPull
  Πd' = push-pull-c'.F-PushPull
  Πd∘Πd' = push-pull-compose-c.F-PushPull
  ρd = ρd-m.Fc
  ρd' = ρd'-m.Fc

  module ρd = LeftRepC ρd
  module ρd' = LeftRepC ρd'

  lemma : RightRepC B₁ MB iB B₃ MB'' iB'' d⊙d' Πd∘Πd'
  lemma .p = {!ρd'.e!} ∘ed {!!}
  lemma .δl = {!!}
  lemma .δr = {!!}
  lemma .DnL = {!!}
  lemma .DnR = {!!}

{-
module Ud⊙d'
  (B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁)
  (B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂)
  (B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃)
  (MB₁ : Monoid ℓMB₁)  (iB₁ : MonoidHom MB₁ (CEndo B₁))
  (MB₂ : Monoid ℓMB₂)  (iB₂ : MonoidHom MB₂ (CEndo B₂))
  (MB₃ : Monoid ℓMB₃)  (iB₃ : MonoidHom MB₃ (CEndo B₃))
  (d  : ErrorDomRel B₁ B₂ ℓd)  (Πd : PushPullC B₁ MB₁ iB₁ B₂ MB₂ iB₂ d)
  (d' : ErrorDomRel B₂ B₃ ℓd') (Πd' : PushPullC B₂ MB₂ iB₂ B₃ MB₃ iB₃ d')
  where
  module push-pull-c = PushPullC-Compose MB₁ iB₁ MB₂ iB₂ MB₃ iB₃ d Πd d' Πd'
  module push-pull-v = U-PushPull (d ⊙ed d') push-pull-c.compPPC
{-
  module A₁ = U-ob B₁
  module A₂ = U-ob B₂
  module A₃ = U-ob B₃

  module pp-B₁ = U-PushPull d Πd

  module rel = U-rel (d ⊙ d')

  module push-pull-c = PushPullC-Compose MB₁ iB₁ MB₂ iB₂ MB₃ iB₃ d Πd d' Πd'
  module push-pull-v = U-PushPull (d ⊙ d') push-pull-c.compPPC
-}
  lemma : (ρd : RightRepC B₁ MB₁ iB₁ B₂ MB₂ iB₂ d Πd) (ρd' : RightRepC B₂ MB₂ iB₂ B₃ MB₃ iB₃ d' Πd') →
    LeftRepV (U-ob B₁) push-pull-v.M-UB push-pull-v.iUB (U-ob B₃) push-pull-v.M-UB' push-pull-v.iUB' (U-rel (d ⊙ed d')) push-pull-v.U-PushPull
  lemma ρd ρd' = {!!}

-}
