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
    --       c                    ⊑A'
    --   A o----* A'          A' o---* A'
    --   |        |           |        |
    -- δl|        | p      p  |        | δr
    --   v        v           v        v
    --   A o----* A           A o----* A'
    --       ⊑A                   c

    DnL : PBSq c (idPRel A) (ptbV MA iA δl) p
    DnR : PBSq (idPRel A') c p (ptbV MA' iA' δr)



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
    equiv-d-d' .sq-d-d' = {!!}  -- α1 ∘esqv α2 ∘esqv α3 -- sq-d-idB⊙d d ∘esqv α ∘esqv sq-d⊙B'-d d'
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

  open LeftRepV

  compose : LeftRepV A₁ MA₁ iA₁ A₃ MA₃ iA₃ (c ⊙ c') Πcc'
  compose .e = ρc'.e ∘p ρc.e
  compose .δl = ρc.δl MA₁.· Πc.pull .fst ρc'.δl
  compose .δr = ρc'.δr MA₃.· Πc'.push .fst ρc.δr
  compose .UpL = {!!} -- CompSqV (CompSqV (CompSqH ρc.UpL (Πc'.pushSq ρc.δr)) is-id-sq) ρc'.UpL
    where
      foo : (idPRel A₂) ⊙ c' ≡ LiftPBRel {ℓc = ℓc'} {ℓc' = ℓ-max ℓA₂ ℓ≤A₂} c'
      foo = {!!}
      is-id-sq : PBSq (idPRel A₂ ⊙ c') c' Id Id
      is-id-sq = transport (cong {!λ x → PBSq x c' Id Id!} foo) {!!}

      
      
  compose .UpR = {!!} -- CompSqV {!ρc.UpR!}  (CompSqV {!!} CompSqH (Πc.pullSq ρc'.δl) {!!})


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
  compose .e = ρd'.e ∘ed ρd.e
  compose .δl = ρd.δl MB₁.· Πd.pull .fst ρd'.δl
  compose .δr = ρd'.δr MB₃.· Πd'.push .fst ρd.δr
  compose .UpL = {!!}
  compose .UpR = {!!}



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
  compose .p = ρc.p ∘p ρc'.p
  compose .δl = ρc.δl MA₁.· Πc.pull .fst ρc'.δl
  compose .δr = ρc'.δr MA₃.· Πc'.push .fst ρc.δr
  compose .DnL = {!!}
  compose .DnR = {!!}

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
  compose .p = ρd.p ∘ed ρd'.p
  compose .δl = ρd.δl MB₁.· Πd.pull .fst ρd'.δl
  compose .δr = ρd'.δr MB₃.· Πd'.push .fst ρd.δr
  compose .DnL = {!!}
      
  compose .DnR = {!!}
