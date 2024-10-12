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

module Semantics.Concrete.Relations.Constructions (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.FreeProduct
open import Cubical.Algebra.Monoid.FreeMonoid as Free
open import Cubical.Data.Sigma

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Constructions
open import Semantics.Concrete.Predomain.Morphism as Mor hiding (Id)
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.Relation as PRel hiding (⊎-inl ; ⊎-inr)
open import Semantics.Concrete.Predomain.Combinators hiding (U)
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Predomain.MonadCombinators k
open import Semantics.Concrete.LockStepErrorOrdering k

open import Semantics.Concrete.Perturbation.Semantic k
open import Semantics.Concrete.Perturbation.Relation k as RelPP hiding (⊎-inl ; ⊎-inr ; U ; F ; Next ; ⊙V ; ⊙C)
open import Semantics.Concrete.Perturbation.Relation.Alt k

open import Semantics.Concrete.Perturbation.QuasiRepresentation k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.Constructions k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.Composition k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.CompositionLemmaU k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.CompositionLemmaF k




open import Semantics.Concrete.Types k as Types hiding (U ; F ; _×_)
open import Semantics.Concrete.Relations.Base k

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

IdV : ∀ (A : ValType ℓA ℓ≤A ℓ≈A ℓMA) → ValRel A A _
IdV A .fst = {!!} -- IdRelV

-- Left rep for Id
IdV A .snd .fst .fst = {!!}
IdV A .snd .fst .snd = {!!}

-- Right rep for F Id
IdV A .snd .snd .fst = {!!}
IdV A .snd .snd .snd = {!!}

open F-rel

module C = ClockedCombinators k
open Clocked k


{-
-- Isomorphism induces a relation

module _ (A : ValType ℓA ℓ≤A ℓ≈A ℓMA) (A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA')
         (isom : Iso ⟨ A ⟩ ⟨ A' ⟩)
  where

  relPP : VRelPP A A' {!!}
  relPP .fst = {!!}
  relPP .snd .fst = {!!}
  relPP .snd .snd = {!!}

  Iso→Rel : ValRel A A' {!!}

  Iso→Rel .fst = {!!}
  Iso→Rel .snd = {!!}
-}


-- If value types A and A' are strongly isomorphic, we obtain a value relation
-- between A and A' induced by the morphism A → A'.
module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  (isom : StrongIsoV A A')
  where

  ValTyIso→ValRel : ValRel A A' ℓ≤A'

  -- Relation + push-pull
  ValTyIso→ValRel .fst = ValTyIso→VRelPP isom

  -- Left rep for the relation
  ValTyIso→ValRel .snd .fst = iso→LeftRepV (StrongIsoV→PredomIso isom)

  -- Right rep for F of the relation
  ValTyIso→ValRel .snd .snd = iso→RightRepC (StrongIsoV→PredomIso isom)


-- Composition

module _
  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁} {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂} {A₃ : ValType ℓA₃ ℓ≤A₃ ℓ≈A₃ ℓMA₃}
  (c₁ : ValRel A₁ A₂ ℓc₁)
  (c₂ : ValRel A₂ A₃ ℓc₂)
  where

  private
    iA₁ = interpV A₁ .fst
    iA₂ = interpV A₂ .fst
    iA₃ = interpV A₃ .fst

  ⊙V : ValRel A₁ A₃ _
  ⊙V .fst = RelPP.⊙V (c₁ .fst) (c₂ .fst)
  
  ⊙V .snd .fst = LeftRepV-Comp (c₁ .fst) (c₂ .fst) (c₁ .snd .fst) (c₂ .snd .fst)
  
  ⊙V .snd .snd = repFcFc'→repFcc' (c₁ .fst) (c₂ .fst) (c₁ .snd .fst) (c₂ .snd .fst) (c₁ .snd .snd) (c₂ .snd .snd)



-- Relations induced by inl and inr

module _  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁}
          {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂}   
  where

  ⊎-inl : ValRel A₁ (A₁ Types.⊎ A₂) (ℓ-max ℓ≤A₁ ℓ≤A₂)
  ⊎-inl .fst = RelPP.⊎-inl
  ⊎-inl .snd .fst = ⊎-inl-LeftRep
  ⊎-inl .snd .snd = ⊎-inl-F-RightRep

  ⊎-inr : ValRel A₂ (A₁ Types.⊎ A₂) (ℓ-max ℓ≤A₁ ℓ≤A₂)
  ⊎-inr .fst = RelPP.⊎-inr
  ⊎-inr .snd .fst = ⊎-inr-LeftRep
  ⊎-inr .snd .snd = ⊎-inr-F-RightRep

-- Next as a relation between A and ▹ A
module _ (A : ValType ℓA ℓ≤A ℓ≈A ℓMA) where

  open LiftPredomain
  open LiftOrd
  open ExtAsEDMorphism


  MA  = PtbV A
  iA  = interpV A
  i▹A = interpV (Types.V▹ A)
  module MA  = MonoidStr (MA .snd)
  module iA  = IsMonoidHom (iA .snd)
  module i▹A = IsMonoidHom (i▹A .snd)

  ▹A = Types.V▹ A
  rA = idPRel (ValType→Predomain A)
  r▹A = idPRel (ValType→Predomain (V▹ A))

  rel-next-A = relNext {k = k} (ValType→Predomain A)
  𝔸 = ValType→Predomain A

  --------------------------------------
  -- Left quasi-representation for next
  --------------------------------------

  repL : LeftRepV A ▹A (RelPP.Next .fst)
  -- emb : A → ▹ A
  repL .fst = C.Next

  -- UpR
  repL .snd .fst .fst = MA.ε
  repL .snd .fst .snd = subst
    (λ δ → PSq rA (RelPP.Next .fst) δ C.Next)
    (sym (cong fst iA.presε))
    sq
    where
      sq : PSq rA (RelPP.Next .fst) Mor.Id C.Next
      sq x y xRy t = xRy

  -- UpL
  repL .snd .snd .fst = MA.ε
  repL .snd .snd .snd =
    subst
          (λ δ → PSq (RelPP.Next .fst) r▹A C.Next δ)
          (sym (cong fst i▹A.presε))
          sq
    where
      sq : PSq (RelPP.Next .fst) r▹A C.Next Mor.Id
      sq = SqV-functionalRel C.Next Mor.Id r▹A
  
  Next : ValRel A ▹A ℓ≤A
  Next .fst = RelPP.Next
  Next .snd .fst = repL
  Next .snd .snd = repR
    where

      ------------------------------------------
      -- Right quasi-representation for F next
      ------------------------------------------

      p : PMor (P▹ 𝔸) (𝕃 𝔸)
      p = (θ-mor ∘p (C.Map▹ η-mor))

      -- delay on the left and right
      dl : PMor 𝔸 (𝕃 𝔸)
      dl = δ-mor ∘p η-mor

      dr : PMor (P▹ 𝔸) (𝕃 (P▹ 𝔸))
      dr = δ-mor ∘p η-mor
      
      rLA = idPRel (𝕃 𝔸)
     

      repR : RightRepC (Types.F A) (Types.F ▹A) (F-rel rel-next-A)

      -- proj : F (▹ A) --o F A
      repR .fst = Ext p

      -- DnR
      repR .snd .fst .fst = i₁ .fst Free.FM-1-gen -- insert one delay on the right
      repR .snd .fst .snd = sq2
        where
          sq : PSq rel-next-A rLA dl p
          sq x y~ x≤y~ = ⊑θθ _ _ (λ t → ⊑ηη x (y~ t) (x≤y~ t))

          sq2 : ErrorDomSq (F-rel (rel-next-A)) (F-rel rA) (Ext dl) (Ext p)
          sq2 = Ext-sq rel-next-A (F-rel rA) dl p sq

      -- DnL
      repR .snd .snd .fst = i₁ .fst Free.FM-1-gen -- insert one delay on the left
      repR .snd .snd .snd = sq2
        where
          sq : PSq r▹A (U-rel (F-rel rel-next-A)) p dr
          sq x~ y~ x~≤y~ = ⊑θθ _ _ (λ t → ⊑ηη (x~ t) y~ (lem t))
            where
            lem : (@tick t : Tick k) → rel-next-A .PRel.R (x~ t) y~
            lem t t' =
              let tirr = tick-irrelevance x~ t t'
              in subst (λ z → rA .PRel.R z (y~ t')) (sym tirr) (x~≤y~ t')
              
          sq2 : ErrorDomSq (F-rel r▹A) (F-rel rel-next-A) (Ext p) (Ext dr)
          sq2 = Ext-sq r▹A (F-rel rel-next-A) p dr sq
      


module _ {A  : ValType ℓA  ℓ≤A  ℓ≈A ℓMA} {A'  : ValType ℓA'  ℓ≤A'  ℓ≈A' ℓMA'} where

  F : ValRel A A' ℓc → CompRel (Types.F A) (Types.F A') _
  F c .fst = RelPP.F (c .fst)

  -- Right rep for F c
  F c .snd .fst = c .snd .snd  -- F-rightRep A A' (VRelPP→PredomainRel (c .fst)) {!!}

  -- Left rep for U (F c)
  F c .snd .snd = U-leftRep (Types.F A) (Types.F A') _ (F-leftRep A A' _ (c .snd .fst))


module _ {B : CompType ℓB ℓ≤B ℓ≈B ℓMB} {B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'} where

  U : CompRel B B' ℓd → ValRel (Types.U B) (Types.U B') _
  U d .fst = RelPP.U (d .fst)

  -- Left rep for U d
  U d .snd .fst = d .snd .snd

  -- Right rep for F (U d)
  U d .snd .snd = F-rightRep (Types.U B) (Types.U B') _ (U-rightRep B B' _ (d .snd .fst))
