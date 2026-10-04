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
open import Common.Later

module Semantics.Concrete.Relations.Constructions (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.FreeProduct
open import Cubical.Algebra.Monoid.FreeMonoid as Free
open import Cubical.Data.Sigma hiding (_×_)

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Constructions
open import Semantics.Concrete.Predomain.Morphism as Mor hiding (Id)
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.Relation as PRel hiding (⊎-inl ; ⊎-inr)
open import Semantics.Concrete.Predomain.Combinators hiding (U)
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Predomain.MonadCombinators k
open import Semantics.Concrete.Predomain.Kleisli k
open import Semantics.Concrete.LockStepErrorOrdering k

open import Semantics.Concrete.Perturbation.Semantic k
open import Semantics.Concrete.Perturbation.Relation k as RelPP
  hiding (⊎-inl ; ⊎-inr ; U ; F ; Next ; ⊙V ; ⊙C ; _×_ ; _⟶_)

open import Semantics.Concrete.Perturbation.QuasiRepresentation k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.Constructions k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.Composition k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.CompositionLemmaU k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.CompositionLemmaF k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.QuasiEquivalence k

open import Semantics.Concrete.Types k as Types hiding (U ; F ; _×_ ; _⟶_)
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
    ℓA'' ℓ≤A'' ℓ≈A'' ℓMA'' : Level
    ℓB'' ℓ≤B'' ℓ≈B'' ℓMB'' : Level

    ℓMA₁ ℓMA₂ ℓMA₃ : Level
    ℓMA₁' ℓMA₂' ℓMA₃' : Level
    ℓMB₁ ℓMB₂ ℓMB₃ : Level
    ℓMAᵢ ℓMAₒ ℓMBᵢ ℓMBₒ : Level
    ℓMAᵢ' ℓMAₒ' ℓMBᵢ' ℓMBₒ' : Level

IdV : ∀ (A : ValType ℓA ℓ≤A ℓ≈A ℓMA) → ValRel A A ℓ≤A
IdV A .fst = IdRelV -- identity relation + push-pull

-- Left rep for Id
IdV A .snd .fst = LeftRepV-Id

-- Right rep for F Id
IdV A .snd .snd = F-rightRep A A _ RightRepV-Id

open F-rel

module C = ClockedCombinators k
open Clocked k



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


-- Products

module _ {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁} {A₁' : ValType ℓA₁' ℓ≤A₁' ℓ≈A₁' ℓMA₁'}
         {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂} {A₂' : ValType ℓA₂' ℓ≤A₂' ℓ≈A₂' ℓMA₂'} where

  _×_ : ValRel A₁ A₁' ℓc₁ → ValRel A₂ A₂' ℓc₂ → ValRel (A₁ Types.× A₂) (A₁' Types.× A₂') _
  (c₁ × c₂) .fst = c₁ .fst RelPP.× c₂ .fst

  -- Left rep for c₁ × c₂
  (c₁ × c₂) .snd .fst = ×-leftRep (c₁ .fst .fst) (c₂ .fst .fst) (c₁ .snd .fst) (c₂ .snd .fst)

  -- Right rep for F (c₁ × c₂)
  (c₁ × c₂) .snd .snd = ×-F-rightRep (c₁ .fst .fst) (c₂ .fst .fst) (c₁ .snd .snd) (c₂ .snd .snd)


-- Arrows

module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
         {B : CompType ℓB ℓ≤B ℓ≈B ℓMB} {B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'} where

  _⟶_ : ValRel A A' ℓc → CompRel B B' ℓd → CompRel (A Types.⟶ B) (A' Types.⟶ B') _
  (c ⟶ d) .fst = c .fst RelPP.⟶ d .fst

  -- Right rep for c ⟶ d
  (c ⟶ d) .snd .fst = RightRepArrow (c .fst .fst) (d .fst .fst) (c .snd .fst) (d .snd .fst)

  -- Left rep for U (c ⟶ d)
  (c ⟶ d) .snd .snd = LeftRepUArrow (c .fst .fst) (d .fst .fst) (c .snd .snd) (d .snd .snd)


-- The arrow action on the identity relations is represented by the
-- same embedding as the identity relation on the arrow type: the
-- embedding of U (IdV A ⟶ F (IdV B)) is the composite of the Kleisli
-- actions of F-mor Id, which is the identity.
module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {B : ValType ℓB ℓ≤B ℓ≈B ℓMB} where

  private
    |A| = ValType→Predomain A
    |B| = ValType→Predomain B

  U⟶F-Id-emb≡ :
      IdV (Types.U (A Types.⟶ Types.F B)) .snd .fst .fst
    ≡ (U (IdV A ⟶ F (IdV B))) .snd .fst .fst
  U⟶F-Id-emb≡ = sym
    ( cong₂ _∘p_
        (cong (λ ϕ → ϕ ⟶Kᴸ (F-ob.F-ob |B|)) (F-mor-pres-id {A = |A|}))
        (cong (λ g → |A| ⟶Kᴿ g) (cong U-mor (F-mor-pres-id {A = |B|})))
    ∙ cong₂ _∘p_ (KlArrowMorphismᴸ-id (F-ob.F-ob |B|)) (KlArrowMorphismᴿ-id |A|)
    ∙ eqPMor _ _ refl )

  U⟶F-Id-emb : ValRel≈ (IdV (Types.U (A Types.⟶ Types.F B))) (U (IdV A ⟶ F (IdV B)))
  U⟶F-Id-emb = eqEmbV→quasiEquivV _ _
    (IdV (Types.U (A Types.⟶ Types.F B)) .snd .fst)
    (U (IdV A ⟶ F (IdV B)) .snd .fst)
    U⟶F-Id-emb≡


----------------------------------------------------------------------
-- Quasi-order-equivalence and the functorial actions (Lemma D.18)
----------------------------------------------------------------------

-- U preserves quasi-order-equivalence.
module _ {B : CompType ℓB ℓ≤B ℓ≈B ℓMB} {B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
         {d  : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd}
         {d' : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd'} where

  private
    ιB : _ → _
    ιB δ = interpC B .fst δ .fst
    ιB' : _ → _
    ιB' δ = interpC B' .fst δ .fst

  U-quasiEquiv : QuasiOrderEquivC B B' d d' →
    QuasiOrderEquivV (Types.U B) (Types.U B') (U-rel d) (U-rel d')
  U-quasiEquiv e .QuasiOrderEquivV.δ₁  = i₂ .fst (e .QuasiOrderEquivC.δ₁)
  U-quasiEquiv e .QuasiOrderEquivV.δ₁' = i₂ .fst (e .QuasiOrderEquivC.δ₁')
  U-quasiEquiv e .QuasiOrderEquivV.sq-c-c' =
    U-sq d d' (ιB (e .QuasiOrderEquivC.δ₁)) (ιB' (e .QuasiOrderEquivC.δ₁')) (e .QuasiOrderEquivC.sq-d-d')
  U-quasiEquiv e .QuasiOrderEquivV.δ₂  = i₂ .fst (e .QuasiOrderEquivC.δ₂)
  U-quasiEquiv e .QuasiOrderEquivV.δ₂' = i₂ .fst (e .QuasiOrderEquivC.δ₂')
  U-quasiEquiv e .QuasiOrderEquivV.sq-c'-c =
    U-sq d' d (ιB (e .QuasiOrderEquivC.δ₂)) (ιB' (e .QuasiOrderEquivC.δ₂')) (e .QuasiOrderEquivC.sq-d'-d)


-- ⟶ preserves quasi-order-equivalence (contravariantly in the first
-- argument, which is why the squares of the value equivalence are used
-- in the opposite direction).
module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
         {B : CompType ℓB ℓ≤B ℓ≈B ℓMB} {B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
         {c  : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc}
         {c₂ : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc'}
         {d  : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd}
         {d₂ : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd'} where

  private
    ιA : _ → _
    ιA δ = interpV A .fst δ .fst
    ιA' : _ → _
    ιA' δ = interpV A' .fst δ .fst
    ιB : _ → _
    ιB δ = interpC B .fst δ .fst
    ιB' : _ → _
    ιB' δ = interpC B' .fst δ .fst
    module M⟶  = MonoidStr (PtbC (A Types.⟶ B) .snd)
    module M⟶' = MonoidStr (PtbC (A' Types.⟶ B') .snd)

  ⟶-quasiEquiv : QuasiOrderEquivV A A' c c₂ → QuasiOrderEquivC B B' d d₂ →
    QuasiOrderEquivC (A Types.⟶ B) (A' Types.⟶ B') (c ⟶rel d) (c₂ ⟶rel d₂)
  ⟶-quasiEquiv ev ec .QuasiOrderEquivC.δ₁ =
    (i₂ .fst (ec .QuasiOrderEquivC.δ₁)) M⟶.· (i₁ .fst (ev .QuasiOrderEquivV.δ₂))
  ⟶-quasiEquiv ev ec .QuasiOrderEquivC.δ₁' =
    (i₂ .fst (ec .QuasiOrderEquivC.δ₁')) M⟶'.· (i₁ .fst (ev .QuasiOrderEquivV.δ₂'))
  ⟶-quasiEquiv ev ec .QuasiOrderEquivC.sq-d-d' = ED-CompSqV
    {d₁ = c ⟶rel d} {d₂ = c₂ ⟶rel d} {d₃ = c₂ ⟶rel d₂}
    {ϕ₁ = ιA (ev .QuasiOrderEquivV.δ₂) ⟶mor IdE} {ϕ₁' = ιA' (ev .QuasiOrderEquivV.δ₂') ⟶mor IdE}
    {ϕ₂ = Mor.Id ⟶mor ιB (ec .QuasiOrderEquivC.δ₁)}  {ϕ₂' = Mor.Id ⟶mor ιB' (ec .QuasiOrderEquivC.δ₁')}
    ((ev .QuasiOrderEquivV.sq-c'-c) ⟶sq (ED-IdSqV d))
    ((Predom-IdSqV c₂) ⟶sq (ec .QuasiOrderEquivC.sq-d-d'))
  ⟶-quasiEquiv ev ec .QuasiOrderEquivC.δ₂ =
    (i₂ .fst (ec .QuasiOrderEquivC.δ₂)) M⟶.· (i₁ .fst (ev .QuasiOrderEquivV.δ₁))
  ⟶-quasiEquiv ev ec .QuasiOrderEquivC.δ₂' =
    (i₂ .fst (ec .QuasiOrderEquivC.δ₂')) M⟶'.· (i₁ .fst (ev .QuasiOrderEquivV.δ₁'))
  ⟶-quasiEquiv ev ec .QuasiOrderEquivC.sq-d'-d = ED-CompSqV
    {d₁ = c₂ ⟶rel d₂} {d₂ = c ⟶rel d₂} {d₃ = c ⟶rel d}
    {ϕ₁ = ιA (ev .QuasiOrderEquivV.δ₁) ⟶mor IdE} {ϕ₁' = ιA' (ev .QuasiOrderEquivV.δ₁') ⟶mor IdE}
    {ϕ₂ = Mor.Id ⟶mor ιB (ec .QuasiOrderEquivC.δ₂)}  {ϕ₂' = Mor.Id ⟶mor ιB' (ec .QuasiOrderEquivC.δ₂')}
    ((ev .QuasiOrderEquivV.sq-c-c') ⟶sq (ED-IdSqV d₂))
    ((Predom-IdSqV c) ⟶sq (ec .QuasiOrderEquivC.sq-d'-d))


-- U (d ⊙ d') is quasi-order-equivalent to U d ⊙ U d' (Lemma D.12):
-- both are quasi-right-represented by the same projection.
module _ {B₁ : CompType ℓB₁ ℓ≤B₁ ℓ≈B₁ ℓMB₁} {B₂ : CompType ℓB₂ ℓ≤B₂ ℓ≈B₂ ℓMB₂}
         {B₃ : CompType ℓB₃ ℓ≤B₃ ℓ≈B₃ ℓMB₃}
         (d : CRelPP B₁ B₂ ℓd) (d' : CRelPP B₂ B₃ ℓd')
         (ρd : RightRepC B₁ B₂ (d .fst)) (ρd' : RightRepC B₂ B₃ (d' .fst)) where

  Udd'≈UdUd' : QuasiOrderEquivV (Types.U B₁) (Types.U B₃)
    (U-rel (d .fst ⊙ed d' .fst)) (U-rel (d .fst) PRel.⊙ U-rel (d' .fst))
  Udd'≈UdUd' = eqEmb→quasiEquivV _ _
    (U-rightRep _ _ (d .fst ⊙ed d' .fst) (RightRepC-Comp d d' ρd ρd'))
    (RightRepV-Comp (RelPP.U d) (RelPP.U d') (U-rightRep _ _ (d .fst) ρd) (U-rightRep _ _ (d' .fst) ρd'))
    refl -- U preserves composition definitionally


-- F (c ⊙ c') is quasi-order-equivalent to F c ⊙ F c' (Lemma D.11):
-- both are quasi-left-represented by the same embedding.
module _ {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁} {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂}
         {A₃ : ValType ℓA₃ ℓ≤A₃ ℓ≈A₃ ℓMA₃}
         (c : VRelPP A₁ A₂ ℓc) (c' : VRelPP A₂ A₃ ℓc')
         (ρc : LeftRepV A₁ A₂ (c .fst)) (ρc' : LeftRepV A₂ A₃ (c' .fst)) where

  Fcc'≈FcFc' : QuasiOrderEquivC (Types.F A₁) (Types.F A₃)
    (F-rel (c .fst PRel.⊙ c' .fst)) (F-rel (c .fst) ⊙ed F-rel (c' .fst))
  Fcc'≈FcFc' = eqEmb→quasiEquivC _ _
    (F-leftRep A₁ A₃ (c .fst PRel.⊙ c' .fst) (LeftRepV-Comp c c' ρc ρc'))
    (LeftRepC-Comp (RelPP.F c) (RelPP.F c')
      (F-leftRep A₁ A₂ (c .fst) ρc) (F-leftRep A₂ A₃ (c' .fst) ρc'))
    (F-mor-pres-comp _ _) -- functoriality of F


-- (c ⊙ c') ⟶ (d ⊙ d') is quasi-order-equivalent to (c ⟶ d) ⊙ (c' ⟶ d')
-- (Lemma D.18): both are quasi-right-represented by the same projection,
-- namely (e_c' ∘ e_c) ⟶ (p_d ∘ p_d').
module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
         {A'' : ValType ℓA'' ℓ≤A'' ℓ≈A'' ℓMA''}
         {B : CompType ℓB ℓ≤B ℓ≈B ℓMB} {B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
         {B'' : CompType ℓB'' ℓ≤B'' ℓ≈B'' ℓMB''}
         (c : VRelPP A A' ℓc) (c' : VRelPP A' A'' ℓc')
         (d : CRelPP B B' ℓd) (d' : CRelPP B' B'' ℓd')
         (ρc : LeftRepV A A' (c .fst)) (ρc' : LeftRepV A' A'' (c' .fst))
         (ρd : RightRepC B B' (d .fst)) (ρd' : RightRepC B' B'' (d' .fst)) where

  ⟶⊙≈⊙⟶ : QuasiOrderEquivC (A Types.⟶ B) (A'' Types.⟶ B'')
    ((c .fst PRel.⊙ c' .fst) ⟶rel (d .fst ⊙ed d' .fst))
    ((c .fst ⟶rel d .fst) ⊙ed (c' .fst ⟶rel d' .fst))
  ⟶⊙≈⊙⟶ = eqProj→quasiEquivC _ _ ρ₁ ρ₂ eq
    where
      ρ₁ : RightRepC (A Types.⟶ B) (A'' Types.⟶ B'') ((c .fst PRel.⊙ c' .fst) ⟶rel (d .fst ⊙ed d' .fst))
      ρ₁ = RightRepArrow (c .fst PRel.⊙ c' .fst) (d .fst ⊙ed d' .fst)
             (LeftRepV-Comp c c' ρc ρc') (RightRepC-Comp d d' ρd ρd')

      ρ₂ : RightRepC (A Types.⟶ B) (A'' Types.⟶ B'') ((c .fst ⟶rel d .fst) ⊙ed (c' .fst ⟶rel d' .fst))
      ρ₂ = RightRepC-Comp (c RelPP.⟶ d) (c' RelPP.⟶ d')
             (RightRepArrow (c .fst) (d .fst) ρc ρd) (RightRepArrow (c' .fst) (d' .fst) ρc' ρd')

      -- Both projections send g to p_d ∘ p_d' ∘ g ∘ e_c' ∘ e_c.
      eq : projC _ _ _ ρ₁ ≡ projC _ _ _ ρ₂
      eq = eqEDMor _ _ (funExt (λ g → eqPMor _ _ refl))


-- The semantic counterpart of the ⇀-trans equation on type precision
-- derivations: (c ⇀ d) ⊙ (c' ⇀ d') is equivalent to (c ⊙ c') ⇀ (d ⊙ d')
-- as value relations.
module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
         {A'' : ValType ℓA'' ℓ≤A'' ℓ≈A'' ℓMA''}
         {B : ValType ℓB ℓ≤B ℓ≈B ℓMB} {B' : ValType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
         {B'' : ValType ℓB'' ℓ≤B'' ℓ≈B'' ℓMB''}
         (c : ValRel A A' ℓc) (c' : ValRel A' A'' ℓc')
         (d : ValRel B B' ℓd) (d' : ValRel B' B'' ℓd') where

  U⟶F-comp-equiv : ValRel≈ (⊙V (U (c ⟶ F d)) (U (c' ⟶ F d'))) (U (⊙V c c' ⟶ F (⊙V d d')))
  U⟶F-comp-equiv =
    quasiEquivV-trans
      -- U(c ⟶ Fd) ⊙ U(c' ⟶ Fd')  ≈  U((c ⟶ Fd) ⊙ (c' ⟶ Fd'))
      (quasiEquivV-sym
        (Udd'≈UdUd' ((c ⟶ F d) .fst) ((c' ⟶ F d') .fst)
                    ((c ⟶ F d) .snd .fst) ((c' ⟶ F d') .snd .fst)))
      (quasiEquivV-trans
        -- ≈ U((c ⊙ c') ⟶ (Fd ⊙ Fd'))
        (U-quasiEquiv
          (quasiEquivC-sym
            (⟶⊙≈⊙⟶ (c .fst) (c' .fst) ((F d) .fst) ((F d') .fst)
                   (c .snd .fst) (c' .snd .fst) ((F d) .snd .fst) ((F d') .snd .fst))))
        -- ≈ U((c ⊙ c') ⟶ F(d ⊙ d'))
        (U-quasiEquiv
          (⟶-quasiEquiv
            (quasiEquivV-refl _)
            (quasiEquivC-sym (Fcc'≈FcFc' (d .fst) (d' .fst) (d .snd .fst) (d' .snd .fst))))))
