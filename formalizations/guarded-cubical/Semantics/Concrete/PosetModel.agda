{-# OPTIONS --rewriting --guarded #-}

open import Common.Later

module Semantics.Concrete.PosetModel (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Relation.Binary.Poset
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HigherCategories.ThinDoubleCategory.ThinDoubleCat
open import Cubical.HigherCategories.ThinDoubleCategory.Constructions.BinProduct

open import Cubical.Algebra.Monoid.Base

open import Cubical.Data.Sigma


open import Cubical.Categories.Category.Base

open import Common.Common

open import Semantics.Lift k
open import Semantics.LockStepErrorOrdering k
open import Semantics.Concrete.DynNew k
open import Common.Poset.Convenience
open import Common.Poset.Constructions
open import Common.Poset.Monotone
open import Common.Poset.MonotoneRelation
open import Semantics.MonotoneCombinators


open import Semantics.Abstract.Model.Model


open Model

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


-- Monoid of all monotone endofunctions on a poset
EndoMonFun : (X : Poset ℓ ℓ') -> Monoid (ℓ-max ℓ ℓ')
EndoMonFun X = makeMonoid {M = MonFun X X} Id mCompU MonFunIsSet
  (λ f g h -> eqMon _ _ refl) (λ f -> eqMon _ _ refl) (λ f -> eqMon _ _ refl)

--
-- A poset along with a monoid of monotone perturbation functions
--
record PosetWithPtb (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    P       : Poset ℓ ℓ'
    Perturb : Monoid ℓ'
    perturb : MonoidHom Perturb (EndoMonFun P)
    --TODO: needs to be injective map
    -- Perturb : ⟨ EndoMonFun P ⟩

  ptb-fun : ⟨ Perturb ⟩ -> ⟨ EndoMonFun P ⟩
  ptb-fun = perturb .fst

open PosetWithPtb

--
-- Monotone functions on Posets with Perturbations
--
PosetWithPtb-Vert : {ℓ ℓ' : Level} (P1 P2 : PosetWithPtb ℓ ℓ') -> Type (ℓ-max ℓ ℓ')
PosetWithPtb-Vert P1 P2 = MonFun (P1 .P) (P2 .P)
-- TODO should there be a condition on preserving the perturbations?


--
-- Monotone relations on Posets with Perturbations
--
{-
PosetWithPtb-Horiz : {ℓ ℓ' ℓR : Level} (P1 P2 : PosetWithPtb ℓ ℓ') ->
  Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓR))
PosetWithPtb-Horiz {ℓR = ℓR} P1 P2 = MonRel (P1 .P) (P2 .P) ℓR
-}

record PosetWithPtb-Horiz {ℓ ℓ' ℓR : Level} (P1 P2 : PosetWithPtb ℓ ℓ') :
  Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓR)) where
  open PosetWithPtb
  field
    R : MonRel (P1 .P) (P2 .P) ℓR
    fillerL-e : ∀ (δᴮ : ⟨ P2 .Perturb ⟩ ) ->
      ∃[ δᴬ ∈ ⟨ P1 .Perturb ⟩ ]
        TwoCell (R .MonRel.R) (R .MonRel.R)
              (MonFun.f (ptb-fun P1 δᴬ)) (MonFun.f (ptb-fun P2 δᴮ))
    fillerL-p : {!!}
    fillerR-e : ∀ (δᴬ : ⟨ P1 .Perturb ⟩) ->
      ∃[ δᴮ ∈ ⟨ P2 .Perturb ⟩ ]
        TwoCell (R .MonRel.R) (R .MonRel.R)
              (MonFun.f (ptb-fun P1 δᴬ)) (MonFun.f (ptb-fun P2 δᴮ))
    fillerR-p : {!!}


-- TODO: Show this is a set by showing that the Sigma type it is iso to
-- is a set (ΣIsSet2ndProp)

PosetWithPtb-Horiz-Set : ∀ {ℓ ℓ' ℓR : Level} {P1 P2 : PosetWithPtb ℓ ℓ'} ->
  isSet (PosetWithPtb-Horiz P1 P2)
PosetWithPtb-Horiz-Set = {!!}

{-

--
-- 1-category where objects are posets with perturbations, and
-- morphisms are monotone functions.
--

VerticalCat : (ℓ ℓ' : Level) -> Category
    (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
    (ℓ-max ℓ ℓ')
VerticalCat ℓ ℓ' = record
    { ob = PosetWithPtb ℓ ℓ'
    ; Hom[_,_] = λ X Y -> PosetWithPtb-Vert X Y
    ; id = MonId
    ; _⋆_ = MonComp
    ; ⋆IdL = λ {X} {Y} f -> eqMon f f refl
    ; ⋆IdR = λ {X} {Y} f -> eqMon f f refl
    ; ⋆Assoc = λ {X} {Y} {Z} {W} f g h -> eqMon _ _ refl
    ; isSetHom = MonFunIsSet }


--
-- 1-category where objects are posets with perturbations, and
-- morphisms are monotone relations
--
-- Because the composition of relations involves an ℓ-max ℓ ℓ',
-- we require that ℓ = ℓ' in order for composition to make sense.
-- Otherwise, the level would continually increase with each composition.
--
HorizontalCat : (ℓ ℓ' : Level) -> Category (ℓ-suc ℓ) (ℓ-suc ℓ)
HorizontalCat ℓ ℓ' = record
    { ob = PosetWithPtb ℓ ℓ
    ; Hom[_,_] = PosetWithPtb-Horiz {ℓR = ℓ}
    ; id = λ {X} -> poset-monrel {ℓo = ℓ} (X .P)
    ; _⋆_ = λ R S -> CompMonRel R S
    ; ⋆IdL = λ R -> CompUnitLeft R
    ; ⋆IdR = λ R -> {!!}
    ; ⋆Assoc = {!!}
    ; isSetHom = isSetMonRel
    }


--
-- The thin double category of posets, monotone functions and monotone relations
--
open ThinDoubleCat

module _ (ℓ ℓ' ℓ'' ℓ''' : Level) where

  open MonRel
  open MonFun

  PosetDoubleCat : ThinDoubleCat (ℓ-suc ℓ) (ℓ-max ℓ ℓ) (ℓ-suc ℓ) ℓ
  PosetDoubleCat .ob = PosetWithPtb ℓ ℓ
  PosetDoubleCat .Vert =  CatToMorphisms (VerticalCat ℓ ℓ)
  PosetDoubleCat .Horiz = CatToMorphisms (HorizontalCat ℓ ℓ)
  PosetDoubleCat .2Cell = λ c d f g ->
                            TwoCell (c .R) (d .R) (f .MonFun.f) (g .MonFun.f)
  PosetDoubleCat .2idH = {!!}
  PosetDoubleCat .2idV = {!!}
  PosetDoubleCat ._2⋆H_ = {!!}
  PosetDoubleCat ._2⋆V_ = {!!}
  PosetDoubleCat .thin = λ c d f g -> isPropTwoCell (d .is-prop-valued)

--
-- The model
--
model : Model {!!} {!!} {!!} {!!}
model .cat = PosetDoubleCat {!!} {!!} {!!} {!!}
model .term = {!!}
model .prod = {!!}
model .Ptb = {!!}
model .ptb = {!!}
model .nat  = {!!}
model .dyn = {!!}


-}
