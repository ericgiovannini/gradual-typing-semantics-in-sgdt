{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.PosetModel (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Reflection.RecordEquiv
open import Cubical.Relation.Binary.Poset
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HigherCategories.ThinDoubleCategory.ThinDoubleCat
-- open import Cubical.HigherCategories.ThinDoubleCategory.Constructions.BinProduct

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_ ; _^_)

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
open import Semantics.Concrete.PosetWithPtb k

-- open import Semantics.Abstract.Model.Model


-- open Model



--
-- 1-category where objects are posets with perturbations, and
-- morphisms are monotone functions.
--

VerticalCat : (ℓ ℓ' ℓ'' : Level) -> Category (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) (ℓ-max ℓ ℓ') 
VerticalCat ℓ ℓ' ℓ'' = record
    { ob = PosetWithPtb ℓ ℓ' ℓ''
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
{-
HorizontalCat : (ℓ ℓ' ℓ'' : Level) -> Category (ℓ-suc ℓ) (ℓ-suc ℓ)
HorizontalCat ℓ ℓ' ℓ'' = record
    { ob = PosetWithPtb ℓ ℓ ℓ
    ; Hom[_,_] = PosetWithPtb-Horiz -- PosetWithPtb-Horiz {ℓR = ℓ}
    ; id = λ {X} -> record
                      { R = poset-monrel (X .P)
                      ; fillerL-e = λ δᴮ → δᴮ , {!!}
                      ; fillerL-p = {!!}
                      ; fillerR-e = {!!}
                      ; fillerR-p = {!!}
                      } -- poset-monrel {ℓo = ℓ} (X .P)
    ; _⋆_ = λ R S -> record
                       { R = CompMonRel ( R .PosetWithPtb-Horiz.R) ( S .PosetWithPtb-Horiz.R)
                       ; fillerL-e = λ δᴮ → {!!} , {!!}
                       ; fillerL-p = {!!}
                       ; fillerR-e = {!!}
                       ; fillerR-p = {!!}
                       } --CompMonRel R S
    ; ⋆IdL = λ R -> {!!}
    ; ⋆IdR = λ R -> {!!}
    ; ⋆Assoc = {!!}
    ; isSetHom = PosetWithPtb-Horiz-Set --isSetMonRel
    }
-}
{-
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
