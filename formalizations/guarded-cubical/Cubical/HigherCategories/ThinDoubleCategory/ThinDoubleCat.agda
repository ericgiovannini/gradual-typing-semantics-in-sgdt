{-# OPTIONS --safe #-}
module Cubical.HigherCategories.ThinDoubleCategory.ThinDoubleCat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Preorder

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


-- Double categories for which there is at most one two-cell for
-- every pair of horizontal and vertical morphisms

record MorphismsForObj (ob : Type ℓ) ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Hom[_,_] : ob → ob → Type ℓ'
    id   : ∀ {x} → Hom[ x , x ]
    _⋆_  : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ]) → Hom[ x , z ]
    ⋆IdL : ∀ {x y} (f : Hom[ x , y ]) → id ⋆ f ≡ f
    ⋆IdR : ∀ {x y} (f : Hom[ x , y ]) → f ⋆ id ≡ f
    ⋆Assoc : ∀ {x y z w} (f : Hom[ x , y ]) (g : Hom[ y , z ]) (h : Hom[ z , w ])
           → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
    isSetHom : ∀ {x y} → isSet Hom[ x , y ]


-- Construct a category from the type of objects + the above record
open MorphismsForObj

toCat : (ob : Type ℓ) -> MorphismsForObj ob ℓ' -> Category ℓ ℓ'
toCat ob mor = record {
  ob = ob ;
  Hom[_,_] = mor .Hom[_,_] ;
  id = mor .id ;
  _⋆_ = mor ._⋆_ ;
  ⋆IdL = mor .⋆IdL ;
  ⋆IdR = mor .⋆IdR ;
  ⋆Assoc = mor .⋆Assoc ;
  isSetHom = mor .isSetHom }

CatToMorphisms : (C : Category ℓ ℓ') → MorphismsForObj (C .Category.ob) ℓ'
CatToMorphisms C .Hom[_,_] = Category.Hom[_,_] C
CatToMorphisms C .id = Category.id C
CatToMorphisms C ._⋆_ = Category._⋆_ C
CatToMorphisms C .⋆IdL = Category.⋆IdL C
CatToMorphisms C .⋆IdR = Category.⋆IdR C
CatToMorphisms C .⋆Assoc = Category.⋆Assoc C
CatToMorphisms C .isSetHom = Category.isSetHom C

record ThinDoubleCat ℓ ℓ' ℓ'' ℓ''' : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ'''))) where
  field
    ob : Type ℓ

    -- Horizontal and vertical morphisms and properties
    Vert : MorphismsForObj ob ℓ'
    Horiz : MorphismsForObj ob ℓ''

  -- Horizontal and vertical hom sets
  HomH[_,_] = MorphismsForObj.Hom[_,_] Horiz
  HomV[_,_] = MorphismsForObj.Hom[_,_] Vert

  -- Horizontal and vertical identity 1-morphisms
  idH = MorphismsForObj.id Horiz
  idV = MorphismsForObj.id Vert

  -- Horizontal and vertical composition operations for 1-morphisms
  _⋆H_ = MorphismsForObj._⋆_ Horiz
  _⋆V_ = MorphismsForObj._⋆_ Vert

  field

    -- 2-cells
    2Cell : {x x' y y' : ob} ->
      (f : HomH[ x , y ])  (f' : HomH[ x' , y' ]) ->
      (p : HomV[ x , x' ]) (q : HomV[ y , y' ]) ->
      Type ℓ'''


    -- Horizontal identity 2-cells
    2idH : {x x' : ob} (p : HomV[ x , x' ])  ->
      2Cell idH idH p p


    -- Vertical identity 2-cells
    2idV : {x y : ob} (f : HomH[ x , y ]) ->
      2Cell f f idV idV
      

    -- Horizontal Composition of 2-cells
    _2⋆H_ : ∀ {x x' y y' z z' : ob} ->
      {f  : HomH[ x  , y ]}  {g  : HomH[ y  , z ]} ->
      {f' : HomH[ x' , y' ]} {g' : HomH[ y' , z' ]} ->
      {p : HomV[ x , x' ]}   {q : HomV[ y , y' ]} {r : HomV[ z , z' ]} ->
      2Cell f f' p q ->
      2Cell g g' q r ->
      2Cell (f ⋆H g) (f' ⋆H g') p r
      
      
    -- Vertical Composition of 2-cells
    _2⋆V_ : ∀ {x x' x'' y y' y'' : ob} ->
      {f : HomH[ x , y ]} {f' : HomH[ x' , y' ]} {f'' : HomH[ x'' , y'' ]}
      {p : HomV[ x , x' ]} {p' : HomV[ x' , x'' ]}
      {q : HomV[ y , y' ]} {q' : HomV[ y' , y'' ]} ->
      2Cell f f' p q ->
      2Cell f' f'' p' q' ->
      2Cell f f'' (p ⋆V p') (q ⋆V q')
    
    -- Identity and associativity, and interchange laws are not
    -- needed because of the thin condition below.

    -- Thin condition
    thin : ∀ {x x' y y'}
      (f : HomH[ x , y ])  (f' : HomH[ x' , y' ]) ->
      (p : HomV[ x , x' ]) (q  : HomV[ y , y' ]) ->
      isProp (2Cell f f' p q)



  -- horizontal and vertical composition of 2-cells: alternative to diagramatic order
  _2∘H_ : ∀ {x x' y y' z z' : ob} ->
      {f  : HomH[ x  , y ]}  {g  : HomH[ y  , z ]} ->
      {f' : HomH[ x' , y' ]} {g' : HomH[ y' , z' ]} ->
      {p : HomV[ x , x' ]}   {q : HomV[ y , y' ]} {r : HomV[ z , z' ]} ->
      2Cell g g' q r ->
      2Cell f f' p q ->
      2Cell (f ⋆H g) (f' ⋆H g') p r
  β 2∘H α = α 2⋆H β


  _2∘V_ : ∀ {x x' x'' y y' y'' : ob} ->
      {f : HomH[ x , y ]} {f' : HomH[ x' , y' ]} {f'' : HomH[ x'' , y'' ]}
      {p : HomV[ x , x' ]} {p' : HomV[ x' , x'' ]}
      {q : HomV[ y , y' ]} {q' : HomV[ y' , y'' ]} ->
      2Cell f' f'' p' q' ->
      2Cell f f' p q ->
      2Cell f f'' (p ⋆V p') (q ⋆V q')
  β 2∘V α = α 2⋆V β

  infixr 9 _2⋆H_
  infixr 9 _2∘H_

  infixr 9 _2⋆V_
  infixr 9 _2∘V_


  -- The horizontal and vertical categories associated with this double category
  VCat : Category ℓ ℓ'
  VCat = toCat ob Vert

  HCat : Category ℓ ℓ''
  HCat = toCat ob Horiz

  open Preorderᴰ
  Squares : Preorderᴰ (VCat ×C VCat) ℓ'' ℓ'''
  Squares .ob[_] (A , B) = HCat [ A , B ]
  Squares .Hom[_][_,_] (f , g) R S = 2Cell R S f g
  Squares .idᴰ = 2idV _
  Squares ._⋆ᴰ_ = _2⋆V_
  Squares .isPropHomᴰ = thin _ _ _ _

open ThinDoubleCat

-- Helpful syntax/notation
_V[_,_] : (C : ThinDoubleCat ℓ ℓ' ℓ'' ℓ''') → (x y : C .ob) → Type ℓ'
_V[_,_] = HomV[_,_]

_H[_,_] : (C : ThinDoubleCat ℓ ℓ' ℓ'' ℓ''') → (x y : C .ob) → Type ℓ''
_H[_,_] = HomH[_,_]

-- TODO
-- Unit, associtivity, and interchange properties for 2-cells follow
-- from the thinness condition



{-
-- The horizontal and vertical categories associated with a double category

open MorphismsForObj

toCat : (ob : Type ℓ) -> MorphismsForObj ob ℓ' -> Category ℓ ℓ'
toCat ob mor = record {
  ob = ob ;
  Hom[_,_] = mor .Hom[_,_] ;
  id = mor .id ;
  _⋆_ = mor ._⋆_ ;
  ⋆IdL = mor .⋆IdL ;
  ⋆IdR = mor .⋆IdR ;
  ⋆Assoc = mor .⋆Assoc ;
  isSetHom = mor .isSetHom }


VCat : ThinDoubleCat ℓ ℓ' -> Category ℓ ℓ'
VCat C = toCat (C .ob) (C .Vert)

HCat : ThinDoubleCat ℓ ℓ' -> Category ℓ ℓ'
HCat C = toCat (C .ob) (C .Horiz)
-}
