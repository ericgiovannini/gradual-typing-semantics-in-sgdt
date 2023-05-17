{-# OPTIONS --safe #-}
-- Reflexive graph of preorder enriched categories
module Cubical.HigherCategories.RGPEC where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Relation.Binary.Base

open import Cubical.HigherCategories.PreorderEnriched.PreorderEnriched

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓc ℓc' ℓc'' ℓd ℓd' ℓd'' : Level

open BinaryRelation
open Category
open PreorderEnrichedCategory

-- Notation note: l, r stand for left, right and t, m, b stand for top, middle, bottom
-- We visualize these squares having the morphisms of the pe-cat be
-- vertical and the Rels being horizontal
record RGPEC ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' (ℓ-max ℓ''' ℓ''''))))) where
  field
    pe-cat : PreorderEnrichedCategory ℓ ℓ' ℓ''
    HRel : ∀ (x y : pe-cat .cat .ob) → Type ℓ'''
    Sq : ∀ {xtl xtr xbl xbr : pe-cat .cat .ob}
        → (Rt : HRel xtl xtr)
        → (fl : pe-cat .cat [ xtl , xbl ])
        → (fr : pe-cat .cat [ xtr , xbr ])
        → (Rb : HRel xbl xbr)
        → Type ℓ''''
    -- Could drop this but more laws
    isPropSq : ∀ {xtl xtr xbl xbr}
        → (Rt : HRel xtl xtr)
        → (fl : pe-cat .cat [ xtl , xbl ])
        → (fr : pe-cat .cat [ xtr , xbr ])
        → (Rb : HRel xbl xbr)
        → isProp (Sq Rt fl fr Rb)
    IdRel : ∀ {x} → HRel x x
    idSq : ∀ {xl xr} → (R : HRel xl xr) → Sq R (pe-cat .cat .id) (pe-cat .cat .id) R
    _⋆Sq_ : ∀ {xtl xtr xml xmr xbl xbr}
          → {Rt : HRel xtl xtr}
          → {ftl : pe-cat .cat [ xtl , xml ]}
          → {ftr : pe-cat .cat [ xtr , xmr ]}
          → {Rm : HRel xml xmr}
          → {fbl : pe-cat .cat [ xml , xbl ]}
          → {fbr : pe-cat .cat [ xmr , xbr ]}
          → {Rb : HRel xbl xbr}
          → (St : Sq Rt ftl ftr Rm)
          → (Sb : Sq Rm fbl fbr Rb)
          → Sq Rt (ftl ⋆⟨ pe-cat .cat ⟩ fbl) (ftr ⋆⟨ pe-cat .cat ⟩ fbr) Rb
    reflSq : ∀ {xt xb} (f : pe-cat .cat [ xt , xb ]) → Sq IdRel f f IdRel
    transSqL : ∀ {xtl xtr xbl xbr}
        → {Rt : HRel xtl xtr}
        → {fl : pe-cat .cat [ xtl , xbl ]}
        → {fl' : pe-cat .cat [ xtl , xbl ]}
        → {fr : pe-cat .cat [ xtr , xbr ]}
        → {Rb : HRel xbl xbr}
        → (Sq Rt fl fr Rb)
        → pe-cat ._≤_ fl' fl
        → (Sq Rt fl' fr Rb)
    transSqR : ∀ {xtl xtr xbl xbr}
        → {Rt : HRel xtl xtr}
        → {fl : pe-cat .cat [ xtl , xbl ]}
        → {fr : pe-cat .cat [ xtr , xbr ]}
        → {fr' : pe-cat .cat [ xtr , xbr ]}
        → {Rb : HRel xbl xbr}
        → (Sq Rt fl fr Rb)
        → pe-cat ._≤_ fr fr'
        → (Sq Rt fl fr' Rb)

    -- This is like a form of univalence: We know f ≤ g ⇒ Sq Id f g Id
    -- (by refl & trans) and this requires that to be an equivalence
    identity-extension : ∀ {x y : pe-cat .cat .ob} → (f g : pe-cat .cat [ x , y ])
                       → Sq IdRel f g IdRel → pe-cat ._≤_ f g
