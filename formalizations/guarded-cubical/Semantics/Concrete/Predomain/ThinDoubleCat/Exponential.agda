{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.Exponential (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Limits.BinProduct k

private
  variable
    ℓ ℓ' : Level
    ℓob ℓv ℓh ℓsq ℓ≈ : Level

module _ (C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈) where

  private open module C = ThinDoubleCat C


  module _ (prod : BinProductsV C) where

    open BinProdsV C prod

    module _ {y z y⇒z : ob}
      (ev : vhom[ y⇒z ×ob y , z ]) where

      record isExpV : Type (ℓ-max (ℓ-max ℓob ℓv) ℓ≈) where
        field
          ump : ∀ {x : ob} → (g : vhom[ x ×ob y , z ])
            → ∃![ λg ∈ vhom[ x , y⇒z ] ] (((λg ×v idV) ⋆V ev) ≡ g)

        lambda : ∀ {x : ob} → (g : vhom[ x ×ob y , z ]) → vhom[ x , y⇒z ]
        lambda g = ump g .fst .fst

        field
          ump-bisim : ∀ {x} (g g' : vhom[ x ×ob y , z ])
            → g ≈vhom g'
            → lambda g ≈vhom lambda g'

          ump-bisim-inv : ∀ {x} (g g' : vhom[ x ×ob y , z ])
            → lambda g ≈vhom lambda g'
            → g ≈vhom g'


    record ExpV (y z : ob) : Type (ℓ-max (ℓ-max ℓob ℓv) ℓ≈) where
      field
        expOb : ob
        expEv : vhom[ expOb ×ob y , z ]
        univProp : isExpV expEv


