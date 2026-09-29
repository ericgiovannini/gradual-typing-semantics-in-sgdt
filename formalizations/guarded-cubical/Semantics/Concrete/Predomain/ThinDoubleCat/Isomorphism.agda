{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.Isomorphism (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Data.Sigma

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k

private
  variable
    ℓ : Level
    ℓob ℓv ℓh ℓsq ℓ≈ : Level


module _ (C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈) where

  open ThinDoubleCat C

  record isIsoV {x y : ob} (f : vhom[ x , y ]) : Type ℓv where
    constructor isisoV
    field
      inv : C [ y , x ]v
      sec : inv ⋆V f ≡ idV
      ret : f ⋆V inv ≡ idV

  CatIsoV : (x y : ob) → Type ℓv
  CatIsoV x y = Σ[ f ∈ vhom[ x , y ] ] isIsoV f

  open isIsoV

  record isIsoSq
      {xᵢ yᵢ xₒ yₒ : ob}
      {cᵢ  : hhom[ xᵢ , yᵢ ]}
      {cₒ  : hhom[ xₒ , yₒ ]}
      {f   : vhom[ xᵢ , xₒ ]}
      {g   : vhom[ yᵢ , yₒ ]}
      (fInv : isIsoV f)
      (gInv : isIsoV g)
      (square : sq cᵢ cₒ f g) : Type ℓsq where

      field
        inv : sq cₒ cᵢ (fInv .inv) (gInv .inv)

        -- no equations are needed, as the squares are thin
