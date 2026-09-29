{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.Limits.Terminal (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Data.Sigma

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k

private
  variable
    ℓ ℓ' : Level
    ℓob ℓv ℓh ℓsq ℓ≈ : Level

module _ (C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈) where

  private open module C = ThinDoubleCat C

  isTerminalV : (x : ob) → Type (ℓ-max ℓob ℓv)
  isTerminalV x = ∀ (y : ob) → isContr (vhom[ y , x ])

  TerminalV : Type (ℓ-max ℓob ℓv)
  TerminalV = Σ[ x ∈ ob ] isTerminalV x

  terminalOb : TerminalV → ob
  terminalOb = fst

  terminalArrow : (T : TerminalV) (y : ob) → vhom[ y , terminalOb T ]
  terminalArrow T y = T .snd y .fst

  terminalArrowUnique : {T : TerminalV} {y : ob} (f : vhom[ y , terminalOb T ])
                      → terminalArrow T y ≡ f
  terminalArrowUnique {T} {y} f = T .snd y .snd f

  terminalEndoIsId : (T : TerminalV) (f : vhom[ terminalOb T , terminalOb T ])
                   → f ≡ idV
  terminalEndoIsId T f = isContr→isProp (T .snd (terminalOb T)) f idV

  hasTerminal : Type (ℓ-max ℓv ℓob)
  hasTerminal = ∥ TerminalV ∥₁


  module _ (T : TerminalV) where

    T-ob = terminalOb T

    module _ (T-hhom : hhom[ T-ob , T-ob ]) where

    -- for all r : x --|-- y, there exists a square:
    --
    --         r        
    --    x ---|--- y   
    --    |         |   
    -- !x |         | !y
    --    v         v   
    --    T ---|--- T   
    --      T-hhom
    --
    -- Uniqueness is automatic since the squares are thin.

      isTerminalH : Type (ℓ-max (ℓ-max ℓob ℓh) ℓsq)
      isTerminalH = ∀ {z₁ z₂ : ob} {q : hhom[ z₁ , z₂ ]}
        → sq q T-hhom (terminalArrow T z₁) (terminalArrow T z₂)


    TerminalH : Type (ℓ-max (ℓ-max ℓob ℓh) ℓsq)
    TerminalH = Σ[ T-hhom ∈ hhom[ T-ob , T-ob ] ] (isTerminalH T-hhom)



  record Terminal : Type (ℓ-max (ℓ-max ℓob ℓv) (ℓ-max ℓh ℓsq)) where
    field
      termV : TerminalV
      termH : TerminalH termV
