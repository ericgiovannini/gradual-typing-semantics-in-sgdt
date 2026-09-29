{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Later

module Semantics.Demo (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum


private
  variable
    ℓ ℓ' : Level

private
  ▹_ : Type ℓ -> Type ℓ
  ▹ A = ▹_,_ k A

-- guarded lift monad

module Test1 where

  data L (X : Type ℓ) : Type ℓ where
    η : X → L X
    θ : ▹ (L X) → L X

  -- μ T . X + ▹ T

  δ : {X : Type ℓ} → L X → L X
  δ l = θ (next l)

  Ω : {X : Type ℓ} →  L X
  Ω = fix θ


  -- fix f ≡ f (next (fix f))

  unfold-Ω : {X : Type ℓ} →  (Ω {X = X}) ≡ δ Ω
  unfold-Ω = fix-eq θ

  join' : {X : Type ℓ} →
   ▹ (L (L X) → L X) →
      L (L X) → L X
  join' _ (η lx) = lx
  join' IH (θ llx~) = θ (λ t → IH t (llx~ t))

  join : {X : Type ℓ} → L (L X) → L X
  join = fix join'

  unfold-join : {X : Type ℓ} → join {X = X} ≡ (join' (next join))
  unfold-join = fix-eq join'


  module _ {X : Type ℓ} where

    lem1 : (lx : L X) → join (η lx) ≡ lx
    lem1 lx = funExt⁻ unfold-join (η lx)


module Test2 where

  L' : (X : Type ℓ) → ▹ Type ℓ → Type ℓ
  L' X L~ = X ⊎ (▸ L~)

  L : (X : Type ℓ) → Type ℓ
  L X = fix {k = k} (L' X)


  module _ (X : Type ℓ) where

    foo : (A : Type ℓ) → ▸ (next {k = k} A) ≡ ▹ A
    foo A = refl
    --
    -- ▸ : ▹ Type → Type
    -- 
    -- ▸ T~ = (t : Tick) → T~ t
    --        -----------------
    --            : Type
    -- 
    -- ▸ (next T) = (t : Tick) → (next T) t = (t : Tick) → T = ▹ T

    -- Know: L X ≡ L' X (next (L X))
    unfold-L : L X ≡ (X ⊎ (▹ (L X)))
    unfold-L = fix-eq (L' X)

    LX : Type ℓ
    LX = L X

    L'X : Type ℓ
    L'X = L' X (next (L X))

    unfold : LX ≡ L'X
    unfold = fix-eq (L' X)

    L'→L : L'X → LX
    L'→L = transport⁻ unfold

    L→L' : L (L X) → L' (L'X) (next (L (L X)))
    L→L' = {!!}


    join' :
      ▹ (L' (L'X) (next (L (L X))) → L'X) →
         L' (L'X) (next (L (L X))) → L'X
    join' IH (inl lx) = lx
    join' IH (inr lx~) = inr (λ t → L'→L (IH t (L→L' (lx~ t))))


module Test3 where

  data L' (X : Type ℓ) (L~ : ▹ Type ℓ) : Type ℓ where
    η : X → L' X L~
    θ : ▸ L~ → L' X L~

  L : (X : Type ℓ) → Type ℓ
  L X = fix (L' X)




open Test1 renaming (L to L1)
open Test3 renaming (L to L3)


-- Test1.L    μ     L  . X + ▹ L     -- F Y = X + Y ----> μ L.    F (▹ L)
-- Test3.L    fix   L~ . X + ▸ L~    -- F Y = X + Y ----> fix L~. F (▸ L~)


-- Define Tree := μ T. X + ▹ T
-- Define L : = Tree
--
-- Then we have
--  L = Tree           [ definition ]
--    = μ T. X + (▹ T) [ definition ]
--    = X + (▹ Tree)   [ unfold the least fixpoint ]
--    = X + (▹ L)      [ definition ] 


-- Define Tree Y := μ T. X + Y
-- Define L' := λ L~. Tree (▸ L~)
-- Define L := fix L'

-- L = fix L'              [ definition ]
--   = L' (next L)         [ unfold the guarded fixpoint ]
--   = Tree (▸ (next L))   [ definition ]
--   = Tree (▹ L)          [ definition ]
--   = μ T. X + ▹ L        [ definition ]
--   = X + ▹ L             [ remove μ T ]



theorem : (X : Type ℓ) → Iso (L1 X) (L3 X)
theorem X = {!!}


-- μ X . 1 + A * X
-- ν X . 1 + A * X
