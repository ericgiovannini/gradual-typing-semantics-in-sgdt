{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.LockStepErrorOrdering (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Relation.Binary.Base


open import Common.Common
open import Semantics.Concrete.GuardedLiftError k
-- open import Semantics.Concrete.GuardedLift k


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓR ℓS : Level
    ℓX ℓY ℓZ : Level
    ℓ≤X ℓ≤Y : Level

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


open BinaryRelation

module LiftOrd (X : Type ℓX) (Y : Type ℓY) (R : X → Y → Type ℓR) where

  data _⊑_ : L℧ X → L℧ Y → Type (ℓ-max (ℓ-max ℓX ℓY) ℓR) where
    ⊑ηη : ∀ (x : X) (y : Y) → R x y → η x ⊑ η y

    ⊑℧⊥ : ∀ ly → ℧ ⊑ ly

    ⊑θθ : ∀ lx~ ly~ → ▸ (λ t → (lx~ t) ⊑ (ly~ t)) → θ lx~ ⊑ θ ly~


  module Elim {B : ∀ lx ly → lx ⊑ ly → Type ℓ'}
    -- In all three of the cases, the user gets to assume that the
    -- eliminator is defined later when constructing an element of B.

    (⊑ηη* : (rec : ▹ (∀ lx ly → (lx⊑ly : lx ⊑ ly) → B lx ly lx⊑ly)) →
            ∀ x y → (xRy : R x y) → B (η x) (η y) (⊑ηη x y xRy))
   
    (⊑℧⊥* : (rec : ▹ (∀ lx ly → (lx⊑ly : lx ⊑ ly) → B lx ly lx⊑ly)) →
            ∀ ly → B ℧ ly (⊑℧⊥ ly))

    (⊑θθ* : (rec : ▹ (∀ lx ly → (lx⊑ly : lx ⊑ ly) → B lx ly lx⊑ly)) →
            ∀ lx~ ly~ → (H~ : ▸ (λ t → (lx~ t) ⊑ (ly~ t))) → B (θ lx~) (θ ly~) (⊑θθ lx~ ly~ H~))
   where

    f : (lx : L℧ X) (ly : L℧ Y) → (lx⊑ly : lx ⊑ ly) → B lx ly lx⊑ly
    f = fix aux
      where
       -- To be able to instantiate the first argument of each of
       -- ⊑ηη*, ⊑℧⊥*, and ⊑θθ* , we need to assume that the eliminator
       -- is defined later.
        aux : ▹ ((lx : L℧ X) (ly : L℧ Y) → (lx⊑ly : lx ⊑ ly) → B lx ly lx⊑ly) →
                 (lx : L℧ X) (ly : L℧ Y) → (lx⊑ly : lx ⊑ ly) → B lx ly lx⊑ly
        aux rec .(η x) .(η y) (⊑ηη x y xRy) = ⊑ηη* rec x y xRy
        aux rec .℧ ly (⊑℧⊥ .ly) = ⊑℧⊥* rec ly
        aux rec .(θ lx~) .(θ ly~) (⊑θθ lx~ ly~ H~) = ⊑θθ* rec lx~ ly~ H~

    -- TODO we may want an unfolding principle for f since it is
    -- defined by guarded fixpoint.


  module Properties where
     η-monotone : {x : X} {y : Y} → R x y → (η x) ⊑ (η y)
     η-monotone {x = x} {y = y} xRy = ⊑ηη x y xRy

     ℧-bot : (ly : L℧ Y) → ℧ ⊑ ly
     ℧-bot ly = ⊑℧⊥ ly

     θ-monotone : {lx~ : ▹ L℧ X} {ly~ : ▹ L℧ Y} →
       ▸ (λ t → lx~ t ⊑ ly~ t) → θ lx~ ⊑ θ ly~
     θ-monotone {lx~ = lx~} {ly~ = ly~} H = ⊑θθ lx~ ly~ H

     δ-monotone : {lx : L℧ X} {ly : L℧ Y} → lx ⊑ ly → (δ lx) ⊑ (δ ly)
     δ-monotone {lx = lx} {ly = ly} lx⊑ly = θ-monotone (next lx⊑ly)

     δ^n-monotone : {lx : L℧ X} {ly : L℧ Y} (n : ℕ) ->
        lx ⊑ ly -> ((δ ^ n) lx) ⊑ ((δ ^ n) ly)
     δ^n-monotone zero lx⊑ly = lx⊑ly
     δ^n-monotone (suc n) lx⊑ly = δ-monotone (δ^n-monotone n lx⊑ly)

     -- prop-valued
     isProp⊑ : ∀ lx ly → isProp (lx ⊑ ly)
     isProp⊑ = fix aux
       where
         aux : ▹ (∀ lx ly → isProp (lx ⊑ ly)) →
                  ∀ lx ly → isProp (lx ⊑ ly)
         aux IH lx ly = {!!}



module Monotone (X : Type ℓX) (Y : Type ℓY)
                (_≤X_ : X → X → Type ℓ≤X)
                (_≤Y_ : Y → Y → Type ℓ≤Y)
                (R : X → Y → Type ℓR)
                (R-≤X-downward : ∀ x' x y → x' ≤X x → R x y → R x' y)
                (R-≤Y-upward : ∀ x y y' → R x y → y ≤Y y' → R x y') where

  open module LR = LiftOrd X Y R
  open module ⊑X = LiftOrd X X _≤X_ renaming (_⊑_ to _⊑X_) 
  open module ⊑Y = LiftOrd Y Y _≤Y_ renaming (_⊑_ to _⊑Y_) 

  ⊑-monotone' : ▹ (∀ lx ly ly' → lx ⊑ ly → ly ⊑Y ly' → lx ⊑ ly') →
                   ∀ lx ly ly' → lx ⊑ ly → ly ⊑Y ly' → lx ⊑ ly'
  ⊑-monotone' _ .(η x) .(η y) .(η y') (⊑ηη x y xRy) (⊑ηη .y y' y≤y') =
    LR.⊑ηη x y' (R-≤Y-upward x y y' xRy y≤y')
  ⊑-monotone' _ .℧ ly ly' (⊑℧⊥ .ly) H2 =
    LR.⊑℧⊥ ly'
  ⊑-monotone' IH .(θ lx~) .(θ ly~) .(θ ly'~) (⊑θθ lx~ ly~ H~) (⊑θθ .ly~ ly'~ H'~) =
    LR.⊑θθ lx~ ly'~ (λ t → IH t (lx~ t) (ly~ t) (ly'~ t) (H~ t) (H'~ t)) -- auto solved this!

  ⊑-montone = fix ⊑-monotone'

  ⊑-antitone' : ▹ (∀ lx' lx ly → lx' ⊑X lx → lx ⊑ ly → lx' ⊑ ly) →
                   ∀ lx' lx ly → lx' ⊑X lx → lx ⊑ ly → lx' ⊑ ly
  ⊑-antitone' IH .(η x') .(η x) .(η y) (⊑ηη x' x x'≤x) (⊑ηη .x y xRy) =
    LR.⊑ηη x' y (R-≤X-downward x' x y x'≤x xRy)
  ⊑-antitone' IH .℧ lx ly (⊑℧⊥ .lx) H2 =
    LR.⊑℧⊥ ly
  ⊑-antitone' IH .(θ lx'~) .(θ lx~) .(θ ly~) (⊑θθ lx'~ lx~ H~) (⊑θθ .lx~ ly~ H'~) =
    LR.⊑θθ lx'~ ly~ (λ t → IH t (lx'~ t) (lx~ t) (ly~ t) (H~ t) (H'~ t))

  ⊑-antitone = fix ⊑-antitone'
  


    -- let foo = LR.Elim.f
    --             {B = λ lx ly lx⊑ly → ∀ ly' → ly ⊑Y ly' → lx ⊑ ly'}
    --             --(λ rec x y xRy → λ ly' ηy⊑ly' → {!!})
    --             --(λ rec → {!!})
    --            {!!}
    --            {!!}
    --            {!!} lx ly H1
    -- in {!!}

  
  

-- Lifting a relation on X to a relation on L℧ X
module LiftOrdHomogenous (X : Type ℓX) (R : X → X → Type ℓR) where

  open LiftOrd X X R public -- brings _⊑_ and properties into scope

  -- reflexive
  ⊑-refl : (isReflR : isRefl R) → isRefl _⊑_
  ⊑-refl isReflR = fix aux
    where
      aux : ▹ (isRefl _⊑_)  → isRefl _⊑_
      aux IH (η x) = ⊑ηη x x (isReflR x)
      aux IH ℧ = ⊑℧⊥ ℧
      aux IH (θ lx~) = ⊑θθ lx~ lx~ (λ t → IH t (lx~ t)) -- auto solved this!
    

  -- anti-symmetric
  ⊑-antisym : (isAntisym _⊑_)
  ⊑-antisym = {!!}


  -- transitive
  ⊑-transitive : isTrans R → isTrans _⊑_
  ⊑-transitive isTransR = {!!}
    where
      aux : ▹ (isTrans _⊑_) → isTrans _⊑_
      aux IH .(η x) .(η y) .(η z) (LiftOrd.⊑ηη x y xRy) (LiftOrd.⊑ηη .y z yRz) =
        ⊑ηη x z (isTransR x y z xRy yRz)
      aux IH .℧ ly lz (LiftOrd.⊑℧⊥ .ly) ly≤lz = {!!}
      aux IH .(θ lx~) .(θ ly~) lz (LiftOrd.⊑θθ lx~ ly~ x) ly≤lz = {!!}
