{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.LockStepErrorOrdering (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Relation.Binary.Base
open import Cubical.HITs.PropositionalTruncation


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

     ℧⊥ : ∀ (ly : L℧ Y) → ℧ ⊑ ly
     ℧⊥ ly = ⊑℧⊥ ly

     -- prop-valued
     isProp⊑ : ∀ lx ly → isProp (lx ⊑ ly)
     isProp⊑ = fix aux
       where
         aux : ▹ (∀ lx ly → isProp (lx ⊑ ly)) →
                  ∀ lx ly → isProp (lx ⊑ ly)
         aux IH lx ly = {!!}


module HetTransitivity
  (X : Type ℓX) (Y : Type ℓY) (Z : Type ℓZ)
  (R : X → Y → Type ℓR) (S : Y → Z → Type ℓS) where

  module LR = LiftOrd X Y R
  module LS = LiftOrd Y Z S

  RS : X → Z → Type {!!}
  RS x z =  ∥ compRel R S x z ∥₁

  module LRS = LiftOrd X Z RS

  het-trans' : ▹ (∀ lx ly lz → lx LR.⊑ ly → ly LS.⊑ lz → lx LRS.⊑ lz) →
                  ∀ lx ly lz → lx LR.⊑ ly → ly LS.⊑ lz → lx LRS.⊑ lz
  het-trans' _ .(η x) .(η y) .(η z) (LR.⊑ηη x y xRy) (LS.⊑ηη .y z ySz) =
    LRS.⊑ηη x z ∣ y , xRy , ySz ∣₁
  het-trans' _ .℧ ly lz (LR.⊑℧⊥ .ly) H2 =
    LRS.⊑℧⊥ lz
  het-trans' IH .(θ lx~) .(θ ly~) .(θ lz~) (LR.⊑θθ lx~ ly~ H~) (LS.⊑θθ .ly~ lz~ H'~) =
    LRS.⊑θθ lx~ lz~ (λ t → IH t (lx~ t) (ly~ t) (lz~ t) (H~ t) (H'~ t)) -- auto solved this!

  het-trans : ∀ lx ly lz → lx LR.⊑ ly → ly LS.⊑ lz → lx LRS.⊑ lz
  het-trans = fix het-trans'


module UpwardClosed
  (X : Type ℓX) (Y : Type ℓY)
  (_≤Y_ : Y → Y → Type ℓ≤Y)
  (R : X → Y → Type ℓR)
  (R-≤Y-upward : ∀ x y y' → R x y → y ≤Y y' → R x y')
  where

  open module LR = LiftOrd X Y R
  open module ⊑Y = LiftOrd Y Y _≤Y_ renaming (_⊑_ to _⊑Y_) 

  ⊑-upward' : ▹ (∀ lx ly ly' → lx ⊑ ly → ly ⊑Y ly' → lx ⊑ ly') →
                 ∀ lx ly ly' → lx ⊑ ly → ly ⊑Y ly' → lx ⊑ ly'
  ⊑-upward' _ .(η x) .(η y) .(η y') (⊑ηη x y xRy) (⊑ηη .y y' y≤y') =
    LR.⊑ηη x y' (R-≤Y-upward x y y' xRy y≤y')
  ⊑-upward' _ .℧ ly ly' (⊑℧⊥ .ly) H2 =
    LR.⊑℧⊥ ly'
  ⊑-upward' IH .(θ lx~) .(θ ly~) .(θ ly'~) (⊑θθ lx~ ly~ H~) (⊑θθ .ly~ ly'~ H'~) =
    LR.⊑θθ lx~ ly'~ (λ t → IH t (lx~ t) (ly~ t) (ly'~ t) (H~ t) (H'~ t)) -- auto solved this!

  ⊑-upward = fix ⊑-upward'


module DownwardClosed
  (X : Type ℓX) (Y : Type ℓY)
  (_≤X_ : X → X → Type ℓ≤X)
  (R : X → Y → Type ℓR)
  (R-≤X-downward : ∀ x' x y → x' ≤X x → R x y → R x' y)
  where

  open module LR = LiftOrd X Y R
  open module ⊑X = LiftOrd X X _≤X_ renaming (_⊑_ to _⊑X_) 

  ⊑-downward' : ▹ (∀ lx' lx ly → lx' ⊑X lx → lx ⊑ ly → lx' ⊑ ly) →
                  ∀ lx' lx ly → lx' ⊑X lx → lx ⊑ ly → lx' ⊑ ly
  ⊑-downward' IH .(η x') .(η x) .(η y) (⊑ηη x' x x'≤x) (⊑ηη .x y xRy) =
    LR.⊑ηη x' y (R-≤X-downward x' x y x'≤x xRy)
  ⊑-downward' IH .℧ lx ly (⊑℧⊥ .lx) H2 =
    LR.⊑℧⊥ ly
  ⊑-downward' IH .(θ lx'~) .(θ lx~) .(θ ly~) (⊑θθ lx'~ lx~ H~) (⊑θθ .lx~ ly~ H'~) =
    LR.⊑θθ lx'~ ly~ (λ t → IH t (lx'~ t) (lx~ t) (ly~ t) (H~ t) (H'~ t))

  ⊑-downward = fix ⊑-downward'
  


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

  -- open LiftOrd X X R public renaming (module Properties to Properties')  -- brings _⊑_ and properties into scope
  open module LR = LiftOrd X X R public renaming (module Properties to Properties')

  module Properties where

    open Properties' public

    -- reflexive
    ⊑-refl : (isReflR : isRefl R) → isRefl _⊑_
    ⊑-refl isReflR = fix aux
      where
        aux : ▹ (isRefl _⊑_)  → isRefl _⊑_
        aux IH (η x) = ⊑ηη x x (isReflR x)
        aux IH ℧ = ⊑℧⊥ ℧
        aux IH (θ lx~) = ⊑θθ lx~ lx~ (λ t → IH t (lx~ t)) -- auto solved this!


  -- anti-symmetric
  ⊑-antisym : isAntisym R → isAntisym _⊑_
  ⊑-antisym isAntisymR = fix aux
    where
      aux : ▹ isAntisym _⊑_ → isAntisym _⊑_
      aux IH .(η x) .(η y) (⊑ηη x y xRy) (⊑ηη y x yRx) = cong η (isAntisymR x y xRy yRx)
      aux IH ℧ ℧ (⊑℧⊥ ℧) (⊑℧⊥ ℧) = refl
      aux IH .(θ lx~) .(θ ly~) (LiftOrd.⊑θθ lx~ ly~ xRy~) (LiftOrd.⊑θθ .ly~ .lx~ yRx~) = 
        cong θ (λ i → λ t → IH t (lx~ t) (ly~ t) (xRy~ t) (yRx~ t) i)

    -- transitive
    ⊑-transitive : isTrans R → isTrans _⊑_
    ⊑-transitive isTransR = fix aux
      where
        aux : ▹ (isTrans _⊑_) → isTrans _⊑_
        aux IH .(η x) .(η y) .(η z) (LiftOrd.⊑ηη x y xRy) (LiftOrd.⊑ηη .y z yRz) =
          ⊑ηη x z (isTransR x y z xRy yRz)
        aux IH .℧ ly lz (LiftOrd.⊑℧⊥ .ly) ly≤lz = LiftOrd.⊑℧⊥ lz
        aux IH .(θ lx~) .(θ ly~) .(θ lz~) (LiftOrd.⊑θθ lx~ ly~ H1~) (LiftOrd.⊑θθ .ly~ lz~ H2~) =
          ⊑θθ lx~ lz~ (λ t → IH t (lx~ t) (ly~ t) (lz~ t) (H1~ t) (H2~ t)) -- auto solved this!
