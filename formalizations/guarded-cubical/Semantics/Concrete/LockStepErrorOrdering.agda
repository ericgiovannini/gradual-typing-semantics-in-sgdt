{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.LockStepErrorOrdering (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Nat hiding (_^_ ; _+_)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Relation.Binary.Base
open import Cubical.HITs.PropositionalTruncation


open import Common.Common
open import Semantics.Concrete.DoublePoset.Error
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.GuardedLift k
  using () renaming (η to ηL)


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

  RS : X → Z → Type (ℓ-max (ℓ-max ℓY ℓR) ℓS)
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
    ⊑-antisym : isAntisym R → (isAntisym _⊑_)
    ⊑-antisym isAntisymR = fix aux
      where
        aux : ▹ (isAntisym _⊑_) → isAntisym _⊑_
        aux IH .(η x) .(η y) (⊑ηη x y xRy) (⊑ηη y x yRx) = cong η (isAntisymR x y xRy yRx)
        aux IH .℧ .℧ (⊑℧⊥ x) (⊑℧⊥ y) = refl
        aux IH .(θ lx~) .(θ ly~) (⊑θθ lx~ ly~ lx~⊑ly~) (⊑θθ ly~ lx~ ly~⊑lx~) =
          cong θ (later-ext (λ t → IH t (lx~ t) (ly~ t) (lx~⊑ly~ t) (ly~⊑lx~ t)))


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





-- Clocked lock-step error ordering as a sum-type.

ret : {X : Type ℓ} → X → L (X ⊎ ⊤)
ret x = L.η (inl x)

err : {X : Type ℓ} → L (X ⊎ ⊤)
err = L.η (inr tt)


module AsSum (X : Type ℓ) (Y : Type ℓ') (R : X → Y → Type ℓR) where

  private
    _+_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
    _+_ = _⊎_
    infixr 20 _+_

  module Rec (rec : (▹ (L (X ⊎ ⊤) → L (Y ⊎ ⊤) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)))) where

    _⊑S'_ :  L (X ⊎ ⊤) → L (Y ⊎ ⊤) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
    _⊑S'_ l1 l2 =
        (Σ[ x ∈ X ] Σ[ y ∈ Y ] (l1 ≡ ret x) × (l2 ≡ ret y) × R x y)
      + (l1 ≡ err)
      + (Σ[ l1~ ∈ ▹ L (X ⊎ ⊤) ] Σ[ l2~ ∈ ▹ L (Y ⊎ ⊤) ]
          (l1 ≡ θ l1~) × (l2 ≡ θ l2~) × (▸ (λ t → rec t (l1~ t) (l2~ t))))

  _⊑S_ : L (X ⊎ ⊤) → L (Y ⊎ ⊤) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
  _⊑S_ = fix Rec._⊑S'_

  unfold-⊑S : _⊑S_ ≡ Rec._⊑S'_ (next _⊑S_)
  unfold-⊑S = fix-eq Rec._⊑S'_

  open Rec (next _⊑S_)

  ⊑S'→⊑S : (l : L (X ⊎ ⊤)) (l' : L (Y ⊎ ⊤)) -> l ⊑S' l' -> l ⊑S l'
  ⊑S'→⊑S l l' l⊑S'l' = transport (sym (λ i -> unfold-⊑S i l l')) l⊑S'l'

  ⊑S→⊑S' : (l : L (X ⊎ ⊤)) (l' : L (Y ⊎ ⊤)) -> l ⊑S l' -> l ⊑S' l'
  ⊑S→⊑S' l l' l⊑Sl' = transport (λ i -> unfold-⊑S i l l') l⊑Sl'


module _ {X : Type ℓ} where

  module Rec (rec : ▹ (L℧ X → L (X ⊎ ⊤))) where

    L-ErrorX→L-X⊎⊤' : (L℧ X → L (X ⊎ ⊤))
    L-ErrorX→L-X⊎⊤' (η x) = L.η (inl x)
    L-ErrorX→L-X⊎⊤' ℧ = L.η (inr tt)
    L-ErrorX→L-X⊎⊤' (θ lx~) = θ (λ t → rec t (lx~ t))

  L-ErrorX→L-X⊎⊤ = fix Rec.L-ErrorX→L-X⊎⊤'
  
  unfold : L-ErrorX→L-X⊎⊤ ≡ Rec.L-ErrorX→L-X⊎⊤' (next L-ErrorX→L-X⊎⊤)
  unfold = fix-eq _

-- The original definition of lock-step error ordering implies the
-- definition as a sum-type.
module _ (X : Type ℓ) (Y : Type ℓ') (R : X → Y → Type ℓR) (k : Clock) where

  open module LR = LiftOrd X Y R
  open module Sum = AsSum X Y R hiding (module Rec)
  open Sum.Rec (next _⊑S_)
  LError→LSumX  = L-ErrorX→L-X⊎⊤ {X = X}
  LError→LSumX' = Rec.L-ErrorX→L-X⊎⊤' {X = X} (next L-ErrorX→L-X⊎⊤)
  LError→LSumY  = L-ErrorX→L-X⊎⊤ {X = Y}
  LError→LSumY' = Rec.L-ErrorX→L-X⊎⊤' {X = Y} (next L-ErrorX→L-X⊎⊤)


  ⊑→⊑S : (l : L℧ X) (l' : L℧ Y) → l ⊑ l' → mapL ErrorX→X⊎⊤ l ⊑S mapL ErrorX→X⊎⊤ l'
  ⊑→⊑S l l' l⊑l' =
    transport (sym (λ i → funExt⁻ (unfold-mapL ErrorX→X⊎⊤) l i ⊑S funExt⁻ (unfold-mapL ErrorX→X⊎⊤) l' i))
      (⊑S'→⊑S _ _ (fix lem l l' l⊑l'))
    where
      lem : ▹ ((l : L℧ X) (l' : L℧ Y) → l ⊑ l' → mapL' ErrorX→X⊎⊤ l ⊑S' mapL' ErrorX→X⊎⊤ l') →
               (l : L℧ X) (l' : L℧ Y) → l ⊑ l' → mapL' ErrorX→X⊎⊤ l ⊑S' mapL' ErrorX→X⊎⊤ l'
      lem _ .(η x) .(η y) (⊑ηη x y xRy) = inl (x , y , refl , refl , xRy) 
      lem _ .(℧) ly (⊑℧⊥ ly) = inr (inl refl)
      lem IH .(θ lx~) .(θ ly~) (⊑θθ lx~ ly~ H~) = inr (inr (map▹ (mapL ErrorX→X⊎⊤) lx~ , map▹ (mapL ErrorX→X⊎⊤) ly~ , refl , refl ,
        λ t → transport
          ((sym (λ i → funExt⁻ (unfold-mapL ErrorX→X⊎⊤) (lx~ t) i ⊑S  funExt⁻ (unfold-mapL ErrorX→X⊎⊤) (ly~ t) i)))
          ((⊑S'→⊑S (mapL' ErrorX→X⊎⊤ (lx~ t)) (mapL' ErrorX→X⊎⊤ (ly~ t)) (IH t (lx~ t) (ly~ t) (H~ t))))))       

  
  -- ⊑→⊑S : (l : L℧ X) (l' : L℧ Y) → l ⊑ l' →
  --   L-ErrorX→L-X⊎⊤ l ⊑S L-ErrorX→L-X⊎⊤ l' -- l ⊑S l'
  -- ⊑→⊑S l l' l⊑l' =
  --   transport (sym (λ i → funExt⁻ unfold l i ⊑S funExt⁻ unfold l' i)) (⊑S'→⊑S _ _ (fix lem l l' l⊑l'))
  --   where
  --     lem : ▹ ((l : L℧ X) (l' : L℧ Y) → l ⊑ l' → LError→LSumX' l ⊑S' LError→LSumY' l') →
  --              (l : L℧ X) (l' : L℧ Y) → l ⊑ l' → LError→LSumX' l ⊑S' LError→LSumY' l'
  --     lem _ .(η x) .(η y) (⊑ηη x y xRy) = inl (x , y , refl , refl , xRy)
  --     lem _ .(℧) ly (⊑℧⊥ ly) = inr (inl refl)
  --     lem IH .(θ lx~) .(θ ly~) (⊑θθ lx~ ly~ H~) =
  --       inr (inr (map▹ LError→LSumX lx~ , map▹ LError→LSumY ly~ , refl , refl ,
  --                 (λ t → transport (sym (λ i → funExt⁻ unfold (lx~ t) i ⊑S funExt⁻ unfold (ly~ t) i))
  --                   (⊑S'→⊑S (LError→LSumX' (lx~ t)) (LError→LSumY' (ly~ t)) (IH t (lx~ t) (ly~ t) (H~ t))))))
                    
