{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.GlobalLockStepErrorOrdering where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport -- pathToIso
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Nat hiding (_^_ ; _+_)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat.Order hiding (eq)

open import Cubical.Functions.FunExtEquiv



open import Common.Common
open import Common.Later
open import Common.ClockProperties

open import Semantics.Lift hiding (ret)
open import Semantics.GlobalLift


private
  variable
    ℓ ℓ' ℓR : Level


_+_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
_+_ = _⊎_
infixr 20 _+_


-- Convenience constructors for L (X + 1)
module _ {k : Clock} {X : Type ℓ}  where

  ret : X → L k (X ⊎ ⊤)
  ret x = η (inl x)

  err : L k (X ⊎ ⊤)
  err = η (inr tt)


module _ {X : Type ℓ} where

  ret^gl : X → L^gl (X ⊎ ⊤)
  ret^gl x = ηL^gl (inl x)

  err^gl : L^gl (X ⊎ ⊤)
  err^gl = ηL^gl (inr tt)
  

-- Clocked lock-step error ordering as a sum-type.
module Clocked (X : Type ℓ) (Y : Type ℓ') (R : X → Y → Type ℓR) (k : Clock) where

  _⊑S'_ : (▹ k , (L k (X ⊎ ⊤) → L k (Y ⊎ ⊤) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓR))) →
                 L k (X ⊎ ⊤) → L k (Y ⊎ ⊤) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
  _⊑S'_ rec l1 l2 =
      (Σ[ x ∈ X ] Σ[ y ∈ Y ] (l1 ≡ ret x) × (l2 ≡ ret y) × R x y)
    + (l1 ≡ err)
    + (Σ[ l1~ ∈ ▹ k , L k (X ⊎ ⊤) ] Σ[ l2~ ∈ ▹ k , L k (Y ⊎ ⊤) ] (l1 ≡ θ l1~) × (l2 ≡ θ l2~) × (▸ (λ t → rec t (l1~ t) (l2~ t))))

  _⊑S_ : L k (X ⊎ ⊤) → L k (Y ⊎ ⊤) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
  _⊑S_ = fix _⊑S'_

  unfold-⊑S : _⊑S_ ≡ _⊑S'_ (next _⊑S_)
  unfold-⊑S = fix-eq _⊑S'_


module _ (X : Type ℓ) (Y : Type ℓ') (R : X → Y → Type ℓR)
         (X-clk-irrel : clock-irrel X)
         (Y-clk-irrel : clock-irrel Y)
         (R-clk-irrel : ∀ x y → clock-irrel (R x y)) where

  open Clocked X Y R

  -- Some convenience definitions and syntax.
  X? = X ⊎ ⊤
  Y? = Y ⊎ ⊤

  ⊑S : (k : Clock) → L k X? → L k Y? → Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
  ⊑S k = _⊑S_ k

  syntax ⊑S k l1 l2 = l1 ⊑[ k ] l2

  -- Definition of the global lock-step error ordering.
  _⊑g_ : L^gl X? → L^gl Y? → Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
  lg1 ⊑g lg2 = ∀ (k : Clock) → (lg1 k) ⊑[ k ] (lg2 k)


  -- The three cases of clocked lock-step error ordering.
  module ClockedCases {k : Clock} (l1 : L k X?) (l2 : L k Y?) where

    ret-ret : Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
    ret-ret = Σ[ x ∈ X ] Σ[ y ∈ Y ] (l1 ≡ ret x) × (l2 ≡ ret y) × R x y

    err-bot : Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
    err-bot = Lift {j = ℓ-max ℓ' ℓR} (l1 ≡ err)

    theta-theta : Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
    theta-theta = Σ[ l1~ ∈ ▹ k , L k X? ] Σ[ l2~ ∈ ▹ k , L k Y? ]
       (l1 ≡ θ l1~) × (l2 ≡ θ l2~) × (▸ (λ t → l1~ t ⊑[ k ] l2~ t))


  -- The three cases of global lock-step error ordering.
  module GlobalCases (lg1 : L^gl X?) (lg2 : L^gl Y?) where

    ret-ret-g : Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
    ret-ret-g = Σ[ x ∈ X ] Σ[ y ∈ Y ]
          (lg1 ≡ ret^gl x) × (lg2 ≡ ret^gl y) × R x y

    err-bot-g : Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
    err-bot-g = Lift {j = ℓ-max ℓ' ℓR} (lg1 ≡ err^gl)

    theta-theta-g : Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
    theta-theta-g = Σ[ lg1' ∈ L^gl X? ] Σ[ lg2' ∈ L^gl Y? ]
          (lg1 ≡ δL^gl lg1') × (lg2 ≡ δL^gl lg2') × (lg1' ⊑g lg2')


  -- The "unfolding" of the definition of the global lock-step error ordering.
  ⊑g-unfolded : L^gl X? → L^gl Y? → Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
  ⊑g-unfolded lg1 lg2 = ret-ret-g + err-bot-g + theta-theta-g
   where open GlobalCases lg1 lg2


  -- Showing the isomorphism between the global lock-step definition and its unfolding.
  
  open GlobalCases
  open ClockedCases

  -- First, we prove three lemmas, one corresponding to each case in the definition.
  lem1 : ∀ lg1 lg2 →
    Iso (∀ (k : Clock) → ret-ret (lg1 k) (lg2 k)) (ret-ret-g lg1 lg2)
  lem1 lg1 lg2 =
    ((k : Clock) → ret-ret (lg1 k) (lg2 k)) Iso⟨ Iso-∀clock-Σ X-clk-irrel ⟩
    _ Iso⟨ Σ-cong-iso-snd (λ x → Iso-∀clock-Σ Y-clk-irrel) ⟩
    _ Iso⟨ Σ-cong-iso-snd (λ x → Σ-cong-iso-snd (λ y → compIso Iso-∀clock-× (prodIso idIso Iso-∀clock-×))) ⟩
    Σ X
     (λ a →
        Σ Y
        (λ a₁ →
           ((k : Clock) → lg1 k ≡ ret a) ×
           ((k : Clock) → lg2 k ≡ ret a₁) × ((k : Clock) → R a a₁))) Iso⟨ Σ-cong-iso-snd (λ x → Σ-cong-iso-snd (λ y → prodIso funExtIso (prodIso funExtIso (Iso-∀kA-A (R-clk-irrel x y))))) ⟩
    ret-ret-g lg1 lg2 ∎Iso

  lem2 :  ∀ lg1 lg2 →
    Iso (∀ (k : Clock) → err-bot (lg1 k) (lg2 k)) (err-bot-g lg1 lg2)
  lem2 lg1 lg2 = {!!} Iso⟨ {!Iso!} ⟩ {!!} Iso⟨ {!!} ⟩ {!!} ∎Iso -- funExtIso

  lem3 :  ∀ lg1 lg2 →
   Iso (∀ (k : Clock) → theta-theta (lg1 k) (lg2 k)) (theta-theta-g lg1 lg2)
  lem3 lg1 lg2 =
    (∀ (k : Clock) → theta-theta (lg1 k) (lg2 k))
      Iso⟨ Σ-Π-Iso ⟩
    _
      Iso⟨ Σ-cong-iso-snd (λ lg1 → Σ-Π-Iso) ⟩
    _
      Iso⟨ compIso (Σ-cong-iso-fst' force-iso) (Σ-cong-iso-snd (λ f → Σ-cong-iso-fst' force-iso)) ⟩
    _
      Iso⟨ Σ-cong-iso-snd (λ _ → Σ-cong-iso-snd (λ _ → compIso Iso-∀clock-× (prodIso funExtIso (compIso Iso-∀clock-×  (prodIso funExtIso force-iso)) ))) ⟩
    theta-theta-g lg1 lg2 ∎Iso

{-
  theta-theta = Σ[ l1~ ∈ ▹ k , L k X? ] Σ[ l2~ ∈ ▹ k , L k Y? ]
       (l1 ≡ θ l1~) × (l2 ≡ θ l2~) × (▸ (λ t → l1~ t ⊑[ k ] l2~ t))
  theta-theta-g = Σ[ lg1' ∈ L^gl X? ] Σ[ lg2' ∈ L^gl Y? ]
          (lg1 ≡ δL^gl lg1') × (lg2 ≡ δL^gl lg2') × (lg1' ⊑g lg2')

Σ[ l1~ ∈ ((k : Clock) → ▹ k , L k X?) ] Σ[ l2~ ∈ ((k : Clock) → ▹ k , L k Y?)]
     ((k : Clock) → lg1 k ≡ θ (l1~ k)) × ((k : Clock) → (lg2 k ≡ θ (l2~ k)) × (▸ (λ t → ⊑S k (l1~ k t) (l2~ k t))))
-}


  -- The unfolding isomorphism satisfied by the global lock-step error ordering.
  -- The construction of this iso uses the above lemmas.
  ⊑g-iso : (lg1 : L^gl X?) (lg2 : L^gl Y?) →
    Iso (lg1 ⊑g lg2) (⊑g-unfolded lg1 lg2)
  ⊑g-iso lg1 lg2 =
    (lg1 ⊑g lg2)
      Iso⟨ pathToIso (λ i → ∀ k → unfold-⊑S k i (lg1 k) (lg2 k)) ⟩
    -- (∀ k → ret-ret (lg1 k) (lg2 k) + err-bot (lg1 k) (lg2 k) + theta-theta (lg1 k) (lg2 k))
    --   Iso⟨ compIso Iso-Π-⊎-clk (⊎Iso idIso {!Iso-Π-⊎-clk!}) ⟩
      --compIso Iso-Π-⊎-clk (⊎Iso idIso (compIso {!Iso-Π-⊎-clk!} idIso))
    _ Iso⟨ compIso Iso-Π-⊎-clk (⊎Iso idIso {!Iso-Π-⊎-clk!}) ⟩
    _ Iso⟨ {!!} ⟩
    {!!} ∎Iso






  -- The unfolding function, given by the above isomorphism.
  unfold-⊑g : {lg1 : L^gl X?} {lg2 : L^gl Y?} →
    (lg1 ⊑g lg2) → (⊑g-unfolded lg1 lg2)
  unfold-⊑g {lg1 = lg1} {lg2 = lg2} = Iso.fun (⊑g-iso lg1 lg2)


  module Adequacy where

    open PartialFunctions

    -- Type alias for the codomain of the big-step term semantics.
    --Fun : {ℓ : Level} → (A : Type ℓ) → Type ℓ
    --Fun A = ℕ → (A ⊎ ⊤)

    Fun-X? = Fun {X = X?} -- the module PartialFunctions takes an implicit argument
    Fun-Y? = Fun {X = Y?}
    
    clock-irrel-⊎ : {ℓ ℓ' : Level} {X : Type ℓ} {Y : Type ℓ'} → (H : clock-irrel X) → (H' : clock-irrel Y) → clock-irrel (X ⊎ Y)
    clock-irrel-⊎ {X = X} {Y = Y} H H' = iso-∀kA-A→clk-irrel (inv , (sec1 , retr1)) --iso-∀kA-A→clk-irrel
      where
        inv : ((k : Clock) → X ⊎ Y) → X ⊎ Y
        inv f with f k0
        ... | inl x = inl x
        ... | inr y = inr y

        sec1 : section (λ a k → a) inv
        sec1 f = ∀kA→A {!!} {!!}

        retr1 : retract (λ a k → a) inv
        retr1 (inl x) = refl
        retr1 (inr y) = refl

    ⟦_⟧x : L^gl X? → Fun-X?
    ⟦ lg? ⟧x = toFun (clock-irrel-⊎ X-clk-irrel  unit-clock-irrel) lg?

    ⟦_⟧y : L^gl Y? → Fun-Y?
    ⟦ lg? ⟧y = toFun (clock-irrel-⊎ Y-clk-irrel  unit-clock-irrel) lg?


    -- First definition of step-indexed lock-step error ordering on functions.
    _⊑fun1[_]_ : (f : Fun-X?) (n : ℕ) → (g : Fun-Y?) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
    f ⊑fun1[ zero ] g =
        (Σ[ x ∈ X ] Σ[ y ∈ Y ] (f ↓fun[ 0 ] inl x) × (g ↓fun[ 0 ] inl y) × R x y)
      + (f ↓fun[ 0 ] inr tt)
      + (f ↑fun[ 0 ] × g ↑fun[ 0 ])
  
    f ⊑fun1[ suc n ] g =
        (Σ[ x ∈ X ] Σ[ y ∈ Y ] (f ↓fun[ 0 ] inl x) × (g ↓fun[ 0 ] inl y) × R x y)
      + (f ↓fun[ 0 ] inr tt)
      + (f ↑fun[ 0 ] × g ↑fun[ 0 ]) × ((f ∘ suc) ⊑fun1[ n ] (g ∘ suc))



-- 1. Formalize second definition of error ordering on functions
-- ("more intuitive definition")

-- 2. Adequacy pt1: derive first definition (for all n) from the unfolding of the
-- iso as defined above

-- 3. Adequacy pt2: show the first definition implies the second one

    _≤fun[_]_ : Fun-X? → ℕ → Fun-Y? → Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
    f ≤fun[ n ] g = ∀ (m : ℕ) → (m ≤ n) →
      (∀ (x : X) → f m ≡ inl (inl x) → Σ[ y ∈ Y ] (g m ≡ inl (inl y)) × R x y) ×
      (∀ (y? : Y?) → g m ≡ inl y? → Σ[ x? ∈ X? ] Σ[ j ∈ ℕ ] (f j ≡ inl x?)
        × ((x? , j) ≤fun2 (y? , m)))
      where
        _≤fun2_ : X? × ℕ → Y? × ℕ → Type ℓ
        (inl x , j) ≤fun2 (y? , i) = {!!}
        (inr tt , j) ≤fun2 (y? , i) = {!!}



    module BigStepX? = BigStepLemmas {X = X?} (clock-irrel-⊎ X-clk-irrel unit-clock-irrel)
    module BigStepY? = BigStepLemmas {X = Y?} (clock-irrel-⊎ Y-clk-irrel unit-clock-irrel)

    adequacy-pt1 : (lg1 : L^gl X?) (lg2 : L^gl Y?) → lg1 ⊑g lg2 → (n : ℕ) →
      ⟦ lg1 ⟧x ⊑fun1[ n ] ⟦ lg2 ⟧y
    adequacy-pt1 lg1 lg2 order zero with unfold-⊑g order
    ... | inl (x , y , eq1 , eq2 , xRy) =
      inl (x , y , BigStepX?.bigStep-η-zero lg1 (inl x) eq1
                 , BigStepY?.bigStep-η-zero lg2 (inl y) eq2 , xRy)
    ... | inr (inl eq1) = inr (inl (BigStepX?.bigStep-η-zero lg1 (inr tt) (lower eq1)))
    ... | inr (inr (lg1' , lg2' , eq1 , eq2 , order')) =
      inr (inr ((λ m m≤zero → (λ i → toFun (clock-irrel-⊎ X-clk-irrel unit-clock-irrel) lg1 (≤0→≡0 m≤zero i)) ∙ BigStepX?.bigStep-δ-zero lg1 lg1' eq1)
              , λ m m≤zero → (λ i → toFun (clock-irrel-⊎ Y-clk-irrel unit-clock-irrel) lg2 (≤0→≡0 m≤zero i)) ∙ BigStepY?.bigStep-δ-zero lg2 lg2' eq2))
    adequacy-pt1 lg1 lg2 order (suc n) with unfold-⊑g order
    ... | inl (x , y , eq1 , eq2 , xRy) =
      (inl (x , y , BigStepX?.bigStep-η-zero lg1 (inl x) eq1
                  , BigStepY?.bigStep-η-zero lg2 (inl y) eq2 , xRy)) , {!!}
    ... | inr (inl eq1) = (inr (inl (BigStepX?.bigStep-η-zero lg1 (inr tt) (lower eq1)))) , {!!}
    ... | inr (inr (lg1' , lg2' , eq1 , eq2 , order')) = {!!}

{-
     (Σ[ x ∈ X ] Σ[ y ∈ Y ] (f ↓fun[ 0 ] inl x) × (g ↓fun[ 0 ] inl y) × R x y)
      + (f ↓fun[ 0 ] inr tt)
      + (f ↑fun[ 0 ] × g ↑fun[ 0 ]) × ((f ∘ suc) ⊑fun1[ n ] (g ∘ suc))
    ret-ret : Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
    ret-ret = Σ[ x ∈ X ] Σ[ y ∈ Y ] (l1 ≡ ret x) × (l2 ≡ ret y) × R x y

    err-bot : Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
    err-bot = Lift {j = ℓ-max ℓ' ℓR} (l1 ≡ err)

    theta-theta : Type (ℓ-max (ℓ-max ℓ ℓ') ℓR)
    theta-theta = Σ[ l1~ ∈ ▹ k , L k X? ] Σ[ l2~ ∈ ▹ k , L k Y? ]
       (l1 ≡ θ l1~) × (l2 ≡ θ l2~) × (▸ (λ t → l1~ t ⊑[ k ] l2~ t))
       
-}
