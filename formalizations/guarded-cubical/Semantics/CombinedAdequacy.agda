{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

module Semantics.CombinedAdequacy where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport -- pathToIso
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_^_ ; _+_)
open import Cubical.Data.Nat.Order hiding (eq)
open import Cubical.Relation.Binary

open import Common.Later
open import Common.ClockProperties


open import Semantics.GlobalLift

open import Semantics.GlobalLockStepErrorOrdering
  renaming (module Adequacy to AdequacyLockStep)
open import Semantics.GlobalWeakBisimilarity
  renaming (module Adequacy to AdequacyBisim)

open BinaryRelation

private
  variable
    ℓ ℓ' ℓR : Level
    ℓ≈X ℓ≈Y ℓ⊑ : Level


module _ (X : Type ℓ) (_≈X_ : X → X → Type ℓ≈X) where

  Sum≈ : (X ⊎ ⊤) → (X ⊎ ⊤) → Type ℓ≈X
  Sum≈ (inl x) (inl x') = x ≈X x'
  Sum≈ (inr tt) (inr tt) = ⊤*
  Sum≈ _ _ = ⊥*

  module _ (H : ∀ x x' → clock-irrel (x ≈X x')) where

    Sum≈-clk-irrel : ∀ x? x'? → clock-irrel (Sum≈ x? x'?)
    Sum≈-clk-irrel (inl x) (inl x') = H x x'
    Sum≈-clk-irrel (inl x) (inr tt) = ⊥*-clock-irrel
    Sum≈-clk-irrel (inr tt) (inl x') = ⊥*-clock-irrel
    Sum≈-clk-irrel (inr tt) (inr tt) = Unit*-clock-irrel

module _
  (X : Type ℓ) (isSetX : isSet X) (X-clk-irrel : clock-irrel X)
  (Y : Type ℓ) (isSetY : isSet Y) (Y-clk-irrel : clock-irrel Y)
  (_≈X_ : X → X → Type ℓ≈X) (≈X-prop-valued : isPropValued _≈X_) (≈X-clk-irrel : ∀ x x' → clock-irrel (x ≈X x'))
  (_≈Y_ : Y → Y → Type ℓ≈Y) (≈Y-prop-valued : isPropValued _≈Y_) (≈Y-clk-irrel : ∀ y y' → clock-irrel (y ≈Y y'))
  (_⊑XY_ : X → Y → Type ℓ⊑) (⊑XY-clk-irrel : ∀ x y → clock-irrel (x ⊑XY y))
  where

  open AdequacyLockStep X Y _⊑XY_ X-clk-irrel Y-clk-irrel ⊑XY-clk-irrel
  
  module AdequacyBisimX = AdequacyBisim
    (X ⊎ ⊤) (Sum≈ X _≈X_) (isSet⊎ isSetX isSetUnit)
    (⊎-clock-irrel X-clk-irrel Unit-clock-irrel) {!!} (Sum≈-clk-irrel X _≈X_ ≈X-clk-irrel)
    
  module AdequacyBisimY = AdequacyBisim
   (Y ⊎ ⊤) (Sum≈ Y _≈Y_) (isSet⊎ isSetY isSetUnit)
   (⊎-clock-irrel Y-clk-irrel Unit-clock-irrel) {!!} (Sum≈-clk-irrel Y _≈Y_ ≈Y-clk-irrel)

  open AdequacyBisimX renaming (_≈fun[_]_ to _≈funX?[_]_)
  open AdequacyBisimY renaming (_≈fun[_]_ to _≈funY?[_]_)

  -- Definition of extensional error ordering
  open PartialFunctions

  X? = X ⊎ ⊤
  Y? = Y ⊎ ⊤

  _≈X?_ : _
  _≈X?_ = Sum≈ X _≈X_
  _≈Y?_ = Sum≈ Y _≈Y_

  -- extensional error relation on results
  _⊑res_ : X? → Y? → Type ℓ⊑
  (inl x) ⊑res (inl y) = x ⊑XY y
  inr tt ⊑res y? = ⊤*
  _ ⊑res _  = ⊥*


  -- The closure of ⊑XY under ≈X on the left and ≈Y on the right
  _X≈⊑≈Y_ : X? → Y? → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ≈X) ℓ≈Y) ℓ⊑)
  x? X≈⊑≈Y y? = Σ[ x'? ∈ X? ] Σ[ y'? ∈ Y? ] (x? ≈X? x'?) × (x'? ⊑res y'?) × (y'? ≈Y? y?)


  -- The extensional error ordering
  _≾_ : Fun {X = X?} → Fun {X = Y?} → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ≈X) ℓ≈Y) ℓ⊑)
  f ≾ g =
      (∀ x → f ↓fun (inl x) → Σ[ y ∈ Y ] g ↓fun (inl y) × ((inl x) X≈⊑≈Y (inl y)))
    × (∀ y? → g ↓fun y? → Σ[ x? ∈ X? ] f ↓fun x? × (x? X≈⊑≈Y y?))


  -- closure of ⊑fun under ≈fun on both sides
  _⊑fun-cl_ : Fun {X = X?} → Fun {X = Y?} → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ≈X) ℓ≈Y) ℓ⊑)
  f ⊑fun-cl g = Σ[ f' ∈ Fun ] Σ[ g' ∈ Fun ]
    (∀ n → (f ≈funX?[ n ] f')) × (∀ n → (f' ⊑fun[ n ] g')) × (∀ n → (g' ≈funY?[ n ] g))


  deconstruct-lem-1 :
   ∀ x (x'? : (X ⊎ ⊤)) → ∀ f' j → (H1 : (f' ↓fun[ j ] x'?)) (H2 : ((inl x) ≈X? x'?)) →
     Σ[ x' ∈ X ] ((f' ↓fun[ j ] (inl x')) × (x ≈X x'))
  deconstruct-lem-1 x (inl x') f j H1 H2 = x' , H1 , H2
  deconstruct-lem-1 x (inr tt) f j H1 H2 = ⊥.rec* H2

  deconstruct-lem-2 :
   ∀ y' (y? : (Y ⊎ ⊤)) → ∀ g' j → (H1 : (g' ↓fun[ j ] y?)) (H2 : ((inl y') ≈Y? y?)) →
     Σ[ y ∈ Y ] ((g' ↓fun[ j ] (inl y)) × (y' ≈Y y))
  deconstruct-lem-2 y' (inl y) f j H1 H2 = y , H1 , H2
  deconstruct-lem-2 y' (inr tt) f j H1 H2 = ⊥.rec* H2

  ≤res→⊑res : ∀ n m x? y? → (x? , n) ≤res (y? , m) → x? ⊑res y?
  ≤res→⊑res n m (inl x) (inl y) (_ , xRy) = xRy
  ≤res→⊑res n m (inr x) y? _ = tt*


  combined-adequacy : ∀ f g → f ⊑fun-cl g → f ≾ g
  combined-adequacy f g (f' , g' , f≈f' , f'⊑g' , g'≈g) .fst x (n , eq) =
    y , (n'' , g↓y) , (inl x' , inl y' , x≈x' , x'⊑y' , y'≈y)
    where
      -- We start by assuming f ↓[ n ] (inl x).

      -- Then since f ≈ f', we know that f' ↓[ n' ] x'? for some x'? s.t. inl x ≈ x'?
      f'↓ : Σ[ j ∈ ℕ ] Σ[ x'? ∈ (X ⊎ ⊤) ] ((f' ↓fun[ j ] x'?) × (in1 x) ≈X? x'?)
      f'↓ = f≈f' n n ≤-refl .fst (inl x) eq
      n' = f'↓ .fst
      x'? = f'↓ .snd .fst
      f'↓[n'] = f'↓ .snd .snd .fst
      inlx≈x'? = f'↓ .snd .snd .snd

      -- Now we observe that x'? must be of the form inl x' with x ≈ x'.
      lemma1 : _
      lemma1 = deconstruct-lem-1 x x'? f' n' f'↓[n'] inlx≈x'?
      x' = lemma1 .fst
      f'↓x' = lemma1 .snd .fst
      x≈x' = lemma1 .snd .snd

      -- Then since f' ⊑ g', we have g' ↓[ n' ] (inl y') for some y' with x' ⊑ y'
      g'↓ : Σ[ y' ∈ Y ] (g' ↓fun[ n' ] (inl y')) × (x' ⊑XY y')
      g'↓ = f'⊑g' (f'↓ .fst) (f'↓ .fst) ≤-refl .fst x' f'↓x'

      y' = g'↓ .fst
      g'↓y' = g'↓ .snd .fst
      x'⊑y' = g'↓ .snd .snd

      -- Then since g' ≈ g, we have g ↓[ n'' ] y? for some y? with inl y' ≈ y?
      g↓ : Σ[ i ∈ ℕ ] Σ[ y? ∈ (Y ⊎ ⊤) ] (g ↓fun[ i ] y?) × ((inl y') ≈Y? y?)
      g↓ = g'≈g n' n' ≤-refl .fst (inl y') g'↓y'
      n'' = g↓ .fst
      y? = g↓ .snd .fst
      g↓[n''] = g↓ .snd .snd .fst
      inly'≈y? = g↓ .snd .snd .snd

      -- Finally we observe that y? must be of the form inl y with y'≈y
      lemma2 : _
      lemma2 = deconstruct-lem-2 y' y? g n'' g↓[n''] inly'≈y?
      y = lemma2 .fst
      g↓y = lemma2 .snd .fst
      y'≈y = lemma2 .snd .snd

  combined-adequacy f g (f' , g' , f≈f' , f'⊑g' , g'≈g) .snd y? (n , eq) =
    x? , ((n''' , f↓[n''']) , (x'? , y'? , x?≈x'? , x'?-⊑res-y'? , y'?≈y?))
    where
      g'↓ : Σ-syntax ℕ (λ j → Σ-syntax (Y ⊎ ⊤) (λ y'? → (g' j ≡ in1 y'?) × Sum≈ Y _≈Y_ y'? y?))
      g'↓ = g'≈g n n ≤-refl .snd y? eq

      n' = g'↓ .fst
      y'? = g'↓ .snd .fst
      g'↓[n'] = g'↓ .snd .snd .fst
      y'?≈y? = g'↓ .snd .snd .snd

      f'↓ : Σ-syntax X?
              (λ x'? → Σ-syntax ℕ (λ j → (f' j ≡ in1 x'?) × ((x'? , j) ≤res (y'? , n'))))
      f'↓ = f'⊑g' n' n' ≤-refl .snd y'? g'↓[n']
      x'? = f'↓ .fst
      n'' = f'↓ .snd .fst
      f'↓[n''] = f'↓ .snd .snd .fst
      x'?-⊑res-y'? = ≤res→⊑res n'' n' x'? y'? (f'↓ .snd .snd .snd) 
      
      f↓ : Σ-syntax ℕ (λ j → Σ-syntax (X ⊎ ⊤) (λ x? → (f j ≡ in1 x?) × Sum≈ X _≈X_ x? x'?))
      f↓ = f≈f' n'' n'' ≤-refl .snd x'? f'↓[n'']

      n''' = f↓ .fst
      x? = f↓ .snd .fst
      f↓[n'''] = f↓ .snd .snd .fst
      x?≈x'? = f↓ .snd .snd .snd
      
      



  -- -- The extensional error ordering
  -- _≾[_]_ : Fun {X = X?} → ℕ → Fun {X = Y?} → Type (ℓ-max ℓ ℓ⊑)
  -- f ≾[ n ] g =
  --     (∀ x → f ↓fun[ n ] (inl x) → Σ[ y ∈ Y ] g ↓fun (inl y) × (x ⊑XY y))
  --   × (∀ y? → g ↓fun[ n ] y? → Σ[ x? ∈ X? ] f ↓fun x? × (x? ⊑res y?))


  -- -- closure of ⊑fun under ≈fun on both sides
  -- _⊑fun-cl[_]_ : Fun {X = X?} → ℕ → Fun {X = Y?} → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ≈X) ℓ≈Y) ℓ⊑)
  -- f ⊑fun-cl[ n ] g = Σ[ f' ∈ Fun ] Σ[ g' ∈ Fun ]
  --   (f ≈funX?[ n ] f') × (f' ⊑fun[ n ] g') × (g' ≈funY?[ n ] g)
  

  -- combined-adequacy : ∀ f g n → f ⊑fun-cl[ n ] g → f ≾[ n ] g
  -- combined-adequacy f g n (f' , g' , f≈f' , f'⊑g' , g'≈g) .fst x eq =
  --   {!!}
  --   where
  --     f'↓ : Σ[ j ∈ ℕ ] Σ[ x? ∈ (X ⊎ ⊤) ] ((f' ↓fun[ j ] x?) × (in1 x) X?≈ x?)
  --     f'↓ = f≈f' n {!!} .fst (inl x) eq

  --     g'↓ : _
  --     g'↓ = {!f'⊑g' n ? .fst!}

  --     g↓ : _
  --     g↓ = {!!}
  -- combined-adequacy f g zero (f' , g' , f≈f' , f'⊑g' , g'≈g) .snd y? g↓y? = {!!}


