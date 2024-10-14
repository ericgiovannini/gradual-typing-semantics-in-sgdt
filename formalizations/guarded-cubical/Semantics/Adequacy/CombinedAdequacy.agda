{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

module Semantics.Adequacy.CombinedAdequacy where


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
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Common.Later
open import Common.ClockProperties

open import Semantics.Concrete.Predomain.Error

open import Semantics.Adequacy.Partial
open import Semantics.Adequacy.BigStepFunction
open import Semantics.Adequacy.GlobalLift

open import Semantics.Adequacy.GlobalLockStepErrorOrdering
  renaming (module Adequacy to AdequacyLockStep)
open import Semantics.Adequacy.GlobalWeakBisimilarity
  renaming (module Adequacy to AdequacyBisim)

open BinaryRelation

private
  variable
    ℓ ℓ' ℓR : Level
    ℓX ℓY : Level
    ℓ≈X ℓ≈Y ℓ⊑ : Level



-- The final adequacy theorem, combining the adequacy for the
-- lock-step error ordering with adequacy for weak bisimilarity to
-- obtain a result involving the closure of the former under the
-- latter on both sides.

module Result
  (X : Type ℓX) (isSetX : isSet X) (X-clk-irrel : clock-irrel X)
  (Y : Type ℓY) (isSetY : isSet Y) (Y-clk-irrel : clock-irrel Y)
  (_≈X_ : X → X → Type ℓ≈X) (≈X-prop-valued : isPropValued _≈X_) (≈X-clk-irrel : ∀ x x' → clock-irrel (x ≈X x'))
  (_≈Y_ : Y → Y → Type ℓ≈Y) (≈Y-prop-valued : isPropValued _≈Y_) (≈Y-clk-irrel : ∀ y y' → clock-irrel (y ≈Y y'))
  (_⊑XY_ : X → Y → Type ℓ⊑) (⊑XY-clk-irrel : ∀ x y → clock-irrel (x ⊑XY y))
  where

  open module LS = AdequacyLockStep X Y _⊑XY_ X-clk-irrel Y-clk-irrel ⊑XY-clk-irrel
  
  module BX = AdequacyBisim
    (X ⊎ ⊤) (Sum≈ X _≈X_) (isSet⊎ isSetX isSetUnit)
    (⊎-clock-irrel X-clk-irrel Unit-clock-irrel) (Sum≈-prop-valued X _≈X_ ≈X-prop-valued)
    (Sum≈-clk-irrel X _≈X_ ≈X-clk-irrel)
    
  module BY = AdequacyBisim
   (Y ⊎ ⊤) (Sum≈ Y _≈Y_) (isSet⊎ isSetY isSetUnit)
   (⊎-clock-irrel Y-clk-irrel Unit-clock-irrel) (Sum≈-prop-valued Y _≈Y_ ≈Y-prop-valued)
   (Sum≈-clk-irrel Y _≈Y_ ≈Y-clk-irrel)

  open BX renaming (_≈fun[_]_ to _≈funX?[_]_)
  open BY renaming (_≈fun[_]_ to _≈funY?[_]_)

  open PartialFunctions
  open BigStepLemmas

  X? = X ⊎ ⊤
  Y? = Y ⊎ ⊤

  _≈X?_ : _
  _≈X?_ = Sum≈ X _≈X_
  _≈Y?_ = Sum≈ Y _≈Y_

  -- (strict) error ordering on results:
  _⊑res_ : X? → Y? → Type ℓ⊑
  (inl x) ⊑res (inl y) = x ⊑XY y
  inr tt ⊑res y? = ⊤*
  _ ⊑res _  = ⊥*


  -- The closure of the error ordering on results under ≈X? on the left and ≈Y? on the right:
  _X?≈⊑≈Y?_ : X? → Y? → Type _
  x? X?≈⊑≈Y? y? = Σ[ x'? ∈ X? ] Σ[ y'? ∈ Y? ]
    (x? ≈X? x'?) × (x'? ⊑res y'?) × (y'? ≈Y? y?)


  -- (*) Closure of the lock-step error ordering on big-step functions
  --     under bisimilarity of functions on both sides.  Notice that
  --     each relation holds *for all n*.
  _⊑fun-cl_ : Fun {X = X?} → Fun {X = Y?} → Type _
  f ⊑fun-cl g = Σ[ f' ∈ Fun ] Σ[ g' ∈ Fun ]
    (∀ n → (f ≈funX?[ n ] f')) × (∀ n → (f' ⊑fun[ n ] g')) × (∀ n → (g' ≈funY?[ n ] g))


  -- (**) A more intuitive notion of step-insensitive error ordering
  -- on big-step semantics
  _≾_ : Fun {X = X?} → Fun {X = Y?} → Type _
  f ≾ g =
      -- If f terminates with a value x, then g terminates with a related value y.
      (∀ x → f ↓fun (inl x) → Σ[ y ∈ Y ] g ↓fun (inl y) × ((inl x) X?≈⊑≈Y? (inl y)))
      
      -- If g terminates with a result y?, then f terminates with a related result x?.
    × (∀ y? → g ↓fun y? → Σ[ x? ∈ X? ] f ↓fun x? × (x? X?≈⊑≈Y? y?))


  ------------------------------------------------------------------------------------
  -- The adequacy theorem says that (*) implies (**).

  --
  -- Lemmas used in the proof
  --
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


  -- The (intensional) adequacy result: the closure of ⊑fun under
  -- bisimilarity on each side implies the more intuitive notion of
  -- step-insensitive error ordering.
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
      -- We start by assuming that g ↓[ n ] y?.

      -- Then since g' ≈ g, we know that g' ↓[ n' ] y'? for some y'? such that y'? ≈ y?
      g'↓ : Σ-syntax ℕ (λ j → Σ-syntax (Y ⊎ ⊤) (λ y'? → (g' j ≡ in1 y'?) × Sum≈ Y _≈Y_ y'? y?))
      g'↓ = g'≈g n n ≤-refl .snd y? eq

      n' = g'↓ .fst
      y'? = g'↓ .snd .fst
      g'↓[n'] = g'↓ .snd .snd .fst
      y'?≈y? = g'↓ .snd .snd .snd

      -- Then since f' ⊑ g', we have f' ↓[ n'' ] x'? for some x'? such that (x'? , n'') ⊑ (y'? , n')
      -- In particular, this means that x'? ⊑ y'?.
      f'↓ : Σ-syntax X?
              (λ x'? → Σ-syntax ℕ (λ j → (f' j ≡ in1 x'?) × ((x'? , j) ≤res (y'? , n'))))
      f'↓ = f'⊑g' n' n' ≤-refl .snd y'? g'↓[n']
      x'? = f'↓ .fst
      n'' = f'↓ .snd .fst
      f'↓[n''] = f'↓ .snd .snd .fst
      x'?-⊑res-y'? = ≤res→⊑res n'' n' x'? y'? (f'↓ .snd .snd .snd) 

      -- Then since f ≈ f', we have f ↓[ n''' ] x? for some x? such that x? ≈ x'?
      f↓ : Σ-syntax ℕ (λ j → Σ-syntax (X ⊎ ⊤) (λ x? → (f j ≡ in1 x?) × Sum≈ X _≈X_ x? x'?))
      f↓ = f≈f' n'' n'' ≤-refl .snd x'? f'↓[n'']

      n''' = f↓ .fst
      x? = f↓ .snd .fst
      f↓[n'''] = f↓ .snd .snd .fst
      x?≈x'? = f↓ .snd .snd .snd


  ---------------------------------------------------------------------------------

  -- Now we define the ordering relation on the partial elements returned by the
  -- big-step semantics, i.e., a relation between Part (X + 1) and Part (Y + 1).
  --
  -- Because we want error on the left to be related to everything in this relation,
  -- including undefined elements, the definition of this relation does not factor
  -- through the relation on X? and Y? we defined above (_X?≈⊑≈Y?_).
  --
  -- Instead, the module ErrorOrdPartial takes in a relation between X and Y, and extends
  -- that to a relation on Part (X + 1) and Part (Y + 1)
  --
  -- Below, we define that relation between X and Y: it is the closure of the error
  -- ordering ⊑XY under ≈X on the left and ≈Y on the right:
  _X≈⊑≈Y_ : X → Y → Type _
  x X≈⊑≈Y y = Σ[ x' ∈ X ] Σ[ y' ∈ Y ] (x ≈X x') × (x' ⊑XY y') × (y' ≈Y y)

  open ErrorOrdPartial _X≈⊑≈Y_  -- brings in ⊑result and ≤part

  ≈cl-then-res→res-then-≈cl : isRefl _≈Y_ → ∀ x? y? → x? ⊑result y? → x? X?≈⊑≈Y? y?
  ≈cl-then-res→res-then-≈cl H = go
    where
      go : _
      go (inl x) (inl y) (x' , y' , x≈x' , x'⊑y' , y'≈y) =
        inl x' , inl y' , x≈x' , x'⊑y' , y'≈y
      go (inr tt) (inl y) (lift tt) =
        inr tt , inl y , tt* , tt* , H y
      go (inr tt) (inr tt) (lift tt) =
        inr tt , inr tt , tt* , tt* , tt*

  res-then-≈cl→≈cl-then-res : ∀ x? y? → x? X?≈⊑≈Y? y? → x? ⊑result y?
  res-then-≈cl→≈cl-then-res = go
    where
      go : _
      go (inl x) (inl y) (inl x' , inl y' , x≈x' , x'⊑y' , y'≈y) =
         x' , y' , x≈x' , x'⊑y' , y'≈y

      -- If x'? is a value inl x' and y? is inr tt, then there are two subcases:
      -- 1. If y'? is a value inl y', then the assumption y'?≈y? is a contradiction.
      go (inl x) (inr tt) (inl x' , inl y' , x≈x' , x'⊑y' , y'?≈y?) = ⊥.rec* y'?≈y?

      -- 2. If y'? is inr tt, then the assumption x'?⊑y'? is a contradiction. 
      go (inl x) (inr tt) (inl x' , inr tt , x?≈x'? , x'?⊑y'? , y'?≈y?) = ⊥.rec* x'?⊑y'?

      go (inr tt) y? (x'? , y'? , x?≈x'? , x'?⊑y'? , y'?≈y?) = tt*


  -- Finally, we have a theorem establishing a relationship between
  -- the big-step ordering on functions ≾ to the ordering on partial
  -- elements: If f is related to g in the big-step ordering on
  -- functions, then the corresponding partial elements are related.
  ≾fun→≤part : ∀ f g → (f .fst) ≾ (g .fst) → (collapse f) ≤part (collapse g)

  -- Pt 1. Assume the LHS terminates.
  ≾fun→≤part f g (H1 , H2) .fst (n , term-n) with (extract' (f .fst) n term-n)
  
  ... | (inl x , eq) = (m , (term .fst)) , subst (λ z? → inl x ⊑result z?) (sym (term .snd)) inl-x-≈⊑≈-result-inl-y
    where
      lem : Σ[ y ∈ Y ] (((g .fst) ↓fun in1 y) × (inl x X?≈⊑≈Y? inl y))
      lem = H1 x (n , eq)

      y = lem .fst
      m = lem .snd .fst .fst

      g↓m : (g .fst) ↓fun[ m ] (inl y)
      g↓m = lem .snd .fst .snd

      inl-x-⊑-inl-y : inl x X?≈⊑≈Y? inl y
      inl-x-⊑-inl-y = lem .snd .snd

      inl-x-≈⊑≈-result-inl-y : inl x ⊑result inl y
      inl-x-≈⊑≈-result-inl-y = res-then-≈cl→≈cl-then-res _ _ inl-x-⊑-inl-y

      term : Σ[ p ∈ terminates-in (g .fst) m ] (extract' (g .fst) m p .fst ≡ inl y)
      term = term-lemma-1 (g .fst) m (inl y) g↓m

  ... | (inr tt , eq) = lift tt -- inl refl

  -- Pt 2. Assume the RHS terminates.
  ≾fun→≤part f g (H1 , H2) .snd (m , term-m) =
    (n , term .fst) , subst (λ z? → z? ⊑result y?) (sym (term .snd)) x?-≈⊑≈-result-y?
    where
      y? = (extract' (g .fst) m term-m) .fst

      eq : g .fst m ≡ inl y?
      eq = (extract' (g .fst) m term-m) .snd

      lem : Σ[ x? ∈ X? ] (((f .fst) ↓fun x?) × (x? X?≈⊑≈Y? y?))
      lem = H2 y? (m , eq)

      x? = lem .fst
      n = lem .snd .fst .fst

      f↓n : (f .fst) ↓fun[ n ] x?
      f↓n = lem .snd .fst. snd

      x?≈⊑≈y? : x? X?≈⊑≈Y? y?
      x?≈⊑≈y? = lem .snd .snd

      x?-≈⊑≈-result-y? : x? ⊑result y?
      x?-≈⊑≈-result-y? = res-then-≈cl→≈cl-then-res _ _ x?≈⊑≈y?

      term : Σ[ p ∈ terminates-in (f .fst) n ] (extract' (f .fst) n p .fst ≡ x?)
      term = term-lemma-1 (f .fst) n x? f↓n
      
        

  ---------------------------------------------------------------------------------

  module _
    (lx lx' : L^gl (X ⊎ ⊤)) (ly' ly : L^gl (Y ⊎ ⊤))
    (lx≈lx' : lx BX.≈g lx') (lx'⊑ly' : lx' ⊑g ly') (ly'≈ly : ly' BY.≈g ly) where

    -- Instantiating the individual adequacy results:

    unique-X : ∀ l → ↓-unique ⟦ l ⟧x
    unique-X l n m x? x'? p q =
          bigStep-unique' (⊎-clock-irrel X-clk-irrel Unit-clock-irrel) l x? x'? n m p q

    unique-Y : ∀ l → ↓-unique ⟦ l ⟧y
    unique-Y l n m y? y'? p q =
          bigStep-unique' (⊎-clock-irrel Y-clk-irrel Unit-clock-irrel) l y? y'? n m p q

    bisim-X-pt1 : (n : ℕ) → BX.bisimFun ⟦ lx ⟧x ⟦ lx' ⟧x n
    bisim-X-pt1 = BX.adequacy-pt1 lx lx' lx≈lx'

    bisim-X-pt2 : (n : ℕ) → BX.bisimFun ⟦ lx ⟧x ⟦ lx' ⟧x n → ⟦ lx ⟧x ≈funX?[ n ] ⟦ lx' ⟧x
    bisim-X-pt2 = BX.adequacy-pt2 ⟦ lx ⟧x ⟦ lx' ⟧x (unique-X lx) (unique-X lx')

    lock-step-pt1 : (n : ℕ) → ⟦ lx' ⟧x ⊑fun1[ n ] ⟦ ly' ⟧y
    lock-step-pt1 = LS.adequacy-pt1 lx' ly' lx'⊑ly'

    lock-step-pt2 : (n : ℕ) → ⟦ lx' ⟧x ⊑fun1[ n ] ⟦ ly' ⟧y → ⟦ lx' ⟧x ⊑fun[ n ] ⟦ ly' ⟧y               
    lock-step-pt2 = LS.adequacy-pt2 ⟦ lx' ⟧x ⟦ ly' ⟧y (unique-X lx') (unique-Y ly')

    bisim-Y-pt1 : (n : ℕ) → BY.bisimFun ⟦ ly' ⟧y ⟦ ly ⟧y n
    bisim-Y-pt1 = BY.adequacy-pt1 ly' ly ly'≈ly

    bisim-Y-pt2 : (n : ℕ) → BY.bisimFun ⟦ ly' ⟧y ⟦ ly ⟧y n → ⟦ ly' ⟧y ≈funY?[ n ] ⟦ ly ⟧y
    bisim-Y-pt2 = BY.adequacy-pt2 ⟦ ly' ⟧y ⟦ ly ⟧y (unique-Y ly') (unique-Y ly)


    -- **************************************************************************
    -- Finally, we combine everything, showing that the denotations of lx and ly
    -- are related in the expected manner.
    -- **************************************************************************

    ⟦_⟧bigstep-X = ⟦_⟧bigstep
      where open BigStep (X ⊎ ⊤) (⊎-clock-irrel X-clk-irrel Unit-clock-irrel)
    ⟦_⟧bigstep-Y = ⟦_⟧bigstep
      where open BigStep (Y ⊎ ⊤) (⊎-clock-irrel Y-clk-irrel Unit-clock-irrel)
    
    intensional-adequacy : ⟦ lx ⟧x ≾ ⟦ ly ⟧y
    intensional-adequacy = combined-adequacy ⟦ lx ⟧x ⟦ ly ⟧y
      (⟦ lx' ⟧x , ⟦ ly' ⟧y
      , (λ n m m≤n → bisim-X-pt2 n (bisim-X-pt1 n) m m≤n)
      , (λ n m m≤n → lock-step-pt2 n (lock-step-pt1 n) m m≤n)
      , (λ n m m≤n → bisim-Y-pt2 n (bisim-Y-pt1 n) m m≤n))
    
    extensional-adequacy : (collapse ⟦ lx ⟧bigstep-X) ≤part (collapse ⟦ ly ⟧bigstep-Y)
    extensional-adequacy = ≾fun→≤part _ _ intensional-adequacy
  














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


