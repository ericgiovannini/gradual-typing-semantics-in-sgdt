{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.DoublePoset.FreeErrorDomain (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Relation.Binary.Base
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Empty


open import Common.Common
-- open import Semantics.Concrete.GuardedLift k renaming (η to Lη ; θ to Lθ)
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.DblPosetCombinators

open import Semantics.Concrete.DoublePoset.ErrorDomain k

open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k

open ClockedCombinators k

private
  variable
    ℓ ℓ' : Level
    ℓA  ℓ≤A  ℓ≈A  : Level
    ℓA' ℓ≤A' ℓ≈A' : Level
    ℓB  ℓ≤B  ℓ≈B  : Level
    ℓc ℓR : Level
    ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ : Level
    ℓAₒ ℓ≤Aₒ ℓ≈Aₒ : Level
    ℓΓ ℓ≤Γ ℓ≈Γ : Level


private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


-- The purpose of this module is to define the functor F : Predomain →
-- ErrorDomain left adjoint to the forgetful functor U.

-- We define:
--
-- - The action on objects
-- - The action on vertical morphisms (i.e. fmap)
-- - The action on horizontal morpisms
-- - The action on squares

-- In the below, the composition UF will sometimes be used to mean
-- the monad L℧


≈ErrorA : {X : Type ℓ} (R : X → X → Type ℓR) → Error X → Error X → Type ℓR
≈ErrorA R (ok x) (ok y) = R x y
≈ErrorA R error error = ⊤*
≈ErrorA R _ _ = ⊥*



open ErrorDomainStr hiding (℧ ; θ)
open PosetBisimStr


-- Defining the "call-by-push-value ext" of type (A → U B) → (F A -* B).
-- This is not the same as the "Kleisli extension" (A → U F A') → (F A -* F A'), because there B has the form F A'
--module CBPVMonad (A : PosetBisim ℓA ℓ≤A ℓ≈A) (B : ErrorDomain ℓB ℓ≤B ℓ≈B) where

module StrongCBPVExt
  (Γ : PosetBisim ℓΓ ℓ≤Γ ℓ≈Γ)
  (A : PosetBisim ℓA ℓ≤A ℓ≈A)
  (B : ErrorDomain ℓB ℓ≤B ℓ≈B)
  (f : ⟨ Γ ⟩ → ⟨ A ⟩ → ⟨ B ⟩) where

  private
    module Γ = PosetBisimStr (Γ .snd)
    module A = PosetBisimStr (A .snd)
    module B = ErrorDomainStr (B .snd)

    module LockStep = LiftOrdHomogenous ⟨ A ⟩ (A._≤_)

  _≤LA_ : _
  _≤LA_ = LockStep._⊑_

  module Rec (rec : ▹ (⟨ Γ ⟩ → L℧ ⟨ A ⟩ → ⟨ B ⟩)) where 
    ext' : ⟨ Γ ⟩ → L℧ ⟨ A ⟩ → ⟨ B ⟩
    ext' γ (η x) = f γ x
    ext' _ ℧ = B.℧
    ext' γ (θ lx~) = B.θ $ (λ t → rec t γ (lx~ t))

  ext : _
  ext = fix Rec.ext'

  unfold-ext : ext ≡ Rec.ext' (next ext)
  unfold-ext = fix-eq Rec.ext'

  open Rec (next ext) public -- brings ext' into scope instantiated with (next ext)

  -- All of the below equations are quantified over an element γ of ⟨ Γ ⟩,
  -- so we group them into a module parameterized by an element γ for
  -- easy re-use by the "non-strong" monad definition in module CBPVExt.
  module Equations (γ : ⟨ Γ ⟩) where

    ext-η : (x : ⟨ A ⟩) → ext γ (η x) ≡ f γ x
    ext-η x = funExt⁻ (funExt⁻ unfold-ext γ) (η x) -- funExt⁻ unfold-ext (η x)

    ext-℧ : ext γ ℧ ≡ B.℧
    ext-℧ = funExt⁻ (funExt⁻ unfold-ext γ) ℧ -- funExt⁻ unfold-ext ℧

    ext-θ : (lx~ : ▹ L℧ ⟨ A ⟩) → ext γ (θ lx~) ≡ B.θ $ (map▹ (ext γ) lx~)
    ext-θ lx~ = funExt⁻ (funExt⁻ unfold-ext γ) (θ lx~) -- funExt⁻ unfold-ext (θ lx~)

    ext-δ : (lx : L℧ ⟨ A ⟩) → ext γ (δ lx) ≡ (B.θ $ next (ext γ lx))
    ext-δ lx = ext-θ (next lx)


module CBPVExt
  (A : PosetBisim ℓA ℓ≤A ℓ≈A)
  (B : ErrorDomain ℓB ℓ≤B ℓ≈B)
  (f : ⟨ A ⟩ → ⟨ B ⟩) where

  private
    module A = PosetBisimStr (A .snd)
    module B = ErrorDomainStr (B .snd)

  f' : Unit → ⟨ A ⟩ → ⟨ B ⟩
  f' _ x = f x

  open StrongCBPVExt UnitPB A B f'
    renaming (ext' to strong-ext' ; ext to strong-ext)

  ext : L℧ ⟨ A ⟩ → ⟨ B ⟩
  ext = strong-ext tt

  -- Re-export all equations, without the need for the client to provide an element of type Unit.
  open Equations tt public

 

  -- We can directly use the ones defined in StrongCBPVExt by just supplying tt to the Equations module
  
  -- ext-η :  (x : ⟨ A ⟩) → ext (η x) ≡ f x
  -- ext-η x = strong-ext-η tt x -- funExt⁻ unfold-ext (η x)

  -- ext-℧ :  ext ℧ ≡ B.℧
  -- ext-℧ = {!!} -- funExt⁻ unfold-ext ℧

  -- ext-θ : (lx~ : ▹ L℧ ⟨ A ⟩) → ext (θ lx~) ≡ B.θ $ (map▹ ext lx~)
  -- ext-θ lx~ = {!!} -- funExt⁻ unfold-ext (θ lx~)

  -- ext-δ :  (lx : L℧ ⟨ A ⟩) → ext (δ lx) ≡ (B.θ $ next (ext lx))
  -- ext-δ lx = ext-θ (next lx)



module Counit (B : ErrorDomain ℓB ℓ≤B ℓ≈B) where

  -- open Free
  open ErrorDomMor
  open CBPVExt (U-ob B) B public

  private module B = ErrorDomainStr (B .snd)

  epsilon : L℧ ⟨ B ⟩ → ⟨ B ⟩
  epsilon = ext id

  -- eps' : ▹ (L℧ ⟨ B ⟩ → ⟨ B ⟩) → L℧ ⟨ B ⟩ → ⟨ B ⟩
  -- eps' _ (η x) = x
  -- eps' _ ℧ = B.℧
  -- eps' rec (θ lx~) = B.θ $ (λ t → rec t (lx~ t))

  -- eps : L℧ ⟨ B ⟩ → ⟨ B ⟩ -- UFUB → UB
  -- eps = fix eps'

  -- unfold-eps : eps ≡ eps' (next eps)
  -- unfold-eps = fix-eq eps'

  -- ε : ErrorDomMor (F-ob (U-ob B)) B   -- FUB -o B
  -- ε .f .PBMor.f = eps
  -- ε .f .PBMor.isMon = {!!}
  -- ε .f .PBMor.pres≈ = {!!}
  -- ε .f℧ = funExt⁻ unfold-eps _
  -- ε .fθ = {!!}



-- In this module, we show that the "delay" function on an error
-- domain B is bisimilar to the identity. This follows from the fact
-- that for value types A, the delay morphism δᴬ = θ ∘ next is
-- bisimilar to the identity on L℧ A

module DelayBisimId (B : ErrorDomain ℓB ℓ≤B ℓ≈B) where

  module B = ErrorDomainStr (B .snd)
  UB = ErrorDomain→Predomain B
  module UB = PosetBisimStr (UB .snd)
  open Counit B
  open PBMor


  {-  Claim: Let g* be the following map:

               η            δ           U ε
    g* :  UB -----> UFUB ------> UFUB ------> UB

      where δ = θ ∘ next and ε : FUB -* B is defined above
      (note that ε is equal to CPBV-ext id).

    Then: 1. g* ≡ δB (where δB = θB ∘ next, and θB is part of the error domain structure on B)
          2. g* ≈ id

  -}

  g* : ⟨ UB ⟩ → ⟨ UB ⟩
  g* = epsilon ∘ δ ∘ η

  δB : PBMor UB UB
  δB = B.θ ∘p Next
  
  δB-f = B.θ.f ∘ next

  fact1 : g* ≡ δB-f
  fact1 = funExt aux
    where
      aux : _
      aux x = epsilon (δ (η x))    ≡⟨ ext-δ id _ ⟩
              δB-f (epsilon (η x)) ≡⟨ cong δB-f (ext-η id x) ⟩
              δB-f x ∎

  fact2a : epsilon ∘ η ≡ id -- monad identity law
  fact2a = funExt aux
    where
      aux : _
      aux x = {!!}

  fact2 : _≈fun_ {Aᵢ = UB} {Aₒ = UB} g* id
  fact2 = {!!}

  --δB≈id : _≈fun_ {Aᵢ = UB} {Aₒ = UB} δB-f id
  --δB≈id = transport (cong₂ (_≈fun_ {Aᵢ = UB} {Aₒ = UB}) fact1 refl) fact2

  δB≈id : δB ≈mon Id
  δB≈id = transport (λ i → eqPBMor {!!} {!!} fact1 i ≈mon Id) fact2

  -- Need a lemma: If f is a predomain morphism, and g is a *function*, such that
  -- g is equal to the underlying function of f, then g is also a predomain morphism




module ExtAsMorphism (A : PosetBisim ℓA ℓ≤A ℓ≈A) (B : ErrorDomain ℓB ℓ≤B ℓ≈B)  where

  --open CBPVExt A B
  module B = ErrorDomainStr (B .snd)

    -- ext-mon : ▹ (monotone {X = 𝕃 A} {Y = ErrorDomain→Predomain B} (ext' (next ext))) →
    --             (monotone {X = 𝕃 A} {Y = ErrorDomain→Predomain B} (ext' (next ext)))
    -- ext-mon _ (LockStep.⊑ηη x y x≤y) = {!!}
    -- ext-mon _ (LockStep.⊑℧⊥ _) = B.℧⊥ _
    -- ext-mon IH (LockStep.⊑θθ lx~ ly~ x) = B.θ.isMon (λ t → {!!})


  module _ (f g : PBMor A (U-ob B)) (f≈g : f ≈mon g) where

    open CBPVExt A B (f .PBMor.f) using () renaming (ext to ext-f ; ext' to ext'-f)
    open CBPVExt A B (g .PBMor.f) using () renaming (ext to ext-g ; ext' to ext'-g)

    -- ext-f = ext (f .PBMor.f)
    -- ext-g = ext (g .PBMor.f)

    -- ext'-f = Rec.ext' (f .PBMor.f) (next ext-f)
    -- ext'-g = Rec.ext' (g .PBMor.f) (next ext-g)


    module ≈A = LiftBisim (Error ⟨ A ⟩) (≈ErrorA  (A .snd .PosetBisimStr._≈_))
    _≈L℧A_ = ≈A._≈_

{-
    ext≈ : ∀ (lx ly : L℧ ⟨ A ⟩) → lx ≈L℧A ly → ext'-f lx B.≈ ext'-g ly
    ext≈ .(η x) .(η y) (LiftBisim.≈ηη (ok x) (ok y) x₁) = f≈g x y {!!}
    ext≈ .(η x) ly (LiftBisim.≈ηθ (ok x) .ly H) = {!!}
    ext≈ lx .(ηL y) (LiftBisim.≈θη .lx y x) = {!!}
    ext≈ .(θ lx~) .(θ ly~) (LiftBisim.≈θθ lx~ ly~ x) = {!!}
    ext≈ _ = {!!}
-}


open Clocked k -- brings in definition of later on predomains

-- Towards constructing the free error domain FA on a predomain A, we
-- first define the underlying predomain UFA.
-- 
--   * The underlying set is L℧ A.
--   * The ordering is the lock-step error ordering.
--   * The bisimilarity relation is weak bisimilarity on L℧ A = L (Error A).
--
module LiftPredomain (A : PosetBisim ℓA ℓ≤A ℓ≈A) where

  module A = PosetBisimStr (A .snd)
  module LockStep = LiftOrdHomogenous ⟨ A ⟩ (A._≤_)
  _≤LA_ = LockStep._⊑_
  module Bisim = LiftBisim (Error ⟨ A ⟩) (≈ErrorA A._≈_)

  𝕃 : PosetBisim ℓA (ℓ-max ℓA ℓ≤A) (ℓ-max ℓA ℓ≈A)
  𝕃 .fst = L℧ ⟨ A ⟩
  𝕃 .snd = posetbisimstr (isSetL℧ _ A.is-set) _≤LA_ {!!} Bisim._≈_ {!!}

  -- θ as a morphism of *predomains* from ▹UFA to UFA
  θ-mor : PBMor (PB▹ 𝕃) 𝕃
  θ-mor .PBMor.f = θ
  θ-mor .PBMor.isMon = LockStep.Properties.θ-monotone
  θ-mor .PBMor.pres≈ = Bisim.Properties.θ-pres≈

  -- δ as a morphism of *predomains* from UFA to UFA.
  δ-mor : PBMor 𝕃 𝕃
  δ-mor .PBMor.f = δ
  δ-mor .PBMor.isMon = LockStep.Properties.δ-monotone
  δ-mor .PBMor.pres≈ = Bisim.Properties.δ-pres≈

  -- δ ≈ id
  δ≈id : δ-mor ≈mon Id
  δ≈id = ≈mon-sym Id δ-mor Bisim.Properties.δ-closed-r


-------------------------
-- 1. Action on objects.
-------------------------

-- Now we extend the predomain structure on L℧ X to an error domain
-- structure. This defines the action of the functor F on objects.

module F-ob (A : PosetBisim ℓA ℓ≤A ℓ≈A) where

  open LiftPredomain -- brings 𝕃 and modules into scope
  
  -- module A = PosetBisimStr (A .snd)
  -- module LockStepA = LiftOrdHomogenous ⟨ A ⟩ (A._≤_)
  -- module WeakBisimErrorA

  F-ob : ErrorDomain ℓA (ℓ-max ℓA ℓ≤A) (ℓ-max ℓA ℓ≈A)
  F-ob = mkErrorDomain (𝕃 A) ℧ (LockStep.Properties.℧⊥ A) (θ-mor A)

  -- F-ob :  ErrorDomain ℓA {!!} {!!}
  -- F-ob .fst = L℧ ⟨ A ⟩
  -- F-ob .snd .is-predomain = {!!}
  -- F-ob .snd .ErrorDomainStr.℧ = ℧
  -- F-ob .snd .ErrorDomainStr.℧⊥ = {!!}
  -- F-ob .snd .ErrorDomainStr.θ =
  --   record { f = θ ; isMon = LockStep.Properties.θ-monotone ; pres≈ = {!!} }



---------------------------------------
-- 2. Action of F on vertical morphisms
---------------------------------------

module F-mor
  {Aᵢ : PosetBisim ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ}
  {Aₒ : PosetBisim ℓAₒ ℓ≤Aₒ ℓ≈Aₒ}
  (f : PBMor Aᵢ Aₒ)
  where

  open F-ob

  F-mor : ErrorDomMor (F-ob Aᵢ) (F-ob Aₒ)
  F-mor = {!!}

  -- Functoriality (identity and composition)



-- Given: f : Aᵢ → Aₒ morphism
-- Define : F f: F Aᵢ -o F Aₒ
-- Given by applying the map function on L℧
-- NTS: map is a morphism of error domains (monotone pres≈, pres℧, presθ)
-- Recall that map is defined using ext (hard to show that ext pres ≈)


-----------------------------------------
-- 3. Action of F on horizontal morphisms
-----------------------------------------

module F-rel
  {A  : PosetBisim ℓA  ℓ≤A  ℓ≈A}
  {A' : PosetBisim ℓA' ℓ≤A' ℓ≈A'}
  (c : PBRel A A' ℓc) where

  module A  = PosetBisimStr (A  .snd)
  module A' = PosetBisimStr (A' .snd)
  module c = PBRel c

  open F-ob
  open ErrorDomRel
  open PBRel

  module Lc = LiftOrd ⟨ A ⟩ ⟨ A' ⟩ (c .PBRel.R)
  open Lc.Properties

  F-rel : ErrorDomRel (F-ob A) (F-ob A') (ℓ-max (ℓ-max ℓA ℓA') ℓc)
  F-rel .UR .R = Lc._⊑_
  F-rel .UR .is-prop-valued = isProp⊑
  F-rel .UR .is-antitone =
    DownwardClosed.⊑-downward ⟨ A ⟩ ⟨ A' ⟩ A._≤_ c.R (λ p q r → c.is-antitone) _ _ _
  F-rel .UR .is-monotone =
    {!!}
  F-rel .R℧ = Lc.Properties.℧⊥
  F-rel .Rθ la~ la'~ = θ-monotone

  -- Lax functoriality of F (i.e. there is a square from (F c ⊙ F c') to F (c ⊙ c'))
  --
  -- TODO


-----------------------------
-- 4. Action of F on squares
-----------------------------

module F-sq where
