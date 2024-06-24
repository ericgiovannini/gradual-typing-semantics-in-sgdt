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
open import Cubical.HITs.PropositionalTruncation hiding (map) renaming (rec to PTrec)
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
open import Semantics.Concrete.DoublePoset.PBSquare

open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k

open import Semantics.Concrete.DoublePoset.Error k
open import Semantics.Concrete.DoublePoset.Monad k
open import Semantics.Concrete.DoublePoset.MonadRelationalResults k

open ClockedCombinators k

private
  variable
    ℓ ℓ' : Level
    ℓA  ℓ≤A  ℓ≈A  : Level
    ℓA' ℓ≤A' ℓ≈A' : Level
    ℓB  ℓ≤B  ℓ≈B  : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ : Level
    ℓA₂ ℓ≤A₂ ℓ≈A₂ : Level
    ℓA₃ ℓ≤A₃ ℓ≈A₃ : Level
    ℓΓ ℓ≤Γ ℓ≈Γ : Level
    ℓC : Level
    ℓc ℓc' ℓR : Level
    ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  : Level
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' : Level
    ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  : Level
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' : Level
    ℓcᵢ ℓcₒ : Level
   

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


open BinaryRelation
open ErrorDomainStr hiding (℧ ; θ ; δ)
open PosetBisimStr
open Clocked k -- brings in definition of later on predomains


-- The purpose of this module is to define the functor F : Predomain →
-- ErrorDomain left adjoint to the forgetful functor U.

-- We define:
--
-- - The action on objects
-- - The action on vertical morphisms (i.e. fmap)
-- - The action on horizontal morpisms
-- - The action on squares

-- In the below, "UF X" will be sometimes be written in place of the monad L℧ X.

--------------------------------------------------------------------------------



-----------------------------------------------------------------------



-------------------------------------
-- The counit of the adjunction F ⊣ U
-------------------------------------

module Counit (B : ErrorDomain ℓB ℓ≤B ℓ≈B) where

  open ErrorDomMor
  private module B = ErrorDomainStr (B .snd)

  open CBPVExt ⟨ B ⟩ ⟨ B ⟩ B.℧ (B.θ.f) public
  open MonadLaws.Unit-Left ⟨ B ⟩ ⟨ B ⟩ B.℧ B.θ.f

  epsilon : L℧ ⟨ B ⟩ → ⟨ B ⟩
  epsilon = ext id

  epsilon∘η≡id : epsilon ∘ η ≡ id
  epsilon∘η≡id = funExt (λ x → monad-unit-left id x)


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
  module BisimL℧B = LiftBisim (Error ⟨ B ⟩) (≈ErrorX B._≈_)


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
      aux x = epsilon (δ (η x))    ≡⟨ Equations.ext-δ id _ ⟩
              δB-f (epsilon (η x)) ≡⟨ cong δB-f (Equations.ext-η id x) ⟩
              δB-f x ∎

  fact2a : epsilon ∘ η ≡ id
  fact2a = epsilon∘η≡id

  fact2b : TwoCell B._≈_ B._≈_ (epsilon ∘ δ ∘ η) (epsilon ∘ id ∘ η)
  fact2b x y x≈y = {!!}
    where
      α : TwoCell B._≈_ BisimL℧B._≈_ η η
      α x y x≈y = BisimL℧B.Properties.η-pres≈ x≈y
      
      β : TwoCell BisimL℧B._≈_ BisimL℧B._≈_ δ id
      β x y x≈y = {!!}
      
      γ : TwoCell BisimL℧B._≈_ B._≈_ epsilon epsilon
      γ x y x≈y = {!!}

  fact2 : _≈fun_ {Aᵢ = UB} {Aₒ = UB} g* id
  fact2 = {!!}

  δB≈id : _≈fun_ {Aᵢ = UB} {Aₒ = UB} δB-f id
  δB≈id = transport (cong₂ (_≈fun_ {Aᵢ = UB} {Aₒ = UB}) fact1 refl) fact2

  -- δB≈id : δB ≈mon Id
  -- δB≈id = transport (λ i → eqPBMor {!!} {!!} fact1 i ≈mon Id) fact2
  -- Need a lemma: If f is a predomain morphism, and g is a *function*, such that
  -- g is equal to the underlying function of f, then g is also a predomain morphism



{-
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

-}


--------------------------
-- Defining the functor F
--------------------------

-- Towards constructing the free error domain FA on a predomain A, we
-- first define the underlying predomain UFA.
-- 
--   * The underlying set is L℧ A.
--   * The ordering is the lock-step error ordering.
--   * The bisimilarity relation is weak bisimilarity on L℧ A = L (Error A).
--
module LiftPredomain (A : PosetBisim ℓA ℓ≤A ℓ≈A) where

  private module A = PosetBisimStr (A .snd)
  module LockStepA = LiftOrdHomogenous ⟨ A ⟩ (A._≤_)
  _≤LA_ = LockStepA._⊑_
  module Bisim = LiftBisim (Error ⟨ A ⟩) (≈ErrorX A._≈_)

  𝕃 : PosetBisim ℓA (ℓ-max ℓA ℓ≤A) (ℓ-max ℓA ℓ≈A)
  𝕃 .fst = L℧ ⟨ A ⟩
  𝕃 .snd = posetbisimstr (isSetL℧ _ A.is-set) _≤LA_ ordering Bisim._≈_ bisim
    where
      ordering : _
      ordering = isorderingrelation
        LockStepA.Properties.isProp⊑
        (LockStepA.Properties.⊑-refl A.is-refl)
        (LockStepA.Properties.⊑-transitive A.is-trans)
        (LockStepA.Properties.⊑-antisym A.is-antisym)

      bisim : _
      bisim = isbisim
              (Bisim.Properties.reflexive {!!})
              (Bisim.Properties.symmetric {!!})
              (Bisim.Properties.is-prop {!!})

  -- η as a morphism of predomain from A to UFA
  η-mor : PBMor A 𝕃
  η-mor .PBMor.f = η
  η-mor .PBMor.isMon = LockStepA.Properties.η-monotone
  η-mor .PBMor.pres≈ = {!η x!} -- Bisim.Properties.η-pres≈

  -- ℧ as a morphism of predomains from any A' to UFA
  ℧-mor : {A' : PosetBisim ℓA' ℓ≤A' ℓ≈A'} → PBMor A' 𝕃
  ℧-mor = K _ ℧ 

  -- θ as a morphism of *predomains* from ▹UFA to UFA
  θ-mor : PBMor (PB▹ 𝕃) 𝕃
  θ-mor .PBMor.f = θ
  θ-mor .PBMor.isMon = LockStepA.Properties.θ-monotone
  θ-mor .PBMor.pres≈ = Bisim.Properties.θ-pres≈

  -- δ as a morphism of *predomains* from UFA to UFA.
  δ-mor : PBMor 𝕃 𝕃
  δ-mor .PBMor.f = δ
  δ-mor .PBMor.isMon = LockStepA.Properties.δ-monotone
  δ-mor .PBMor.pres≈ = Bisim.Properties.δ-pres≈

  -- δ ≈ id
  -- δ≈id : δ-mor ≈mon Id
  -- δ≈id = ≈mon-sym Id δ-mor Bisim.Properties.δ-closed-r




-------------------------
-- 1. Action on objects.
-------------------------

-- We extend the predomain structure on L℧ X defined above to an error
-- domain structure. This defines the action of the functor F on
-- objects.

module F-ob (A : PosetBisim ℓA ℓ≤A ℓ≈A) where

  open LiftPredomain -- brings 𝕃 and modules into scope
  
  -- module A = PosetBisimStr (A .snd)
  -- module LockStepA = LiftOrdHomogenous ⟨ A ⟩ (A._≤_)
  -- module WeakBisimErrorA

  F-ob : ErrorDomain ℓA (ℓ-max ℓA ℓ≤A) (ℓ-max ℓA ℓ≈A)
  F-ob = MkErrorDomain.mkErrorDomain
    (𝕃 A) ℧ (LockStepA.Properties.℧⊥ A) (θ-mor A)
    (≈mon-sym Id (δ-mor A) (Bisim.Properties.δ-closed-r A))


---------------------------------------
-- 2. Action of F on vertical morphisms
---------------------------------------

module F-mor
  {Aᵢ : PosetBisim ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ}
  {Aₒ : PosetBisim ℓAₒ ℓ≤Aₒ ℓ≈Aₒ}
  (f : PBMor Aᵢ Aₒ)
  where

  module Aᵢ = PosetBisimStr (Aᵢ .snd)
  module Aₒ = PosetBisimStr (Aₒ .snd)

  open F-ob
  open Map
  open MapProperties
  open MapRelationalProps ⟨ Aᵢ ⟩ ⟨ Aᵢ ⟩ ⟨ Aₒ ⟩ ⟨ Aₒ ⟩ Aᵢ._≤_ Aₒ._≤_

  F-mor : ErrorDomMor (F-ob Aᵢ) (F-ob Aₒ)
  F-mor .ErrorDomMor.f .PBMor.f = map (f .PBMor.f)
  F-mor .ErrorDomMor.f .PBMor.isMon = map-monotone (f .PBMor.f) (f .PBMor.f) {!!} _ _
  F-mor .ErrorDomMor.f .PBMor.pres≈ = {!!}
  F-mor .ErrorDomMor.f℧ = map-℧ (f .PBMor.f)
  F-mor .ErrorDomMor.fθ = map-θ (f .PBMor.f)

  -- Functoriality (identity and composition)






-- Given: f : Aᵢ → Aₒ morphism
-- Define : F f: F Aᵢ -o F Aₒ
-- Given by applying the map function on L℧
-- NTS: map is a morphism of error domains (monotone pres≈, pres℧, presθ)


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
    UpwardClosed.⊑-upward ⟨ A ⟩ ⟨ A' ⟩ A'._≤_ c.R (λ p q r → c.is-monotone) _ _ _
  F-rel .R℧ = Lc.Properties.℧⊥
  F-rel .Rθ la~ la'~ = θ-monotone


-- The action of F on relations preserves identity.
F-rel-presId : ∀ {A : PosetBisim ℓA ℓ≤A ℓ≈A} →
  F-rel.F-rel (idPRel A) ≡ idEDRel (F-ob.F-ob A)
F-rel-presId = eqEDRel _ _ refl -- both have the same underlying relation

-- Lax functoriality of F (i.e. there is a square from (F c ⊙ F c') to F (c ⊙ c'))
module F-rel-lax-functoriality
  {A₁ : PosetBisim ℓA₁  ℓ≤A₁  ℓ≈A₁}
  {A₂ : PosetBisim ℓA₂  ℓ≤A₂  ℓ≈A₂}
  {A₃ : PosetBisim ℓA₃  ℓ≤A₃  ℓ≈A₃}
  (c : PBRel A₁ A₂ ℓc) (c' : PBRel A₂ A₃ ℓc') where

  open F-ob
  open F-rel
  open HetTransitivity ⟨ A₁ ⟩ ⟨ A₂ ⟩ ⟨ A₃ ⟩ (c .PBRel.R) (c' .PBRel.R)

  open HorizontalComp
  open HorizontalCompUMP (F-rel c) (F-rel c') IdE IdE IdE (F-rel (c ⊙ c'))


  lax-functoriality : ErrorDomSq (F-rel c ⊙ed F-rel c') (F-rel (c ⊙ c')) IdE IdE
  lax-functoriality = ElimHorizComp α
    where
      -- By the universal property of the free composition, it
      -- suffices to build a predomain square whose top is the *usual*
      -- composition of the underlying relations:
      α : PBSq ((U-rel (F-rel c)) ⊙ (U-rel (F-rel c')))
               (U-rel (F-rel (c ⊙ c')))
               Id Id
      α lx lz lx-LcLc'-lz =
        -- We use the fact that the lock-step error ordering is
        -- "heterogeneously transitive", i.e. if lx LR ly and ly LS lz,
        -- then lx L(R ∘ S) lz.
        PTrec
          (PBRel.is-prop-valued (U-rel (F-rel (c ⊙ c'))) lx lz)
          (λ {(ly , lx-Lc-ly , ly-Lc'-lz) → het-trans lx ly lz lx-Lc-ly ly-Lc'-lz})
          lx-LcLc'-lz

-----------------------------
-- 4. Action of F on squares
-----------------------------

module F-sq
  {Aᵢ  : PosetBisim ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ}
  {Aᵢ' : PosetBisim ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
  {Aₒ  : PosetBisim ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ} 
  {Aₒ' : PosetBisim ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'}
  (cᵢ  : PBRel Aᵢ Aᵢ' ℓcᵢ)
  (cₒ  : PBRel Aₒ Aₒ' ℓcₒ)
  (f   : PBMor Aᵢ  Aₒ)
  (g   : PBMor Aᵢ' Aₒ') where

  open F-mor
  open F-rel

  module cᵢ = PBRel cᵢ
  module cₒ = PBRel cₒ

  open MapRelationalProps ⟨ Aᵢ ⟩ ⟨ Aᵢ' ⟩ ⟨ Aₒ ⟩ ⟨ Aₒ' ⟩ cᵢ.R cₒ.R

  F-sq : PBSq cᵢ cₒ f g →
    ErrorDomSq (F-rel cᵢ) (F-rel cₒ) (F-mor f) (F-mor g)
  F-sq α = map-monotone (f .PBMor.f) (g .PBMor.f) α

