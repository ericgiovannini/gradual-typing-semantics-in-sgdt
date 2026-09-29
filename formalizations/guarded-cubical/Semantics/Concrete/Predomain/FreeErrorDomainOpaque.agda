{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.Predomain.FreeErrorDomainOpaque (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Relation.Binary.Base
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.HITs.PropositionalTruncation hiding (map) renaming (rec to PTrec)
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Empty
open import Cubical.Foundations.HLevels

open import Common.Common
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions hiding (𝔽)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Combinators
open import Semantics.Concrete.Predomain.SquareOpaque

open import Semantics.Concrete.Predomain.SimpleErrorDomain k
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.ErrorDomain.Square k
open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k

open import Semantics.Concrete.Predomain.Error
open import Semantics.Concrete.Predomain.Ext k
open import Semantics.Concrete.Predomain.MonadRelationalResults k

open ClockedCombinators k

private
  variable
    ℓ ℓ' : Level
    ℓA  ℓ≤A  ℓ≈A  : Level
    ℓA' ℓ≤A' ℓ≈A' : Level
    ℓB  ℓ≤B  ℓ≈B  : Level
    ℓB' ℓ≤B' ℓ≈B' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ : Level
    ℓA₂ ℓ≤A₂ ℓ≈A₂ : Level
    ℓA₃ ℓ≤A₃ ℓ≈A₃ : Level
    ℓΓ ℓ≤Γ ℓ≈Γ : Level
    ℓC : Level
    ℓc ℓc' ℓd ℓR : Level
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
open PredomainStr
open Clocked k -- brings in definition of later on predomains
open Equations

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
module LiftPredomain (A : Predomain ℓA ℓ≤A ℓ≈A) where

  private module A = PredomainStr (A .snd)
  module LockStepA = LiftOrdHomogenous ⟨ A ⟩ (A._≤_)
  _≤LA_ = LockStepA._⊑_
  module BisimLift = LiftBisim (Error ⟨ A ⟩) (≈ErrorX A._≈_)

  bisimErrorA : IsBisim (≈ErrorX A._≈_)
  bisimErrorA = IsBisimErrorX A._≈_ A.isBisim
  module BisimErrorA = IsBisim (bisimErrorA)

  opaque
    𝕃 : Predomain ℓA (ℓ-max ℓA ℓ≤A) (ℓ-max ℓA ℓ≈A)
    𝕃 .fst = L℧ ⟨ A ⟩
    𝕃 .snd = predomainstr (isSetL℧ _ A.is-set) _≤LA_ ordering BisimLift._≈_ bisim
      where
        ordering : IsOrderingRelation _≤LA_
        ordering = isorderingrelation
          LockStepA.Properties.isProp⊑
          (LockStepA.Properties.⊑-refl A.is-refl)
          (LockStepA.Properties.⊑-transitive A.is-trans)
          (LockStepA.Properties.⊑-antisym A.is-antisym)

        bisim : IsBisim BisimLift._≈_
        bisim = isbisim
                (BisimLift.Properties.reflexive BisimErrorA.is-refl)
                (BisimLift.Properties.symmetric BisimErrorA.is-sym)
                (BisimLift.Properties.is-prop BisimErrorA.is-prop-valued)


module _ {A : Predomain ℓA ℓ≤A ℓ≈A} where

  open LiftPredomain A

  -- η as a morphism of predomain from A to 𝕃A
  opaque
    unfolding 𝕃
    
    η-mor : PMor A 𝕃
    η-mor .PMor.f = η
    η-mor .PMor.isMon = LockStepA.Properties.η-monotone
    η-mor .PMor.pres≈ = BisimLift.Properties.η-pres≈

    -- ℧ as a morphism of predomains from any A' to 𝕃A
    ℧-mor : {A' : Predomain ℓA' ℓ≤A' ℓ≈A'} → PMor A' 𝕃
    ℧-mor = K _ ℧ 

    -- θ as a morphism of *predomains* from ▹𝕃A to 𝕃A
    θ-mor : PMor (P▹ 𝕃) 𝕃
    θ-mor .PMor.f = θ
    θ-mor .PMor.isMon = LockStepA.Properties.θ-monotone
    θ-mor .PMor.pres≈ = BisimLift.Properties.θ-pres≈

    -- δ as a morphism of *predomains* from 𝕃A to 𝕃A.
    δ-mor : PMor 𝕃 𝕃
    δ-mor .PMor.f = δ
    δ-mor .PMor.isMon = LockStepA.Properties.δ-monotone
    δ-mor .PMor.pres≈ = BisimLift.Properties.δ-pres≈

  -- δ ≈ id
  -- δ≈id : δ-mor ≈mon Id
  -- δ≈id = ≈mon-sym Id δ-mor BisimLift.Properties.δ-closed-r




-------------------------
-- 1. Action on objects.
-------------------------

-- We extend the predomain structure on L℧ X defined above to an error
-- domain structure. This defines the action of the functor F on
-- objects.

module F-ob (A : Predomain ℓA ℓ≤A ℓ≈A) where

  open LiftPredomain -- brings 𝕃 and modules into scope
  
  -- module A = PredomainStr (A .snd)
  -- module LockStepA = LiftOrdHomogenous ⟨ A ⟩ (A._≤_)
  -- module WeakBisimErrorA

  opaque
    unfolding 𝕃 δ-mor
    
    F-ob : ErrorDomain ℓA (ℓ-max ℓA ℓ≤A) (ℓ-max ℓA ℓ≈A)
    F-ob = mkErrorDomain
      (𝕃 A) ℧ (LockStepA.Properties.℧⊥ A) (θ-mor)
      (≈mon-sym Id (δ-mor)
        (BisimLift.Properties.δ-closed-r A (BisimErrorA.is-prop-valued A)))

open F-ob

module _ {A : Predomain ℓA ℓ≤A ℓ≈A} where
  open F-ob
  opaque
    unfolding LiftPredomain.𝕃 F-ob
    
    ηM : PMor A (U-ob (F-ob A))
    ηM = η-mor

    -- ℧ as a morphism of predomains from any A' to UFA
    ℧M : {A' : Predomain ℓA' ℓ≤A' ℓ≈A'} → PMor A' (U-ob (F-ob A))
    ℧M = ℧-mor

    -- θ as a morphism of *predomains* from ▹UFA to UFA
    θM : PMor (P▹ (U-ob (F-ob A))) (U-ob (F-ob A))
    θM = θ-mor
  
    -- δ as a morphism of *predomains* from UFA to UFA.
    δM : PMor (U-ob (F-ob A)) (U-ob (F-ob A))
    δM = δ-mor



-- Monadic ext as a morphism of error domains

module ExtAsEDMorphism
  {A : Predomain ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} where

  open F-ob

  private
    module A = PredomainStr (A .snd)
    module B = ErrorDomainStr (B .snd)
  
  -- open Ext ⟨ A ⟩ ⟨ B ⟩ B.℧ B.θ.f renaming (module Equations to Equations')
  
  open ExtMonotone ⟨ A ⟩ ⟨ A ⟩ A._≤_
                   ⟨ B ⟩ B.℧ B.θ.f ⟨ B ⟩ B.℧ B.θ.f
                   B._≤_ B.℧⊥
                   (λ _ _ x~≤y~ → B.θ.isMon (λ t → x~≤y~ t))
                   
  open StrongExtPresBisim
    Unit (λ _ _ → Unit)
    ⟨ A ⟩ A._≈_
    ⟨ B ⟩ B.℧ B.θ.f
    B._≈_
    B.is-prop-valued-Bisim
    B.is-refl-Bisim
    B.is-sym
    (λ x~ y~ H~ → B.θ.pres≈ H~)
    B.δ≈id

  module Equations-U (f : PMor A (U-ob B)) where
    private
      f' : ⟨ A ⟩ → ⟨ ErrorDomain→SimpleErrorDomain B ⟩s
      f' = ⟨ErrorDomain⟩→⟨SimpleErrorDomain⟩ ∘ f .PMor.f

      open Equations f' public

  module _ (f : PMor A (U-ob B)) where
    private
      f' : ⟨ A ⟩ → ⟨ ErrorDomain→SimpleErrorDomain B ⟩s
      f' = ⟨ErrorDomain⟩→⟨SimpleErrorDomain⟩ ∘ f .PMor.f
      
    opaque
      unfolding F-ob mkSimpleErrorDomain ⟨_⟩s
    
      Ext : ErrorDomMor (F-ob A) B
      Ext .ErrorDomMor.f .PMor.f =
        ext {B = ErrorDomain→SimpleErrorDomain B} (f .PMor.f)
          -- ⟨SimpleErrorDomain⟩→⟨ErrorDomain⟩ ∘ ext f' ∘ ⟨ErrorDomain⟩→⟨SimpleErrorDomain⟩ {B = F-ob A}
      Ext .ErrorDomMor.f .PMor.isMon = {!!}
      Ext .ErrorDomMor.f .PMor.pres≈ = λ x₁ → {!!}
      Ext .ErrorDomMor.f℧ = {!Equations-U.ext-℧ f!} -- Equations-U.ext-℧ f
      Ext .ErrorDomMor.fθ = {!!} -- Equations-U.ext-θ f

  module _ (f : PMor A (U-ob B)) where

    opaque
      unfolding Ext F-ob mkSimpleErrorDomain ⟨_⟩s η𝔽 ℧𝔽 θ𝔽 δ𝔽 ηM ℧M θM δM

      Ext-ηF-type : Type (ℓ-max ℓA ℓB)
      Ext-ηF-type = ∀ x → (Ext f .ErrorDomMor.fun (η𝔽 x)) ≡ f .PMor.f x

      Ext-℧F-type : Type ℓB
      Ext-℧F-type = Ext f .ErrorDomMor.fun ℧𝔽 ≡ B.℧

      Ext-θF-type : Type (ℓ-max ℓA ℓB)
      Ext-θF-type = ∀ lx~ → (Ext f .ErrorDomMor.fun (θ𝔽 lx~)) ≡
                           B.θ.f (map▹ (Ext f .ErrorDomMor.fun) lx~)

      Ext-δF-type : Type (ℓ-max ℓA ℓB)
      Ext-δF-type = ∀ lx → (Ext f .ErrorDomMor.fun (δ𝔽 lx)) ≡ B.δ .PMor.f (Ext f .ErrorDomMor.fun lx)

      {-
      Ext-ηF : Ext-ηF-type
      Ext-ηF x = Equations.ext-η (f .PMor.f) x

      Ext-℧F : Ext-℧F-type
      Ext-℧F = {!!}

      Ext-θF : Ext-θF-type
      Ext-θF = {!!}

      Ext-δF : Ext-δF-type
      Ext-δF = {!!}
      -}


      Ext-ηM : ∀ x → (Ext f .ErrorDomMor.fun (ηM .PMor.f x)) ≡ f .PMor.f x
      Ext-ηM x = Equations.ext-η (f .PMor.f) x

      Ext-℧M : ∀ (x : ⟨ A ⟩) → Ext f .ErrorDomMor.fun (℧M {A' = A} .PMor.f x)  ≡ B.℧
      Ext-℧M = {!!}

      Ext-θM : ∀ lx~ → Ext f. ErrorDomMor.fun (θM .PMor.f lx~) ≡ {!!}
      Ext-θM = {!!}

     

      -- Ext-℧M-type : Type ℓB
      -- Ext-℧M-type = Ext f .ErrorDomMor.fun ℧𝔽 ≡ B.℧

      -- Ext-θM-type : Type (ℓ-max ℓA ℓB)
      -- Ext-θM-type = ∀ lx~ → (Ext f .ErrorDomMor.fun (θ𝔽 lx~)) ≡
      --                      B.θ.f (map▹ (Ext f .ErrorDomMor.fun) lx~)

      -- Ext-δM-type : Type (ℓ-max ℓA ℓB)
      -- Ext-δM-type = ∀ lx → (Ext f .ErrorDomMor.fun (δ𝔽 lx)) ≡ B.δ .PMor.f (Ext f .ErrorDomMor.fun lx)

{-
  opaque
    unfolding F-ob
    
    Ext : PMor A (U-ob B) → ErrorDomMor (F-ob A) B
    Ext f .ErrorDomMor.f .PMor.f = ext (f .PMor.f)
    Ext f .ErrorDomMor.f .PMor.isMon =
      ext-mon (f .PMor.f) (f .PMor.f) (≤mon→≤mon-het f f (≤mon-refl f)) _ _
    Ext f .ErrorDomMor.f .PMor.pres≈ =
      strong-ext-pres≈ (λ _ → f .PMor.f) (λ _ → f .PMor.f) (λ _ _ _ → ≈mon-refl f) tt tt tt _ _
    Ext f .ErrorDomMor.f℧ = Equations-U.ext-℧ f
    Ext f .ErrorDomMor.fθ = Equations-U.ext-θ f

  module _ (f : PMor A (U-ob B)) where

   opaque
     unfolding LiftPredomain.𝕃 F-ob η-mor ηM Ext
     
     Ext-η : (U-mor (Ext f) ∘p ηM) ≡ f
     Ext-η = eqPMor _ _ (funExt (λ x → Equations-U.ext-η f x))

     Ext-℧ : (U-mor (Ext f) ∘p ℧M) ≡ (K B.Pre B.℧)
     Ext-℧ = eqPMor _ _ (funExt (λ x → Equations-U.ext-℧ f))

     Ext-θ : (U-mor (Ext f) ∘p θM) ≡ (B.θ ∘p (Map▹ (U-mor (Ext f))))
     Ext-θ = eqPMor _ _ (funExt (λ lx~ → Equations-U.ext-θ f lx~))

     Ext-δ : (U-mor (Ext f) ∘p δM) ≡ (B.δ ∘p U-mor (Ext f))
     Ext-δ = eqPMor _ _ (funExt (λ lx → Equations-U.ext-δ f lx))
-}

opaque
  unfolding F-ob.F-ob ExtAsEDMorphism.Ext ηM
  Ext-unit-right : ∀ {A : Predomain ℓA ℓ≤A ℓ≈A} →
    ExtAsEDMorphism.Ext ηM ≡ IdE {B = F-ob.F-ob A}
  Ext-unit-right {A = A} = {!!}
  -- eqEDMor _ _ (funExt (λ lx → MonadLaws.monad-unit-right lx))



---------------------------------------
-- 2. Action of F on vertical morphisms
---------------------------------------

module F-mor
  {Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ}
  {Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ}
 
  where

  module Aᵢ = PredomainStr (Aᵢ .snd)
  module Aₒ = PredomainStr (Aₒ .snd)

  open F-ob
  open MapProperties
  open MapMonotone ⟨ Aᵢ ⟩ ⟨ Aᵢ ⟩ ⟨ Aₒ ⟩ ⟨ Aₒ ⟩ Aᵢ._≤_ Aₒ._≤_
  open MapPresBisim ⟨ Aᵢ ⟩ ⟨ Aₒ ⟩ Aᵢ._≈_ Aₒ._≈_
                     Aₒ.is-prop-valued-Bisim Aₒ.is-refl-Bisim Aₒ.is-sym



  module _ (f : PMor Aᵢ Aₒ) where

    opaque
      unfolding F-ob mkSimpleErrorDomain ℧𝔽 θ𝔽
      -- if we didn't unfold mkSimpleErrorDomain we would need to manually convert between
      -- ⟨ ErrorDomain→Predomain (F-ob A) ⟩ and ⟨ 𝔽 A ⟩s
    
      F-mor : ErrorDomMor (F-ob Aᵢ) (F-ob Aₒ)
      F-mor .ErrorDomMor.f .PMor.f = map (f .PMor.f)
      F-mor .ErrorDomMor.f .PMor.isMon = {!!}
        -- map-monotone (f .PMor.f) (f .PMor.f) (≤mon→≤mon-het f f (≤mon-refl f)) _ _
      F-mor .ErrorDomMor.f .PMor.pres≈ = {!!}
        -- map-pres-≈ (λ z → f .PMor.f z) (λ z → f .PMor.f z) (λ x y x≈y → f .PMor.pres≈ x≈y) _ _
      F-mor .ErrorDomMor.f℧ = map-℧ (f .PMor.f)
      F-mor .ErrorDomMor.fθ = map-θ (f .PMor.f)

  module _ (f : PMor Aᵢ Aₒ) where

    opaque
      unfolding F-ob.F-ob F-mor ηM
      
      F-mor-η : (U-mor (F-mor f) ∘p ηM) ≡ (ηM ∘p f)
      F-mor-η = PMorExt _ _ (λ x → ext-η _ x) -- eqPMor _ _ (funExt (λ x → map-η (f .PMor.f) x))



-- Functoriality (identity and composition)
open F-mor

opaque
  unfolding F-ob.F-ob F-mor
  F-mor-pres-id : {A : Predomain ℓA ℓ≤A ℓ≈A} →
    F-mor (Id {X = A}) ≡ IdE
  F-mor-pres-id = eqEDMor (F-mor Id) IdE pres-id
    where open MapProperties

  F-mor-pres-comp :
    {A₁ : Predomain ℓA₁  ℓ≤A₁  ℓ≈A₁}
    {A₂ : Predomain ℓA₂  ℓ≤A₂  ℓ≈A₂}
    {A₃ : Predomain ℓA₃  ℓ≤A₃  ℓ≈A₃} →
    (g : PMor A₂ A₃) (f : PMor A₁ A₂) →
    F-mor (g ∘p f) ≡ (F-mor g) ∘ed (F-mor f)
  F-mor-pres-comp g f =
    eqEDMor (F-mor (g ∘p f)) ((F-mor g) ∘ed (F-mor f)) (pres-comp (f .PMor.f) (g .PMor.f))
    where open MapProperties
  


-- Given: f : Aᵢ → Aₒ morphism
-- Define : F f: F Aᵢ -o F Aₒ
-- Given by applying the map function on L℧
-- NTS: map is a morphism of error domains (monotone pres≈, pres℧, presθ)


-----------------------------------------
-- 3. Action of F on horizontal morphisms
-----------------------------------------

module F-rel
  {A  : Predomain ℓA  ℓ≤A  ℓ≈A}
  {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  (c : PRel A A' ℓc) where

  private
    module A  = PredomainStr (A  .snd)
    module A' = PredomainStr (A' .snd)
    module c = PRel c

  open F-ob
  open ErrorDomRel
  open PRel

  private
    module Lc = LiftOrd ⟨ A ⟩ ⟨ A' ⟩ (c .PRel.R)
  open Lc.Properties

  opaque
    unfolding F-ob
    
    F-rel : ErrorDomRel (F-ob A) (F-ob A') (ℓ-max (ℓ-max ℓA ℓA') ℓc)
    F-rel .UR .R = Lc._⊑_
    F-rel .UR .is-prop-valued = isProp⊑
    F-rel .UR .is-antitone =
      DownwardClosed.⊑-downward ⟨ A ⟩ ⟨ A' ⟩ A._≤_ c.R (λ p q r → c.is-antitone) _ _ _
    F-rel .UR .is-monotone =
      UpwardClosed.⊑-upward ⟨ A ⟩ ⟨ A' ⟩ A'._≤_ c.R (λ p q r → c.is-monotone) _ _ _
    F-rel .R℧ = Lc.Properties.℧⊥
    F-rel .Rθ la~ la'~ = θ-monotone


open F-rel


-- The action of F on relations preserves identity.
opaque
  unfolding F-rel
  F-rel-presId : ∀ {A : Predomain ℓA ℓ≤A ℓ≈A} →
    F-rel (idPRel A) ≡ idEDRel (F-ob.F-ob A)
  F-rel-presId = eqEDRel _ _ refl -- both have the same underlying relation

-- Lax functoriality of F (i.e. there is a square from (F c ⊙ F c') to F (c ⊙ c'))
module F-rel-lax-functoriality
  {A₁ : Predomain ℓA₁  ℓ≤A₁  ℓ≈A₁}
  {A₂ : Predomain ℓA₂  ℓ≤A₂  ℓ≈A₂}
  {A₃ : Predomain ℓA₃  ℓ≤A₃  ℓ≈A₃}
  (c : PRel A₁ A₂ ℓc) (c' : PRel A₂ A₃ ℓc') where

  open F-ob
  open F-rel
  open HetTransitivity ⟨ A₁ ⟩ ⟨ A₂ ⟩ ⟨ A₃ ⟩ (c .PRel.R) (c' .PRel.R)

  open HorizontalComp
  open HorizontalCompUMP (F-rel c) (F-rel c') IdE IdE IdE (F-rel (c ⊙ c'))

  opaque
    unfolding F-ob F-rel PSq
    lax-functoriality : ErrorDomSq (F-rel c ⊙ed F-rel c') (F-rel (c ⊙ c')) IdE IdE
    lax-functoriality = ElimHorizComp α
      where
        -- By the universal property of the free composition, it
        -- suffices to build a predomain square whose top is the *usual*
        -- composition of the underlying relations:
        α : PSq ((U-rel (F-rel c)) ⊙ (U-rel (F-rel c')))
                 (U-rel (F-rel (c ⊙ c')))
                 Id Id
        α lx lz lx-LcLc'-lz =
          -- We use the fact that the lock-step error ordering is
          -- "heterogeneously transitive", i.e. if lx LR ly and ly LS lz,
          -- then lx L(R ∘ S) lz.
          PTrec
            (PRel.is-prop-valued (U-rel (F-rel (c ⊙ c'))) lx lz)
            (λ {(ly , lx-Lc-ly , ly-Lc'-lz) → het-trans lx ly lz lx-Lc-ly ly-Lc'-lz})
            lx-LcLc'-lz

-----------------------------
-- 4. Action of F on squares
-----------------------------

module F-sq
  {Aᵢ  : Predomain ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ}
  {Aᵢ' : Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
  {Aₒ  : Predomain ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ} 
  {Aₒ' : Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'}
  (cᵢ  : PRel Aᵢ Aᵢ' ℓcᵢ)
  (cₒ  : PRel Aₒ Aₒ' ℓcₒ)
  (f   : PMor Aᵢ  Aₒ)
  (g   : PMor Aᵢ' Aₒ') where

  open F-mor
  open F-rel

  module cᵢ = PRel cᵢ
  module cₒ = PRel cₒ

  open MapMonotone ⟨ Aᵢ ⟩ ⟨ Aᵢ' ⟩ ⟨ Aₒ ⟩ ⟨ Aₒ' ⟩ cᵢ.R cₒ.R

  opaque
    unfolding F-ob F-mor F-rel
    F-sq : PSq cᵢ cₒ f g →
      ErrorDomSq (F-rel cᵢ) (F-rel cₒ) (F-mor f) (F-mor g)
    F-sq α = {!!} --map-monotone (f .PMor.f) (g .PMor.f) α


-- Ext lifts to squares

module _
  {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
  (c : PRel A A' ℓc) (d : ErrorDomRel B B' ℓd)
  (f : PMor A (U-ob B)) (g : PMor A' (U-ob B'))
  where

  private
    module B = ErrorDomainStr (B .snd)
    module B' = ErrorDomainStr (B' .snd)
    module d = ErrorDomRel d

  open ExtAsEDMorphism
  open ExtMonotone
    ⟨ A ⟩ ⟨ A' ⟩ (c .PRel.R)
    ⟨ B ⟩ B.℧ B.θ.f ⟨ B' ⟩ B'.℧ B'.θ.f
    (d .ErrorDomRel.R)
    d.R℧
    d.Rθ
  open F-ob
  open F-rel

  opaque
    unfolding F-ob F-rel Ext
    Ext-sq : PSq c (U-rel d) f g → ErrorDomSq (F-rel c) d (Ext f) (Ext g)
    Ext-sq α = {!!} -- ext-mon (f .PMor.f) (g .PMor.f) α


module _
  {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  (c : PRel A A' ℓc)
  where
  open F-rel

  private
    module Lc = LiftOrd ⟨ A ⟩ ⟨ A' ⟩ (c .PRel.R)
  open Lc.Properties

  opaque
    unfolding F-rel ηM PSq
    η-sq : PSq c (U-rel (F-rel c)) ηM ηM
    η-sq x y xRy = η-monotone xRy



-- TODO these next two don't really belong in this file since they apply to
-- any error domain.
module _
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
  (d : ErrorDomRel B B' ℓd)
  where

  private
    module B  = ErrorDomainStr (B .snd)
    module B' = ErrorDomainStr (B' .snd)
    module d = ErrorDomRel d

--  θB-sq : PSq ? ? ? ?
  

module _
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
  (d : ErrorDomRel B B' ℓd)
  where

  private
    module B  = ErrorDomainStr (B .snd)
    module B' = ErrorDomainStr (B' .snd)
    module d = ErrorDomRel d

  opaque
    unfolding PSq
    δB-sq : PSq (U-rel d) (U-rel d) B.δ B'.δ
    δB-sq x y xRy = d.Rθ (next x) (next y) (next xRy)
    -- This could be factored as the composition of a square
    -- for θ with a square for next
  


-- If two error domain morphisms out of the free error domain agree on
-- inputs of the form η x, then they are equal.
module _ {A : Predomain ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} where

  private module B = ErrorDomainStr (B .snd)
  open ExtAsEDMorphism

  open F-ob
  open PMor

  opaque
    unfolding F-ob LiftPredomain.𝕃 ηM
    F-extensionality : (ϕ ϕ' : ErrorDomMor (F-ob A) B) →
      (U-mor ϕ ∘p ηM ≡ U-mor ϕ' ∘p ηM) →
      ϕ ≡ ϕ'
    F-extensionality ϕ ϕ' eq = eqEDMor _ _ (funExt (fix aux))
      where
        module ϕ = ErrorDomMor ϕ
        module ϕ' = ErrorDomMor ϕ'
        
        aux : ▹ ((lx : L℧ ⟨ A ⟩) → ϕ.f .PMor.f lx ≡ ϕ'.f .PMor.f lx) →
                 (lx : L℧ ⟨ A ⟩) → ϕ.f .PMor.f lx ≡ ϕ'.f .PMor.f lx
        aux _ (η x) = funExt⁻ (cong PMor.f eq) x
        aux _ ℧ = ϕ.f℧ ∙ sym ϕ'.f℧
        aux IH (θ lx~) =
            (ϕ.fθ lx~)
          ∙ cong B.θ.f (later-ext (λ t → IH t (lx~ t)))
          ∙ (sym (ϕ'.fθ lx~))

    F-extensionality' : (ϕ ϕ' : ErrorDomMor (F-ob A) B) →
      (∀ x → ϕ .ErrorDomMor.fun (ηM .f x) ≡ ϕ' .ErrorDomMor.fun (ηM .f x)) →
      ϕ ≡ ϕ'
    F-extensionality' ϕ ϕ' eq = eqEDMor _ _ (funExt (fix aux))
      where
        module ϕ = ErrorDomMor ϕ
        module ϕ' = ErrorDomMor ϕ'
        
        aux : ▹ ((lx : L℧ ⟨ A ⟩) → ϕ.f .PMor.f lx ≡ ϕ'.f .PMor.f lx) →
                 (lx : L℧ ⟨ A ⟩) → ϕ.f .PMor.f lx ≡ ϕ'.f .PMor.f lx
        aux _ (η x) = eq x
        aux _ ℧ = ϕ.f℧ ∙ sym ϕ'.f℧
        aux IH (θ lx~) =
            ϕ.fθ lx~
          ∙ cong B.θ.f (later-ext (λ t → IH t (lx~ t)))
          ∙ sym (ϕ'.fθ lx~)

-- For every error domain ϕ morphism out of the free error domain,
-- there is a unique f such that ϕ = ext f.

module _ {A : Predomain ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} where

  private module B = ErrorDomainStr (B .snd)
  -- open CBPVExt ⟨ A ⟩ ⟨ B ⟩ B.℧ B.θ.f
  open ExtAsEDMorphism

  ext-unique :
    (ϕ : ErrorDomMor (F-ob.F-ob A) B) →
    ∃![ f ∈ PMor A (U-ob B) ] ϕ ≡ Ext f
  ext-unique ϕ .fst .fst = U-mor ϕ ∘p ηM
  ext-unique ϕ .fst .snd = F-extensionality' ϕ _ λ x → sym (Ext-ηM (U-mor ϕ ∘p ηM) x)
  ext-unique ϕ .snd (g , eq) =
    ΣPathPProp (λ g → EDMorIsSet ϕ (Ext g))
               ((cong₂ _∘p_ (cong U-mor eq) refl) ∙ (eqPMor _ _ (funExt λ x → Ext-ηM g x)))

        -- know : ϕ ≡ ext g
        -- NTS: Uϕ ∘ η ≡ g



open F-ob

-- Constructing an error domain square between morphisms out of the free error domain
module _
  {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
  (c : PRel A A' ℓc) (d : ErrorDomRel B B' ℓd)
  (ϕ : ErrorDomMor (F-ob A) B) (ϕ' : ErrorDomMor (F-ob A') B')
  where
  open F-rel
  open ExtAsEDMorphism

  F-rel-free :
    PSq c (U-rel d) (U-mor ϕ ∘p ηM) (U-mor ϕ' ∘p ηM) →
    ErrorDomSq (F-rel c) d ϕ ϕ'
  F-rel-free α = subst2 (λ ψ ψ' → ErrorDomSq (F-rel c) d ψ ψ') (sym eq1) (sym eq2) ext-sq
    where
      f : PMor A (U-ob B)
      f = ext-unique ϕ .fst .fst

      f' : PMor A' (U-ob B')
      f' = ext-unique ϕ' .fst .fst

      _ : f ≡ (U-mor ϕ ∘p ηM)
      _ = refl

      eq1 : ϕ ≡ Ext f
      eq1 = (ext-unique ϕ .fst .snd)

      eq2 : ϕ' ≡ Ext f'
      eq2 = (ext-unique ϕ' .fst. snd)

      ext-sq : ErrorDomSq (F-rel c) d (Ext f) (Ext f')
      ext-sq = Ext-sq c d f f' α



module _
  {A₁ : Predomain ℓA₁  ℓ≤A₁  ℓ≈A₁}
  {A₂ : Predomain ℓA₂  ℓ≤A₂  ℓ≈A₂}
  {A₃ : Predomain ℓA₃  ℓ≤A₃  ℓ≈A₃}
  (c : PRel A₁ A₂ ℓc) (c' : PRel A₂ A₃ ℓc') where

  open F-ob
  open F-rel
  open HetTransitivity ⟨ A₁ ⟩ ⟨ A₂ ⟩ ⟨ A₃ ⟩ (c .PRel.R) (c' .PRel.R)

  -- open HorizontalComp
  open HorizontalCompUMP (F-rel c) (F-rel c') IdE IdE IdE (F-rel (c ⊙ c'))

  opaque
    unfolding F-ob F-rel PSq ηM PSq

    func-test : ErrorDomSq (F-rel (c ⊙ c')) (F-rel c ⊙ed F-rel c') IdE IdE
    func-test = F-rel-free (c ⊙ c') (F-rel c ⊙ed F-rel c') IdE IdE
      (⊙-elim c c' (U-mor IdE ∘p ηM) (U-mor IdE ∘p ηM) (U-rel (F-rel c ⊙ed F-rel c'))
        λ {x z (y , xRy , yRz) →
          HCRel.inj _ (ηM .PMor.f y) _ (η-sq c x y xRy) (η-sq c' y z yRz)})
