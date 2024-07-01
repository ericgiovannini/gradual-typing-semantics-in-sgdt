{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

open import Common.Later

module Semantics.Concrete.DoublePoset.KleisliFunctors (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure


open import Common.Common
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

open import Semantics.Concrete.DoublePoset.Error
open import Semantics.Concrete.DoublePoset.Monad k
open import Semantics.Concrete.DoublePoset.MonadRelationalResults k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.MonadCombinators k

open ClockedCombinators k

private
  variable
    ℓ ℓ' : Level
    ℓA  ℓ≤A  ℓ≈A  : Level
    ℓA' ℓ≤A' ℓ≈A' : Level
    ℓB  ℓ≤B  ℓ≈B  : Level
    ℓB' ℓ≤B' ℓ≈B' : Level
    ℓΓ ℓ≤Γ ℓ≈Γ : Level
    ℓC : Level
    ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  : Level
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' : Level
    ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  : Level
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' : Level
    ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ  : Level
    ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ' : Level
    ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ' : Level
    ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ  : Level
    ℓc ℓd ℓR ℓcᵢ ℓcₒ ℓdᵢ ℓdₒ : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ : Level
    ℓA₁' ℓ≤A₁' ℓ≈A₁' : Level
    ℓA₂ ℓ≤A₂ ℓ≈A₂ : Level
    ℓA₂' ℓ≤A₂' ℓ≈A₂' : Level
    ℓA₃ ℓ≤A₃ ℓ≈A₃ : Level

    ℓB₁ ℓ≤B₁ ℓ≈B₁ : Level
    ℓB₂ ℓ≤B₂ ℓ≈B₂ : Level
    ℓB₃ ℓ≤B₃ ℓ≈B₃ : Level
   

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

open F-ob
open F-mor
open LiftPredomain
open PBMor


-- Pair' :
--   {ℓAₒ₁ ℓ≤Aₒ₁ ℓ≈Aₒ₁ ℓAₒ₂ ℓ≤Aₒ₂ ℓ≈Aₒ₂ : Level}
--   {A : PosetBisim ℓA ℓ≤A ℓ≈A}
--   {Aₒ₁ : PosetBisim ℓAₒ₁ ℓ≤Aₒ₁ ℓ≈Aₒ₁}
--   {Aₒ₂ : PosetBisim ℓAₒ₂ ℓ≤Aₒ₂ ℓ≈Aₒ₂} →
--   PBMor A Aₒ₁ → PBMor A Aₒ₂ → PBMor A (Aₒ₁ ×dp Aₒ₂)
-- Pair' = {!PairFun!}

-- Times :
--   {ℓAᵢ₁ ℓ≤Aᵢ₁ ℓ≈Aᵢ₁ ℓAᵢ₂ ℓ≤Aᵢ₂ ℓ≈Aᵢ₂
--    ℓAₒ₁ ℓ≤Aₒ₁ ℓ≈Aₒ₁ ℓAₒ₂ ℓ≤Aₒ₂ ℓ≈Aₒ₂ : Level}
--   {Aᵢ₁ : PosetBisim ℓAᵢ₁ ℓ≤Aᵢ₁ ℓ≈Aᵢ₁}
--   {Aᵢ₂ : PosetBisim ℓAᵢ₂ ℓ≤Aᵢ₂ ℓ≈Aᵢ₂}
--   {Aₒ₁ : PosetBisim ℓAₒ₁ ℓ≤Aₒ₁ ℓ≈Aₒ₁}
--   {Aₒ₂ : PosetBisim ℓAₒ₂ ℓ≤Aₒ₂ ℓ≈Aₒ₂} →
--   PBMor Aᵢ₁ Aₒ₁ → PBMor Aᵢ₂ Aₒ₂ → PBMor (Aᵢ₁ ×dp Aᵢ₂) (Aₒ₁ ×dp Aₒ₂)
-- Times f g = Pair' (f ∘p π1) (g ∘p π2)

-- Comp' :
--     {Γ : PosetBisim ℓΓ ℓ≤Γ ℓ≈Γ}
--     {A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁}
--     {A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂}
--     {A₃ : PosetBisim ℓA₃ ℓ≤A₃ ℓ≈A₃} →
--     ⟨ (Γ ×dp A₂ ==> A₃) ⟩ -> ⟨ (Γ ×dp A₁ ==> A₂) ⟩ -> ⟨ (Γ ×dp A₁ ==> A₃) ⟩
-- Comp' {Γ = Γ} g f = g ∘p Pair' π1 f
-- record {
--   f = λ { (γ , a) → PBMor.f f (γ , (PBMor.f g (γ , a))) } ;
--   isMon = λ { {γ1 , a1} {γ2 , a2} (γ1≤γ2 , a1≤a2) →
--     isMon f (γ1≤γ2 , (isMon g (γ1≤γ2 , a1≤a2))) } ;
--   pres≈ = λ { {γ1 , a1} {γ2 , a2} (γ1≈γ2 , a1≈a2) →
--     pres≈ f (γ1≈γ2 , (pres≈ g (γ1≈γ2 , a1≈a2))) } }


-----------------------------------------------
-- The Kleisli value and computation morphisms
-----------------------------------------------

-- The Kleisli value morphisms from Aᵢ to Aₒ are defined to be error
-- domain morphisms from FAᵢ to FAₒ.
KlMorV : (Aᵢ : PosetBisim ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ) (Aₒ : PosetBisim ℓAₒ ℓ≤Aₒ ℓ≈Aₒ) →
  Type (ℓ-max (ℓ-max (ℓ-max ℓAᵢ ℓ≤Aᵢ) ℓ≈Aᵢ) ((ℓ-max (ℓ-max ℓAₒ ℓ≤Aₒ) ℓ≈Aₒ)))
KlMorV Aᵢ Aₒ = ErrorDomMor (F-ob Aᵢ) (F-ob Aₒ)

-- The Kleisli computation morphisms from Bᵢ to Bₒ are defined to be
-- predomain morphisms from UBᵢ to UBₒ
KlMorC : (Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ) (Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ) →
  Type (ℓ-max (ℓ-max (ℓ-max ℓBᵢ ℓ≤Bᵢ) ℓ≈Bᵢ) ((ℓ-max (ℓ-max ℓBₒ ℓ≤Bₒ) ℓ≈Bₒ)))
KlMorC Bᵢ Bₒ = PBMor (U-ob Bᵢ) (U-ob Bₒ)


-- Kleisli identity morphisms

Id-KV : (A : PosetBisim ℓA ℓ≤A ℓ≈A) → KlMorV A A
Id-KV A = IdE

Id-KC : (B : ErrorDomain ℓB ℓ≤B ℓ≈B) → KlMorC B B
Id-KC B = Id


--------------------
-- Kleisli Functors
--------------------



-- The Kleisli arrow functor
-----------------------------

_⟶kob_ : (A : PosetBisim ℓA ℓ≤A ℓ≈A) (B : ErrorDomain ℓB ℓ≤B ℓ≈B) →
    ErrorDomain
        (ℓ-max (ℓ-max (ℓ-max ℓA ℓ≤A) ℓ≈A) (ℓ-max (ℓ-max ℓB ℓ≤B) ℓ≈B))
        (ℓ-max ℓA ℓ≤B)
        (ℓ-max (ℓ-max ℓA ℓ≈A) ℓ≈B)
A ⟶kob B = A ⟶ob B



-- Some auxiliary definitions used below.

-- Map' : ∀ {Aᵢ : PosetBisim ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aₒ : PosetBisim ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} →
--   PBMor Aᵢ Aₒ → PBMor (𝕃 Aᵢ) (𝕃 Aₒ)
-- Map' = U-mor ∘ F-mor

Map' : ∀ {Aᵢ : PosetBisim ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aₒ : PosetBisim ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} →
  PBMor ((Aᵢ ==> Aₒ) ×dp 𝕃 Aᵢ) (𝕃 Aₒ)
Map' = Uncurry MapCombinator.Map
-- ((Γ ×dp Aᵢ) ==> Aₒ) → ((Γ ×dp 𝕃 Aᵢ) ==> 𝕃 Aₒ)

Uε : ∀ {B : ErrorDomain ℓB ℓ≤B ℓ≈B} → PBMor (𝕃 (U-ob B)) (U-ob B)
Uε {B = B} = U-mor (Ext Id)
  where
    open ExtAsEDMorphism {A = U-ob B} {B = B}

Uε-η : ∀ {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  ∀ b → Uε {B = B} .f (η b) ≡ b
Uε-η {ℓB = ℓB} {B = B} b = Equations.ext-η Id b
  where
    open ExtAsEDMorphism {A = U-ob B} {B = B}
    -- open CBPVExt {ℓA = ℓB} {ℓB = ℓB} ⟨ B ⟩ ⟨ B ⟩


-- We are given a Kleisli value morphism ϕ from Aₒ to Aᵢ,
-- i.e. an error domain morphism from FAₒ to FAᵢ.
--
-- The result is a Kleisli computation morphism from
-- Aᵢ ⟶kob B to Aₒ ⟶kob B, i.e. a predomain morphism from
-- U(Aᵢ ⟶ob B) to U(Aₒ ⟶ob B).
KlArrowMorphismᴸ :
    {Aᵢ : PosetBisim  ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aₒ : PosetBisim  ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} →
    (ϕ : KlMorV Aₒ Aᵢ) (B : ErrorDomain ℓB ℓ≤B ℓ≈B) →
    KlMorC (Aᵢ ⟶kob B) (Aₒ ⟶kob B)
KlArrowMorphismᴸ {Aᵢ = Aᵢ} {Aₒ = Aₒ} ϕ B =
  Curry (With2nd Uε ∘p' Map' ∘p' With2nd (U-mor ϕ) ∘p' With2nd (η-mor))
  

  -- Curry ({!!} --> UFUB --> UB
  --        ∘p' {!!} -- U (A ⟶kob B) ×dp UFAᵢ --> UFUB
  --        ∘p' With2nd (U-mor ϕ)
  --        ∘p' With2nd (η-mor Aₒ))
         
-- Curry ({!!} ∘p  U-mor (F-mor {!!}) ∘p (U-mor ϕ) ∘p With2nd (η-mor Aₒ))

-- We need to return a predomain morphism from U(Aᵢ ⟶ B) to U(Aₒ ⟶ B).
-- 
-- So let g : U(Aᵢ ⟶ob B), i.e. g : Aᵢ ==> UB. Then we have
--
--       η          Uϕ          UFg          Uε
--  Aₒ -----> UFAₒ -----> UFAᵢ -----> UFUB -----> UB

syntax KlArrowMorphismᴸ ϕ B = ϕ ⟶Kᴸ B


-----------------------------------------------------------------

-- We are given a Kleisli computation morphism f from Bᵢ to Bₒ, i.e. a
-- predomain morphism from UBᵢ to UBₒ
--
-- The result is a Kleisli value morphism from
-- A ⟶kob Bᵢ to A ⟶kob Bₒ, i.e. a predomain morphism from
-- U(A ⟶ob Bᵢ) to U(A ⟶ob Bₒ).

KlArrowMorphismᴿ :
  {Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ} {Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ} →
  (A : PosetBisim ℓA ℓ≤A ℓ≈A) → (f : KlMorC Bᵢ Bₒ) →
  KlMorC (A ⟶kob Bᵢ) (A ⟶kob Bₒ)
KlArrowMorphismᴿ A f = Curry (f ∘p App)

-- We need to return a predomain morphism from U(A ⟶ Bᵢ) to U(A ⟶ Bₒ).
-- 
-- So let g : U(A ⟶ob Bᵢ), i.e. g : A ==> UBᵢ. Then we have
--
--       g          f         
--   A -----> UBᵢ -----> UBₒ

_⟶Kᴿ_ = KlArrowMorphismᴿ

-----------------------------------------------------------------
-- Separate functoriality

open Map
open MapProperties


KlArrowMorphismᴸ-id :
  {A : PosetBisim ℓA ℓ≤A ℓ≈A} (B : ErrorDomain ℓB ℓ≤B ℓ≈B) →
  (Id-KV A) ⟶Kᴸ B ≡ Id
KlArrowMorphismᴸ-id {A = A} B = eqPBMor _ _ (funExt (λ g → eqPBMor _ _ (funExt
  (λ x →
    Uε .f (map (g .f) (η x))
     ≡⟨ (λ i → Uε {B = B} .f (map-η (g .f) x i)) ⟩
   Uε .f (η (g .f x))
     ≡⟨ Uε-η (g .f x) ⟩
   g .f x ∎))))

  -- ((λ x → Uε .f (map (g .f) (η x)))
  --   ≡⟨ {!!} ⟩
  -- (λ x → Uε .f (η (g .f x)))
  --   ≡⟨ {!!} ⟩
  -- g .f ∎  )))

  where open CBPVExt ⟨ A ⟩ ⟨ B ⟩


KlArrowMorphismᴿ-id :
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} (A : PosetBisim ℓA ℓ≤A ℓ≈A) →
  A ⟶Kᴿ (Id-KC B) ≡ Id
KlArrowMorphismᴿ-id B = eqPBMor _ _ (funExt (λ x → eqPBMor _ _ refl))

-- Not needed as of now...
KlArrowMorphismᴸ-comp :
  {A₁ : PosetBisim  ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : PosetBisim  ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₃ : PosetBisim ℓA₃ ℓ≤A₃ ℓ≈A₃} →
  (ϕ : KlMorV A₃ A₂) (ϕ' : KlMorV A₂ A₁) (B : ErrorDomain ℓB ℓ≤B ℓ≈B) →
  (ϕ' ∘ed ϕ) ⟶Kᴸ B ≡ (ϕ ⟶Kᴸ B) ∘p (ϕ' ⟶Kᴸ B)
KlArrowMorphismᴸ-comp ϕ ϕ' B =
  eqPBMor _ _ (funExt (λ h → eqPBMor _ _ (funExt (λ x → {!!}))))
-- KlArrowMorphismᴸ-comp = {!!}
  where
    open MonadLaws.Ext-Assoc
    open CBPVExt


-- LHS:
--       η           Uϕ         Uϕ'         UFg          Uε
--  A₃ -----> UFA₃ -----> UFA₂ -----> UFA₁ -----> UFUB -----> UB




KlArrowMorphismᴿ-comp :
  {B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁}
  {B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂}
  {B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃} →
  (A : PosetBisim ℓA ℓ≤A ℓ≈A) →
  (f : KlMorC B₁ B₂) (g : KlMorC B₂ B₃) →
  A ⟶Kᴿ (g ∘p f) ≡ (A ⟶Kᴿ g) ∘p (A ⟶Kᴿ f)
KlArrowMorphismᴿ-comp A f g =
  eqPBMor _ _ (funExt (λ h → eqPBMor _ _ (funExt (λ x → refl))))




-----------------------------------------------------------------
-- Action on squares

open F-rel

module KlArrowMorphismᴸ-sq
  {Aᵢ  : PosetBisim  ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ}
  {Aₒ  : PosetBisim  ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ}
  {Aᵢ' : PosetBisim  ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
  {Aₒ' : PosetBisim  ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'}
  {B   : ErrorDomain ℓB  ℓ≤B  ℓ≈B}
  {B'  : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
  {cᵢ  : PBRel Aᵢ Aᵢ' ℓcᵢ}
  {cₒ  : PBRel Aₒ Aₒ' ℓcₒ}
  (ϕ   : KlMorV Aₒ  Aᵢ)
  (ϕ'  : KlMorV Aₒ' Aᵢ')
  {d   : ErrorDomRel B B' ℓd}
  (α   : ErrorDomSq (F-rel cₒ) (F-rel cᵢ) ϕ ϕ')
  -- (β   : ErrorDomSq {!!} {!!} {!!} {!!})
  where
  
  open PBRel
  open ErrorDomRel hiding (module B ; module B')
  module B = ErrorDomainStr (B .snd)
  module B' = ErrorDomainStr (B' .snd)
  module cₒ = PBRel cₒ
  module d = ErrorDomRel d
  
  module ExtMon = ExtMonotone
    ⟨ B ⟩ ⟨ B' ⟩ (d.R)
    ⟨ B ⟩ (B.℧) (B.θ.f)
    ⟨ B' ⟩ B'.℧ B'.θ.f
    (d.R) (d.R℧) (d.Rθ)
  -- (A : Type ℓA) (A' : Type ℓA') (_RAA'_ : A → A' → Type ℓRAA')
  -- (B  : Type ℓB)  (℧B  : B)  (θB  : (▹ B) → B)
  -- (B' : Type ℓB') (℧B' : B') (θB' : (▹ B') → B')
  -- (_RBB'_ : B → B' → Type ℓRBB')
  -- (R℧B⊥ : ∀ x → ℧B RBB' x)
  -- (Rθ  : ∀ (x~ : ▹ B) (y~ : ▹ B') →
  --   ▸ (λ t → (x~ t) RBB' (y~ t)) → (θB x~) RBB' (θB' y~))

  module MapMon = MapMonotone
    ⟨ Aᵢ ⟩ ⟨ Aᵢ' ⟩ ⟨ B ⟩ ⟨ B' ⟩ (cᵢ .R) (d .R)
  module LiftRel = LiftOrd ⟨ Aₒ ⟩ ⟨ Aₒ' ⟩ (cₒ.R)

--   {ℓAᵢ ℓAᵢ' ℓAₒ ℓAₒ' ℓRᵢ ℓRₒ : Level}
--   (Aᵢ : Type ℓAᵢ) (Aᵢ' : Type ℓAᵢ')
--   (Aₒ : Type ℓAₒ) (Aₒ' : Type ℓAₒ')
--   (_Rᵢ_ : Aᵢ → Aᵢ' → Type ℓRᵢ)
--   (_Rₒ_ : Aₒ → Aₒ' → Type ℓRₒ)


-- KlArrowMorphismᴸ {Aᵢ = Aᵢ} {Aₒ = Aₒ} ϕ B =
--   Curry (With2nd Uε ∘p' Map' ∘p' With2nd (U-mor ϕ) ∘p' With2nd (η-mor))

-- NTS: U-rel (cₒ ⟶rel d) .PBRel.R (KlArrowMorphismᴸ ϕ B .PBMor.f f)
--      (KlArrowMorphismᴸ ϕ' B' .PBMor.f g)

  Sq : PBSq (U-rel (cᵢ ⟶rel d)) (U-rel (cₒ ⟶rel d)) (ϕ ⟶Kᴸ B) (ϕ' ⟶Kᴸ B')
  Sq f g f≤g aₒ aₒ' H =
    ExtMon.ext-mon
      id id (ED-IdSqV d) _ _
      (MapMon.map-monotone
        (f .PBMor.f) (g .PBMor.f)
        f≤g
        (ϕ .ErrorDomMor.f .PBMor.f (η aₒ))
        (ϕ' .ErrorDomMor.f .PBMor.f (η aₒ'))
        (α (η aₒ) (η aₒ') (LiftRel.Properties.η-monotone H)))
  

module KlArrowMorphismᴿ-sq
  {A  : PosetBisim  ℓA  ℓ≤A  ℓ≈A}
  {A'  : PosetBisim  ℓA'  ℓ≤A'  ℓ≈A'}
  {Bᵢ  : ErrorDomain  ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ}
  {Bₒ  : ErrorDomain  ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ}
  {Bᵢ' : ErrorDomain  ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ'}
  {Bₒ' : ErrorDomain  ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ'}
  (c : PBRel A A' ℓc)
  {dᵢ  : ErrorDomRel Bᵢ Bᵢ' ℓdᵢ}
  {dₒ  : ErrorDomRel Bₒ Bₒ' ℓdₒ}
  {f   : KlMorC Bᵢ  Bₒ}
  {g   : KlMorC Bᵢ' Bₒ'}
  (α   : PBSq (U-rel dᵢ) (U-rel dₒ) f g)
  -- (β   : PBSq c c Id Id)
  where

  Sq : PBSq (U-rel (c ⟶rel dᵢ)) (U-rel (c ⟶rel dₒ)) (A ⟶Kᴿ f) (A' ⟶Kᴿ g)
  Sq h₁ h₂ h₁≤h₂ a a' caa' =
    α (h₁ .PBMor.f a) (h₂ .PBMor.f a') (h₁≤h₂ a a' caa')


{-
PBRel.R (dₒ .UR)
  (PBMor.f f (PBMor.f h₁ a))
  (PBMor.f g (PBMor.f h₂ a'))
-}

-------------------------------
-- The Kleisli product functor
-------------------------------

open ExtAsEDMorphism
open StrongExtCombinator

_×kob_ : (A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁) (A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂) →
  PosetBisim (ℓ-max ℓA₁ ℓA₂) (ℓ-max ℓ≤A₁ ℓ≤A₂) (ℓ-max ℓ≈A₁ ℓ≈A₂)
A₁ ×kob A₂ = A₁ ×dp A₂


KlProdMorphismᴸ :
    {A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : PosetBisim ℓA₁' ℓ≤A₁' ℓ≈A₁'}
    (ϕ : KlMorV A₁ A₁') (A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂) →
    KlMorV (A₁ ×kob A₂) (A₁' ×kob A₂)
KlProdMorphismᴸ {A₁ = A₁} {A₁' = A₁'} ϕ A₂ = Ext (pt2 ∘p pt1)
  where
    pt1 : PBMor (A₁ ×dp A₂) ((U-ob (F-ob A₁')) ×dp A₂)
    pt1 = (U-mor ϕ ∘p η-mor) ×mor Id

    pt2 : PBMor ((U-ob (F-ob A₁')) ×dp A₂) (U-ob (F-ob (A₁' ×dp A₂)))
    pt2 = (Uncurry (StrongExt .f (Curry (η-mor ∘p SwapPair)))) ∘p SwapPair

  -- (U-mor (Ext (? ×mor ?))) ∘p (U-mor ϕ) ∘p η-mor

_×Kᴸ_ = KlArrowMorphismᴸ

test : {A₁ : Type ℓA₁} {A₁' : Type ℓA₁'} →
    (ϕ : (L℧ A₁ → L℧ A₁')) (A₂ : Type ℓA₂) →
    L℧ (A₁ × A₂) → L℧ (A₁' × A₂)
test ϕ A₂ lp =
  ext _ _ ℧ θ
    (λ { (x , y) →
      ext _ _ ℧ θ (λ x' → η (x' , y))
                  (ϕ (η x))})
    lp
  where open CBPVExt


KlProdMorphismᴿ :
    {A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : PosetBisim ℓA₂' ℓ≤A₂' ℓ≈A₂'}
    (A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁) (ϕ : KlMorV A₂ A₂') →
    KlMorV (A₁ ×kob A₂) (A₁ ×kob A₂')
KlProdMorphismᴿ {A₂ = A₂} {A₂' = A₂'} A₁ ϕ = Ext (pt2 ∘p pt1)
  where
    pt1 : PBMor (A₁ ×dp A₂) (A₁ ×dp (U-ob (F-ob A₂')))
    pt1 = Id ×mor (U-mor ϕ ∘p η-mor)

    pt2 : PBMor (A₁ ×dp (U-ob (F-ob A₂'))) (U-ob (F-ob (A₁ ×dp A₂')))
    pt2 = Uncurry (StrongExt .f (Curry η-mor))

_×Kᴿ_ = KlArrowMorphismᴿ


-- Separate functoriality
--
-- Not needed as of now.



-- Action on squares

