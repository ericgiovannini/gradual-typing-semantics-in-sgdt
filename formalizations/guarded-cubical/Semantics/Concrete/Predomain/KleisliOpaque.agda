{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

open import Common.Later

module Semantics.Concrete.Predomain.KleisliOpaque (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure


open import Common.Common
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions hiding (𝔽)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Combinators
open import Semantics.Concrete.Predomain.SquareOpaque
open import Semantics.Concrete.Predomain.SquareCombinators

open import Semantics.Concrete.Predomain.SimpleErrorDomain k
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.ErrorDomain.Square k
open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k

open import Semantics.Concrete.Predomain.Error

open import Semantics.Concrete.Predomain.Ext k
open import Semantics.Concrete.Predomain.MonadRelationalResultsOpaque k
open import Semantics.Concrete.Predomain.FreeErrorDomainOpaque k
open import Semantics.Concrete.Predomain.MonadCombinatorsOpaque k

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
    ℓA₁'' ℓ≤A₁'' ℓ≈A₁'' : Level
    ℓA₂'' ℓ≤A₂'' ℓ≈A₂'' : Level

    ℓB₁ ℓ≤B₁ ℓ≈B₁ : Level
    ℓB₂ ℓ≤B₂ ℓ≈B₂ : Level
    ℓB₃ ℓ≤B₃ ℓ≈B₃ : Level

    ℓAᵢ₁  ℓ≤Aᵢ₁  ℓ≈Aᵢ₁ : Level
    ℓAᵢ₁' ℓ≤Aᵢ₁' ℓ≈Aᵢ₁' : Level
    ℓAₒ₁  ℓ≤Aₒ₁  ℓ≈Aₒ₁ : Level
    ℓAₒ₁' ℓ≤Aₒ₁' ℓ≈Aₒ₁' : Level
    ℓAᵢ₂  ℓ≤Aᵢ₂  ℓ≈Aᵢ₂ : Level
    ℓAₒ₂  ℓ≤Aₒ₂  ℓ≈Aₒ₂ : Level
    ℓcᵢ₁ ℓcₒ₁ ℓc₂ ℓcᵢ₂ ℓcₒ₂ ℓc₁ : Level
    
    ℓAᵢ₂' ℓ≤Aᵢ₂' ℓ≈Aᵢ₂' : Level
    ℓAₒ₂' ℓ≤Aₒ₂' ℓ≈Aₒ₂' : Level
   

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

open F-ob
open F-mor
open LiftPredomain
open PMor


-----------------------------------------------
-- The Kleisli value and computation morphisms
-----------------------------------------------

-- The Kleisli value morphisms from Aᵢ to Aₒ are defined to be error
-- domain morphisms from FAᵢ to FAₒ.
KlMorV : (Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ) (Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ) →
  Type (ℓ-max (ℓ-max (ℓ-max ℓAᵢ ℓ≤Aᵢ) ℓ≈Aᵢ) ((ℓ-max (ℓ-max ℓAₒ ℓ≤Aₒ) ℓ≈Aₒ)))
KlMorV Aᵢ Aₒ = ErrorDomMor (F-ob Aᵢ) (F-ob Aₒ)

-- The Kleisli computation morphisms from Bᵢ to Bₒ are defined to be
-- predomain morphisms from UBᵢ to UBₒ
KlMorC : (Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ) (Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ) →
  Type (ℓ-max (ℓ-max (ℓ-max ℓBᵢ ℓ≤Bᵢ) ℓ≈Bᵢ) ((ℓ-max (ℓ-max ℓBₒ ℓ≤Bₒ) ℓ≈Bₒ)))
KlMorC Bᵢ Bₒ = PMor (U-ob Bᵢ) (U-ob Bₒ)


-- Kleisli identity morphisms

Id-KV : (A : Predomain ℓA ℓ≤A ℓ≈A) → KlMorV A A
Id-KV A = IdE

Id-KC : (B : ErrorDomain ℓB ℓ≤B ℓ≈B) → KlMorC B B
Id-KC B = Id




-----------------------
-- Kleisli arrow
-----------------------

_⟶kob_ : (A : Predomain ℓA ℓ≤A ℓ≈A) (B : ErrorDomain ℓB ℓ≤B ℓ≈B) →
    ErrorDomain
        (ℓ-max (ℓ-max (ℓ-max ℓA ℓ≤A) ℓ≈A) (ℓ-max (ℓ-max ℓB ℓ≤B) ℓ≈B))
        (ℓ-max ℓA ℓ≤B)
        (ℓ-max (ℓ-max ℓA ℓ≈A) ℓ≈B)
A ⟶kob B = A ⟶ob B


-- We are given a Kleisli value morphism ϕ from Aₒ to Aᵢ,
-- i.e. an error domain morphism from FAₒ to FAᵢ.
--
-- The result is a Kleisli computation morphism from
-- Aᵢ ⟶kob B to Aₒ ⟶kob B, i.e. a predomain morphism from
-- U(Aᵢ ⟶ob B) to U(Aₒ ⟶ob B).
KlArrowMorphismᴸ :
    {Aᵢ : Predomain  ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aₒ : Predomain  ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} →
    (ϕ : KlMorV Aₒ Aᵢ) (B : ErrorDomain ℓB ℓ≤B ℓ≈B) →
    KlMorC (Aᵢ ⟶kob B) (Aₒ ⟶kob B)
KlArrowMorphismᴸ {Aᵢ = Aᵢ} {Aₒ = Aₒ} ϕ B =
  Curry (ext' ∘p' With2nd (U-mor ϕ) ∘p' With2nd ηM)
  where
    open ExtAsEDMorphism

    ext' : ∀ {A : Predomain ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
      ⟨ U-ob (A ⟶kob B) ×dp U-ob (F-ob A) ==> U-ob B ⟩
    ext' = Uncurry ExtCombinator.Ext

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
  (A : Predomain ℓA ℓ≤A ℓ≈A) → (f : KlMorC Bᵢ Bₒ) →
  KlMorC (A ⟶kob Bᵢ) (A ⟶kob Bₒ)

-- We need to return a predomain morphism from U(A ⟶ Bᵢ) to U(A ⟶ Bₒ).
-- 
-- So let g : U(A ⟶ob Bᵢ), i.e. g : A ==> UBᵢ. Then we have
--
--       g          f         
--   A -----> UBᵢ -----> UBₒ
KlArrowMorphismᴿ A f = Curry (f ∘p App)


_⟶Kᴿ_ = KlArrowMorphismᴿ


-- Separate functoriality
--------------------------

-- open Map
-- open MapProperties

open Equations


KlArrowMorphismᴸ-id :
  {A : Predomain ℓA ℓ≤A ℓ≈A} (B : ErrorDomain ℓB ℓ≤B ℓ≈B) →
  (Id-KV A) ⟶Kᴸ B ≡ Id
KlArrowMorphismᴸ-id {A = A} B = PMorExt _ _ (λ g → PMorExt _ _ λ x  → {!!})
  -- eqPMor _ _ (funExt (λ g → eqPMor _ _ (funExt (λ x → 
  --   _ ≡⟨ ext-η (g .f) x ⟩ g .f x ∎ ))))
  where
    module B = ErrorDomainStr (B .snd)
    -- open CBPVExt.Equations _ _ _ _ -- ⟨ A ⟩ ⟨ B ⟩ B.℧ B.θ.f


KlArrowMorphismᴿ-id :
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} (A : Predomain ℓA ℓ≤A ℓ≈A) →
  A ⟶Kᴿ (Id-KC B) ≡ Id
KlArrowMorphismᴿ-id B = eqPMor _ _ (funExt (λ x → eqPMor _ _ refl))


open StrongExtCombinator
open ExtAsEDMorphism
open ExtCombinator renaming (Ext to ExtCombinator)

opaque
  unfolding StrongExt Ext ExtCombinator ext
  KlArrowMorphismᴸ-comp :
    {A₁ : Predomain  ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : Predomain  ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₃ : Predomain ℓA₃ ℓ≤A₃ ℓ≈A₃} →
    (ϕ : KlMorV A₃ A₂) (ϕ' : KlMorV A₂ A₁) (B : ErrorDomain ℓB ℓ≤B ℓ≈B) →
    (ϕ' ∘ed ϕ) ⟶Kᴸ B ≡ (ϕ ⟶Kᴸ B) ∘p (ϕ' ⟶Kᴸ B)
  KlArrowMorphismᴸ-comp {A₁ = A₁} {A₂ = A₂} {A₃ = A₃} ϕ ϕ' B =
    PMorExt _ _ λ h → PMorExt _ _ λ x → funExt⁻ (cong ErrorDomMor.fun (sym (lemma1 h))) (ϕ.fun (ηM .f x))
    where
     
      module ϕ = ErrorDomMor ϕ
      module B = ErrorDomainStr (B .snd)

      -- lem1 : ∀ (h : PMor A₁ (U-ob B))
      --   → ((ExtCombinator .f h .f) ∘ (ϕ' .ErrorDomMor.fun)) ≡ (ExtCombinator .f ((ϕ' ⟶Kᴸ B) .f h) .f)
      -- lem1 h = {!F-extensionality'!}

      lemma1 : ∀ h → Ext ((ϕ' ⟶Kᴸ B) $ h) ≡ (Ext h) ∘ed ϕ'
      lemma1 h = F-extensionality' _ _ λ x → Ext-ηM ((ϕ' ⟶Kᴸ B) $ h) x

  -- NTS: ext h (ϕ' (ϕ (η x))) ≡ ext (λ a → ext h (ϕ' (η a))) (ϕ (η x))
  -- STS: ext h ∘ ϕ' ≡ ext (ext h ∘ ϕ' ∘ η)



KlArrowMorphismᴿ-comp :
  {B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁}
  {B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂}
  {B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃} →
  (A : Predomain ℓA ℓ≤A ℓ≈A) →
  (f : KlMorC B₁ B₂) (g : KlMorC B₂ B₃) →
  A ⟶Kᴿ (g ∘p f) ≡ (A ⟶Kᴿ g) ∘p (A ⟶Kᴿ f)
KlArrowMorphismᴿ-comp A f g =
  eqPMor _ _ (funExt (λ h → eqPMor _ _ (funExt (λ x → refl))))



-- Action on squares
--------------------

open F-rel

module _
  {Aᵢ  : Predomain  ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ}
  {Aₒ  : Predomain  ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ}
  {Aᵢ' : Predomain  ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
  {Aₒ' : Predomain  ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'}
  {B   : ErrorDomain ℓB  ℓ≤B  ℓ≈B}
  {B'  : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
  {cᵢ  : PRel Aᵢ Aᵢ' ℓcᵢ}
  {cₒ  : PRel Aₒ Aₒ' ℓcₒ}
  (ϕ   : KlMorV Aₒ  Aᵢ)
  (ϕ'  : KlMorV Aₒ' Aᵢ')
  {d   : ErrorDomRel B B' ℓd}
  (α   : ErrorDomSq (F-rel cₒ) (F-rel cᵢ) ϕ ϕ')
  -- (β   : ErrorDomSq {!!} {!!} {!!} {!!})
  where
  
  open PRel
  open ErrorDomRel hiding (module B ; module B')
  
  private
    module B = ErrorDomainStr (B .snd)
    module B' = ErrorDomainStr (B' .snd)
    module cₒ = PRel cₒ
    module d = ErrorDomRel d
    module LiftRel = LiftOrd ⟨ Aₒ ⟩ ⟨ Aₒ' ⟩ (cₒ.R)


  opaque
    unfolding PSq
    KlArrowMorphismᴸ-sq : PSq (U-rel (cᵢ ⟶rel d)) (U-rel (cₒ ⟶rel d)) (ϕ ⟶Kᴸ B) (ϕ' ⟶Kᴸ B')
    KlArrowMorphismᴸ-sq f g f≤g aₒ aₒ' aₒRaₒ' = {!!}
  
    -- Ext-sq cᵢ d f g f≤g (U-mor ϕ $ η aₒ) (U-mor ϕ' $ η aₒ')
    --   (α (η aₒ) (η aₒ') (LiftRel.Properties.η-monotone aₒRaₒ'))


module _
  {A  : Predomain  ℓA  ℓ≤A  ℓ≈A}
  {A'  : Predomain  ℓA'  ℓ≤A'  ℓ≈A'}
  {Bᵢ  : ErrorDomain  ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ}
  {Bₒ  : ErrorDomain  ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ}
  {Bᵢ' : ErrorDomain  ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ'}
  {Bₒ' : ErrorDomain  ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ'}
  (c : PRel A A' ℓc)
  {dᵢ  : ErrorDomRel Bᵢ Bᵢ' ℓdᵢ}
  {dₒ  : ErrorDomRel Bₒ Bₒ' ℓdₒ}
  {f   : KlMorC Bᵢ  Bₒ}
  {g   : KlMorC Bᵢ' Bₒ'}
  (α   : PSq (U-rel dᵢ) (U-rel dₒ) f g)
  -- (β   : PSq c c Id Id)
  where

  opaque
    unfolding PSq
    KlArrowMorphismᴿ-sq : PSq (U-rel (c ⟶rel dᵢ)) (U-rel (c ⟶rel dₒ)) (A ⟶Kᴿ f) (A' ⟶Kᴿ g)
    KlArrowMorphismᴿ-sq h₁ h₂ h₁≤h₂ a a' caa' =
      α (h₁ .PMor.f a) (h₂ .PMor.f a') (h₁≤h₂ a a' caa')


-------------------------------
-- Kleisli actions on product
-------------------------------

open ExtAsEDMorphism
open StrongExtCombinator

_×kob_ : (A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁) (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) →
  Predomain (ℓ-max ℓA₁ ℓA₂) (ℓ-max ℓ≤A₁ ℓ≤A₂) (ℓ-max ℓ≈A₁ ℓ≈A₂)
A₁ ×kob A₂ = A₁ ×dp A₂



module _
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁'}
  (ϕ : KlMorV A₁ A₁') (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) where

  KlProdᴸ-pt1 : PMor (A₁ ×dp A₂) ((U-ob (F-ob A₁')) ×dp A₂)
  KlProdᴸ-pt1 = (U-mor ϕ ∘p ηM) ×mor Id

  KlProdᴸ-pt2 : PMor ((U-ob (F-ob A₁')) ×dp A₂) (U-ob (F-ob (A₁' ×dp A₂)))
  KlProdᴸ-pt2 = (Uncurry (StrongExt .f (Curry (ηM ∘p SwapPair)))) ∘p SwapPair
  -- Uncurry {!StrongExt₁ .f ?!} ∘p SwapPair 

  KlProdMorphismᴸ :
    KlMorV (A₁ ×kob A₂) (A₁' ×kob A₂)
  KlProdMorphismᴸ = Ext (KlProdᴸ-pt2 ∘p KlProdᴸ-pt1)
     
  _×Kᴸ_ = KlProdMorphismᴸ


-- Identity
opaque
  unfolding Ext StrongExt η𝔽 ηM
  KlProdMorphismᴸ-Id :
    {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁}
    (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) →
    (IdE {B = F-ob A₁}) ×Kᴸ A₂ ≡ IdE
  KlProdMorphismᴸ-Id A₂ = F-extensionality' _ _
    (λ{ (x , y) → ext-η _ (x , y) ∙ st-ext-η _ y x})
    
    -- The below line works but has a bunch of unsolved implicits
    -- (λ{ (x , y) → Ext-ηM _ (x , y) ∙ StrongExt-η _ y x}) 

-- Composition

  KlProdMorphismᴸ-Comp :
    {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁'}
    {A₁'' : Predomain ℓA₁'' ℓ≤A₁'' ℓ≈A₁''} →
    (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) (ϕ : KlMorV A₁ A₁') (ϕ' : KlMorV A₁' A₁'') →
    ((ϕ' ∘ed ϕ) ×Kᴸ A₂) ≡ (ϕ' ×Kᴸ A₂) ∘ed (ϕ ×Kᴸ A₂)
  KlProdMorphismᴸ-Comp {A₁ = A₁} {A₁' = A₁'} {A₁'' = A₁''} A₂ ϕ ϕ' =
    F-extensionality' _ _ λ{ (x , y) → ext-η _ (x , y) ∙ goal x y}
    where
      opaque
        unfolding StrongExt₁
        
        lem'' : (y : ⟨ A₂ ⟩) →
          --Ext (U-mor (StrongExt₁ .f (Curry (ηM ∘p SwapPair)) .f {!!}) ∘p (U-mor ϕ' ∘p (η-mor ∘p π1)))
          Ext (KlProdᴸ-pt2 ϕ' A₂ ∘p ((U-mor ϕ' ∘p ηM) ×mor Id))
            ∘ed (StrongExt₁ .f (Curry (ηM ∘p SwapPair)) .f y)
          ≡ (StrongExt₁ .f (Curry (ηM ∘p SwapPair)) .f y) ∘ed ϕ'
        lem'' y = F-extensionality' _ _ λ x' → cong (ext _) (st-ext-η {!!} y x') ∙ ext-η _ (x' , y)
      
        lem' : ∀ (y : ⟨ A₂ ⟩) →
          (ext {B = 𝔽 ⟨ A₁'' ×dp A₂ ⟩}
            (λ x₁ → st-ext {B = 𝔽 ⟨ A₁'' ×dp A₂ ⟩}
                      (λ γ' a → η (a , γ'))
                      (x₁ .snd)
                      (ϕ' .ErrorDomMor.fun (η (x₁ .fst)))))
           ∘ (st-ext (λ γ' a → η (a , γ')) y) 
          ≡ ((st-ext (λ γ' a → η (a , γ')) y) ∘ (ErrorDomMor.fun ϕ'))
        lem' y = cong ErrorDomMor.fun (lem'' y)
     
      
      goal : ∀ x y →
          (KlProdᴸ-pt2 (ϕ' ∘ed ϕ) A₂ ∘p KlProdᴸ-pt1 (ϕ' ∘ed ϕ) A₂) .f (x , y)
        ≡ ErrorDomMor.f  ((ϕ' ×Kᴸ A₂) ∘ed (ϕ ×Kᴸ A₂)) .f (ηM .f (x , y))
      goal x y = sym (cong₂ ext refl (ext-η _ (x , y)) ∙ (funExt⁻ (lem' y) (ϕ .ErrorDomMor.fun (η x))))



-- Action on squares
module _
  {Aᵢ₁  : Predomain  ℓAᵢ₁  ℓ≤Aᵢ₁  ℓ≈Aᵢ₁}
  {Aᵢ₁' : Predomain  ℓAᵢ₁' ℓ≤Aᵢ₁' ℓ≈Aᵢ₁'}
  {Aₒ₁  : Predomain  ℓAₒ₁  ℓ≤Aₒ₁  ℓ≈Aₒ₁}
  {Aₒ₁' : Predomain  ℓAₒ₁' ℓ≤Aₒ₁' ℓ≈Aₒ₁'}
  {A₂   : Predomain  ℓA₂   ℓ≤A₂   ℓ≈A₂}
  {A₂'  : Predomain  ℓA₂'  ℓ≤A₂'  ℓ≈A₂'}
  (cᵢ₁ : PRel Aᵢ₁ Aᵢ₁' ℓcᵢ₁)
  (cₒ₁ : PRel Aₒ₁ Aₒ₁' ℓcₒ₁)
  (c₂ :  PRel A₂ A₂' ℓc₂) 
  (ϕ  : KlMorV Aᵢ₁  Aₒ₁)
  (ϕ' : KlMorV Aᵢ₁' Aₒ₁')
  (α : ErrorDomSq (F-rel cᵢ₁) (F-rel cₒ₁) ϕ ϕ')
  where
  open F-rel
  open ExtAsEDMorphism

  KlProdMorphismᴸ-Sq :    
    ErrorDomSq (F-rel (cᵢ₁ ×pbmonrel c₂)) (F-rel (cₒ₁ ×pbmonrel c₂)) (ϕ ×Kᴸ A₂) (ϕ' ×Kᴸ A₂')
  KlProdMorphismᴸ-Sq = Ext-sq _ _ _ _
    (CompSqV
      ((CompSqV (η-sq cᵢ₁) (U-sq _ _ _ _ α)) ×-Sq Predom-IdSqV _)
      (CompSqV
        Sq-SwapPair
        (Sq-Uncurry (Sq-StrongExt _ _ (F-rel _) _ _ (Sq-Curry (CompSqV Sq-SwapPair (η-sq _)))))))

{-
  KlProdᴸ-pt1 : PMor (A₁ ×dp A₂) ((U-ob (F-ob A₁')) ×dp A₂)
  KlProdᴸ-pt1 = (U-mor ϕ ∘p ηM) ×mor Id

  KlProdᴸ-pt2 : PMor ((U-ob (F-ob A₁')) ×dp A₂) (U-ob (F-ob (A₁' ×dp A₂)))
  KlProdᴸ-pt2 = (Uncurry (StrongExt' .f (Curry (ηM ∘p SwapPair)))) ∘p SwapPair

  KlProdMorphismᴸ :
    KlMorV (A₁ ×kob A₂) (A₁' ×kob A₂)
  KlProdMorphismᴸ = Ext (KlProdᴸ-pt2 ∘p KlProdᴸ-pt1)
-}  


----------------------------------------------------------------------


KlProdMorphismᴿ :
    {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : Predomain ℓA₂' ℓ≤A₂' ℓ≈A₂'}
    (A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁) (ϕ : KlMorV A₂ A₂') →
    KlMorV (A₁ ×kob A₂) (A₁ ×kob A₂')
KlProdMorphismᴿ {A₂ = A₂} {A₂' = A₂'} A₁ ϕ = Ext (pt2 ∘p pt1)
  where
    pt1 : PMor (A₁ ×dp A₂) (A₁ ×dp (U-ob (F-ob A₂')))
    pt1 = Id ×mor (U-mor ϕ ∘p ηM)

    pt2 : PMor (A₁ ×dp (U-ob (F-ob A₂'))) (U-ob (F-ob (A₁ ×dp A₂')))
    pt2 = Uncurry (StrongExt .f (Curry ηM))

_×Kᴿ_ = KlProdMorphismᴿ


-- Identity
KlProdMorphismᴿ-Id :
  {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂}
  (A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁) →
  A₁ ×Kᴿ (IdE {B = F-ob A₂}) ≡ IdE
KlProdMorphismᴿ-Id = {!!}

-- Composition
KlProdMorphismᴿ-Comp :
    {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : Predomain ℓA₂' ℓ≤A₂' ℓ≈A₂'}
    {A₂'' : Predomain ℓA₂'' ℓ≤A₂'' ℓ≈A₂''} →
    (A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁) (ϕ : KlMorV A₂ A₂') (ϕ' : KlMorV A₂' A₂'') →
    (A₁ ×Kᴿ (ϕ' ∘ed ϕ)) ≡ (A₁ ×Kᴿ ϕ') ∘ed (A₁ ×Kᴿ ϕ)
KlProdMorphismᴿ-Comp = {!!}


-- Action on squares
module _
  {A₁   : Predomain  ℓA₁   ℓ≤A₁   ℓ≈A₁}
  {A₁'  : Predomain  ℓA₁'  ℓ≤A₁'  ℓ≈A₁'}
  {Aᵢ₂  : Predomain  ℓAᵢ₂  ℓ≤Aᵢ₂  ℓ≈Aᵢ₂}
  {Aᵢ₂' : Predomain  ℓAᵢ₂' ℓ≤Aᵢ₂' ℓ≈Aᵢ₂'}
  {Aₒ₂  : Predomain  ℓAₒ₂  ℓ≤Aₒ₂  ℓ≈Aₒ₂}
  {Aₒ₂' : Predomain  ℓAₒ₂' ℓ≤Aₒ₂' ℓ≈Aₒ₂'}
  (cᵢ₂ : PRel Aᵢ₂ Aᵢ₂' ℓcᵢ₂)
  (cₒ₂ : PRel Aₒ₂ Aₒ₂' ℓcₒ₂)
  (c₁ :  PRel A₁ A₁' ℓc₁) 
  (ϕ  : KlMorV Aᵢ₂  Aₒ₂)
  (ϕ' : KlMorV Aᵢ₂' Aₒ₂')

  where
  open F-rel

  KlProdMorphismᴿ-Sq :
    (α : ErrorDomSq (F-rel cᵢ₂) (F-rel cₒ₂) ϕ ϕ') →
    ErrorDomSq (F-rel (c₁ ×pbmonrel cᵢ₂)) (F-rel (c₁ ×pbmonrel cₒ₂)) (A₁ ×Kᴿ ϕ) (A₁' ×Kᴿ ϕ')
  KlProdMorphismᴿ-Sq α = {!!}



-- More lemmas about Kleisli action of ×

module _
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁'}
  (ϕ : KlMorV A₁ A₁') (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) where

  opaque
    unfolding Ext StrongExt ηM η𝔽
    
    KlProd∘η : U-mor (ϕ ×Kᴸ A₂) ∘p ηM ≡ (KlProdᴸ-pt2 ϕ A₂ ∘p KlProdᴸ-pt1 ϕ A₂)
    KlProd∘η = PMorExt _ _ λ {(x , y) → ext-η _ (x , y)}


module _
  (A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁)
  (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂)
  where

  opaque
    unfolding Ext StrongExt ηM η𝔽 δM δ𝔽
    
    KlProdᴸ-δ* : (δ* {A = A₁}) ×Kᴸ A₂ ≡ (δ* {A = A₁ ×dp A₂})
    KlProdᴸ-δ* = F-extensionality' _ _ λ {(x , y) →
        ext-η _ (x , y)
      ∙ cong (st-ext (λ γ' a → η (a , γ')) y) (ext-η _ x)
      ∙ st-ext-δ _ y (ηM $ x)
      ∙ cong δ (st-ext-η _ y x)
      ∙ sym (ext-η _ (x , y))}

module _
  (A₁  : Predomain ℓA₁  ℓ≤A₁  ℓ≈A₁)
  (A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁')
  (A₂  : Predomain ℓA₂  ℓ≤A₂  ℓ≈A₂)
  (f : PMor A₁ A₁')
  where

  opaque
    unfolding Ext StrongExt F-mor ηM
    KlProdᴸ-F : (F-mor f) ×Kᴸ A₂ ≡ F-mor (f ×mor Id)
    KlProdᴸ-F = F-extensionality' _ _ λ {(x , y) →
        ext-η _ (x , y)
      ∙ cong (st-ext _ y) (ext-η _ x)
      ∙ st-ext-η _ y (f $ x)
      ∙ sym (ext-η _ (x , y))}
  

module _
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁'}
  (ϕ : KlMorV A₁ A₁')
  where

  private
    module ϕ = ErrorDomMor ϕ

  opaque
    unfolding Ext ηM η𝔽 PSq F-rel
    EDMor∘δ* : ϕ ∘ed δ* ≡ δ* ∘ed ϕ
    EDMor∘δ* = F-extensionality' _ _
      (λ x → cong ϕ.fun (ext-η _ x) ∙ (ϕ.fθ (next (ηM $ x))) ∙ {!!})

    EDMor∘δ*⊑ : ErrorDomSq (F-rel (idPRel A₁)) (F-rel (idPRel A₁')) (δ* ∘ed ϕ) (ϕ ∘ed δ*)
    EDMor∘δ*⊑ = F-rel-free (idPRel A₁) (F-rel (idPRel A₁')) (δ* ∘ed ϕ) (ϕ ∘ed δ*) {!!}
      where
        α : PSq (idPRel A₁) (U-rel (F-rel (idPRel A₁')))
                (U-mor (δ* ∘ed ϕ) ∘p ηM)
                (U-mor (ϕ ∘ed δ*) ∘p ηM)
        α x y xRy with ϕ.fun (η x)
        ... | η x₁ = {!!}
        ... | ℧ = {!!}
        ... | θ x₁ = {!!}



module _
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁'}
  (ϕ : KlMorV A₁ A₁') (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) where

  opaque
    unfolding Ext StrongExt ηM η𝔽 δM δ𝔽
    
    KlProd∘δ* : (ϕ ×Kᴸ A₂) ∘ed δ* ≡ δ* ∘ed (ϕ ×Kᴸ A₂)
    KlProd∘δ* = -- EDMor∘δ* (ϕ ×Kᴸ A₂)
     -- F-extensionality' _ _ λ{ (x , y) → {!(ϕ ×Kᴸ A₂) !}}

      F-extensionality' _ _ λ {(x , y) →
        cong ((ϕ ×Kᴸ A₂) .ErrorDomMor.fun) (ext-η _ (x , y))
      ∙ ext-δ _ (ηM $ (x , y))
      ∙ cong δ (ext-η _ (x , y))
      ∙ sym
          (cong (ext (λ x' → δ (η x'))) (ext-η _ (x , y))
          ∙ {!!})}

