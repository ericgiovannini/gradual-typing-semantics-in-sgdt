{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

open import Common.Later

module Semantics.Concrete.Predomain.Kleisli (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure


open import Common.Common
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Combinators
open import Semantics.Concrete.Predomain.Square

open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k

open import Semantics.Concrete.Predomain.Error
open import Semantics.Concrete.Predomain.Monad k
open import Semantics.Concrete.Predomain.MonadRelationalResults k
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Predomain.MonadCombinators k

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
  Curry (ext' ∘p' With2nd (U-mor ϕ) ∘p' With2nd η-mor)
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

open Map
open MapProperties


KlArrowMorphismᴸ-id :
  {A : Predomain ℓA ℓ≤A ℓ≈A} (B : ErrorDomain ℓB ℓ≤B ℓ≈B) →
  (Id-KV A) ⟶Kᴸ B ≡ Id
KlArrowMorphismᴸ-id {A = A} B = eqPMor _ _ (funExt (λ g → eqPMor _ _ (funExt (λ x → 
  _ ≡⟨ ext-η (g .f) x ⟩ g .f x ∎ ))))
  where
    module B = ErrorDomainStr (B .snd)
    open CBPVExt.Equations _ _ _ _ -- ⟨ A ⟩ ⟨ B ⟩ B.℧ B.θ.f


KlArrowMorphismᴿ-id :
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} (A : Predomain ℓA ℓ≤A ℓ≈A) →
  A ⟶Kᴿ (Id-KC B) ≡ Id
KlArrowMorphismᴿ-id B = eqPMor _ _ (funExt (λ x → eqPMor _ _ refl))

KlArrowMorphismᴸ-comp :
  {A₁ : Predomain  ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : Predomain  ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₃ : Predomain ℓA₃ ℓ≤A₃ ℓ≈A₃} →
  (ϕ : KlMorV A₃ A₂) (ϕ' : KlMorV A₂ A₁) (B : ErrorDomain ℓB ℓ≤B ℓ≈B) →
  (ϕ' ∘ed ϕ) ⟶Kᴸ B ≡ (ϕ ⟶Kᴸ B) ∘p (ϕ' ⟶Kᴸ B)
KlArrowMorphismᴸ-comp {A₁ = A₁} {A₂ = A₂} {A₃ = A₃} ϕ ϕ' B =
  eqPMor _ _ (funExt (λ h → (eq1 h) ∙ (eq2 h) ∙ (eq3 h)))
  where
    open MonadLaws.Ext-Assoc
    open CBPVExt
    open ExtAsEDMorphism
    module ϕ = ErrorDomMor ϕ
    module B = ErrorDomainStr (B .snd)

    lemma1 : ∀ h → Ext ((ϕ' ⟶Kᴸ B) $ h) ≡ (Ext h) ∘ed ϕ'
    lemma1 h = F-extensionality _ _
      ((Equations.Ext-η _) ∙
       (eqPMor _ _ (funExt λ x → refl)))

    eq1 : ∀ h →
      f ((ϕ' ∘ed ϕ) ⟶Kᴸ B) h ≡
      U-mor (Ext h ∘ed ϕ') ∘p (U-mor ϕ ∘p η-mor)
    eq1 h = eqPMor _ _ refl

    eq2 : ∀ (h : ⟨ U-ob (A₁ ⟶kob B) ⟩) →
      U-mor ((Ext h) ∘ed ϕ') ∘p (U-mor ϕ ∘p η-mor) ≡
      U-mor (Ext ((ϕ' ⟶Kᴸ B) $ h)) ∘p (U-mor ϕ ∘p η-mor)
    eq2 h = sym (cong₂ _∘p_ (cong U-mor (lemma1 h)) refl)

    eq3 : ∀ h →
      U-mor (Ext ((ϕ' ⟶Kᴸ B) $ h)) ∘p (U-mor ϕ ∘p η-mor) ≡
      f (KlArrowMorphismᴸ ϕ B ∘p KlArrowMorphismᴸ ϕ' B) h
    eq3 h = eqPMor _ _ refl


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


  KlArrowMorphismᴸ-sq : PSq (U-rel (cᵢ ⟶rel d)) (U-rel (cₒ ⟶rel d)) (ϕ ⟶Kᴸ B) (ϕ' ⟶Kᴸ B')
  KlArrowMorphismᴸ-sq f g f≤g aₒ aₒ' aₒRaₒ' =
    Ext-sq cᵢ d f g f≤g (U-mor ϕ $ η aₒ) (U-mor ϕ' $ η aₒ')
      (α (η aₒ) (η aₒ') (LiftRel.Properties.η-monotone aₒRaₒ'))
  

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

  KlArrowMorphismᴿ-sq : PSq (U-rel (c ⟶rel dᵢ)) (U-rel (c ⟶rel dₒ)) (A ⟶Kᴿ f) (A' ⟶Kᴿ g)
  KlArrowMorphismᴿ-sq h₁ h₂ h₁≤h₂ a a' caa' =
    α (h₁ .PMor.f a) (h₂ .PMor.f a') (h₁≤h₂ a a' caa')


{-
PRel.R (dₒ .UR)
  (PMor.f f (PMor.f h₁ a))
  (PMor.f g (PMor.f h₂ a'))
-}

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
  KlProdᴸ-pt1 = (U-mor ϕ ∘p η-mor) ×mor Id

  KlProdᴸ-pt2 : PMor ((U-ob (F-ob A₁')) ×dp A₂) (U-ob (F-ob (A₁' ×dp A₂)))
  KlProdᴸ-pt2 = (Uncurry (StrongExt .f (Curry (η-mor ∘p SwapPair)))) ∘p SwapPair

  KlProdMorphismᴸ :
    KlMorV (A₁ ×kob A₂) (A₁' ×kob A₂)
  KlProdMorphismᴸ = Ext (KlProdᴸ-pt2 ∘p KlProdᴸ-pt1)
     
    -- (U-mor (Ext (? ×mor ?))) ∘p (U-mor ϕ) ∘p η-mor

  _×Kᴸ_ = KlProdMorphismᴸ


-- Identity
KlProdMorphismᴸ-Id :
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁}
  (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) →
  (IdE {B = F-ob A₁}) ×Kᴸ A₂ ≡ IdE
KlProdMorphismᴸ-Id = {!!}

-- Composition
KlProdMorphismᴸ-Comp :
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁'}
  {A₁'' : Predomain ℓA₁'' ℓ≤A₁'' ℓ≈A₁''} →
  (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) (ϕ : KlMorV A₁ A₁') (ϕ' : KlMorV A₁' A₁'') →
  ((ϕ' ∘ed ϕ) ×Kᴸ A₂) ≡ (ϕ' ×Kᴸ A₂) ∘ed (ϕ ×Kᴸ A₂)
KlProdMorphismᴸ-Comp = {!!}


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
  KlProdMorphismᴸ-Sq x y H =
    let foo = Ext-sq (cᵢ₁ ×pbmonrel c₂) (F-rel (cₒ₁ ×pbmonrel c₂)) (U-mor (ϕ ×Kᴸ A₂) ∘p η-mor) (U-mor (ϕ' ×Kᴸ A₂') ∘p η-mor) γ x y H in
    let foo2 = F-rel-free (cᵢ₁ ×pbmonrel c₂) (F-rel (cₒ₁ ×pbmonrel c₂)) (ϕ ×Kᴸ A₂) (ϕ' ×Kᴸ A₂') {!!} x y H in {!!}
    where
      pt1 = KlProdᴸ-pt1 ϕ A₂
      pt2 = KlProdᴸ-pt2 ϕ A₂

      pt1' = KlProdᴸ-pt1 ϕ' A₂'
      pt2' = KlProdᴸ-pt2 ϕ' A₂'

      β : PSq (cᵢ₁ ×pbmonrel c₂) (U-rel (F-rel (cₒ₁ ×pbmonrel c₂))) (pt2 ∘p pt1) (pt2' ∘p pt1')
      β = CompSqV
            {c₁ = cᵢ₁ ×pbmonrel c₂} {c₂ = U-rel (F-rel cₒ₁) ×pbmonrel c₂} {c₃ = U-rel (F-rel (cₒ₁ ×pbmonrel c₂))}
            ({!!} ×-Sq (Predom-IdSqV c₂))
            {!!}
            -- (λ x y xRy → StrongExt-Sq cᵢ₁ {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!})

      γ : PSq (cᵢ₁ ×pbmonrel c₂) (U-rel (F-rel (cₒ₁ ×pbmonrel c₂)))
               (U-mor (ϕ ×Kᴸ A₂) ∘p η-mor) (U-mor (ϕ' ×Kᴸ A₂') ∘p η-mor)
      γ = subst2
        (λ p q → PSq (cᵢ₁ ×pbmonrel c₂) (U-rel (F-rel (cₒ₁ ×pbmonrel c₂))) p q)
        {!!} {!!}
        -- (Equations.Ext-η {!pt2 ∘p pt1!}) (Equations.Ext-η {!!})
        β

     

{-
      β = subst2
        (λ p q → PSq (cᵢ₁ ×pbmonrel c₂) (U-rel (F-rel (cₒ₁ ×pbmonrel c₂))) p q)
        (Equations.Ext-η _) (Equations.Ext-η _)
        (λ { (x , y) (x' , y') (xRx' , yRy') →
          Ext-sq (cᵢ₁ ×pbmonrel c₂) (F-rel (cₒ₁ ×pbmonrel c₂)) _ _ (λ p q pRq → Ext-sq (cᵢ₁ ×pbmonrel c₂) (F-rel (cₒ₁ ×pbmonrel c₂)) _ _ (λ v w vRw → Ext-sq (cₒ₁ ×pbmonrel c₂) {!F-rel (cₒ₁ ×pbmonrel c₂)!} {!!} {!!} {!!} {!!} {!!} {!!}) (η-mor $ p) (η-mor $ q) (η-sq _ p q pRq))
                 (η-mor $ (x , y)) (η-mor $ (x' , y'))
                 (η-sq (cᵢ₁ ×pbmonrel c₂) (x , y) (x' , y') (xRx' , yRy'))})
-}                 
  
-- F-rel-free {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} -- Ext-sq {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
  


----------------------------------------------------------------------

KlProdMorphismᴿ :
    {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : Predomain ℓA₂' ℓ≤A₂' ℓ≈A₂'}
    (A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁) (ϕ : KlMorV A₂ A₂') →
    KlMorV (A₁ ×kob A₂) (A₁ ×kob A₂')
KlProdMorphismᴿ {A₂ = A₂} {A₂' = A₂'} A₁ ϕ = Ext (pt2 ∘p pt1)
  where
    pt1 : PMor (A₁ ×dp A₂) (A₁ ×dp (U-ob (F-ob A₂')))
    pt1 = Id ×mor (U-mor ϕ ∘p η-mor)

    pt2 : PMor (A₁ ×dp (U-ob (F-ob A₂'))) (U-ob (F-ob (A₁ ×dp A₂')))
    pt2 = Uncurry (StrongExt .f (Curry η-mor))

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
