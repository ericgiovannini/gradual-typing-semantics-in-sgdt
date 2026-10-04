{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

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
    ℓΓ' ℓ≤Γ' ℓ≈Γ' : Level
    ℓcΓ : Level
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

-- Squares for the cartesian combinators. These are the same as the
-- corresponding lemmas in SquareCombinators, restated for the
-- (transparent) notion of square used here.
private
  Sq-SwapPair :
    {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁'}
    {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : Predomain ℓA₂' ℓ≤A₂' ℓ≈A₂'}
    {c₁ : PRel A₁ A₁' ℓc₁} {c₂ : PRel A₂ A₂' ℓc₂} →
    PSq (c₁ ×pbmonrel c₂) (c₂ ×pbmonrel c₁)
        (SwapPair {A = A₁} {B = A₂}) (SwapPair {A = A₁'} {B = A₂'})
  Sq-SwapPair (x₁ , x₂) (y₁ , y₂) (p , q) = q , p

  Sq-Curry :
    {Γ  : Predomain ℓΓ  ℓ≤Γ  ℓ≈Γ}  {Γ'  : Predomain ℓΓ'  ℓ≤Γ'  ℓ≈Γ'}
    {Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aᵢ' : Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
    {Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} {Aₒ' : Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'}
    {cΓ : PRel Γ Γ' ℓcΓ} {cᵢ : PRel Aᵢ Aᵢ' ℓcᵢ} {cₒ : PRel Aₒ Aₒ' ℓcₒ}
    {f : PMor (Γ ×dp Aᵢ) Aₒ} {g : PMor (Γ' ×dp Aᵢ') Aₒ'} →
    PSq (cΓ ×pbmonrel cᵢ) cₒ f g →
    PSq cΓ (cᵢ ==>pbmonrel cₒ) (Curry {Γ = Γ} {A = Aᵢ} f) (Curry {Γ = Γ'} {A = Aᵢ'} g)
  Sq-Curry α γ γ' γ≤γ' x y x≤y = α (γ , x) (γ' , y) (γ≤γ' , x≤y)

  Sq-Uncurry :
    {Γ  : Predomain ℓΓ  ℓ≤Γ  ℓ≈Γ}  {Γ'  : Predomain ℓΓ'  ℓ≤Γ'  ℓ≈Γ'}
    {Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aᵢ' : Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
    {Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} {Aₒ' : Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'}
    {cΓ : PRel Γ Γ' ℓcΓ} {cᵢ : PRel Aᵢ Aᵢ' ℓcᵢ} {cₒ : PRel Aₒ Aₒ' ℓcₒ}
    {f : PMor Γ (Aᵢ ==> Aₒ)} {g : PMor Γ' (Aᵢ' ==> Aₒ')} →
    PSq cΓ (cᵢ ==>pbmonrel cₒ) f g →
    PSq (cΓ ×pbmonrel cᵢ) cₒ (Uncurry f) (Uncurry g)
  Sq-Uncurry α (γ , x) (γ' , y) (γ≤γ' , x≤y) = α γ γ' γ≤γ' x y x≤y


-- The strong extension StrongExt is not itself a morphism of error
-- domains (see the comment in MonadCombinators), but its fibre at a
-- fixed parameter γ is: it is the extension of (g γ) : A → UB to an
-- error domain morphism FA ⊸ B.
module _
  {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {A : Predomain ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B}
  (g : ⟨ U-ob (Γ ⟶ob (A ⟶ob B)) ⟩) (γ : ⟨ Γ ⟩) where

  private
    module B   = ErrorDomainStr (B .snd)
    module SE  = StrongCBPVExt ⟨ Γ ⟩ ⟨ A ⟩ ⟨ B ⟩ B.℧ B.θ.f (λ γ' → g .f γ' .f)
    module SEq = SE.Equations γ

  StrongExt-ED : ErrorDomMor (F-ob A) B
  StrongExt-ED .ErrorDomMor.f  = StrongExt {Γ = Γ} {A = A} {B = B} .f g .f γ
  StrongExt-ED .ErrorDomMor.f℧ = SEq.ext-℧
  StrongExt-ED .ErrorDomMor.fθ = SEq.ext-θ

  StrongExt-ED-η : (x : ⟨ A ⟩) → StrongExt-ED .ErrorDomMor.fun (η x) ≡ g .f γ .f x
  StrongExt-ED-η = SEq.ext-η

  StrongExt-ED-δ : (lx : ⟨ U-ob (F-ob A) ⟩) →
    StrongExt-ED .ErrorDomMor.fun (δ lx) ≡ B.θ.f (next (StrongExt-ED .ErrorDomMor.fun lx))
  StrongExt-ED-δ = SEq.ext-δ


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

  _×Kᴸ_ = KlProdMorphismᴸ


-- Identity
KlProdMorphismᴸ-Id :
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁}
  (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) →
  (IdE {B = F-ob A₁}) ×Kᴸ A₂ ≡ IdE
KlProdMorphismᴸ-Id {A₁ = A₁} A₂ = F-extensionality _ _
  (ExtAsEDMorphism.Equations.Ext-η _
   ∙ eqPMor _ _ (funExt (λ { (x , y) →
       StrongExt-ED-η {Γ = A₂} {A = A₁} {B = F-ob (A₁ ×dp A₂)}
         (Curry (η-mor ∘p SwapPair)) y x })))

-- Composition
KlProdMorphismᴸ-Comp :
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁'}
  {A₁'' : Predomain ℓA₁'' ℓ≤A₁'' ℓ≈A₁''} →
  (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) (ϕ : KlMorV A₁ A₁') (ϕ' : KlMorV A₁' A₁'') →
  ((ϕ' ∘ed ϕ) ×Kᴸ A₂) ≡ (ϕ' ×Kᴸ A₂) ∘ed (ϕ ×Kᴸ A₂)
KlProdMorphismᴸ-Comp {A₁ = A₁} {A₁' = A₁'} {A₁'' = A₁''} A₂ ϕ ϕ' =
  F-extensionality _ _
    (ExtAsEDMorphism.Equations.Ext-η _
     ∙ eqPMor _ _ (funExt (λ { (x , y) → goal x y })))
  where
    module ϕ = ErrorDomMor ϕ

    -- The strong extension at parameter y, for A₁' and for A₁''.
    S'  : ⟨ A₂ ⟩ → ErrorDomMor (F-ob A₁')  (F-ob (A₁'  ×dp A₂))
    S'  = StrongExt-ED {Γ = A₂} {A = A₁'}  {B = F-ob (A₁'  ×dp A₂)} (Curry (η-mor ∘p SwapPair))

    S'' : ⟨ A₂ ⟩ → ErrorDomMor (F-ob A₁'') (F-ob (A₁'' ×dp A₂))
    S'' = StrongExt-ED {Γ = A₂} {A = A₁''} {B = F-ob (A₁'' ×dp A₂)} (Curry (η-mor ∘p SwapPair))

    -- (ϕ' ×Kᴸ A₂) ∘ S' y ≡ S'' y ∘ ϕ' as morphisms F A₁' ⊸ F (A₁'' × A₂).
    -- Both are error domain morphisms out of a free error domain, so
    -- it suffices to check them on η x'.
    lem : (y : ⟨ A₂ ⟩) → (ϕ' ×Kᴸ A₂) ∘ed S' y ≡ S'' y ∘ed ϕ'
    lem y = F-extensionality _ _ (eqPMor _ _ (funExt (λ x' →
        cong ((ϕ' ×Kᴸ A₂) .ErrorDomMor.fun)
             (StrongExt-ED-η {Γ = A₂} {A = A₁'} {B = F-ob (A₁' ×dp A₂)}
               (Curry (η-mor ∘p SwapPair)) y x')
      ∙ ExtAsEDMorphism.Equations-U.ext-η
             (KlProdᴸ-pt2 ϕ' A₂ ∘p KlProdᴸ-pt1 ϕ' A₂) (x' , y))))

    goal : (x : ⟨ A₁ ⟩) (y : ⟨ A₂ ⟩) →
        (KlProdᴸ-pt2 (ϕ' ∘ed ϕ) A₂ ∘p KlProdᴸ-pt1 (ϕ' ∘ed ϕ) A₂) .f (x , y)
      ≡ (U-mor ((ϕ' ×Kᴸ A₂) ∘ed (ϕ ×Kᴸ A₂)) ∘p η-mor) .f (x , y)
    goal x y = sym
      ( cong ((ϕ' ×Kᴸ A₂) .ErrorDomMor.fun)
             (ExtAsEDMorphism.Equations-U.ext-η
               (KlProdᴸ-pt2 ϕ A₂ ∘p KlProdᴸ-pt1 ϕ A₂) (x , y))
      ∙ funExt⁻ (cong ErrorDomMor.fun (lem y)) (ϕ.fun (η x)) )


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

  -- The square is built in two stages, matching the definition
  -- Ext (pt2 ∘p pt1): first the square for pt1 (the given square α
  -- under η, in the first component, and the identity square in the
  -- second), then the square for pt2 (the strong extension preserves
  -- squares, after swapping/currying).
  KlProdMorphismᴸ-Sq :
    ErrorDomSq (F-rel (cᵢ₁ ×pbmonrel c₂)) (F-rel (cₒ₁ ×pbmonrel c₂)) (ϕ ×Kᴸ A₂) (ϕ' ×Kᴸ A₂')
  KlProdMorphismᴸ-Sq =
    Ext-sq (cᵢ₁ ×pbmonrel c₂) (F-rel (cₒ₁ ×pbmonrel c₂))
      (KlProdᴸ-pt2 ϕ  A₂  ∘p KlProdᴸ-pt1 ϕ  A₂)
      (KlProdᴸ-pt2 ϕ' A₂' ∘p KlProdᴸ-pt1 ϕ' A₂')
      (CompSqV
        {c₁ = cᵢ₁ ×pbmonrel c₂}
        {c₂ = U-rel (F-rel cₒ₁) ×pbmonrel c₂}
        {c₃ = U-rel (F-rel (cₒ₁ ×pbmonrel c₂))}
        ( _×-Sq_
            {f₁ = U-mor ϕ ∘p η-mor} {g₁ = U-mor ϕ' ∘p η-mor} {f₂ = Id} {g₂ = Id}
            (CompSqV {c₁ = cᵢ₁} {c₂ = U-rel (F-rel cᵢ₁)} {c₃ = U-rel (F-rel cₒ₁)}
               {f₁ = η-mor} {g₁ = η-mor} {f₂ = U-mor ϕ} {g₂ = U-mor ϕ'}
               (η-sq cᵢ₁) (U-sq (F-rel cᵢ₁) (F-rel cₒ₁) ϕ ϕ' α))
            (Predom-IdSqV c₂) )
        (CompSqV
          {c₁ = U-rel (F-rel cₒ₁) ×pbmonrel c₂}
          {c₂ = c₂ ×pbmonrel U-rel (F-rel cₒ₁)}
          {c₃ = U-rel (F-rel (cₒ₁ ×pbmonrel c₂))}
          {f₁ = SwapPair {A = U-ob (F-ob Aₒ₁)}  {B = A₂}}
          {g₁ = SwapPair {A = U-ob (F-ob Aₒ₁')} {B = A₂'}}
          {f₂ = Uncurry (StrongExt {Γ = A₂}  {A = Aₒ₁}  {B = F-ob (Aₒ₁  ×dp A₂)}  .f (Curry (η-mor ∘p SwapPair)))}
          {g₂ = Uncurry (StrongExt {Γ = A₂'} {A = Aₒ₁'} {B = F-ob (Aₒ₁' ×dp A₂')} .f (Curry (η-mor ∘p SwapPair)))}
          Sq-SwapPair
          (Sq-Uncurry
            {cΓ = c₂} {cᵢ = U-rel (F-rel cₒ₁)} {cₒ = U-rel (F-rel (cₒ₁ ×pbmonrel c₂))}
            {f = StrongExt {Γ = A₂}  {A = Aₒ₁}  {B = F-ob (Aₒ₁  ×dp A₂)}  .f (Curry (η-mor ∘p SwapPair))}
            {g = StrongExt {Γ = A₂'} {A = Aₒ₁'} {B = F-ob (Aₒ₁' ×dp A₂')} .f (Curry (η-mor ∘p SwapPair))}
            (StrongExt-Sq c₂ cₒ₁ (F-rel (cₒ₁ ×pbmonrel c₂))
              (Curry (η-mor ∘p SwapPair)) (Curry (η-mor ∘p SwapPair))
              (Sq-Curry
                {cΓ = c₂} {cᵢ = cₒ₁} {cₒ = U-rel (F-rel (cₒ₁ ×pbmonrel c₂))}
                {f = η-mor ∘p SwapPair} {g = η-mor ∘p SwapPair}
                (CompSqV {c₁ = c₂ ×pbmonrel cₒ₁} {c₂ = cₒ₁ ×pbmonrel c₂}
                         {c₃ = U-rel (F-rel (cₒ₁ ×pbmonrel c₂))}
                  Sq-SwapPair (η-sq (cₒ₁ ×pbmonrel c₂))))))))



----------------------------------------------------------------------

module _
  {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : Predomain ℓA₂' ℓ≤A₂' ℓ≈A₂'}
  (A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁) (ϕ : KlMorV A₂ A₂') where

  KlProdᴿ-pt1 : PMor (A₁ ×dp A₂) (A₁ ×dp (U-ob (F-ob A₂')))
  KlProdᴿ-pt1 = Id ×mor (U-mor ϕ ∘p η-mor)

  KlProdᴿ-pt2 : PMor (A₁ ×dp (U-ob (F-ob A₂'))) (U-ob (F-ob (A₁ ×dp A₂')))
  KlProdᴿ-pt2 = Uncurry (StrongExt .f (Curry η-mor))

  KlProdMorphismᴿ : KlMorV (A₁ ×kob A₂) (A₁ ×kob A₂')
  KlProdMorphismᴿ = Ext (KlProdᴿ-pt2 ∘p KlProdᴿ-pt1)

_×Kᴿ_ = KlProdMorphismᴿ


-- Identity
KlProdMorphismᴿ-Id :
  {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂}
  (A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁) →
  A₁ ×Kᴿ (IdE {B = F-ob A₂}) ≡ IdE
KlProdMorphismᴿ-Id {A₂ = A₂} A₁ = F-extensionality _ _
  (ExtAsEDMorphism.Equations.Ext-η _
   ∙ eqPMor _ _ (funExt (λ { (x , y) →
       StrongExt-ED-η {Γ = A₁} {A = A₂} {B = F-ob (A₁ ×dp A₂)}
         (Curry η-mor) x y })))

-- Composition
KlProdMorphismᴿ-Comp :
    {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : Predomain ℓA₂' ℓ≤A₂' ℓ≈A₂'}
    {A₂'' : Predomain ℓA₂'' ℓ≤A₂'' ℓ≈A₂''} →
    (A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁) (ϕ : KlMorV A₂ A₂') (ϕ' : KlMorV A₂' A₂'') →
    (A₁ ×Kᴿ (ϕ' ∘ed ϕ)) ≡ (A₁ ×Kᴿ ϕ') ∘ed (A₁ ×Kᴿ ϕ)
KlProdMorphismᴿ-Comp {A₂ = A₂} {A₂' = A₂'} {A₂'' = A₂''} A₁ ϕ ϕ' =
  F-extensionality _ _
    (ExtAsEDMorphism.Equations.Ext-η _
     ∙ eqPMor _ _ (funExt (λ { (x , y) → goal x y })))
  where
    module ϕ = ErrorDomMor ϕ

    -- The strong extension at parameter x, for A₂' and for A₂''.
    T'  : ⟨ A₁ ⟩ → ErrorDomMor (F-ob A₂')  (F-ob (A₁ ×dp A₂'))
    T'  = StrongExt-ED {Γ = A₁} {A = A₂'}  {B = F-ob (A₁ ×dp A₂')}  (Curry η-mor)

    T'' : ⟨ A₁ ⟩ → ErrorDomMor (F-ob A₂'') (F-ob (A₁ ×dp A₂''))
    T'' = StrongExt-ED {Γ = A₁} {A = A₂''} {B = F-ob (A₁ ×dp A₂'')} (Curry η-mor)

    lem : (x : ⟨ A₁ ⟩) → (A₁ ×Kᴿ ϕ') ∘ed T' x ≡ T'' x ∘ed ϕ'
    lem x = F-extensionality _ _ (eqPMor _ _ (funExt (λ y' →
        cong ((A₁ ×Kᴿ ϕ') .ErrorDomMor.fun)
             (StrongExt-ED-η {Γ = A₁} {A = A₂'} {B = F-ob (A₁ ×dp A₂')}
               (Curry η-mor) x y')
      ∙ ExtAsEDMorphism.Equations-U.ext-η
             (KlProdᴿ-pt2 A₁ ϕ' ∘p KlProdᴿ-pt1 A₁ ϕ') (x , y'))))

    goal : (x : ⟨ A₁ ⟩) (y : ⟨ A₂ ⟩) →
        (KlProdᴿ-pt2 A₁ (ϕ' ∘ed ϕ) ∘p KlProdᴿ-pt1 A₁ (ϕ' ∘ed ϕ)) .f (x , y)
      ≡ (U-mor ((A₁ ×Kᴿ ϕ') ∘ed (A₁ ×Kᴿ ϕ)) ∘p η-mor) .f (x , y)
    goal x y = sym
      ( cong ((A₁ ×Kᴿ ϕ') .ErrorDomMor.fun)
             (ExtAsEDMorphism.Equations-U.ext-η
               (KlProdᴿ-pt2 A₁ ϕ ∘p KlProdᴿ-pt1 A₁ ϕ) (x , y))
      ∙ funExt⁻ (cong ErrorDomMor.fun (lem x)) (ϕ.fun (η y)) )


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
  KlProdMorphismᴿ-Sq α =
    Ext-sq (c₁ ×pbmonrel cᵢ₂) (F-rel (c₁ ×pbmonrel cₒ₂))
      (KlProdᴿ-pt2 A₁  ϕ  ∘p KlProdᴿ-pt1 A₁  ϕ)
      (KlProdᴿ-pt2 A₁' ϕ' ∘p KlProdᴿ-pt1 A₁' ϕ')
      (CompSqV
        {c₁ = c₁ ×pbmonrel cᵢ₂}
        {c₂ = c₁ ×pbmonrel U-rel (F-rel cₒ₂)}
        {c₃ = U-rel (F-rel (c₁ ×pbmonrel cₒ₂))}
        ( _×-Sq_
            {f₁ = Id} {g₁ = Id} {f₂ = U-mor ϕ ∘p η-mor} {g₂ = U-mor ϕ' ∘p η-mor}
            (Predom-IdSqV c₁)
            (CompSqV {c₁ = cᵢ₂} {c₂ = U-rel (F-rel cᵢ₂)} {c₃ = U-rel (F-rel cₒ₂)}
               {f₁ = η-mor} {g₁ = η-mor} {f₂ = U-mor ϕ} {g₂ = U-mor ϕ'}
               (η-sq cᵢ₂) (U-sq (F-rel cᵢ₂) (F-rel cₒ₂) ϕ ϕ' α)) )
        (Sq-Uncurry
          {cΓ = c₁} {cᵢ = U-rel (F-rel cₒ₂)} {cₒ = U-rel (F-rel (c₁ ×pbmonrel cₒ₂))}
          {f = StrongExt {Γ = A₁}  {A = Aₒ₂}  {B = F-ob (A₁  ×dp Aₒ₂)}  .f (Curry η-mor)}
          {g = StrongExt {Γ = A₁'} {A = Aₒ₂'} {B = F-ob (A₁' ×dp Aₒ₂')} .f (Curry η-mor)}
          (StrongExt-Sq c₁ cₒ₂ (F-rel (c₁ ×pbmonrel cₒ₂))
            (Curry η-mor) (Curry η-mor)
            (Sq-Curry
              {cΓ = c₁} {cᵢ = cₒ₂} {cₒ = U-rel (F-rel (c₁ ×pbmonrel cₒ₂))}
              {f = η-mor} {g = η-mor}
              (η-sq (c₁ ×pbmonrel cₒ₂))))))


------------------------------------------------------------------
-- Further properties of the Kleisli product actions
------------------------------------------------------------------

-- These are used to show that the syntactic Kleisli product actions
-- on perturbations (Perturbation.Kleisli) agree with the semantic
-- ones (Perturbation.Semantic):
--
--   * the actions commute with the delay morphism δ*,
--   * the actions turn F-mor f into F-mor (f ×mor Id) resp. F-mor (Id ×mor f),
--   * the actions preserve bisimilarity with the identity.

module _ (A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁) (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) where

  private
    gᴸ = Curry {Γ = A₂} {A = A₁} (η-mor {A = A₁ ×dp A₂} ∘p SwapPair)
    gᴿ = Curry {Γ = A₁} {A = A₂} (η-mor {A = A₁ ×dp A₂})

    Sᴸ : ⟨ A₂ ⟩ → ErrorDomMor (F-ob A₁) (F-ob (A₁ ×dp A₂))
    Sᴸ = StrongExt-ED {Γ = A₂} {A = A₁} {B = F-ob (A₁ ×dp A₂)} gᴸ

    Sᴿ : ⟨ A₁ ⟩ → ErrorDomMor (F-ob A₂) (F-ob (A₁ ×dp A₂))
    Sᴿ = StrongExt-ED {Γ = A₁} {A = A₂} {B = F-ob (A₁ ×dp A₂)} gᴿ

  -- Commuting with δ*
  KlProdᴸ-δ* : (δ* {A = A₁}) ×Kᴸ A₂ ≡ δ* {A = A₁ ×dp A₂}
  KlProdᴸ-δ* = F-extensionality _ _
    (ExtAsEDMorphism.Equations.Ext-η _
     ∙ eqPMor _ _ (funExt (λ { (x , y) →
         cong (Sᴸ y .ErrorDomMor.fun) (ExtAsEDMorphism.Equations-U.ext-η (δ-mor ∘p η-mor) x)
       ∙ StrongExt-ED-δ gᴸ y (η x)
       ∙ cong δ (StrongExt-ED-η gᴸ y x)
       ∙ sym (ExtAsEDMorphism.Equations-U.ext-η (δ-mor ∘p η-mor) (x , y)) })))

  KlProdᴿ-δ* : A₁ ×Kᴿ (δ* {A = A₂}) ≡ δ* {A = A₁ ×dp A₂}
  KlProdᴿ-δ* = F-extensionality _ _
    (ExtAsEDMorphism.Equations.Ext-η _
     ∙ eqPMor _ _ (funExt (λ { (x , y) →
         cong (Sᴿ x .ErrorDomMor.fun) (ExtAsEDMorphism.Equations-U.ext-η (δ-mor ∘p η-mor) y)
       ∙ StrongExt-ED-δ gᴿ x (η y)
       ∙ cong δ (StrongExt-ED-η gᴿ x y)
       ∙ sym (ExtAsEDMorphism.Equations-U.ext-η (δ-mor ∘p η-mor) (x , y)) })))

  -- Preservation of bisimilarity with the identity
  KlProdMorphismᴸ-≈id : (ϕ : KlMorV A₁ A₁) → (U-mor ϕ) ≈mon Id → U-mor (ϕ ×Kᴸ A₂) ≈mon Id
  KlProdMorphismᴸ-≈id ϕ ϕ≈id =
    transport (λ i → U-mor (ϕ ×Kᴸ A₂) ≈mon (lem2 i)) lem1
    where
      module LP = PredomainStr ((U-ob (F-ob (A₁ ×dp A₂))) .snd)

      -- pt2 ∘ pt1 is bisimilar to η
      pt≈η : _≈mon_ {X = A₁ ×dp A₂} {Y = U-ob (F-ob (A₁ ×dp A₂))}
               (KlProdᴸ-pt2 ϕ A₂ ∘p KlProdᴸ-pt1 ϕ A₂) η-mor
      pt≈η (x , y) (x' , y') (x≈x' , y≈y') =
        subst (λ z → (KlProdᴸ-pt2 ϕ A₂ ∘p KlProdᴸ-pt1 ϕ A₂) .PMor.f (x , y) LP.≈ z)
              (StrongExt-ED-η gᴸ y' x')
              (StrongExt {Γ = A₂} {A = A₁} {B = F-ob (A₁ ×dp A₂)} .f gᴸ .pres≈ y≈y'
                (ϕ .ErrorDomMor.fun (η x)) (η x')
                (ϕ≈id (η x) (η x') (η-mor .pres≈ x≈x')))

      lem1 : U-mor (ϕ ×Kᴸ A₂) ≈mon U-mor (Ext η-mor)
      lem1 = ExtCombinator.Ext .pres≈ {x = KlProdᴸ-pt2 ϕ A₂ ∘p KlProdᴸ-pt1 ϕ A₂} {y = η-mor} pt≈η

      lem2 : U-mor (Ext (η-mor {A = A₁ ×dp A₂})) ≡ Id
      lem2 = cong U-mor Ext-unit-right

  KlProdMorphismᴿ-≈id : (ϕ : KlMorV A₂ A₂) → (U-mor ϕ) ≈mon Id → U-mor (A₁ ×Kᴿ ϕ) ≈mon Id
  KlProdMorphismᴿ-≈id ϕ ϕ≈id =
    transport (λ i → U-mor (A₁ ×Kᴿ ϕ) ≈mon (lem2 i)) lem1
    where
      module LP = PredomainStr ((U-ob (F-ob (A₁ ×dp A₂))) .snd)

      pt≈η : _≈mon_ {X = A₁ ×dp A₂} {Y = U-ob (F-ob (A₁ ×dp A₂))}
               (KlProdᴿ-pt2 A₁ ϕ ∘p KlProdᴿ-pt1 A₁ ϕ) η-mor
      pt≈η (x , y) (x' , y') (x≈x' , y≈y') =
        subst (λ z → (KlProdᴿ-pt2 A₁ ϕ ∘p KlProdᴿ-pt1 A₁ ϕ) .PMor.f (x , y) LP.≈ z)
              (StrongExt-ED-η gᴿ x' y')
              (StrongExt {Γ = A₁} {A = A₂} {B = F-ob (A₁ ×dp A₂)} .f gᴿ .pres≈ x≈x'
                (ϕ .ErrorDomMor.fun (η y)) (η y')
                (ϕ≈id (η y) (η y') (η-mor .pres≈ y≈y')))

      lem1 : U-mor (A₁ ×Kᴿ ϕ) ≈mon U-mor (Ext η-mor)
      lem1 = ExtCombinator.Ext .pres≈ {x = KlProdᴿ-pt2 A₁ ϕ ∘p KlProdᴿ-pt1 A₁ ϕ} {y = η-mor} pt≈η

      lem2 : U-mor (Ext (η-mor {A = A₁ ×dp A₂})) ≡ Id
      lem2 = cong U-mor Ext-unit-right


-- Interaction with the action of F on morphisms
module _ {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁'}
         (f : PMor A₁ A₁') (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) where

  private
    gᴸ = Curry {Γ = A₂} {A = A₁'} (η-mor {A = A₁' ×dp A₂} ∘p SwapPair)
    Sᴸ : ⟨ A₂ ⟩ → ErrorDomMor (F-ob A₁') (F-ob (A₁' ×dp A₂))
    Sᴸ = StrongExt-ED {Γ = A₂} {A = A₁'} {B = F-ob (A₁' ×dp A₂)} gᴸ

  KlProdᴸ-F : (F-mor f) ×Kᴸ A₂ ≡ F-mor (f ×mor Id)
  KlProdᴸ-F = F-extensionality _ _
    (ExtAsEDMorphism.Equations.Ext-η _
     ∙ eqPMor _ _ (funExt (λ { (x , y) →
         cong (Sᴸ y .ErrorDomMor.fun) (map-η (f .PMor.f) x)
       ∙ StrongExt-ED-η gᴸ y (f .PMor.f x)
       ∙ sym (map-η ((f ×mor Id) .PMor.f) (x , y)) })))

module _ (A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁)
         {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : Predomain ℓA₂' ℓ≤A₂' ℓ≈A₂'}
         (f : PMor A₂ A₂') where

  private
    gᴿ = Curry {Γ = A₁} {A = A₂'} (η-mor {A = A₁ ×dp A₂'})
    Sᴿ : ⟨ A₁ ⟩ → ErrorDomMor (F-ob A₂') (F-ob (A₁ ×dp A₂'))
    Sᴿ = StrongExt-ED {Γ = A₁} {A = A₂'} {B = F-ob (A₁ ×dp A₂')} gᴿ

  KlProdᴿ-F : A₁ ×Kᴿ (F-mor f) ≡ F-mor (Id ×mor f)
  KlProdᴿ-F = F-extensionality _ _
    (ExtAsEDMorphism.Equations.Ext-η _
     ∙ eqPMor _ _ (funExt (λ { (x , y) →
         cong (Sᴿ x .ErrorDomMor.fun) (map-η (f .PMor.f) y)
       ∙ StrongExt-ED-η gᴿ x (f .PMor.f y)
       ∙ sym (map-η ((Id ×mor f) .PMor.f) (x , y)) })))
