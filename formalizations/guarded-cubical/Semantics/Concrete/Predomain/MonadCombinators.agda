{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}


open import Common.Later

module Semantics.Concrete.Predomain.MonadCombinators (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Structure

open import Common.Common
-- open import Semantics.Concrete.GuardedLift k renaming (η to Lη ; θ to Lθ)
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.Constructions
open import Semantics.Concrete.Predomain.Combinators


open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k

open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Predomain.Error
open import Semantics.Concrete.Predomain.Monad k
open import Semantics.Concrete.Predomain.MonadRelationalResults k



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
    ℓΓ' ℓ≤Γ' ℓ≈Γ' : Level
    ℓC : Level
    ℓc ℓc' ℓd ℓR : Level
    ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  : Level
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' : Level
    ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  : Level
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' : Level
    ℓcᵢ ℓcₒ : Level
    ℓcΓ ℓcΓᵢ ℓcΓₒ : Level
    ℓΓᵢ ℓ≤Γᵢ ℓ≈Γᵢ : Level
    ℓΓᵢ' ℓ≤Γᵢ' ℓ≈Γᵢ' : Level
    ℓΓₒ ℓ≤Γₒ ℓ≈Γₒ : Level
    ℓΓₒ' ℓ≤Γₒ' ℓ≈Γₒ' : Level
    ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ : Level
    ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ' : Level    
    ℓBₒ ℓ≤Bₒ ℓ≈Bₒ : Level
    ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ' : Level
    
   

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


open PMor
open LiftPredomain
open F-ob
open ErrorDomMor



module StrongExtCombinator
  {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ}
  {A : Predomain ℓA ℓ≤A ℓ≈A}
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} where

  private
    module Γ = PredomainStr (Γ .snd)
    module A = PredomainStr (A .snd)
    module B = ErrorDomainStr (B .snd)
  open StrongCBPVExt ⟨ Γ ⟩ ⟨ A ⟩ ⟨ B ⟩ B.℧ B.θ.f
  module LA = LiftOrdHomogenous ⟨ A ⟩ A._≤_
  LA-refl = LA.Properties.⊑-refl A.is-refl
  
  open StrongExtMonotone
    ⟨ Γ ⟩ ⟨ Γ ⟩ Γ._≤_
    ⟨ A ⟩ ⟨ A ⟩ A._≤_
    ⟨ B ⟩ B.℧ B.θ.f
    ⟨ B ⟩ B.℧ B.θ.f
    B._≤_ B.℧⊥ (λ x~ y~ → B.θ .isMon)

  open StrongExtPresBisim
    ⟨ Γ ⟩ Γ._≈_
    ⟨ A ⟩ A._≈_
    ⟨ B ⟩ B.℧ B.θ.f
    B._≈_
    B.is-prop-valued-Bisim
    B.is-refl-Bisim
    B.is-sym
    (λ x~ y~ H~ → B.θ.pres≈ H~)
    B.δ≈id


  module ΓAB = ErrorDomainStr ((Γ ⟶ob (A ⟶ob B)) .snd)

  aux2 : ⟨ Γ ⟶ob (A ⟶ob B) ⟩ → ⟨ Γ ⟩ → ⟨ 𝕃 A ⟶ob B ⟩
  aux2 g γ .f = ext (λ γ' → g .f γ' .f) γ
  aux2 g γ .isMon =
    strong-ext-mon _ _ β γ γ (Γ.is-refl γ) _ _
    where
      β : _
      β γ γ' γ≤γ' a a' a≤a' =
        ≤mon→≤mon-het (g $ γ) (g $ γ') (g .isMon γ≤γ') a a' a≤a' -- g .isMon γ≤γ'
  aux2 g γ .pres≈ = strong-ext-pres≈ _ _ β γ γ (Γ.is-refl-Bisim γ) _ _
    where
      β : _
      β γ γ' γ≈γ' = g .pres≈ γ≈γ'

  aux : ⟨ Γ ⟶ob (A ⟶ob B) ⟩ → ⟨ (Γ ⟶ob (𝕃 A ⟶ob B)) ⟩
  aux g .f = aux2 g
  aux g .isMon {x = γ} {y = γ'} =
    λ γ≤γ' lx → strong-ext-mon _ _ β γ γ' γ≤γ' lx lx (LA-refl lx)
    where
      β : _
      β γ γ' γ≤γ' a a' a≤a' =
        ≤mon→≤mon-het (g $ γ) (g $ γ') (g .isMon γ≤γ') a a' a≤a'
  aux g .pres≈ = strong-ext-pres≈ _ _ β _ _
    where
      β : _
      β γ γ' γ≈γ' = g .pres≈ γ≈γ'
 
  StrongExt : PMor (U-ob (Γ ⟶ob (A ⟶ob B))) (U-ob ((Γ ⟶ob (𝕃 A ⟶ob B))))
  StrongExt .PMor.f g = aux g
  StrongExt .isMon {x = g₁} {y = g₂} g₁≤g₂ =
    λ γ lx → strong-ext-mon _ _ α γ γ (Γ.is-refl γ) lx lx (LA-refl lx)
    where
      α : TwoCell Γ._≤_ (TwoCell A._≤_ B._≤_) _ _
      α γ γ' γ≤γ' a a' a≤a' =
        let g₁γ≤g₂γ' = λ x → U-ob (A ⟶ob B) .snd .PredomainStr.is-trans (g₁ .PMor.f γ) (g₂ .PMor.f γ) (g₂ .PMor.f γ') (g₁≤g₂ γ) (g₂ .PMor.isMon γ≤γ') x in
        ≤mon→≤mon-het (g₁ $ γ) (g₂ $ γ') g₁γ≤g₂γ' a a' a≤a' -- ≤mon→≤mon-het g₁ g₂ g₁≤g₂ γ γ' γ≤γ'
  StrongExt .pres≈ {x = g} {y = h} = strong-ext-pres≈ _ _
 
  -- Goal :              (a : A .fst) → f (f g₁ γ) a B.≤ f (f g₂ γ') a
  -- Have:  (γ : Γ .fst) (a : A .fst) → f (f g₁ γ) a B.≤ f (f g₂ γ) a

  -- Ext : ErrorDomMor (Γ ⟶ob (A ⟶ob B)) ((Γ ⟶ob (𝕃 A ⟶ob B)))
  -- Ext .f℧ = eqPMor _ _ (funExt (λ γ → eqPMor _ _ (funExt (λ lx → {!Equations.ext-℧ ? ? ?!}))))
  -- Ext .fθ = {!!}

  -- This is *not* a morphism of error domains, becasue it does not
  -- preserve error:
  --
  -- For that, we would need to have
  --   ext (λ γ' x → B.℧) γ lx ≡ B.℧
  -- But lx may be a θ, in which case the LHS will be B.θ(...)

  -- PMor (Γ ×dp A) B → PMor (Γ ×dp 𝕃 A) B


module ExtCombinator
  {A : Predomain ℓA ℓ≤A ℓ≈A}
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} where

  module A = PredomainStr (A .snd)
  module B = ErrorDomainStr (B .snd)

  open StrongExtCombinator {Γ = UnitP} {A = A} {B = B}

  Ext : PMor (U-ob (A ⟶ob B)) (U-ob (𝕃 A ⟶ob B))
  Ext = from ∘p StrongExt ∘p to
    where
      to : PMor (U-ob (A ⟶ob B)) (U-ob (UnitP ⟶ob (A ⟶ob B)))
      to = Curry π1

      from : PMor (U-ob (UnitP ⟶ob (𝕃 A ⟶ob B))) (U-ob (𝕃 A ⟶ob B))
      from = ((PairFun UnitP! Id) ~-> Id) ∘p Uncurry'

module MapCombinator
  {Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ}
  {Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} where

  open ExtCombinator {A = Aᵢ} {B = F-ob Aₒ}

  Map : PMor (Aᵢ ==> Aₒ) (𝕃 Aᵢ ==> 𝕃 Aₒ)
  Map = Ext ∘p (Id ~-> η-mor)


module _ {A : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} where

  open F-ob
  open ErrorDomainStr (F-ob A .snd) using (δ≈id) -- brings in δ≈id for L℧ A
  
  open ExtAsEDMorphism {A = A} {B = F-ob A} using () renaming (Ext to Ext-ErrorDom)
  open ExtCombinator {A = A} {B = F-ob A} renaming (Ext to ExtCombinator)
  open CBPVExt ⟨ A ⟩ (L℧ ⟨ A ⟩) ℧ θ
  open MonadLaws.Unit-Right ⟨ A ⟩

  δ* : ErrorDomMor (F-ob A) (F-ob A)
  δ* = Ext-ErrorDom (δ-mor ∘p η-mor)

  δ*≈id : (U-mor δ*) ≈mon Id
  δ*≈id = transport (λ i → (U-mor δ*) ≈mon (lem3 i)) lem2

    where
      lem1 : _≈mon_ {X = A} {Y = 𝕃 A} (δ-mor ∘p η-mor) (Id ∘p η-mor)
      lem1 = ≈mon-comp
        {f = η-mor} {g = η-mor} {f' = δ-mor} {g' = Id}
        (≈mon-refl η-mor) δ≈id

      lem2 : (U-mor δ*) ≈mon (U-mor (Ext-ErrorDom (Id ∘p η-mor)))
      lem2 = ExtCombinator .pres≈ {x = δ-mor ∘p η-mor} {y = η-mor} lem1

      lem3 : (U-mor (Ext-ErrorDom (Id ∘p η-mor))) ≡ Id
      lem3 = eqPMor _ _ (funExt (λ lx → monad-unit-right lx))

  -- NTS : (U δ*) ≈mon Id
  -- We have δ* = ext (δ ∘ η) and Id = ext (Id ∘ η)
  -- Since ext preserves bisimilarity, it suffices to show that δ ∘ η ≈ Id ∘ η,
  -- where δ = θ ∘ next : UFA → UFA.
  -- Since δ ≈ Id and η ≈ η, the result follows by the fact that composition
  -- preserves bisimilarity.



δ*Sq : {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  (c : PRel A A' ℓc) → ErrorDomSq (F-rel.F-rel c) (F-rel.F-rel c) δ* δ*
δ*Sq {A = A} {A' = A'} c =
  Ext-sq c (F-rel.F-rel c) (δ-mor ∘p η-mor) (δ-mor ∘p η-mor)
  (CompSqV
    {c₁ = c} {c₂ = U-rel (F-rel.F-rel c)} {c₃ = U-rel (F-rel.F-rel c)}
    (η-sq c) (δB-sq (F-rel.F-rel c)))

{-
ext-mon _ _ (λ a a' caa' →
  -- Lc.Properties.δ-monotone (Lc.Properties.η-monotone caa'))
  {!!} {!!})
  where
    open F-ob
    -- open F-rel c
    open F-rel
    
    open ExtMonotone ⟨ A ⟩ ⟨ A' ⟩ (c .PRel.R) (L℧ ⟨ A ⟩) ℧ θ (L℧ ⟨ A' ⟩) ℧ θ (F-rel c .ErrorDomRel.R)
      (F-rel c .ErrorDomRel.R℧) (F-rel c .ErrorDomRel.Rθ)
      -- (Lc.Properties.℧⊥) (λ _ _ → Lc.Properties.θ-monotone)

-}

module _
  {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ}   {Γ' : Predomain ℓΓ' ℓ≤Γ' ℓ≈Γ'}
  {A : Predomain ℓA ℓ≤A ℓ≈A}   {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B}  {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
  (cΓ : PRel Γ Γ' ℓcΓ)
  (c : PRel A A' ℓc)
  (d : ErrorDomRel B B' ℓd)
  (f : U-ob (Γ  ⟶ob (A  ⟶ob B)) .fst)
  (g : U-ob (Γ' ⟶ob (A' ⟶ob B')) .fst)
  where
  open StrongExtCombinator

  private
    module B  = ErrorDomainStr (B .snd)
    module B' = ErrorDomainStr (B' .snd)

  open StrongExtMonotone
    ⟨ Γ ⟩ ⟨ Γ' ⟩ (cΓ .PRel.R)
    ⟨ A ⟩ ⟨ A' ⟩ (c .PRel.R)
    ⟨ B ⟩  B.℧  B.θ.f
    ⟨ B' ⟩ B'.℧ B'.θ.f
    (d .ErrorDomRel.R) (d .ErrorDomRel.R℧) (d .ErrorDomRel.Rθ)

  StrongExt-Sq :
    PSq cΓ (U-rel (c ⟶rel d)) f g →
    PSq cΓ (U-rel (U-rel (F-rel.F-rel c) ⟶rel d)) (StrongExt .PMor.f f) (StrongExt .PMor.f g)
  StrongExt-Sq = strong-ext-mon (λ γ → f .PMor.f γ .PMor.f) (λ γ' → g .PMor.f γ' .PMor.f)
