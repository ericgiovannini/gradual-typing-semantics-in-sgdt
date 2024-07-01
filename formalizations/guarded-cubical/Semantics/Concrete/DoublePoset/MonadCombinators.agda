{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}


open import Common.Later

module Semantics.Concrete.DoublePoset.MonadCombinators (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Structure

open import Common.Common
-- open import Semantics.Concrete.GuardedLift k renaming (η to Lη ; θ to Lθ)
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.Constructions
open import Semantics.Concrete.DoublePoset.DblPosetCombinators


open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k

open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.Error
open import Semantics.Concrete.DoublePoset.Monad k
open import Semantics.Concrete.DoublePoset.MonadRelationalResults k



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


open PBMor
open LiftPredomain
open F-ob
open ErrorDomMor



module StrongExtCombinator
  {Γ : PosetBisim ℓΓ ℓ≤Γ ℓ≈Γ}
  {A : PosetBisim ℓA ℓ≤A ℓ≈A}
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} where

  module Γ = PosetBisimStr (Γ .snd)
  module A = PosetBisimStr (A .snd)
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
 
  StrongExt : PBMor (U-ob (Γ ⟶ob (A ⟶ob B))) (U-ob ((Γ ⟶ob (𝕃 A ⟶ob B))))
  StrongExt .PBMor.f g = aux g
  StrongExt .isMon {x = g₁} {y = g₂} g₁≤g₂ =
    λ γ lx → strong-ext-mon _ _ α γ γ (Γ.is-refl γ) lx lx (LA-refl lx)
    where
      α : TwoCell Γ._≤_ (TwoCell A._≤_ B._≤_) _ _
      α γ γ' γ≤γ' a a' a≤a' = {!≤mon→≤mon-het g₁ g₂ g₁≤g₂ γ γ' γ≤γ'!}
  StrongExt .pres≈ {x = g} {y = h} = strong-ext-pres≈ _ _

  -- Ext : ErrorDomMor (Γ ⟶ob (A ⟶ob B)) ((Γ ⟶ob (𝕃 A ⟶ob B)))
  -- Ext .f℧ = eqPBMor _ _ (funExt (λ γ → eqPBMor _ _ (funExt (λ lx → {!Equations.ext-℧ ? ? ?!}))))
  -- Ext .fθ = {!!}

  -- This is *not* a morphism of error domains, becasue it does not
  -- preserve error:
  --
  -- For that, we would need to have
  --   ext (λ γ' x → B.℧) γ lx ≡ B.℧
  -- But lx may be a θ, in which case the LHS will be B.θ(...)

  -- PBMor (Γ ×dp A) B → PBMor (Γ ×dp 𝕃 A) B


module ExtCombinator
  {A : PosetBisim ℓA ℓ≤A ℓ≈A}
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} where

  module A = PosetBisimStr (A .snd)
  module B = ErrorDomainStr (B .snd)

  open StrongExtCombinator {Γ = UnitPB} {A = A} {B = B}

  Ext : PBMor (U-ob (A ⟶ob B)) (U-ob (𝕃 A ⟶ob B))
  Ext = from ∘p StrongExt ∘p to
    where
      to : PBMor (U-ob (A ⟶ob B)) (U-ob (UnitPB ⟶ob (A ⟶ob B)))
      to = Curry π1

      from : PBMor (U-ob (UnitPB ⟶ob (𝕃 A ⟶ob B))) (U-ob (𝕃 A ⟶ob B))
      from = ((PairFun UnitPB! Id) ~-> Id) ∘p Uncurry'

module MapCombinator
  {Aᵢ : PosetBisim ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ}
  {Aₒ : PosetBisim ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} where

  open ExtCombinator {A = Aᵢ} {B = F-ob Aₒ}

  Map : PBMor (Aᵢ ==> Aₒ) (𝕃 Aᵢ ==> 𝕃 Aₒ)
  Map = Ext ∘p (Id ~-> η-mor)


module _ {A : PosetBisim ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} where

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
      lem3 = eqPBMor _ _ (funExt (λ lx → monad-unit-right lx))

  -- NTS : (U δ*) ≈mon Id
  -- We have δ* = ext (δ ∘ η) and Id = ext (Id ∘ η)
  -- Since ext preserves bisimilarity, it suffices to show that δ ∘ η ≈ Id ∘ η,
  -- where δ = θ ∘ next : UFA → UFA.
  -- Since δ ≈ Id and η ≈ η, the result follows by the fact that composition
  -- preserves bisimilarity.



δ*Sq : {A : PosetBisim ℓA ℓ≤A ℓ≈A} {A' : PosetBisim ℓA' ℓ≤A' ℓ≈A'}
  (c : PBRel A A' ℓc) → ErrorDomSq (F-rel.F-rel c) (F-rel.F-rel c) δ* δ*
δ*Sq {A = A} {A' = A'} c = ext-mon _ _ (λ a a' caa' →
  Lc.Properties.δ-monotone (Lc.Properties.η-monotone caa'))
  where
    open F-ob
    open F-rel c
    
    open ExtMonotone ⟨ A ⟩ ⟨ A' ⟩ (c .PBRel.R) (L℧ ⟨ A ⟩) ℧ θ (L℧ ⟨ A' ⟩) ℧ θ (Lc._⊑_)
      (Lc.Properties.℧⊥) (λ _ _ → Lc.Properties.θ-monotone)

