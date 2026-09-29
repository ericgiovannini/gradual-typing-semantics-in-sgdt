{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}


open import Common.Later

module Semantics.Concrete.Predomain.MonadCombinatorsOpaque (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function hiding (_$_)

open import Common.Common
-- open import Semantics.Concrete.GuardedLift k renaming (η to Lη ; θ to Lθ)
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.SquareOpaque
open import Semantics.Concrete.Predomain.Constructions
open import Semantics.Concrete.Predomain.Combinators


open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k
open import Semantics.Concrete.Predomain.Error

open import Semantics.Concrete.Predomain.SimpleErrorDomain k
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.ErrorDomain.Square k
open import Semantics.Concrete.Predomain.FreeErrorDomainOpaque k
open import Semantics.Concrete.Predomain.Ext k
open import Semantics.Concrete.Predomain.MonadRelationalResultsOpaque k


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


module _
  {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ}
  {A : Predomain ℓA ℓ≤A ℓ≈A}
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} where

  private
    module Γ = PredomainStr (Γ .snd)
    module A = PredomainStr (A .snd)
    module B = ErrorDomainStr (B .snd)
    
    module LA = LiftOrdHomogenous ⟨ A ⟩ A._≤_
    LA-refl = LA.Properties.⊑-refl A.is-refl
    
    module ΓAB = ErrorDomainStr ((Γ ⟶ob (A ⟶ob B)) .snd)
  
    |B| = ErrorDomain→SimpleErrorDomain B
    ⊑B = ErrorDomRel→SEDrel (idEDRel B)

  module _ (g : ⟨ Γ ⟶ob (A ⟶ob B) ⟩) where
    private
      opaque
        unfolding ⟨_⟩s F-ob 𝕃 _⊑ls_ ErrorDomRel→SEDrel ⟨SimpleErrorDomain⟩→⟨ErrorDomain⟩ _≈FA_
        |g| : ⟨ Γ ⟩ → ⟨ A ⟩ → ⟨ |B| ⟩s
        |g| γ' = g .f γ' .f      

        β≤ : TwoCell Γ._≤_ (TwoCell A._≤_ (⊑B .SEDrel.R)) |g| |g|
        β≤ γ γ' γ≤γ' a a' a≤a' =
          ≤mon→≤mon-het (g $ γ) (g $ γ') (g .isMon γ≤γ') a a' a≤a'

    opaque
      unfolding ⟨_⟩s F-ob 𝕃 _⊑ls_ ErrorDomRel→SEDrel ⟨SimpleErrorDomain⟩→⟨ErrorDomain⟩ _≈FA_ |g| ℧𝔽 θ𝔽
      
      StrongExt-fun₁ : ⟨ Γ ⟩ → ⟨ F-ob A ⊸ B ⟩
      StrongExt-fun₁ γ .f .f = st-ext {B = |B|} |g| γ
      StrongExt-fun₁ γ .f .isMon {x = x} {y = y} =
        strong-ext-mon-sq Γ._≤_ A._≤_ |B| |B| ⊑B |g| |g| β≤ γ γ (Γ.is-refl γ) x y      
      StrongExt-fun₁ γ .f .pres≈ {x = x} {y = y} x≈y =
        strong-ext-pres≈ ⟨ Γ ⟩ Γ._≈_ ⟨ A ⟩ A._≈_ B |g| |g| β≈ γ γ (Γ.is-refl-Bisim γ) x y x≈y
          where
           β≈ : TwoCell Γ._≈_ (TwoCell A._≈_ B._≈_) |g| |g|
           β≈ γ γ' γ≈γ' = g .pres≈ γ≈γ'             
      StrongExt-fun₁ γ .f℧ = st-ext-℧ |g| γ
      StrongExt-fun₁ γ .fθ = st-ext-θ |g| γ


      StrongExt-fun₂ : ⟨ (Γ ==> (F-ob A ⊸ B)) ⟩
      StrongExt-fun₂ .f = StrongExt-fun₁
      StrongExt-fun₂ .isMon {x = γ} {y = γ'} = λ γ≤γ' lx →
        strong-ext-mon-sq Γ._≤_ A._≤_ |B| |B| ⊑B |g| |g| β≤ γ γ' γ≤γ' lx lx (LA-refl lx)
      StrongExt-fun₂ .pres≈ = strong-ext-pres≈ ⟨ Γ ⟩ Γ._≈_ ⟨ A ⟩ A._≈_ B |g| |g| β≈ _ _
        where
          β≈ : TwoCell Γ._≈_ (TwoCell A._≈_ B._≈_) |g| |g|
          β≈ γ γ' γ≈γ' = g .pres≈ γ≈γ'


  opaque
    unfolding StrongExt-fun₂
    StrongExt₁ : PMor (U-ob (Γ ⟶ob (A ⟶ob B))) (Γ ==> (F-ob A ⊸ B)) 
    StrongExt₁ .f = StrongExt-fun₂
    StrongExt₁ .isMon {x = g₁} {y = g₂} g₁≤g₂ =
      λ γ lx →
        strong-ext-mon-sq Γ._≤_ A._≤_ |B| |B| ⊑B |g₁| |g₂| α γ γ (Γ.is-refl γ) lx lx (LA-refl lx)
      where
        |g₁| : ⟨ Γ ⟩ → ⟨ A ⟩ → ⟨ |B| ⟩s
        |g₁| γ1 = g₁ .f γ1 .f

        |g₂| : ⟨ Γ ⟩ → ⟨ A ⟩ → ⟨ |B| ⟩s
        |g₂| γ1 = g₂ .f γ1 .f

        α : TwoCell Γ._≤_ (TwoCell A._≤_ B._≤_) |g₁| |g₂|
        α γ γ' γ≤γ' a a' a≤a' =
          let g₁γ≤g₂γ' = λ x → U-ob (A ⟶ob B) .snd .PredomainStr.is-trans (g₁ .PMor.f γ) (g₂ .PMor.f γ) (g₂ .PMor.f γ') (g₁≤g₂ γ) (g₂ .PMor.isMon γ≤γ') x in
          ≤mon→≤mon-het (g₁ $ γ) (g₂ $ γ') g₁γ≤g₂γ' a a' a≤a'
    StrongExt₁ .pres≈ = strong-ext-pres≈ ⟨ Γ ⟩ Γ._≈_ ⟨ A ⟩ A._≈_ B _ _

  opaque
    unfolding StrongExt₁ ηM ℧M θM
    StrongExt₁-η : ∀ h γ x → StrongExt₁ .f h .f γ .fun (ηM .f x) ≡ h .f γ .f x
    StrongExt₁-η h γ x = st-ext-η (λ γ' x' → h .f γ' .f x') γ x
    





module StrongExtCombinator
  {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ}
  {A : Predomain ℓA ℓ≤A ℓ≈A}
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} where

  private
    module Γ = PredomainStr (Γ .snd)
    module A = PredomainStr (A .snd)
    module B = ErrorDomainStr (B .snd)
    
    module LA = LiftOrdHomogenous ⟨ A ⟩ A._≤_
    LA-refl = LA.Properties.⊑-refl A.is-refl
 
    module ΓAB = ErrorDomainStr ((Γ ⟶ob (A ⟶ob B)) .snd)
  
    |B| = ErrorDomain→SimpleErrorDomain B
    ⊑B = ErrorDomRel→SEDrel (idEDRel B)

  opaque
    unfolding ⟨_⟩s 𝕃 _⊑ls_ ErrorDomRel→SEDrel ⟨SimpleErrorDomain⟩→⟨ErrorDomain⟩ _≈FA_
    
    aux2 : ⟨ Γ ⟶ob (A ⟶ob B) ⟩ → ⟨ Γ ⟩ → ⟨ 𝕃 A ⟶ob B ⟩
    aux2 g γ .f = st-ext {B = |B|} (λ γ' → g .f γ' .f) γ
    aux2 g γ .isMon {x = x} {y = y} =
      strong-ext-mon-sq Γ._≤_ A._≤_ |B| |B| ⊑B |g| |g| β γ γ (Γ.is-refl γ) x y
      where
        |g| : ⟨ Γ ⟩ → ⟨ A ⟩ → ⟨ |B| ⟩s
        |g| γ' = g .f γ' .f
        
        β : TwoCell Γ._≤_ (TwoCell A._≤_ (⊑B .SEDrel.R)) |g| |g|
        β γ γ' γ≤γ' a a' a≤a' =
          ≤mon→≤mon-het (g $ γ) (g $ γ') (g .isMon γ≤γ') a a' a≤a'
          
    aux2 g γ .pres≈ {x = x} {y = y} x≈y =
      strong-ext-pres≈ ⟨ Γ ⟩ Γ._≈_ ⟨ A ⟩ A._≈_ B |g| |g| β γ γ (Γ.is-refl-Bisim γ) x y x≈y
      where
        |g| : ⟨ Γ ⟩ → ⟨ A ⟩ → ⟨ |B| ⟩s
        |g| γ' = g .f γ' .f
        
        β : TwoCell Γ._≈_ (TwoCell A._≈_ B._≈_) |g| |g|
        β γ γ' γ≈γ' = g .pres≈ γ≈γ'


    aux : ⟨ Γ ⟶ob (A ⟶ob B) ⟩ → ⟨ (Γ ⟶ob (𝕃 A ⟶ob B)) ⟩
    aux g .f = aux2 g
    aux g .isMon {x = γ} {y = γ'} =
      λ γ≤γ' lx →
      strong-ext-mon-sq Γ._≤_ A._≤_ |B| |B| ⊑B |g| |g| β γ γ' γ≤γ' lx lx (LA-refl lx)
      where
        |g| : ⟨ Γ ⟩ → ⟨ A ⟩ → ⟨ |B| ⟩s
        |g| γ1 = g .f γ1 .f
        
        β : TwoCell Γ._≤_ (TwoCell A._≤_ B._≤_) |g| |g|
        β γ γ' γ≤γ' a a' a≤a' =
          ≤mon→≤mon-het (g $ γ) (g $ γ') (g .isMon γ≤γ') a a' a≤a'

    aux g .pres≈ =
      strong-ext-pres≈ ⟨ Γ ⟩ Γ._≈_ ⟨ A ⟩ A._≈_ B |g| |g| β _ _
      where
        |g| : ⟨ Γ ⟩ → ⟨ A ⟩ → ⟨ |B| ⟩s
        |g| γ1 = g .f γ1 .f
        
        β : TwoCell Γ._≈_ (TwoCell A._≈_ B._≈_) |g| |g|
        β γ γ' γ≈γ' = g .pres≈ γ≈γ'


    StrongExt' : PMor (U-ob (Γ ⟶ob (A ⟶ob B))) (U-ob ((Γ ⟶ob (𝕃 A ⟶ob B))))
    StrongExt' .PMor.f g = aux g
    StrongExt' .isMon {x = g₁} {y = g₂} g₁≤g₂ =
      λ γ lx →
        strong-ext-mon-sq Γ._≤_ A._≤_ |B| |B| ⊑B |g₁| |g₂| α γ γ (Γ.is-refl γ) lx lx (LA-refl lx)
      where
        |g₁| : ⟨ Γ ⟩ → ⟨ A ⟩ → ⟨ |B| ⟩s
        -- |g₁| γ1 = ⟨ErrorDomain⟩→⟨SimpleErrorDomain⟩ ∘ (g₁ .f γ1 .f)
        |g₁| γ1 = g₁ .f γ1 .f

        |g₂| : ⟨ Γ ⟩ → ⟨ A ⟩ → ⟨ |B| ⟩s
        -- |g₂| γ1 = ⟨ErrorDomain⟩→⟨SimpleErrorDomain⟩ ∘ (g₂ .f γ1 .f)
        |g₂| γ1 = g₂ .f γ1 .f

        α : TwoCell Γ._≤_ (TwoCell A._≤_ B._≤_) |g₁| |g₂|
        α γ γ' γ≤γ' a a' a≤a' =
          let g₁γ≤g₂γ' = λ x → U-ob (A ⟶ob B) .snd .PredomainStr.is-trans (g₁ .PMor.f γ) (g₂ .PMor.f γ) (g₂ .PMor.f γ') (g₁≤g₂ γ) (g₂ .PMor.isMon γ≤γ') x in
          ≤mon→≤mon-het (g₁ $ γ) (g₂ $ γ') g₁γ≤g₂γ' a a' a≤a'
    StrongExt' .pres≈ {x = g} {y = h} = strong-ext-pres≈ ⟨ Γ ⟩ Γ._≈_ ⟨ A ⟩ A._≈_ B _ _

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


    opaque
      unfolding F-ob
      StrongExt : PMor (U-ob (Γ ⟶ob (A ⟶ob B))) (Γ ==> ((U-ob (F-ob A)) ==> U-ob B))
      StrongExt = StrongExt'

      StrongExt'' : PMor (U-ob (Γ ⟶ob (A ⟶ob B))) (Γ ==> ((F-ob A)) ⊸ B)
      StrongExt'' = {!StrongExt'!}

  open PMor

  opaque
    unfolding F-ob 𝕃 StrongExt StrongExt' η𝔽 ℧𝔽 θ𝔽 ηM ℧M θM η-mor ℧-mor θ-mor

    StrongExt'-η : ∀ h γ x → StrongExt' .f h .f γ .f (η-mor .f x) ≡ h .f γ .f x
    StrongExt'-η h γ x = st-ext-η (λ γ' x' → h .f γ' .f x') γ x
    
    StrongExt-η : ∀ h γ x → StrongExt .f h .f γ .f (ηM .f x) ≡ h .f γ .f x
    StrongExt-η = StrongExt'-η
    





module ExtCombinator
  {A : Predomain ℓA ℓ≤A ℓ≈A}
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} where

  private
    module A = PredomainStr (A .snd)
    module B = ErrorDomainStr (B .snd)
  open PMor

  open StrongExtCombinator {Γ = UnitP} {A = A} {B = B}

  opaque
    unfolding F-ob
    Ext : PMor (U-ob (A ⟶ob B)) ((U-ob (F-ob A)) ==> U-ob B)
    Ext = from ∘p StrongExt ∘p to
      where
        to : PMor (U-ob (A ⟶ob B)) (U-ob (UnitP ⟶ob (A ⟶ob B)))
        to = Curry π1

        from : PMor (U-ob (UnitP ⟶ob (𝕃 A ⟶ob B))) (U-ob (𝕃 A ⟶ob B))
        from = ((PairFun UnitP! Id) ~-> Id) ∘p Uncurry'

  opaque
    unfolding Ext ηM ℧M θM
    
    Ext-η : ∀ h x → Ext .f h .f (ηM .f x) ≡ h .f x
    Ext-η h x = StrongExt-η _ tt x







module MapCombinator
  {Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ}
  {Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} where

  open ExtCombinator {A = Aᵢ} {B = F-ob Aₒ}

  Map : PMor (Aᵢ ==> Aₒ) (𝕃 Aᵢ ==> 𝕃 Aₒ)
  Map = {!!} -- Ext ∘p (Id ~-> η-mor)


module _ {A : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} where

  open F-ob
  open ErrorDomainStr (F-ob A .snd) using (δ≈id) -- brings in δ≈id for L℧ A
  
  open ExtAsEDMorphism {A = A} {B = F-ob A} using () renaming (Ext to Ext-ErrorDom)
  open ExtCombinator {A = A} {B = F-ob A} renaming (Ext to ExtCombinator)
  --open CBPVExt ⟨ A ⟩ (L℧ ⟨ A ⟩) ℧ θ
  -- open MonadLaws.Unit-Right ⟨ A ⟩

  δ* : ErrorDomMor (F-ob A) (F-ob A)
  δ* = Ext-ErrorDom (δM ∘p ηM)

  δ*≈id : (U-mor δ*) ≈mon Id
  δ*≈id = transport (λ i → (U-mor δ*) ≈mon (lem3 i)) lem2

    where
      opaque -- opaque may not be needed...
        unfolding F-ob
        lem1 : _≈mon_ {X = A} {Y = 𝕃 A} (δ-mor ∘p η-mor) (Id ∘p η-mor)
        lem1 = ≈mon-comp
          {f = η-mor} {g = η-mor} {f' = δ-mor} {g' = Id}
          (≈mon-refl η-mor) δ≈id

        lem2 : (U-mor δ*) ≈mon (U-mor (Ext-ErrorDom (Id ∘p ηM)))
        lem2 = {!!} -- ExtCombinator .pres≈ {x = δ-mor ∘p η-mor} {y = η-mor} lem1

        lem3 : (U-mor (Ext-ErrorDom (Id ∘p ηM))) ≡ Id
        lem3 = {!!} -- eqPMor _ _ (funExt (λ lx → MonadLaws.monad-unit-right lx))
 

  -- NTS : (U δ*) ≈mon Id
  -- We have δ* = ext (δ ∘ η) and Id = ext (Id ∘ η)
  -- Since ext preserves bisimilarity, it suffices to show that δ ∘ η ≈ Id ∘ η,
  -- where δ = θ ∘ next : UFA → UFA.
  -- Since δ ≈ Id and η ≈ η, the result follows by the fact that composition
  -- preserves bisimilarity.


opaque
  unfolding ηM δM
  δ*Sq : {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
    (c : PRel A A' ℓc) → ErrorDomSq (F-rel.F-rel c) (F-rel.F-rel c) δ* δ*
  δ*Sq {A = A} {A' = A'} c =
    Ext-sq c (F-rel.F-rel c) (δM ∘p ηM) (δM ∘p ηM)
    (CompSqV
      {c₁ = c} {c₂ = U-rel (F-rel.F-rel c)} {c₃ = U-rel (F-rel.F-rel c)}
      (η-sq c) (δB-sq (F-rel.F-rel c)))


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
  open F-rel

  private
    module B  = ErrorDomainStr (B .snd)
    module B' = ErrorDomainStr (B' .snd)


  Sq-StrongExt :
    PSq cΓ (U-rel (c ⟶rel d)) f g →
    PSq cΓ (U-rel (U-rel (F-rel c) ⟶rel d)) (StrongExt .PMor.f f) (StrongExt .PMor.f g)
  Sq-StrongExt = {!!} -- strong-ext-mon (λ γ → f .PMor.f γ .PMor.f) (λ γ' → g .PMor.f γ' .PMor.f)

