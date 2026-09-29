{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.DoubleFunctor (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.HLevels
import Cubical.Data.Sigma as Data
open import Cubical.Foundations.Structure
open import Cubical.Data.List

open import Cubical.Relation.Binary

open import Common.Common
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions
  using (LiftPredomain ; ℕ ; UnitP ; _×dp_ ; _⊎p_ ; π1 ; π2)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Combinators hiding (S ; U)
open import Semantics.Concrete.Predomain.SquareOpaque
open import Semantics.Concrete.Predomain.SquareCombinators

open BinaryRelation


private
  variable
    ℓ  ℓ≤  ℓ≈ : Level
    ℓ' ℓ≤' ℓ≈' : Level
    ℓ'' : Level

    ℓA  ℓ≤A  ℓ≈A     : Level
    ℓA' ℓ≤A' ℓ≈A'    : Level

    ℓAᵢ   ℓ≤Aᵢ   ℓ≈Aᵢ   : Level
    ℓAᵢ'  ℓ≤Aᵢ'  ℓ≈Aᵢ'  : Level
    ℓAᵢ'' ℓ≤Aᵢ'' ℓ≈Aᵢ'' : Level
    ℓAₒ   ℓ≤Aₒ   ℓ≈Aₒ   : Level
    ℓAₒ'  ℓ≤Aₒ'  ℓ≈Aₒ'  : Level
    ℓAₒ'' ℓ≤Aₒ'' ℓ≈Aₒ'' : Level

    ℓA₁   ℓ≤A₁   ℓ≈A₁   : Level
    ℓA₁'  ℓ≤A₁'  ℓ≈A₁'  : Level
    ℓA₂   ℓ≤A₂   ℓ≈A₂   : Level
    ℓA₂'  ℓ≤A₂'  ℓ≈A₂'  : Level
    ℓA₃   ℓ≤A₃   ℓ≈A₃   : Level
    ℓA₃'  ℓ≤A₃'  ℓ≈A₃'  : Level

    ℓc ℓcᵢ ℓcₒ ℓcᵢ' ℓcₒ'   : Level

    ℓXᵢ ℓXᵢ' ℓXₒ ℓXₒ' : Level
    ℓX₁ ℓX₂ ℓX₃ : Level
    ℓR ℓS : Level
    ℓRᵢ ℓRₒ : Level

    X : Type ℓ
    Y : Type ℓ'
    Z : Type ℓ''



_⇒rel_ : {X : Type ℓ} {Y : Type ℓ'}
  → Rel X Y ℓR
  → Rel X Y ℓS
  → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓR) ℓS)
R ⇒rel S = TwoCell R S (λ x → x) (λ x → x)


{-
A "double functor" of predomains consists of:

  - An action on objects
  - An action on predomain morphisms
  - An action on predomain relations
  - An action on predomain squares

such that:

  - The action on morphisms satisfies preserves identity and composition.

  - The action on relations preserves identity and composition laxly.

(There are no equations involving the action on squares, since there
is at most one square with a given frame.)
 
-}
record DoubleFunctor : Typeω where

  field
    fℓ  : Level → Level
    fℓ≤ : Level → Level
    fℓ≈ : Level → Level
    fℓR : Level → Level
    
    F-ob : Predomain ℓ ℓ≤ ℓ≈ → Predomain (fℓ ℓ) (fℓ≤ ℓ≤) (fℓ≈ ℓ≈)

    F-mor :
        {Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ}
      → PMor Aᵢ Aₒ → PMor (F-ob Aᵢ) (F-ob Aₒ)
      
    F-mor-id : {A : Predomain ℓA ℓ≤A ℓ≈A}
      → F-mor (Id {X = A}) ≡ Id

    F-mor-comp :
      {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁}
      {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂}
      {A₃ : Predomain ℓA₃ ℓ≤A₃ ℓ≈A₃}
      → (f : PMor A₁ A₂)
      → (g : PMor A₂ A₃)
      → (F-mor (g ∘p f) ≡ (F-mor g) ∘p (F-mor f))

    F-rel : ∀ {ℓR}
      → {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
      → PRel A A' ℓR → PRel (F-ob A) (F-ob A') (fℓR ℓR)

    -- we also want lax functoriality for the relations

    F-sq : ∀
      {Aᵢ  : Predomain ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ}
      {Aᵢ' : Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
      {Aₒ  : Predomain ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ} 
      {Aₒ' : Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'}
      → (cᵢ  : PRel Aᵢ Aᵢ' ℓcᵢ)
      → (cₒ  : PRel Aₒ Aₒ' ℓcₒ)
      → (f   : PMor Aᵢ  Aₒ)
      → (g   : PMor Aᵢ' Aₒ')
      → PSq cᵢ cₒ f g
      → PSq (F-rel cᵢ) (F-rel cₒ) (F-mor f) (F-mor g)


open DoubleFunctor



{-

A sufficient way of specifying a double functor of predomains is by
specifying an action on types, on functions, on relations, and on
squares.

Here, the relations and squares are the usual set/function-based
notions of relation and two-cell, *not* predomain relations/squares.

Note also that not all double functors arise in this manner: for
example, the action on objects may depend crucially on the predomain
structure, as is the case with the functor Hom(- , A') that sends a
predomain A to the predomain of morphisms from A to A' for some fixed
A'. To do this we already need the predomain structure on A.

-}

record MinimalData : Typeω where

  field
    gℓ-typ  : Level → Level
    gℓ-rel  : Level → Level
    G-typ   : Type ℓ → Type (gℓ-typ ℓ)
    G-isSet : ∀ (X : Type ℓ) → isSet X → isSet (G-typ X)
    G-fun : {X : Type ℓ} {Y : Type ℓ'}
      → (X → Y) → (G-typ X → G-typ Y)
    G-fun-id : {X : Type ℓ}
      → G-fun {X = X} id ≡ id
    G-fun-comp : {X₁ : Type ℓX₁} {X₂ : Type ℓX₂} {X₃ : Type ℓX₃}
      → (f : X₁ → X₂)
      → (g : X₂ → X₃)
      → G-fun (g ∘ f) ≡ (G-fun g) ∘ (G-fun f) 
    G-rel : ∀ {ℓR}
      → Rel X Y ℓR
      → Rel (G-typ X) (G-typ Y) (gℓ-rel ℓR)
    G-sq : {Xᵢ  : Type ℓXᵢ} {Xᵢ' : Type ℓXᵢ'}
           {Xₒ  : Type ℓXₒ} {Xₒ' : Type ℓXₒ'}
      → (Rᵢ  : Rel Xᵢ Xᵢ' ℓRᵢ)
      → (Rₒ  : Rel Xₒ Xₒ' ℓRₒ)
      → (f   : Xᵢ  → Xₒ)
      → (g   : Xᵢ' → Xₒ')
      → TwoCell Rᵢ Rₒ f g
      → TwoCell (G-rel Rᵢ) (G-rel Rₒ) (G-fun f) (G-fun g)

  preserves : (P : ∀ {ℓ ℓ' ℓR : Level} {X : Type ℓ} {Y : Type ℓ'} → Rel X Y ℓR → Type)
    → Typeω
  preserves P = ∀ {ℓ ℓ' ℓR} {X : Type ℓ} {Y : Type ℓ'} (R : Rel X Y ℓR)
    → P R → P (G-rel R)

   
  field
    G-prop : ∀ {X : Type ℓ} {Y : Type ℓ'} (R : Rel X Y ℓR)
      → (∀ x y → isProp (R x y))
      → (∀ gx gy → isProp (G-rel R gx gy))
      
    G-refl : {X : Type ℓ}  (R : Rel X X ℓR)
      → isRefl R
      → isRefl (G-rel R)

    G-sym : (R : Rel X X ℓR)
      → isSym R
      → isSym (G-rel R)

    G-antisym : (R : Rel X X ℓR)
      → isAntisym R
      → isAntisym (G-rel R)

    G-hetTrans : {ℓR ℓS : Level} {R : Rel X Y ℓR} {S : Rel Y Z ℓS}
      → ∀ {gx gy gz}
      → G-rel R gx gy
      → G-rel S gy gz
      → G-rel (compRel R S) gx gz -- what if we want to take the propositional truncation?


  G-relImp : ∀ {ℓR ℓS}
      → {R : Rel X Y ℓR} {S : Rel X Y ℓS}
      → R ⇒rel S
      → G-rel R ⇒rel G-rel S
  G-relImp {R = R} {S = S} R⇒S =
    subst2 (λ f g → TwoCell (G-rel R) (G-rel S) f g) G-fun-id G-fun-id (G-sq R S id id R⇒S)

open MinimalData


{- Given the above data, we can construct a double functor of
predomains. -}

module _ (M : MinimalData)
  where
  
  private module M = MinimalData M

  module _ (A : Predomain ℓ ℓ≤ ℓ≈) where
    private
      module A = PredomainStr (A .snd)
     
    |GA| = M.G-typ ⟨ A ⟩

    ⊑GA : |GA| → |GA| → Type (M.gℓ-rel ℓ≤)
    ⊑GA = M.G-rel A._≤_

    isTrans⊑GA : isTrans ⊑GA
    isTrans⊑GA x y z x≤y y≤z =
      M.G-relImp ≤⊙≤→≤ x z G-compRel-xz
      where
        G-compRel-xz : M.G-rel (compRel A._≤_ A._≤_) x z
        G-compRel-xz = M.G-hetTrans x≤y y≤z
        
        ≤⊙≤→≤ : compRel A._≤_ A._≤_ ⇒rel A._≤_
        ≤⊙≤→≤ x z (y , x≤y , y≤z) = A.is-trans x y z x≤y y≤z

    isOrd : IsOrderingRelation ⊑GA
    isOrd = isorderingrelation
      (M.G-prop A._≤_ A.is-prop-valued)
      (M.G-refl A._≤_ A.is-refl)
      isTrans⊑GA
      (M.G-antisym A._≤_ A.is-antisym)

    ≈GA : |GA| → |GA| → Type (M.gℓ-rel ℓ≈)
    ≈GA = M.G-rel A._≈_

    isBisim : IsBisim ≈GA
    isBisim = isbisim
      (M.G-refl A._≈_ A.is-refl-Bisim)
      (M.G-sym A._≈_ A.is-sym)
      (M.G-prop A._≈_ A.is-prop-valued-Bisim)

    G-ob : Predomain (M.gℓ-typ ℓ) (M.gℓ-rel ℓ≤) (M.gℓ-rel ℓ≈)
    G-ob .fst = M.G-typ ⟨ A ⟩
    G-ob .snd = predomainstr (M.G-isSet ⟨ A ⟩ A.is-set) ⊑GA isOrd ≈GA isBisim

  module _ {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'} where
    private
      module A  = PredomainStr (A  .snd)
      module A' = PredomainStr (A' .snd)

    module _ (f : PMor A A') where

      G-pmor : PMor (G-ob A) (G-ob A')
      G-pmor .PMor.f = M.G-fun (f .PMor.f)
      G-pmor .PMor.isMon x≤y =
        M.G-sq A._≤_ A'._≤_ (f .PMor.f) (f .PMor.f) (λ _ _ → f .PMor.isMon) _ _ x≤y
      G-pmor .PMor.pres≈ x≈y =
        M.G-sq A._≈_ A'._≈_ (f .PMor.f) (f .PMor.f) (λ a b → f .PMor.pres≈) _ _ x≈y

    module _ (c : PRel A A' ℓc) where
      G-prel : PRel (G-ob A) (G-ob A') (M.gℓ-rel ℓc)
      G-prel .PRel.R = M.G-rel (c .PRel.R)
      G-prel .PRel.is-prop-valued = M.G-prop (c .PRel.R) (c .PRel.is-prop-valued)
      G-prel .PRel.is-antitone = {!!}
      G-prel .PRel.is-monotone {x = x} {y = y} {y' = y'} xRy y≤y' =
        M.G-relImp c⊙≤⇒c x y' H
        where
          c⊙≤⇒c : compRel (PRel.R c) A'._≤_ ⇒rel PRel.R c
          c⊙≤⇒c x₁ x₃ (x₂ , x₁Rx₂ , x₂≤x₃) = PRel.is-monotone c x₁Rx₂ x₂≤x₃

          H : M.G-rel (compRel (PRel.R c) A'._≤_) x y'
          H = M.G-hetTrans xRy y≤y'

  mkDoubleFunctor : DoubleFunctor
  mkDoubleFunctor .fℓ = M.gℓ-typ
  mkDoubleFunctor .fℓ≤ = M.gℓ-rel
  mkDoubleFunctor .fℓ≈ = M.gℓ-rel
  mkDoubleFunctor .fℓR = M.gℓ-rel
  mkDoubleFunctor .F-ob = G-ob
  mkDoubleFunctor .F-mor = G-pmor
  mkDoubleFunctor .F-mor-id = eqPMor _ _ M.G-fun-id
  mkDoubleFunctor .F-mor-comp f g = eqPMor _ _ (M.G-fun-comp (f .PMor.f) (g .PMor.f))
  mkDoubleFunctor .F-rel = G-prel
  mkDoubleFunctor .F-sq cᵢ cₒ f g α =
    mkPSq
      (G-prel cᵢ) (G-prel cₒ) (G-pmor f) (G-pmor g)
      (M.G-sq _ _ _ _ (PSq→TwoCell cᵢ cₒ f g α))




