{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.CBPV (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.HLevels

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Isomorphism k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Constructions.Opposite k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Constructions.Product k

open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Constant k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Identity k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Compose k
open import Semantics.Concrete.Predomain.ThinDoubleCat.NatTrans.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Adjoint k
open import Semantics.Concrete.Predomain.ThinDoubleCat.LeftAdjointTo k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Limits.Terminal k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Limits.BinProduct k

private
  variable
    ℓ : Level
    ℓob ℓv ℓh ℓsq ℓ≈ : Level
    ℓob' ℓv' ℓh' ℓsq' ℓ≈' : Level

   
open UnitCounit


-- If U is a functor, then the adjunction F ⊣ U implies F is functorial
-- Strength condition: U(A ⟶ B) ≅ A => UB


record Action
  {ℓobC ℓvC ℓhC ℓsqC ℓ≈C : Level}
  {ℓobD ℓvD ℓhD ℓsqD ℓ≈D : Level}
  (C : ThinDoubleCat ℓobC ℓvC ℓhC ℓsqC ℓ≈C)
  (D : ThinDoubleCat ℓobD ℓvD ℓhD ℓsqD ℓ≈D)
  (termC : Terminal C)
  (prodsC : BinProducts C)
  : Type {!!} where

  private
    module C = ThinDoubleCat C
    module termC = Terminal termC
    module prodC = BinProducts prodsC
    
    C⊤ : C.ob
    C⊤ = termC.termV .fst

  field
    arr : ThinDoubleFunctor ((C ^op) ×C D) D

  A₁⟶A₂⟶B : ThinDoubleFunctor ((C ^op ×C C ^op) ×C D) D
  A₁⟶A₂⟶B = arr ∘F
    ((Pr₁ ∘F Pr₁) ,F
     (arr ∘F ((Pr₂ ∘F Pr₁) ,F Pr₂)))

  A₁×A₂⟶B : ThinDoubleFunctor ((C ^op ×C C ^op) ×C D) D
  A₁×A₂⟶B = arr ∘F (({!!} ∘F Pr₁) ,F Pr₂)

  field

    -- unitor: (⊤ ⟶ B) ≅ B
    ⟶-unit : NatIso (arr ∘F ((K C⊤) ,F (IdF D))) (IdF D)

    -- associator: (A₁ ⟶ (A₂ ⟶ B)) ≅ (A₁ × A₂) ⟶ B
    ⟶-assoc : NatIso {C = (C ^op ×C C ^op) ×C D} {D = D}
      A₁⟶A₂⟶B
      {!!}

    -- coherence laws



record Model
  (ℓobV ℓvV ℓhV ℓsqV ℓ≈V : Level)
  (ℓobE ℓvE ℓhE ℓsqE ℓ≈E : Level)
  : Type {!!} where

  field

    -- A thin double category of values, morphisms, relations, and squares
    V : ThinDoubleCat ℓobV ℓvV ℓhV ℓsqV ℓ≈V

    -- A thin double category of computations, morphisms, relations, and squares
    E : ThinDoubleCat ℓobE ℓvE ℓhE ℓsqE ℓ≈E

    -- A pair of adjoint functors F ⊣ U between V and E
    U : ThinDoubleFunctor E V

    F : LeftAdjointTo U


    -- V has products and coproducts
    term  : Terminal V
    prods : BinProducts V


    -- V is Cartesian closed
    

    -- A action of V^op on E, i.e., a functor arr : V^op × E → E
    -- arr : ThinDoubleFunctor ((V ^op) ×C E) E
    -- unitors and associator, and coherence laws
    arr : Action V E term prods

    -- strength:
    -- U(A ⟶ B) ≅ A => UB coherently


    -- V(Γ × A , UB) ≅ E(F(Γ × A) , B)
    -- 

  module V = ThinDoubleCat V
  module E = ThinDoubleCat E
  module U = ThinDoubleFunctor U

  field

    -- A natural transformation δ : U => U
    δ : ThinDoubleNatTrans U U

    -- A natural transformation ℧ : Id => U
    -- ℧ : ThinDoubleNatTrans 𝟙⟨ {!!} ⟩ {!U!}
    ℧ : {A : V.ob} {B : E.ob} → V [ A , U.F-ob B ]v

    -- δ ≈ id
    δ≈id : ∀ (B : E.ob) → (δ ⟦ B ⟧) V.≈vhom V.idV

    -- The error morphisms are less than everything
    ℧⊥ : ∀ {A : V.ob} {B : E.ob}
      → (f : V [ A , U.F-ob B ]v)
      → V [ V.idH , V.idH {U.F-ob B} , ℧ , f ]sq





    -- F : ThinDoubleFunctor V E
    -- U : ThinDoubleFunctor E V

    -- adj : F ⊣ U
