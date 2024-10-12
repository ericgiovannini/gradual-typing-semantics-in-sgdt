{-# OPTIONS --guarded --rewriting #-}

{-# OPTIONS --lossy-unification #-}

{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.DoublePoset.DblPosetCombinators where

open import Cubical.Relation.Binary
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function hiding (_$_)

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Convenience
open import Semantics.Concrete.DoublePoset.Constructions


open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_^_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum

open import Common.Common

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓA ℓ'A ℓ''A ℓA' ℓ'A' ℓ''A' : Level
    ℓB ℓ'B ℓ''B ℓB' ℓ'B' ℓ''B' : Level
    ℓC ℓ'C ℓ''C ℓC' ℓ'C' ℓ''C' ℓΓ ℓ'Γ ℓ''Γ : Level
    ℓD ℓ'D ℓ''D : Level
    Γ :  PosetBisim ℓΓ ℓ'Γ ℓ''Γ
    A :  PosetBisim ℓA ℓ'A ℓ''A
    A' : PosetBisim ℓA' ℓ'A' ℓ''A'
    B :  PosetBisim ℓB ℓ'B ℓ''B
    B' : PosetBisim ℓB' ℓ'B' ℓ''B'
    C :  PosetBisim ℓC ℓ'C ℓ''C
    C' : PosetBisim ℓC' ℓ'C' ℓ''C'
    D : PosetBisim ℓD ℓ'D ℓ''D
    ℓX : Level
    ℓ≤A ℓ≈A : Level
    ℓA₁  ℓ≤A₁  ℓ≈A₁  : Level
    ℓA₁' ℓ≤A₁' ℓ≈A₁' : Level
    ℓA₂  ℓ≤A₂  ℓ≈A₂  : Level
    ℓA₂' ℓ≤A₂' ℓ≈A₂' : Level
    ℓA₃  ℓ≤A₃  ℓ≈A₃  : Level

    
open PBMor
open import Semantics.Concrete.DoublePoset.DPMorProofs


mTransport : {A B : PosetBisim ℓ ℓ' ℓ''} -> (eq : A ≡ B) -> ⟨ A ==> B ⟩
mTransport {A} {B} eq = record {
  f = λ b → transport (λ i -> ⟨ eq i ⟩) b ;
  isMon = λ {b1} {b2} b1≤b2 → rel-transport-≤ eq b1≤b2 ;
  pres≈ = λ {b1} {b2} b1≈b2 → rel-transport-≈ eq b1≈b2 }

mTransportSym : {A B : PosetBisim ℓ ℓ' ℓ''} -> (eq : A ≡ B) -> ⟨ B ==> A ⟩
mTransportSym {A} {B} eq = record {
  f = λ b → transport (λ i -> ⟨ sym eq i ⟩) b ;
  isMon = λ {b1} {b2} b1≤b2 → rel-transport-≤ (sym eq) b1≤b2 ;
  pres≈ = λ {b1} {b2} b1≤b2 → rel-transport-≈ (sym eq) b1≤b2 }

mTransportDomain : {A B C : PosetBisim ℓ ℓ' ℓ''} ->
  (eq : A ≡ B) ->
  PBMor A C ->
  PBMor B C
mTransportDomain {A} {B} {C} eq f = record {
  f = g eq f ;
  isMon = mon-transport-domain-≤ eq f ;
  pres≈ = mon-transport-domain-≈ eq f  }
  where
    g : {A B C : PosetBisim ℓ ℓ' ℓ''} ->
      (eq : A ≡ B) ->
      PBMor A C ->
      ⟨ B ⟩ -> ⟨ C ⟩
    g eq f b = PBMor.f f (transport (λ i → ⟨ sym eq i ⟩ ) b)

        
mCompU : PBMor B C -> PBMor A B -> PBMor A C
mCompU f1 f2 = record {
  f = λ a -> f1 .f (f2 .f a) ;
  isMon = λ x≤y -> f1 .isMon (f2 .isMon x≤y) ;
  pres≈ = λ x≈y → f1 .pres≈ (f2 .pres≈ x≈y) }


mComp :
    ⟨ (B ==> C) ==> (A ==> B) ==> (A ==> C) ⟩
mComp = record {
  f = λ fBC → record {
    f = λ fAB → mCompU fBC fAB ;
    isMon = λ {f1} {f2} f1≤f2 -> λ a → isMon fBC (f1≤f2 a) ;
    pres≈ = λ {f1} {f2} f1≈f2 → λ a1 a2 a1≈a2 → pres≈ fBC (f1≈f2 a1 a2 a1≈a2) } ;
  isMon = λ {f1} {f2} f1≤f2 → λ f' a → f1≤f2 (PBMor.f f' a) ;
  pres≈ = λ {fBC} {fBC'} fBC≈fBC' fAB fAB' fAB≈fAB' a a' a≈a' →
    fBC≈fBC' _ _ (fAB≈fAB' a a' a≈a') }


Pair : ⟨ A ==> B ==> (A ×dp B) ⟩
Pair {A = A} {B = B} = record {
  f = λ a → record {
    f = λ b → a , b ;
    isMon = λ b1≤b2 → (reflexive-≤ A a) , b1≤b2 ;
    pres≈ = λ b1≈b2 → (reflexive-≈ A a) , b1≈b2 } ;
  isMon = λ {a1} {a2} a1≤a2 b → a1≤a2 , reflexive-≤ B b ;
  pres≈ = λ {a1} {a2} a1≈a2 b1 b2 b1≈b2 → a1≈a2 , b1≈b2 }

PairFun : (f : ⟨ A ==> B ⟩) -> (g : ⟨ A ==> C ⟩ ) -> ⟨ A ==> B ×dp C ⟩
PairFun f g = record {
  f = λ a -> (PBMor.f f a) , (PBMor.f g a) ;
  isMon = λ {a1} {a2} a1≤a2 → isMon f a1≤a2 , isMon g a1≤a2 ;
  pres≈ = λ {a1} {a2} a1≈a2 → (pres≈ f a1≈a2) , (pres≈ g a1≈a2) }

_×mor_ : ⟨ A ==> B ⟩ → ⟨ C ==> D ⟩ → ⟨ A ×dp C ==> B ×dp D ⟩
_×mor_ f g = PairFun (f ∘p π1) (g ∘p π2)

Case' : ⟨ A ==> C ⟩ -> ⟨ B ==> C ⟩ -> ⟨ (A ⊎p B) ==> C ⟩
Case' f g = record {
  f = λ { (inl a) → PBMor.f f a ; (inr b) → PBMor.f g b} ;
  isMon = λ { {inl a1} {inl a2} a1≤a2 → isMon f (lower a1≤a2) ;
              {inr b1} {inr b2} b1≤b2 → isMon g (lower b1≤b2) }  ;
  pres≈ = λ { {inl a1} {inl a2} a1≤a2 → pres≈ f (lower a1≤a2) ;
              {inr b1} {inr b2} b1≤b2 → pres≈ g (lower b1≤b2) } }

_⊎-mor_ :  ⟨ A ==> B ⟩ -> ⟨ C ==> D ⟩ -> ⟨ (A ⊎p C) ==> (B ⊎p D) ⟩
_⊎-mor_ f g = Case' (σ1 ∘p f) (σ2 ∘p g)

Case : ⟨ (A ==> C) ==> (B ==> C) ==> ((A ⊎p B) ==> C) ⟩
Case {C = C} = record {
  f = λ fAC → record {
    f = λ fBC → record {
      f = λ { (inl a) → f fAC a; (inr b) → f fBC b} ;
      isMon = λ { {inl a1} {inl a2} a1≤a2 → isMon fAC (lower a1≤a2) ;
                  {inr b1} {inr b2} b1≤b2 → isMon fBC (lower b1≤b2) };
      pres≈ = λ { {inl a1} {inl a2} a1≈a2 → pres≈ fAC (lower a1≈a2) ;
                  {inr b1} {inr b2} b1≈b2 → pres≈ fBC (lower b1≈b2) } } ;
    isMon = λ { {f1} {f2} f1≤f2 (inl a) → reflexive-≤ C (f fAC a) ;
                {f1} {f2} f1≤f2 (inr b) → f1≤f2 b } ;
    pres≈ = λ { {f1} {f2} f1≈f2 (inl a1) (inl a2) a1≈a2 → pres≈ fAC (lower a1≈a2) ;
                {f1} {f2} f1≈f2 (inr b1) (inr b2) b1≈b2 → f1≈f2 b1 b2 (lower b1≈b2) } } ;
  isMon = λ { {f1} {f2} f1≤f2 fBC (inl a) → f1≤f2 a ;
              {f1} {f2} f1≤f2 fBC (inr b) → reflexive-≤ C (f fBC b) } ;
  pres≈ = λ { {f1} {f2} f1≈f2 g1 g2 g1≈g2 (inl a1) (inl a2) a1≈a2 → f1≈f2 a1 a2 (lower a1≈a2) ;
              {f1} {f2} f1≈f2 g1 g2 g1≈g2 (inr b1) (inr b2) b1≈b2 → g1≈g2 b1 b2 (lower b1≈b2) } }

mSuc : ⟨ ℕ ==> ℕ ⟩
mSuc = record {
    f = suc ;
    isMon = λ {n1} {n2} n1≤n2 -> λ i -> suc (n1≤n2 i) ;
    pres≈ = λ {n1} {n2} n1≈n2 → λ i → suc (n1≈n2 i) }

U : ⟨ A ==> B ⟩ -> ⟨ A ⟩ -> ⟨ B ⟩
U f = PBMor.f f


S : (Γ : PosetBisim ℓΓ ℓ'Γ ℓ''Γ) ->
    ⟨ Γ ×dp A ==> B ⟩ -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> B ⟩
S Γ f g = record {
  f = λ γ → PBMor.f f (γ , (U g γ)) ;
  isMon = λ {γ1} {γ2} γ1≤γ2 ->
        isMon f (γ1≤γ2 , (isMon g γ1≤γ2)) ;
  pres≈ = λ {γ1} {γ2} γ1≈γ2 -> pres≈ f (γ1≈γ2 , pres≈ g γ1≈γ2) }

_!_<*>_ :
    (Γ : PosetBisim ℓ ℓ' ℓ'') -> ⟨ Γ ×dp A ==> B ⟩ -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> B ⟩
Γ ! f <*> g = S Γ f g

K : (Γ : PosetBisim ℓΓ ℓ'Γ ℓ''Γ) -> {A : PosetBisim ℓA ℓ'A ℓ''A} -> ⟨ A ⟩ -> ⟨ Γ ==> A ⟩
K _ {A} = λ a → record {
    f = λ γ → a ;
    isMon = λ {a1} {a2} a1≤a2 → reflexive-≤ A a ;
    pres≈ = λ {a1} {a2} a1≈a2 → reflexive-≈ A a }

-- Id : {A : PosetBisim ℓ ℓ' ℓ''} -> ⟨ A ==> A ⟩
-- Id = record {
--   f = id ;
--   isMon = λ x≤y → x≤y ;
--   pres≈ = λ x≈y → x≈y }


Curry :  ⟨ (Γ ×dp A) ==> B ⟩ -> ⟨ Γ ==> A ==> B ⟩
Curry {Γ = Γ} {A = A} g = record {
    f = λ γ →
      record {
        f = λ a → f g (γ , a) ;
        -- For a fixed γ, f as defined directly above is monotone
        isMon = λ {a} {a'} a≤a' → isMon g (reflexive-≤ Γ _ , a≤a') ;
        pres≈ = λ {a} {a'} a≈a' → pres≈ g (reflexive-≈ Γ _ , a≈a') } ;

    -- The outer f is monotone in γ
    isMon = λ {γ} {γ'} γ≤γ' → λ a -> isMon g (γ≤γ' , reflexive-≤ A a) ;
    pres≈ = λ {γ} {γ'} γ≈γ' → λ a1 a2 a1≈a2 -> pres≈ g (γ≈γ' , a1≈a2) }


Lambda :  ⟨ ((Γ ×dp A) ==> B) ==> (Γ ==> A ==> B) ⟩
Lambda {Γ = Γ} {A = A} = record {
  f = Curry {Γ = Γ} {A = A} ;
  isMon = λ {f1} {f2} f1≤f2 γ a → f1≤f2 (γ , a) ;
  pres≈ = λ {f1} {f2} f1≈f2 → λ γ γ' γ≈γ' a1 a2 a1≈a2 →
    f1≈f2 (γ , a1) (γ' , a2) (γ≈γ' , a1≈a2) }


Uncurry : ⟨ Γ ==> A ==> B ⟩ -> ⟨ (Γ ×dp A) ==> B ⟩
Uncurry f = record {
  f = λ (γ , a) → PBMor.f (PBMor.f f γ) a ;
  isMon = λ {(γ1 , a1)} {(γ2 , a2)} (γ1≤γ2 , a1≤a2) ->
      let fγ1≤fγ2 = isMon f γ1≤γ2 in 
        ≤mon→≤mon-het (PBMor.f f γ1) (PBMor.f f γ2) fγ1≤fγ2 a1 a2 a1≤a2 ;
  pres≈ = λ {(γ1 , a1)} {(γ2 , a2)} (γ1≈γ2 , a1≈a2) ->
      let fγ1≈fγ2 = pres≈ f γ1≈γ2 in
        fγ1≈fγ2 a1 a2 a1≈a2 }

App : ⟨ ((A ==> B) ×dp A) ==> B ⟩
App = Uncurry Id

Uncurry' : ⟨ (Γ ==> A ==> B)  ==> ((Γ ×dp A) ==> B) ⟩
Uncurry' = record {
  f = Uncurry ;
  isMon = λ { {f} {g} f≤g (γ , a) → f≤g γ a } ;
  pres≈ = λ { {f} {g} f≈g (γ , a) (γ' , a') (γ≈γ' , a≈a') → f≈g γ γ' γ≈γ' a a' a≈a' }}

{-
Swap : (Γ : PosetBisim ℓ ℓ' ℓ'') -> {A B : PosetBisim ℓ ℓ' ℓ''} -> ⟨ Γ ==> A ==> B ⟩ -> ⟨ A ==> Γ ==> B ⟩
Swap Γ {A = A} f = record {
  f = λ a → record {
    f = λ γ → PBMor.f (PBMor.f f γ) a ;
    isMon =  λ {γ1} {γ2} γ1≤γ2 ->
      let fγ1≤fγ2 = isMon f γ1≤γ2 in
        ≤mon→≤mon-het _ _ fγ1≤fγ2 a a (reflexive-≤ A a) ;
    pres≈ =  λ {γ1} {γ2} γ1≈γ2 ->
      let fγ1≈fγ2 = pres≈ f γ1≈γ2 in
        ≈mon→≈mon-het _ _ fγ1≈fγ2 a a (reflexive-≈ A a) } ;
  isMon = λ {a1} {a2} a1≤a2 -> λ γ → {!!} ;
  pres≈ = {!!} }
-}

SwapPair : ⟨ (A ×dp B) ==> (B ×dp A) ⟩
SwapPair = record {
  f = λ { (a , b) -> b , a } ;
  isMon = λ { {a1 , b1} {a2 , b2} (a1≤a2 , b1≤b2) → b1≤b2 , a1≤a2} ;
  pres≈ = λ { {a1 , b1} {a2 , b2} (a1≈a2 , b1≈b2) → b1≈b2 , a1≈a2 } }


With1st :
    ⟨ Γ ==> B ⟩ -> ⟨ Γ ×dp A ==> B ⟩
With1st {Γ = Γ} {A = A} f = mCompU f (π1 {A = Γ} {B = A})

With2nd :
    ⟨ A ==> B ⟩ -> ⟨ Γ ×dp A ==> B ⟩
With2nd {A = A} {Γ = Γ} f = mCompU f (π2 {A = Γ} {B = A})

IntroArg' :
    ⟨ Γ ==> B ⟩ -> ⟨ B ==> B' ⟩ -> ⟨ Γ ==> B' ⟩
IntroArg' {Γ = Γ} {B = B} {B' = B'} fΓB fBB' = S Γ (With2nd {A = B} {Γ = Γ} fBB') fΓB

IntroArg : {Γ B B' : PosetBisim ℓ ℓ' ℓ''} ->
  ⟨ B ==> B' ⟩ -> ⟨ (Γ ==> B) ==> (Γ ==> B') ⟩
IntroArg {Γ = Γ} {B = B} {B' = B'} f = (Curry {Γ = Γ ==> B} {A = Γ}) (mCompU f (App {A = Γ} {B = B}))

PairAssocLR :
  ⟨ A ×dp B ×dp C ==> A ×dp (B ×dp C) ⟩
PairAssocLR = record {
  f = λ { ((a , b) , c) → a , (b , c) } ;
  isMon = λ { {(a1 , b1) , c1} {(a2 , b2) , c2} ((a1≤a2 , b1≤b2) , c1≤c2) →
    a1≤a2 , (b1≤b2 , c1≤c2)} ;
  pres≈ = λ { {(a1 , b1) , c1} {(a2 , b2) , c2} ((a1≈a2 , b1≈b2) , c1≈c2) →
    a1≈a2 , (b1≈b2 , c1≈c2) }}

PairAssocRL :
 ⟨ A ×dp (B ×dp C) ==> A ×dp B ×dp C ⟩
PairAssocRL = record {
  f =  λ { (a , (b , c)) -> (a , b) , c } ;
  isMon = λ { {a1 , (b1 , c1)} {a2 , (b2 , c2)} (a1≤a2 , (b1≤b2 , c1≤c2)) →
    (a1≤a2 , b1≤b2) , c1≤c2} ;
  pres≈ =  λ { {a1 , (b1 , c1)} {a2 , (b2 , c2)} (a1≈a2 , (b1≈b2 , c1≈c2)) →
    (a1≈a2 , b1≈b2) , c1≈c2 } }

PairCong :
  ⟨ A ==> A' ⟩ -> ⟨ (Γ ×dp A) ==> (Γ ×dp A') ⟩
PairCong f = record {
  f = λ { (γ , a) → γ , (f $ a)} ;
  isMon = λ { {γ1 , a1} {γ2 , a2} (γ1≤γ2 , a1≤a2) → γ1≤γ2 , isMon f a1≤a2 }  ;
  pres≈ = λ { {γ1 , a1} {γ2 , a2} (γ1≈γ2 , a1≈a2) → γ1≈γ2 , pres≈ f a1≈a2 } }

TransformDomain :
    ⟨ Γ ×dp A ==> B ⟩ ->
    ⟨ ( A ==> B ) ==> ( A' ==> B ) ⟩ ->
    ⟨ Γ ×dp A' ==> B ⟩
TransformDomain {Γ = Γ} {A = A} fΓ×A->B f =
  Uncurry (IntroArg' (Curry {Γ = Γ} {A = A} fΓ×A->B) f)

mComp' : (Γ : PosetBisim ℓΓ ℓ'Γ ℓ''Γ) ->
    ⟨ (Γ ×dp B ==> C) ⟩ -> ⟨ (Γ ×dp A ==> B) ⟩ -> ⟨ (Γ ×dp A ==> C) ⟩
mComp' {B = B} {C = C} {A = A} Γ f g = record {
  f = λ { (γ , a) → PBMor.f f (γ , (PBMor.f g (γ , a))) } ;
  isMon = λ { {γ1 , a1} {γ2 , a2} (γ1≤γ2 , a1≤a2) →
    isMon f (γ1≤γ2 , (isMon g (γ1≤γ2 , a1≤a2))) } ;
  pres≈ = λ { {γ1 , a1} {γ2 , a2} (γ1≈γ2 , a1≈a2) →
    pres≈ f (γ1≈γ2 , (pres≈ g (γ1≈γ2 , a1≈a2))) } }

_∘m_ :
   ⟨ (Γ ×dp B ==> C) ⟩ -> ⟨ (Γ ×dp A ==> B) ⟩ -> ⟨ (Γ ×dp A ==> C) ⟩
_∘m_ {Γ = Γ} {B = B} {C = C} {A = A} = mComp' {B = B} {C = C} {A = A} Γ

_∘p'_ = _∘m_
infixl 20 _∘p'_

_$_∘m_ :  (Γ : PosetBisim ℓ ℓ' ℓ'') -> {A B C : PosetBisim ℓ ℓ' ℓ''} ->
    ⟨ (Γ ×dp B ==> C) ⟩ -> ⟨ (Γ ×dp A ==> B) ⟩ -> ⟨ (Γ ×dp A ==> C) ⟩
_$_∘m_ Γ {A = A} {B = B} {C = C} f g = mComp' {B = B} {C = C} {A = A} Γ f g
infixl 20 _∘m_

-- Comp : (Γ : PosetBisim ℓ ℓ' ℓ'') -> {A B C : PosetBisim ℓ ℓ' ℓ''} ->
--     ⟨ Γ ×dp B ==> C ⟩ -> ⟨ Γ ×dp A ==> B ⟩ -> ⟨ Γ ×dp A ==> C ⟩
-- Comp Γ f g = {!!}

_~->_ : {A : PosetBisim ℓA ℓ'A ℓ''A} {B : PosetBisim ℓB ℓ'B ℓ''B}
        {C : PosetBisim ℓC ℓ'C ℓ''C} {D : PosetBisim ℓD ℓ'D ℓ''D} ->
    ⟨ A ==> B ⟩ -> ⟨ C ==> D ⟩ -> ⟨ (B ==> C) ==> (A ==> D) ⟩
_~->_ {A = A} {B = B} {C = C} {D = D} pre post =
  Curry {Γ = B ==> C} {A = A} {B = D} ((mCompU post App) ∘m (With2nd pre))

_^m_ : ⟨ A ==> A ⟩ -> Nat -> ⟨ A ==> A ⟩
g ^m n = record {
  f = fun n ;
  isMon = mon n ;
  pres≈ = pres n }
  where
    fun : Nat -> _
    fun m = (PBMor.f g) ^ m

    mon : (m : Nat) -> monotone (fun m)
    mon zero {x} {y} x≤y = x≤y
    mon (suc m) {x} {y} x≤y = isMon g (mon m x≤y)

    pres : (m : Nat) -> preserve≈ (fun m)
    pres zero {x} {y} x≈y = x≈y
    pres (suc m) {x} {y} x≈y = pres≈ g (pres m x≈y)


module ClockedCombinators (k : Clock) where
  private
    ▹_ : Type ℓ → Type ℓ
    ▹_ A = ▹_,_ k A

  -- open import Semantics.Lift k
  -- open ClockedConstructions k
  -- open import Semantics.Concrete.MonotonicityProofs
  -- open import Semantics.LockStepErrorOrdering k
  -- open import Semantics.Concrete.DoublePoset.LockStepErrorBisim k
  -- open import Semantics.WeakBisimilarity k


  -- open LiftPosetBisim
  open ClockedProofs k
  open Clocked k

  Map▹ :
    ⟨ A ==> B ⟩ -> ⟨ (PB▹ A) ==> (PB▹ B) ⟩
  Map▹ {A} {B} f = record {
    f = map▹ (PBMor.f f) ;
    isMon = λ {a1} {a2} a1≤a2 t → isMon f (a1≤a2 t) ;
    pres≈ = λ {a1} {a2} a1≈a2 t → pres≈ f (a1≈a2 t) }


  Ap▹ :
    ⟨ (PB▹ (A ==> B)) ==> ((PB▹ A) ==> (PB▹ B)) ⟩
  Ap▹ {A = A} {B = B} = record {
    f = UAp▹ ;
    isMon = UAp▹-mon ;
    pres≈ = UAp▹-pres≈}
    where
      UAp▹ :
        ⟨ (PB▹ (A ==> B)) ⟩ -> ⟨ (PB▹ A) ==> (PB▹ B) ⟩
      UAp▹ f~ = record {
        f = _⊛_ (λ t → PBMor.f (f~ t)) ;
        isMon = λ {a1} {a2} a1≤a2 t → isMon (f~ t) (a1≤a2 t) ;
        pres≈ = λ {a1} {a2} a1≈a2 t → pres≈ (f~ t) (a1≈a2 t) }

      UAp▹-mon : {f1~ f2~ : ▹ ⟨ A ==> B ⟩} ->
        ▸ (λ t -> rel-≤ (A ==> B) (f1~ t) (f2~ t)) ->
        rel-≤ ((PB▹ A) ==> (PB▹ B)) (UAp▹ f1~) (UAp▹ f2~)
      UAp▹-mon {f1~} {f2~} f1~≤f2~ a~ t = f1~≤f2~ t (a~ t)

      UAp▹-pres≈ : {f1~ f2~ : ▹ ⟨ A ==> B ⟩} ->
        ▸ (λ t -> rel-≈ (A ==> B) (f1~ t) (f2~ t)) ->
        rel-≈ ((PB▹ A) ==> (PB▹ B)) (UAp▹ f1~) (UAp▹ f2~)
      UAp▹-pres≈ {f1~} {f2~} f1~≈f2~ a1~ a2~ a1~≈a2~ t =
        f1~≈f2~ t (a1~ t) (a2~ t) (a1~≈a2~ t)

  Next : {A : PosetBisim ℓ ℓ' ℓ''} -> ⟨ A ==> PB▹ A ⟩
  Next = record {
    f = next ;
    isMon = λ {a1} {a2} a1≤a2 t → a1≤a2 ;
    pres≈ = λ {a1} {a2} a1≈a2 t → a1≈a2 }

{-
  mθ : {A : PosetBisim ℓ ℓ' ℓ''} ->
    ⟨ (PB▹ (𝕃 A)) ==> 𝕃 A ⟩
  mθ {A = A} = record { f = θ ; isMon = ord-θ-monotone A ; pres≈ = λ x → {!!} }

  -- 𝕃's return as a monotone function
  mRet : {A : PosetBisim ℓ ℓ' ℓ''} -> ⟨ A ==> 𝕃 A ⟩
  mRet {A = A} = record { f = ret ; isMon = ord-η-monotone A ; pres≈ = λ x → {!!} }
    where
      open Bisim ⟨ A ⊎p UnitPB ⟩ (rel-≈ (A ⊎p UnitPB))

  Δ : {A : PosetBisim ℓ ℓ' ℓ''} -> ⟨ 𝕃 A ==> 𝕃 A ⟩
  Δ {A = A} = record {
      f = δ ;
      isMon = λ x≤y → ord-δ-monotone A x≤y ;
      pres≈ = {!!} }

  mExtU : PBMor A (𝕃 B) -> PBMor (𝕃 A) (𝕃 B)
  mExtU f = record {
      f = λ la -> bind la (PBMor.f f) ;
      isMon = monotone-bind-mon-≤ f ;
      pres≈ = monotone-bind-mon-≈ f }

  mExt : ⟨ (A ==> 𝕃 B) ==> (𝕃 A ==> 𝕃 B) ⟩
  mExt {A = A} = record {
      f = mExtU ;
      isMon = λ {f1} {f2} f1≤f2 la →
        ext-monotone-≤ (PBMor.f f1) (PBMor.f f2)
          (≤mon→≤mon-het f1 f2 f1≤f2) la la (reflexive-≤ (𝕃 A) la) ;
      pres≈ = λ {f1} {f2} f1≈f2 la la' la≈la' →
        ext-monotone-≈ (PBMor.f f1) (PBMor.f f2) f1≈f2 la la' la≈la' }

  mExt' : (Γ : PosetBisim ℓ ℓ' ℓ'') ->
      ⟨ (Γ ×dp A ==> 𝕃 B) ⟩ -> ⟨ (Γ ×dp 𝕃 A ==> 𝕃 B) ⟩
  mExt' Γ f = TransformDomain f mExt

  mRet' : (Γ : PosetBisim ℓ ℓ' ℓ'') -> { A : PosetBisim ℓ ℓ' ℓ''} -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> 𝕃 A ⟩
  mRet' Γ f = record {
    f = λ γ -> ret (PBMor.f f γ) ;
    isMon = λ {γ1} {γ2} γ1≤γ2 → ret-monotone-≤ (PBMor.f f γ1) (PBMor.f f γ2) (isMon f γ1≤γ2);
    pres≈ = λ {γ1} {γ2} γ1≈γ2 → ret-monotone-≈ (PBMor.f f γ1) (PBMor.f f γ2) (pres≈ f γ1≈γ2)} -- _ ! K _ mRet <*> a

  Bind : (Γ : PosetBisim ℓ ℓ' ℓ'') ->
      ⟨ Γ ==> 𝕃 A ⟩ -> ⟨ Γ ×dp A ==> 𝕃 B ⟩ -> ⟨ Γ ==> 𝕃 B ⟩
  Bind Γ la f = S Γ (mExt' Γ f) la

  -- Mapping a monotone function
  mMap : ⟨ (A ==> B) ==> (𝕃 A ==> 𝕃 B) ⟩
  mMap {A = A} {B = B} = Curry (mExt' (A ==> B) ((With2nd mRet) ∘m App))

  mMap' :
      ⟨ (Γ ×dp A ==> B) ⟩ -> ⟨ (Γ ×dp 𝕃 A ==> 𝕃 B) ⟩
  mMap' f = record {
    f = λ { (γ , la) -> mapL (λ a -> PBMor.f f (γ , a)) la} ;
    isMon = λ { {γ , la} {γ' , la'} (γ≤γ' , la≤la') → {!!} } ;
    pres≈ = {!!} }

  Map :
      ⟨ (Γ ×dp A ==> B) ⟩ -> ⟨ (Γ ==> 𝕃 A) ⟩ -> ⟨ (Γ ==> 𝕃 B) ⟩
  Map {Γ = Γ} f la = S Γ (mMap' f) la -- Γ ! mMap' f <*> la


    -- Embedding of function spaces is monotone
  mFunEmb : (A A' B B' : PosetBisim ℓ ℓ' ℓ'') ->
      ⟨ A' ==> 𝕃 A ⟩ ->
      ⟨ B ==> B' ⟩ ->
      ⟨ (A ==> 𝕃 B) ==> (A' ==> 𝕃 B') ⟩
  mFunEmb A A' B B' fA'LA fBB' =
      Curry (Bind ((A ==> 𝕃 B) ×dp A')
        (mCompU fA'LA π2)
        (Map (mCompU fBB' π2) ({!!})))
    --  _ $ (mExt' _ (_ $ (mMap' (K _ fBB')) ∘m Id)) ∘m (K _ fA'LA)
    -- mComp' (mExt' (mComp' (mMap' (K fBB')) Id)) (K fA'LA)

  mFunProj : (A A' B B' : PosetBisim ℓ ℓ' ℓ'') ->
     ⟨ A ==> A' ⟩ ->
     ⟨ B' ==> 𝕃 B ⟩ ->
     ⟨ (A' ==> 𝕃 B') ==> 𝕃 (A ==> 𝕃 B) ⟩
  mFunProj A A' B B' fAA' fB'LB = {!!}
    -- mRet' (mExt' (K fB'LB) ∘m Id ∘m (K fAA'))
-}


module _
  (X : hSet ℓX) where
  
  isoSigmaUnit : PredomIso (ΣP X (λ _ → UnitPB)) (flat X)
  isoSigmaUnit .PredomIso.fun = Σ-elim (λ x → K _ x)
  isoSigmaUnit .PredomIso.inv = flatRec X _ (λ x → x , tt)
  isoSigmaUnit .PredomIso.invRight x = refl
  isoSigmaUnit .PredomIso.invLeft (x , tt) = refl

-- module _ {ℓ ℓ≤ ℓ≈ : Level} where
--   isoPiBot : PredomIso {ℓA = ℓ} (ΠP ⊥ {ℓ = ℓ} {ℓ≤ = ℓ≤} {ℓ≈ = ℓ≈} ⊥.rec) UnitPB
--   isoPiBot .PredomIso.fun = UnitPB!
--   isoPiBot .PredomIso.inv = recUnitPB (λ x → ⊥.rec x)
--   isoPiBot .PredomIso.invRight tt = refl
--   isoPiBot .PredomIso.invLeft a = funExt (λ bot → ⊥.rec bot)

module _ {ℓ ℓ≤ ℓ≈ : Level} {A : PosetBisim ℓA ℓ≤A ℓ≈A} where
  isoPiBot : PredomIso (ΠP ⊥ (λ _ → A)) UnitPB
  isoPiBot .PredomIso.fun = UnitPB!
  isoPiBot .PredomIso.inv = recUnitPB (λ x → ⊥.rec x)
  isoPiBot .PredomIso.invRight tt = refl
  isoPiBot .PredomIso.invLeft a = funExt (λ bot → ⊥.rec bot)


idPredomIso : {A : PosetBisim ℓA ℓ≤A ℓ≈A} → PredomIso A A
idPredomIso .PredomIso.fun = Id
idPredomIso .PredomIso.inv = Id
idPredomIso .PredomIso.invRight _ = refl
idPredomIso .PredomIso.invLeft _ = refl


module _
  {A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : PosetBisim ℓA₁' ℓ≤A₁' ℓ≈A₁'}
  {A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : PosetBisim ℓA₂' ℓ≤A₂' ℓ≈A₂'}
  (iso₁ : PredomIso A₁ A₁') (iso₂ : PredomIso A₂ A₂')
  where

  ×-PredomIso : PredomIso (A₁ ×dp A₂) (A₁' ×dp A₂')
  ×-PredomIso .PredomIso.fun = iso₁ .PredomIso.fun ×mor iso₂ .PredomIso.fun
  ×-PredomIso .PredomIso.inv = iso₁ .PredomIso.inv ×mor iso₂ .PredomIso.inv
  ×-PredomIso .PredomIso.invRight (x , y) = ≡-× (iso₁ .PredomIso.invRight x) (iso₂ .PredomIso.invRight y)
  ×-PredomIso .PredomIso.invLeft (x , y)  = ≡-× (iso₁ .PredomIso.invLeft x) (iso₂ .PredomIso.invLeft y)
  

module _
  (X : hSet ℓX)
  (A₁ : ⟨ X ⟩ → PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁)
  (A₂ : ⟨ X ⟩ → PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂)
  (isom : ((x : ⟨ X ⟩) → PredomIso (A₁ x) (A₂ x)))
  where

  ΣP-cong-iso-snd : PredomIso (ΣP X A₁) (ΣP X A₂)
  ΣP-cong-iso-snd .PredomIso.fun = Σ-mor X A₁ A₂ (PredomIso.fun ∘ isom)
  ΣP-cong-iso-snd .PredomIso.inv = Σ-mor X A₂ A₁ (PredomIso.inv ∘ isom)
  ΣP-cong-iso-snd .PredomIso.invRight (x , a₂) = ΣPathP (refl , (PredomIso.invRight (isom x) a₂))
  ΣP-cong-iso-snd .PredomIso.invLeft (x , a₁) = ΣPathP (refl , (PredomIso.invLeft (isom x) a₁))

module _
  (X : Type ℓ)
  (A₁ : X → PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁)
  (A₂ : X → PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂)
  (isom : ((x : X) → PredomIso (A₁ x) (A₂ x)))
  where

  ΠP-iso : PredomIso (ΠP X A₁) (ΠP X A₂)
  ΠP-iso .PredomIso.fun = Π-mor X A₁ A₂ (PredomIso.fun ∘ isom)
  ΠP-iso .PredomIso.inv = Π-mor X A₂ A₁ (PredomIso.inv ∘ isom)
  ΠP-iso .PredomIso.invRight as = funExt (λ x → PredomIso.invRight (isom x) (as x))
  ΠP-iso .PredomIso.invLeft as = funExt (λ x → PredomIso.invLeft (isom x) (as x))

module _
  {A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁}
  {A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂}
  {A₃ : PosetBisim ℓA₃ ℓ≤A₃ ℓ≈A₃}
  (f : PredomIso A₁ A₂)
  (g : PredomIso A₂ A₃)
  where

  compPredomIso : PredomIso A₁ A₃
  compPredomIso .PredomIso.fun = PredomIso.fun g ∘p PredomIso.fun f
  compPredomIso .PredomIso.inv = PredomIso.inv f ∘p PredomIso.inv g
  compPredomIso .PredomIso.invRight x =
    cong (PBMor.f (PredomIso.fun g)) (PredomIso.invRight f _) ∙ PredomIso.invRight g x
  compPredomIso .PredomIso.invLeft x =
    cong (PBMor.f (PredomIso.inv f)) (PredomIso.invLeft g _) ∙ PredomIso.invLeft f x
