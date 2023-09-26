{-# OPTIONS --guarded --rewriting #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.DoublePoset.DblPosetCombinators where

open import Cubical.Relation.Binary
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function hiding (_$_)

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Convenience
open import Semantics.Concrete.DoublePoset.Constructions

open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_^_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Sum

open import Common.Common

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓA ℓ'A ℓ''A ℓA' ℓ'A' ℓ''A' : Level
    ℓB ℓ'B ℓ''B ℓB' ℓ'B' ℓ''B' : Level
    ℓC ℓ'C ℓ''C ℓC' ℓ'C' ℓ''C' ℓΓ ℓ'Γ ℓ''Γ : Level
    Γ :  DoublePoset ℓΓ ℓ'Γ ℓ''Γ
    A :  DoublePoset ℓA ℓ'A ℓ''A
    A' : DoublePoset ℓA' ℓ'A' ℓ''A'
    B :  DoublePoset ℓB ℓ'B ℓ''B
    B' : DoublePoset ℓB' ℓ'B' ℓ''B'
    C :  DoublePoset ℓC ℓ'C ℓ''C
    C' : DoublePoset ℓC' ℓ'C' ℓ''C'
    
open DPMor


mTransport : {A B : DoublePoset ℓ ℓ' ℓ''} -> (eq : A ≡ B) -> ⟨ A ==> B ⟩
mTransport {A} {B} eq = record {
  f = λ b → transport (λ i -> ⟨ eq i ⟩) b ;
  isMon = λ {b1} {b2} b1≤b2 → {!!} ;
  pres≈ = λ {b1} {b2} b1≈b2 → {!!} }

mTransportDomain : {A B C : DoublePoset ℓ ℓ' ℓ''} ->
  (eq : A ≡ B) ->
  DPMor A C ->
  DPMor B C
mTransportDomain {A} {B} {C} eq f = record {
  f = g eq f ;
  isMon = {!!} ;
  pres≈ = {!!}  }
  where
    g : {A B C : DoublePoset ℓ ℓ' ℓ''} ->
      (eq : A ≡ B) ->
      DPMor A C ->
      ⟨ B ⟩ -> ⟨ C ⟩
    g eq f b = DPMor.f f (transport (λ i → ⟨ sym eq i ⟩ ) b)


mCompU : DPMor B C -> DPMor A B -> DPMor A C
mCompU f1 f2 = record {
  f = λ a -> f1 .f (f2 .f a) ;
  isMon = λ x≤y -> f1 .isMon (f2 .isMon x≤y) ;
  pres≈ = λ x≈y → f1 .pres≈ (f2 .pres≈ x≈y) }

{-
mComp :
    ⟨ (B ==> C) ==> (A ==> B) ==> (A ==> C) ⟩
mComp = record {
  f = λ fBC → record {
    f = λ fAB → mCompU fBC fAB ;
    isMon = λ {f1} {f2} f1≤f2 -> λ a → isMon fBC (f1≤f2 a) ;
    pres≈ = λ {f1} {f2} f1≈f2 → λ a → pres≈ {!!} {!!} } ;
  isMon = λ {f1} {f2} f1≤f2 → λ f' a → f1≤f2 (DPMor.f f' a) ;
  pres≈ = λ {f1} {f2} f1≈f2 → λ f' a' → {!f1≈f2!} }
-}

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
  f = λ a -> (DPMor.f f a) , (DPMor.f g a) ;
  isMon = λ {a1} {a2} a1≤a2 → isMon f a1≤a2 , isMon g a1≤a2 ;
  pres≈ = λ {a1} {a2} a1≈a2 → (pres≈ f a1≈a2) , (pres≈ g a1≈a2) }

Case' : ⟨ A ==> C ⟩ -> ⟨ B ==> C ⟩ -> ⟨ (A ⊎p B) ==> C ⟩
Case' f g = record {
  f = λ { (inl a) → DPMor.f f a ; (inr b) → DPMor.f g b} ;
  isMon = λ { {inl a1} {inl a2} a1≤a2 → isMon f (lower a1≤a2) ;
              {inr b1} {inr b2} b1≤b2 → isMon g (lower b1≤b2) }  ;
  pres≈ = λ { {inl a1} {inl a2} a1≤a2 → pres≈ f (lower a1≤a2) ;
              {inr b1} {inr b2} b1≤b2 → pres≈ g (lower b1≤b2) } }


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
U f = DPMor.f f


S : (Γ : DoublePoset ℓΓ ℓ'Γ ℓ''Γ) ->
    ⟨ Γ ×dp A ==> B ⟩ -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> B ⟩
S Γ f g = record {
  f = λ γ → DPMor.f f (γ , (U g γ)) ;
  isMon = λ {γ1} {γ2} γ1≤γ2 ->
        isMon f (γ1≤γ2 , (isMon g γ1≤γ2)) ;
  pres≈ = λ {γ1} {γ2} γ1≈γ2 -> pres≈ f (γ1≈γ2 , pres≈ g γ1≈γ2) }

_!_<*>_ :
    (Γ : DoublePoset ℓ ℓ' ℓ'') -> ⟨ Γ ×dp A ==> B ⟩ -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> B ⟩
Γ ! f <*> g = S Γ f g

K : (Γ : DoublePoset ℓΓ ℓ'Γ ℓ''Γ) -> {A : DoublePoset ℓA ℓ'A ℓ''A} -> ⟨ A ⟩ -> ⟨ Γ ==> A ⟩
K _ {A} = λ a → record {
    f = λ γ → a ;
    isMon = λ {a1} {a2} a1≤a2 → reflexive-≤ A a ;
    pres≈ = λ {a1} {a2} a1≈a2 → reflexive-≈ A a }

Id : {A : DoublePoset ℓ ℓ' ℓ''} -> ⟨ A ==> A ⟩
Id = record {
  f = id ;
  isMon = λ x≤y → x≤y ;
  pres≈ = λ x≈y → x≈y }


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
  f = λ (γ , a) → DPMor.f (DPMor.f f γ) a ;
  isMon = λ {(γ1 , a1)} {(γ2 , a2)} (γ1≤γ2 , a1≤a2) ->
      let fγ1≤fγ2 = isMon f γ1≤γ2 in 
        ≤mon→≤mon-het (DPMor.f f γ1) (DPMor.f f γ2) fγ1≤fγ2 a1 a2 a1≤a2 ;
  pres≈ = λ {(γ1 , a1)} {(γ2 , a2)} (γ1≈γ2 , a1≈a2) ->
      let fγ1≈fγ2 = pres≈ f γ1≈γ2 in
        ≈mon→≈mon-het (DPMor.f f γ1) (DPMor.f f γ2) fγ1≈fγ2 a1 a2 a1≈a2 }

App : ⟨ ((A ==> B) ×dp A) ==> B ⟩
App = Uncurry Id

-- very slow
{-
Swap : (Γ : DoublePoset ℓ ℓ' ℓ'') -> {A B : DoublePoset ℓ ℓ' ℓ''} -> ⟨ Γ ==> A ==> B ⟩ -> ⟨ A ==> Γ ==> B ⟩
Swap Γ {A = A} f = record {
  f = λ a → record {
    f = λ γ → DPMor.f (DPMor.f f γ) a ;
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

IntroArg : {Γ B B' : DoublePoset ℓ ℓ' ℓ''} ->
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

mComp' : (Γ : DoublePoset ℓΓ ℓ'Γ ℓ''Γ) ->
    ⟨ (Γ ×dp B ==> C) ⟩ -> ⟨ (Γ ×dp A ==> B) ⟩ -> ⟨ (Γ ×dp A ==> C) ⟩
mComp' {B = B} {C = C} {A = A} Γ f g = record {
  f = λ { (γ , a) → DPMor.f f (γ , (DPMor.f g (γ , a))) } ;
  isMon = λ { {γ1 , a1} {γ2 , a2} (γ1≤γ2 , a1≤a2) →
    isMon f (γ1≤γ2 , (isMon g (γ1≤γ2 , a1≤a2))) } ;
  pres≈ = λ { {γ1 , a1} {γ2 , a2} (γ1≈γ2 , a1≈a2) →
    pres≈ f (γ1≈γ2 , (pres≈ g (γ1≈γ2 , a1≈a2))) } }

_∘m_ :
   ⟨ (Γ ×dp B ==> C) ⟩ -> ⟨ (Γ ×dp A ==> B) ⟩ -> ⟨ (Γ ×dp A ==> C) ⟩
_∘m_ {Γ = Γ} {B = B} {C = C} {A = A} = mComp' {B = B} {C = C} {A = A} Γ

_$_∘m_ :  (Γ : DoublePoset ℓ ℓ' ℓ'') -> {A B C : DoublePoset ℓ ℓ' ℓ''} ->
    ⟨ (Γ ×dp B ==> C) ⟩ -> ⟨ (Γ ×dp A ==> B) ⟩ -> ⟨ (Γ ×dp A ==> C) ⟩
_$_∘m_ Γ {A = A} {B = B} {C = C} f g = mComp' {B = B} {C = C} {A = A} Γ f g
infixl 20 _∘m_

Comp : (Γ : DoublePoset ℓ ℓ' ℓ'') -> {A B C : DoublePoset ℓ ℓ' ℓ''} ->
    ⟨ Γ ×dp B ==> C ⟩ -> ⟨ Γ ×dp A ==> B ⟩ -> ⟨ Γ ×dp A ==> C ⟩
Comp Γ f g = {!!}

_~->_ : {A B C D : DoublePoset ℓ ℓ' ℓ''} ->
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
    fun m = (DPMor.f g) ^ m

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

  open import Semantics.Lift k
  open ClockedConstructions k
  -- open import Semantics.Concrete.MonotonicityProofs
  -- open import Semantics.LockStepErrorOrdering k


  -- open LiftPoset
  -- open ClockedProofs k

  Map▹ :
    ⟨ A ==> B ⟩ -> ⟨ DP▸'_ A ==> DP▸'_ B ⟩
  Map▹ {A} {B} f = record {
    f = map▹ (DPMor.f f) ;
    isMon = λ {a1} {a2} a1≤a2 t → isMon f (a1≤a2 t) ;
    pres≈ = λ {a1} {a2} a1≈a2 t → pres≈ f (a1≈a2 t) }

  Ap▹ :
    ⟨ (DP▸'_ (A ==> B)) ==> (DP▸'_ A ==> DP▸'_ B) ⟩
  Ap▹ {A = A} {B = B} = record {
    f = UAp▹ ;
    isMon = UAp▹-mon ;
    pres≈ = UAp▹-pres≈}
    where
      UAp▹ :
        ⟨ (DP▸'_ (A ==> B)) ⟩ -> ⟨ (DP▸'_ A ==> DP▸'_ B) ⟩
      UAp▹ f~ = record {
        f = _⊛_ (λ t → DPMor.f (f~ t)) ;
        isMon = λ {a1} {a2} a1≤a2 t → isMon (f~ t) (a1≤a2 t) ;
        pres≈ = λ {a1} {a2} a1≈a2 t → pres≈ (f~ t) (a1≈a2 t) }

      UAp▹-mon : {f1~ f2~ : ▹ ⟨ A ==> B ⟩} ->
        ▸ (λ t -> rel-≤ (A ==> B) (f1~ t) (f2~ t)) ->
        rel-≤ ((DP▸'_ A) ==> (DP▸'_ B)) (UAp▹ f1~) (UAp▹ f2~)
      UAp▹-mon {f1~} {f2~} f1~≤f2~ a~ t = f1~≤f2~ t (a~ t)

      UAp▹-pres≈ : {f1~ f2~ : ▹ ⟨ A ==> B ⟩} ->
        ▸ (λ t -> rel-≈ (A ==> B) (f1~ t) (f2~ t)) ->
        rel-≈ ((DP▸'_ A) ==> (DP▸'_ B)) (UAp▹ f1~) (UAp▹ f2~)
      UAp▹-pres≈ {f1~} {f2~} f1~≈f2~ a1~ a2~ a1~≈a2~ t =
        f1~≈f2~ t (a1~ t) (a2~ t) (a1~≈a2~ t)

  Next : {A : DoublePoset ℓ ℓ' ℓ''} -> ⟨ A ==> DP▸'_ A ⟩
  Next = record {
    f = next ;
    isMon = λ {a1} {a2} a1≤a2 t → a1≤a2 ;
    pres≈ = λ {a1} {a2} a1≈a2 t → a1≈a2 }

