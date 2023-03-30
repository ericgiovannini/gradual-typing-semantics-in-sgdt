{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Common.MonFuns (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat renaming (ℕ to Nat)

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Data.Unit
-- open import Cubical.Data.Prod
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.Foundations.Function

open import Common.Common
open import Semantics.StrongBisimulation k
open import Syntax.GradualSTLC
open import Syntax.SyntacticTermPrecision k
open import Common.Lemmas k


private
  variable
    l : Level
    A B : Set l
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A

open MonFun

open LiftPredomain

-- abstract

-- Composing monotone functions
mCompU : {A B C : Predomain} -> MonFun B C -> MonFun A B -> MonFun A C
mCompU f1 f2 = record {
    f = λ a -> f1 .f (f2 .f a) ;
    isMon = λ x≤y -> f1 .isMon (f2 .isMon x≤y) }
  where open MonFun

mComp : {A B C : Predomain} ->
    -- MonFun (arr' B C) (arr' (arr' A B) (arr' A C))
    ⟨ (B ==> C) ==> (A ==> B) ==> (A ==> C) ⟩
mComp = record {
    f = λ fBC →
      record {
        f = λ fAB → mCompU fBC fAB ;
        isMon = λ {f1} {f2} f1≤f2 ->
          λ a1 a2 a1≤a2 → MonFun.isMon fBC (f1≤f2 a1 a2 a1≤a2) } ;
    isMon = λ {f1} {f2} f1≤f2 →
      λ fAB1 fAB2 fAB1≤fAB2 →
        λ a1 a2 a1≤a2 ->
          f1≤f2 (MonFun.f fAB1 a1) (MonFun.f fAB2 a2)
            (fAB1≤fAB2 a1 a2 a1≤a2) }
     


  -- 𝕃's return as a monotone function
mRet : {A : Predomain} -> ⟨ A ==> 𝕃 A ⟩
mRet {A} = record { f = ret ; isMon = ord-η-monotone A }


  -- Delay as a monotone function
Δ : {A : Predomain} -> ⟨ 𝕃 A ==> 𝕃 A ⟩
Δ {A} = record { f = δ ; isMon = λ x≤y → ord-δ-monotone A x≤y }

  -- Lifting a monotone function functorially
_~->_ : {A B C D : Predomain} ->
    ⟨ A ==> B ⟩ -> ⟨ C ==> D ⟩ -> ⟨ (B ==> C) ==> (A ==> D) ⟩
pre ~-> post = {!!}
  -- λ f -> mCompU post (mCompU f pre)


  -- Extending a monotone function to 𝕃
mExtU : {A B : Predomain} -> MonFun A (𝕃 B) -> MonFun (𝕃 A) (𝕃 B)
mExtU f = record {
    f = λ la -> bind la (MonFun.f f) ;
    isMon = monotone-bind-mon f }

mExt : {A B : Predomain} -> ⟨ (A ==> 𝕃 B) ==> (𝕃 A ==> 𝕃 B) ⟩
mExt = record {
    f = mExtU ;
    isMon = λ {f1} {f2} f1≤f2 -> ext-monotone (MonFun.f f1) (MonFun.f f2) f1≤f2 }
     
  -- mBind : ⟨ 𝕃 A ==> (A ==> 𝕃 B) ==> 𝕃 B ⟩

  -- Monotone successor function
mSuc : ⟨ ℕ ==> ℕ ⟩
mSuc = record {
    f = suc ;
    isMon = λ {n1} {n2} n1≤n2 -> λ i -> suc (n1≤n2 i) }


  -- Combinators

U : {A B : Predomain} -> ⟨ A ==> B ⟩ -> ⟨ A ⟩ -> ⟨ B ⟩
U f = MonFun.f f

_$_ : {A B : Predomain} -> ⟨ A ==> B ⟩ -> ⟨ A ⟩ -> ⟨ B ⟩
_$_ = U

S : (Γ : Predomain) -> {A B : Predomain} ->
    ⟨ Γ ×d A ==> B ⟩ -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> B ⟩
S Γ f g =
    record {
      f = λ γ -> MonFun.f f (γ , (U g γ)) ;
      isMon = λ {γ1} {γ2} γ1≤γ2 ->
        MonFun.isMon f (γ1≤γ2 , (MonFun.isMon g γ1≤γ2)) }

  {- λ {γ1} {γ2} γ1≤γ2 →
        let fγ1≤fγ2 = MonFun.isMon f γ1≤γ2 in
          fγ1≤fγ2 (MonFun.f g γ1) (MonFun.f g γ2) (MonFun.isMon g γ1≤γ2) } -}


_!_<*>_ : {A B : Predomain} ->
    (Γ : Predomain) -> ⟨ Γ ×d A ==> B ⟩ -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> B ⟩
Γ ! f <*> g = S Γ f g

infixl 20 _<*>_


K : (Γ : Predomain) -> {A : Predomain} -> ⟨ A ⟩ -> ⟨ Γ ==> A ⟩
K _ {A} = λ a → record {
    f = λ γ → a ;
    isMon = λ {a1} {a2} a1≤a2 → reflexive A a }


Id : {A : Predomain} -> ⟨ A ==> A ⟩
Id = record { f = id ; isMon = λ x≤y → x≤y }


Curry : {Γ A B : Predomain} -> ⟨ (Γ ×d A) ==> B ⟩ -> ⟨ Γ ==> A ==> B ⟩
Curry {Γ} g = record {
    f = λ γ →
      record {
        f = λ a → MonFun.f g (γ , a) ;
        -- For a fixed γ, f as defined directly above is monotone
        isMon = λ {a} {a'} a≤a' → MonFun.isMon g (reflexive Γ _ , a≤a') } ;

    -- The outer f is monotone in γ
    isMon = λ {γ} {γ'} γ≤γ' → λ a a' a≤a' -> MonFun.isMon g (γ≤γ' , a≤a') }

Uncurry : {Γ A B : Predomain} -> ⟨ Γ ==> A ==> B ⟩ -> ⟨ (Γ ×d A) ==> B ⟩
Uncurry f = record {
    f = λ (γ , a) → MonFun.f (MonFun.f f γ) a ;
    isMon = λ {(γ1 , a1)} {(γ2 , a2)} (γ1≤γ2 , a1≤a2) ->
      let fγ1≤fγ2 = MonFun.isMon f γ1≤γ2 in
        fγ1≤fγ2 a1 a2 a1≤a2 }


App : {A B : Predomain} -> ⟨ ((A ==> B) ×d A) ==> B ⟩
App = Uncurry Id


Swap : (Γ : Predomain) -> {A B : Predomain} -> ⟨ Γ ==> A ==> B ⟩ -> ⟨ A ==> Γ ==> B ⟩
Swap Γ f = record {
    f = λ a →
      record {
        f = λ γ → MonFun.f (MonFun.f f γ) a ;
        isMon = λ {γ1} {γ2} γ1≤γ2 ->
          let fγ1≤fγ2 = MonFun.isMon f γ1≤γ2 in
          fγ1≤fγ2 a a (reflexive _ a) } ;
    isMon = λ {a1} {a2} a1≤a2 ->
      λ γ1 γ2 γ1≤γ2 -> {!!} } -- γ1 γ2 γ1≤γ2 → {!!} }


SwapPair : {A B : Predomain} -> ⟨ (A ×d B) ==> (B ×d A) ⟩
SwapPair = record {
  f = λ { (a , b) -> b , a } ;
  isMon = λ { {a1 , b1} {a2 , b2} (a1≤a2 , b1≤b2) → b1≤b2 , a1≤a2} }


-- Apply a monotone function to the first or second argument of a pair

With1st : {Γ A B : Predomain} ->
    ⟨ Γ ==> B ⟩ -> ⟨ Γ ×d A ==> B ⟩
-- ArgIntro1 {_} {A} f = Uncurry (Swap A (K A f))
With1st {_} {A} f = mCompU f π1

With2nd : {Γ A B : Predomain} ->
    ⟨ A ==> B ⟩ -> ⟨ Γ ×d A ==> B ⟩
With2nd f = mCompU f π2
-- ArgIntro2 {Γ} f = Uncurry (K Γ f)

{-
Cong2nd : {Γ A A' B : Predomain} ->
    ⟨ Γ ×d A ==> B ⟩ -> ⟨ A' ==> A ⟩ -> ⟨ Γ ×d A' ==> B ⟩
Cong2nd = {!!}
-}



IntroArg' : {Γ B B' : Predomain} ->
    ⟨ Γ ==> B ⟩ -> ⟨ B ==> B' ⟩ -> ⟨ Γ ==> B' ⟩
IntroArg' {Γ} {B} {B'} fΓB fBB' = S Γ (With2nd fBB') fΓB
-- S : ⟨ Γ ×d A ==> B ⟩ -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> B ⟩

IntroArg : {Γ B B' : Predomain} ->
  ⟨ B ==> B' ⟩ -> ⟨ (Γ ==> B) ==> (Γ ==> B') ⟩
IntroArg f = Curry (mCompU f App)


PairAssocLR : {A B C : Predomain} ->
  ⟨ A ×d B ×d C ==> A ×d (B ×d C) ⟩
PairAssocLR = record {
  f = λ { ((a , b) , c) → a , (b , c) } ;
  isMon = λ { {(a1 , b1) , c1} {(a2 , b2) , c2} ((a1≤a2 , b1≤b2) , c1≤c2) →
    a1≤a2 , (b1≤b2 , c1≤c2)} }

PairAssocRL : {A B C : Predomain} ->
 ⟨ A ×d (B ×d C) ==> A ×d B ×d C ⟩
PairAssocRL = record {
  f =  λ { (a , (b , c)) -> (a , b) , c } ;
  isMon = λ { {a1 , (b1 , c1)} {a2 , (b2 , c2)} (a1≤a2 , (b1≤b2 , c1≤c2)) →
    (a1≤a2 , b1≤b2) , c1≤c2} }

PairCong : {Γ A A' : Predomain} ->
  ⟨ A ==> A' ⟩ -> ⟨ (Γ ×d A) ==> (Γ ×d A') ⟩
PairCong f = record {
  f = λ { (γ , a) → γ , (f $ a)} ;
  isMon = λ { {γ1 , a1} {γ2 , a2} (γ1≤γ2 , a1≤a2) → γ1≤γ2 , isMon f a1≤a2 }}

{-
PairCong : {Γ A A' : Predomain} ->
  ⟨ A ==> A' ⟩ -> ⟨ (Γ ×d A) ==> (Γ ×d A') ⟩
PairCong f = Uncurry (mCompU {!!} {!!})
-- Goal: 
-- Γ ==> (A ==> Γ ×d A')
-- Write it as : Γ ==> (A ==> (A' ==> Γ ×d A'))
-- i.e. Γ ==> A' ==> Γ ×d A'
-- Pair : ⟨ A ==> B ==> A ×d B ⟩
-}

TransformDomain : {Γ A A' B : Predomain} ->
    ⟨ Γ ×d A ==> B ⟩ ->
    ⟨ ( A ==> B ) ==> ( A' ==> B ) ⟩ ->
    ⟨ Γ ×d A' ==> B ⟩
TransformDomain fΓ×A->B f = Uncurry (IntroArg' (Curry fΓ×A->B) f)



  -- Convenience versions of comp, ext, and ret using combinators

mComp' : (Γ : Predomain) -> {A B C : Predomain} ->
    ⟨ (Γ ×d B ==> C) ⟩ -> ⟨ (Γ ×d A ==> B) ⟩ -> ⟨ (Γ ×d A ==> C) ⟩
mComp' Γ {A} {B} {C} f g = S {!!} (mCompU f aux) g
    where
      aux : ⟨ Γ ×d A ×d B ==> Γ ×d B ⟩
      aux = mCompU π1 (mCompU (mCompU PairAssocRL (PairCong SwapPair)) PairAssocLR)

      aux2 : ⟨ Γ ×d B ==> C ⟩ -> ⟨ Γ ×d A ×d B ==> C ⟩
      aux2 h = mCompU f aux


_∘m_ : {Γ A B C : Predomain} ->
   ⟨ (Γ ×d B ==> C) ⟩ -> ⟨ (Γ ×d A ==> B) ⟩ -> ⟨ (Γ ×d A ==> C) ⟩
_∘m_ {Γ} = mComp' Γ

_$_∘m_ :  (Γ : Predomain) -> {A B C : Predomain} ->
    ⟨ (Γ ×d B ==> C) ⟩ -> ⟨ (Γ ×d A ==> B) ⟩ -> ⟨ (Γ ×d A ==> C) ⟩
Γ $ f ∘m g = mComp' Γ f g
infixl 20 _∘m_


mExt' : (Γ : Predomain) -> {A B : Predomain} ->
    ⟨ (Γ ×d A ==> 𝕃 B) ⟩ -> ⟨ (Γ ×d 𝕃 A ==> 𝕃 B) ⟩
mExt' Γ f = TransformDomain f mExt

mRet' : (Γ : Predomain) -> { A : Predomain} -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> 𝕃 A ⟩
mRet' Γ a = {!!} -- _ ! K _ mRet <*> a

Bind : (Γ : Predomain) -> {A B : Predomain} ->
    ⟨ Γ ==> 𝕃 A ⟩ -> ⟨ Γ ×d A ==> 𝕃 B ⟩ -> ⟨ Γ ==> 𝕃 B ⟩
Bind Γ la f = S Γ (mExt' Γ f) la

Comp : (Γ : Predomain) -> {A B C : Predomain} ->
    ⟨ Γ ×d B ==> C ⟩ -> ⟨ Γ ×d A ==> B ⟩ -> ⟨ Γ ×d A ==> C ⟩
Comp Γ f g = {!!}





-- Mapping a monotone function
mMap : {A B : Predomain} -> ⟨ (A ==> B) ==> (𝕃 A ==> 𝕃 B) ⟩
mMap {A} {B} = Curry (mExt' (A ==> B) ((With2nd mRet) ∘m App))
-- Curry (mExt' {!!} {!!}) -- mExt' (mComp' (Curry {!!}) {!!}) -- mExt (mComp mRet f)


mMap' : {Γ A B : Predomain} ->
    ⟨ (Γ ×d A ==> B) ⟩ -> ⟨ (Γ ×d 𝕃 A ==> 𝕃 B) ⟩
mMap' f = {!!}

Map : {Γ A B : Predomain} ->
    ⟨ (Γ ×d A ==> B) ⟩ -> ⟨ (Γ ==> 𝕃 A) ⟩ -> ⟨ (Γ ==> 𝕃 B) ⟩
Map {Γ} f la = S Γ (mMap' f) la -- Γ ! mMap' f <*> la


  {-
  -- Montone function between function spaces
  mFun : {A A' B B' : Predomain} ->
    MonFun A' A ->
    MonFun B B' ->
    MonFun (arr' A B) (arr' A' B')
  mFun fA'A fBB' = record {
    f = λ fAB → {!!} ; --  mComp (mComp fBB' fAB) fA'A ;
    isMon = λ {fAB-1} {fAB-2} fAB-1≤fAB-2 →
      λ a'1 a'2 a'1≤a'2 ->
        MonFun.isMon fBB'
          (fAB-1≤fAB-2
            (MonFun.f fA'A a'1)
            (MonFun.f fA'A a'2)
            (MonFun.isMon fA'A a'1≤a'2))}

  -- NTS :
  -- In the space of monotone functions from A' to B', we have
  -- mComp (mComp fBB' f1) fA'A) ≤ (mComp (mComp fBB' f2) fA'A)
  -- That is, given a'1 and a'2 of type ⟨ A' ⟩ with a'1 ≤ a'2 we
  -- need to show that
  -- (fBB' ∘ fAB-1 ∘ fA'A)(a'1) ≤ (fBB' ∘ fAB-2 ∘ fA'A)(a'2)
  -- By monotonicity of fBB', STS that
  -- (fAB-1 ∘ fA'A)(a'1) ≤  (fAB-2 ∘ fA'A)(a'2)
  -- which follows by assumption that fAB-1 ≤ fAB-2 and monotonicity of fA'A
  -}

  -- Embedding of function spaces is monotone
mFunEmb : (A A' B B' : Predomain) ->
    ⟨ A' ==> 𝕃 A ⟩ ->
    ⟨ B ==> B' ⟩ ->
    ⟨ (A ==> 𝕃 B) ==> (A' ==> 𝕃 B') ⟩
mFunEmb A A' B B' fA'LA fBB' =
    Curry (Bind ((A ==> 𝕃 B) ×d A')
      (mCompU fA'LA π2)
      (Map (mCompU fBB' π2) ({!!})))
  --  _ $ (mExt' _ (_ $ (mMap' (K _ fBB')) ∘m Id)) ∘m (K _ fA'LA)
  -- mComp' (mExt' (mComp' (mMap' (K fBB')) Id)) (K fA'LA)

mFunProj : (A A' B B' : Predomain) ->
   ⟨ A ==> A' ⟩ ->
   ⟨ B' ==> 𝕃 B ⟩ ->
   ⟨ (A' ==> 𝕃 B') ==> 𝕃 (A ==> 𝕃 B) ⟩
mFunProj A A' B B' fAA' fB'LB = {!!}
  -- mRet' (mExt' (K fB'LB) ∘m Id ∘m (K fAA'))

  -- 

  {-
  record {
    f = λ f -> {!!} ; -- mComp (mExt (mComp (mMap fBB') f)) fA'LA ;
    isMon = λ {f1} {f2} f1≤f2 ->
      λ a'1 a'2 a'1≤a'2 ->
        ext-monotone
          (mapL (MonFun.f fBB') ∘ MonFun.f f1)
          (mapL (MonFun.f fBB') ∘ MonFun.f f2)
          ({!!})
          (MonFun.isMon fA'LA a'1≤a'2) }
  -}

  -- mComp (mExt (mComp (mMap fBB') f1)) fA'LA ≤ mComp (mExt (mComp (mMap fBB') f2)) fA'LA
  -- ((ext ((mapL fBB') ∘ f1)) ∘ fA'LA) (a'1) ≤ ((ext ((mapL fBB') ∘ f2)) ∘ fA'LA) (a'2)


{-
 -- Properties
bind-unit-l : {Γ A B : Predomain} ->
    (f : ⟨ Γ ×d A ==> 𝕃 B ⟩) ->
    (a : ⟨ Γ ==> A ⟩) ->
    rel (Γ ==> 𝕃 B)
      (Bind Γ (mRet' Γ a) f)
      (Γ ! f <*> a)
bind-unit-l = {!!}

bind-unit-r : {Γ A B : Predomain} ->
    (la : ⟨ Γ ==> 𝕃 A ⟩) ->
    rel (Γ ==> 𝕃 A)
     la
     (Bind Γ la (mRet' _ π2))
bind-unit-r la = {!!}


bind-Ret' : {Γ A : Predomain} ->
    (la : ⟨ Γ ==> 𝕃 A ⟩) ->
    (a : ⟨ Γ ×d A ==> A ⟩) ->
    rel (Γ ==> 𝕃 A)
      la
      (Bind Γ la ((mRet' _ a)))
bind-Ret' = {!!}
      

bind-K : {Γ A B : Predomain} ->
    (la : ⟨ Γ ==> 𝕃 A ⟩) ->
    (lb : ⟨ 𝕃 B ⟩) ->
     rel (Γ ==> 𝕃 B)
       (K Γ lb)
       (Bind Γ la ((K (Γ ×d A) lb)))
bind-K = {!!}

 {- Goal: rel (⟦ Γ ⟧ctx ==> 𝕃 ⟦ B ⟧ty) ⟦ err [ N ] ⟧tm
      (Bind ⟦ Γ ⟧ctx ⟦ N ⟧tm (Curry ⟦ err ⟧tm))
 -}

-}
