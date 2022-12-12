{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Later

module MonFuns (k : Clock) where

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

open import StrongBisimulation k
open import GradualSTLC
open import SyntacticTermPrecision k
open import Lemmas k


private
  variable
    l : Level
    A B : Set l
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A


open 𝕃

abstract

  -- Composing monotone functions
  mComp : {A B C : Predomain} ->
    -- MonFun (arr' B C) (arr' (arr' A B) (arr' A C))
    ⟨ (B ==> C) ==> (A ==> B) ==> (A ==> C) ⟩
  mComp = record {
    f = λ fBC →
      record {
        f = λ fAB → mComp' fBC fAB ;
        isMon = λ {f1} {f2} f1≤f2 ->
          λ a1 a2 a1≤a2 → MonFun.isMon fBC (f1≤f2 a1 a2 a1≤a2) } ;
    isMon = λ {f1} {f2} f1≤f2 →
      λ fAB1 fAB2 fAB1≤fAB2 →
        λ a1 a2 a1≤a2 ->
          f1≤f2 (MonFun.f fAB1 a1) (MonFun.f fAB2 a2)
            (fAB1≤fAB2 a1 a2 a1≤a2) }
    where
      mComp' : {A B C : Predomain} -> MonFun B C -> MonFun A B -> MonFun A C
      mComp' f1 f2 = record {
        f = λ a -> f1 .f (f2 .f a) ;
        isMon = λ x≤y -> f1 .isMon (f2 .isMon x≤y) }
        where open MonFun


  -- 𝕃's return as a monotone function
  mRet : {A : Predomain} -> ⟨ A ==> 𝕃 A ⟩
  mRet {A} = record { f = ret ; isMon = ord-η-monotone A }


  -- Extending a monotone function to 𝕃
  mExt : {A B : Predomain} -> ⟨ (A ==> 𝕃 B) ==> (𝕃 A ==> 𝕃 B) ⟩
  mExt = record {
    f = mExt' ;
    isMon = λ {f1} {f2} f1≤f2  -> ext-monotone (MonFun.f f1) (MonFun.f f2) f1≤f2 }
    where
      mExt' : {A B : Predomain} -> MonFun A (𝕃 B) -> MonFun (𝕃 A) (𝕃 B)
      mExt' f = record {
        f = λ la -> bind la (MonFun.f f) ;
        isMon = monotone-bind-mon f }


  -- Monotone successor function
  mSuc : ⟨ ℕ ==> ℕ ⟩
  mSuc = record {
    f = suc ;
    isMon = λ {n1} {n2} n1≤n2 -> λ i -> suc (n1≤n2 i) }


  -- Combinators

  S : {Γ A B : Predomain} ->
    ⟨ Γ ==> A ==> B ⟩ -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> B ⟩
  S f g =
    record {
      f = λ γ -> MonFun.f (MonFun.f f γ) (MonFun.f g γ) ;
      isMon = λ {γ1} {γ2} γ1≤γ2 →
        let fγ1≤fγ2 = MonFun.isMon f γ1≤γ2 in
          fγ1≤fγ2 (MonFun.f g γ1) (MonFun.f g γ2) (MonFun.isMon g γ1≤γ2) }


  _<*>_ : {Γ A B : Predomain} -> ⟨ Γ ==> A ==> B ⟩ -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> B ⟩
  f <*> g = S f g

  infixl 20 _<*>_


  K : {Γ : Predomain} -> {A : Predomain} -> ⟨ A ⟩ -> ⟨ Γ ==> A ⟩
  K {_} {A} = λ a → record {
    f = λ γ → a ;
    isMon = λ {a1} {a2} a1≤a2 → reflexive A a }

  Id : {A : Predomain} -> ⟨ A ==> A ⟩
  Id = record { f = id ; isMon = λ x≤y → x≤y }

  Curry : {Γ A B : Predomain} -> ⟨ (Γ ×d A) ==> B ⟩ -> ⟨ Γ ==> A ==> B ⟩
  Curry f = record { f = λ γ →
    record { f = λ a → MonFun.f f (γ , a) ; isMon = {!!} } ; isMon = {!!} }

  Uncrry : {Γ A B : Predomain} -> ⟨ Γ ==> A ==> B ⟩ -> ⟨ (Γ ×d A) ==> B ⟩
  Uncrry = {!!}

  swap : {Γ A B : Predomain} -> ⟨ Γ ==> A ==> B ⟩ -> ⟨ A ==> Γ ==> B ⟩
  swap f = record {
    f = λ a →
      record {
        f = λ γ → MonFun.f (MonFun.f f γ) a ;
        isMon = λ {γ1} {γ2} γ1≤γ2 ->
          let fγ1≤fγ2 = MonFun.isMon f γ1≤γ2 in
          fγ1≤fγ2 a a (reflexive _ a) } ;
    isMon = λ {a1} {a2} a1≤a2 ->
      λ γ1 γ2 γ1≤γ2 -> {!!} } -- γ1 γ2 γ1≤γ2 → {!!} }


  -- Convenience versions of comp, ext, and ret using combinators

  mComp' : {Γ A B C : Predomain} ->
    ⟨ (Γ ==> B ==> C) ⟩ -> ⟨ (Γ ==> A ==> B) ⟩ -> ⟨ (Γ ==> A ==> C) ⟩
  mComp' f g = (K mComp) <*> f <*> g

  _∘m_ :  {Γ A B C : Predomain} ->
    ⟨ (Γ ==> B ==> C) ⟩ -> ⟨ (Γ ==> A ==> B) ⟩ -> ⟨ (Γ ==> A ==> C) ⟩
  f ∘m g = mComp' f g
  infixl 20 _∘m_

  mExt' : {Γ A B : Predomain} ->
    ⟨ (Γ ==> A ==> 𝕃 B) ⟩ -> ⟨ (Γ ==> 𝕃 A ==> 𝕃 B) ⟩
  mExt' f = K mExt <*> f

  mRet' : {Γ A : Predomain} -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> 𝕃 A ⟩
  mRet' a = K mRet <*> a


  -- Mapping a monotone function
  mMap : {A B : Predomain} -> ⟨ (A ==> B) ==> (𝕃 A ==> 𝕃 B) ⟩
  mMap = {!!} -- mExt' (mComp' (Curry {!!}) {!!}) -- mExt (mComp mRet f)


  mMap' : {Γ A B : Predomain} ->
    ⟨ (Γ ==> A ==> B) ⟩ -> ⟨ (Γ ==> 𝕃 A ==> 𝕃 B) ⟩
  mMap' = {!!}


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
  mFunEmb : {A A' B B' : Predomain} ->
    ⟨ A' ==> 𝕃 A ⟩ ->
    ⟨ B ==> B' ⟩ ->
    ⟨ (A ==> 𝕃 B) ==> (A' ==> 𝕃 B') ⟩
  mFunEmb fA'LA fBB' = (mExt' (mMap' (K fBB') ∘m Id)) ∘m (K fA'LA)
  -- mComp' (mExt' (mComp' (mMap' (K fBB')) Id)) (K fA'LA)

  mFunProj : {A A' B B' : Predomain} ->
   ⟨ A ==> A' ⟩ ->
   ⟨ B' ==> 𝕃 B ⟩ ->
   ⟨ (A' ==> 𝕃 B') ==> 𝕃 (A ==> 𝕃 B) ⟩
  mFunProj fAA' fB'LB = mRet' (mExt' (K fB'LB) ∘m Id ∘m (K fAA'))

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
