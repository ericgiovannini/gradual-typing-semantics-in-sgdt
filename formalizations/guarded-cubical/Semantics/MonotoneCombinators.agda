{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.MonotoneCombinators where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_^_)

open import Cubical.Relation.Binary
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Data.Unit
-- open import Cubical.Data.Prod
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Sum

open import Cubical.Foundations.Function hiding (_$_)

open import Common.Common



open import Cubical.Relation.Binary.Poset
open import Common.Poset.Convenience
open import Common.Poset.Monotone
open import Common.Poset.Constructions


private
  variable
    ℓ ℓ' : Level
    ℓA ℓ'A ℓA' ℓ'A' ℓB ℓ'B ℓB' ℓ'B' ℓC ℓ'C ℓΓ ℓ'Γ : Level
    Γ :  Poset ℓΓ ℓ'Γ
    A :  Poset ℓA ℓ'A
    A' : Poset ℓA' ℓ'A'
    B :  Poset ℓB ℓ'B
    B' : Poset ℓB' ℓ'B'
    C :  Poset ℓC ℓ'C
    


open MonFun
open import Semantics.Concrete.MonotonicityProofs


mTransport : {A B : Poset ℓ ℓ'} -> (eq : A ≡ B) -> ⟨ A ==> B ⟩
mTransport {A} {B} eq = record {
  f = λ b → transport (λ i -> ⟨ eq i ⟩) b ;
  isMon = λ {b1} {b2} b1≤b2 → rel-transport eq b1≤b2 }


mTransportSym : {A B : Poset ℓ ℓ'} -> (eq : A ≡ B) -> ⟨ B ==> A ⟩
mTransportSym {A} {B} eq = record {
  f = λ b → transport (λ i -> ⟨ sym eq i ⟩) b ;
  isMon = λ {b1} {b2} b1≤b2 → rel-transport (sym eq) b1≤b2 }

mTransportDomain : {A B C : Poset ℓ ℓ'} ->
  (eq : A ≡ B) ->
  MonFun A C ->
  MonFun B C
mTransportDomain {A} {B} {C} eq f = record {
  f = g eq f;
  isMon = mon-transport-domain eq f }
  where
    g : {A B C : Poset ℓ ℓ'} ->
      (eq : A ≡ B) ->
      MonFun A C ->
      ⟨ B ⟩ -> ⟨ C ⟩
    g eq f b = MonFun.f f (transport (λ i → ⟨ sym eq i ⟩ ) b)




-- Composing monotone functions
mCompU : MonFun B C -> MonFun A B -> MonFun A C
mCompU f1 f2 = record {
    f = λ a -> f1 .f (f2 .f a) ;
    isMon = λ x≤y -> f1 .isMon (f2 .isMon x≤y) }
  where open MonFun

mComp :
    ⟨ (B ==> C) ==> (A ==> B) ==> (A ==> C) ⟩
mComp = record {
    f = λ fBC →
      record {
        f = λ fAB → mCompU fBC fAB ;
        isMon = λ {f1} {f2} f1≤f2 -> λ a → isMon fBC (f1≤f2 a) } ;
    isMon = λ {f1} {f2} f1≤f2 → λ f' a → f1≤f2 (MonFun.f f' a) }


Pair : ⟨ A ==> B ==> (A ×p B) ⟩
Pair {A = A} {B = B} = record {
  f = λ a →
    record {
      f = λ b -> a , b ;
      isMon = λ b1≤b2 → (reflexive A a) , b1≤b2 } ;
  isMon = λ {a1} {a2} a1≤a2 b → a1≤a2 , reflexive B b }

PairFun : (f : ⟨ A ==> B ⟩) -> (g : ⟨ A ==> C ⟩ ) -> ⟨ A ==> B ×p C ⟩
PairFun f g = record {
  f = λ a -> (MonFun.f f a) , (MonFun.f g a) ;
  isMon = {!!} }


Case' : ⟨ A ==> C ⟩ -> ⟨ B ==> C ⟩ -> ⟨ (A ⊎p B) ==> C ⟩
Case' f g = record {
  f = λ { (inl a) → MonFun.f f a ; (inr b) → MonFun.f g b} ;
  isMon = λ { {inl a1} {inl a2} a1≤a2 → isMon f (lower a1≤a2) ;
              {inr b1} {inr b2} b1≤b2 → isMon g (lower b1≤b2) } }

Case : ⟨ (A ==> C) ==> (B ==> C) ==> ((A ⊎p B) ==> C) ⟩
Case = {!!}





  -- Monotone successor function
mSuc : ⟨ ℕ ==> ℕ ⟩
mSuc = record {
    f = suc ;
    isMon = λ {n1} {n2} n1≤n2 -> λ i -> suc (n1≤n2 i) }


  -- Combinators

U : ⟨ A ==> B ⟩ -> ⟨ A ⟩ -> ⟨ B ⟩
U f = MonFun.f f

S : (Γ : Poset ℓΓ ℓ'Γ) ->
    ⟨ Γ ×p A ==> B ⟩ -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> B ⟩
S Γ f g =
    record {
      f = λ γ -> MonFun.f f (γ , (U g γ)) ;
      isMon = λ {γ1} {γ2} γ1≤γ2 ->
        MonFun.isMon f (γ1≤γ2 , (MonFun.isMon g γ1≤γ2)) }


_!_<*>_ :
    (Γ : Poset ℓ ℓ') -> ⟨ Γ ×p A ==> B ⟩ -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> B ⟩
Γ ! f <*> g = S Γ f g


K : (Γ : Poset ℓ ℓ') -> {A : Poset ℓ ℓ'} -> ⟨ A ⟩ -> ⟨ Γ ==> A ⟩
K _ {A} = λ a → record {
    f = λ γ → a ;
    isMon = λ {a1} {a2} a1≤a2 → reflexive A a }


Id : {A : Poset ℓ ℓ'} -> ⟨ A ==> A ⟩
Id = record { f = id ; isMon = λ x≤y → x≤y }


Curry :  ⟨ (Γ ×p A) ==> B ⟩ -> ⟨ Γ ==> A ==> B ⟩
Curry {Γ = Γ} {A = A} g = record {
    f = λ γ →
      record {
        f = λ a → MonFun.f g (γ , a) ;
        -- For a fixed γ, f as defined directly above is monotone
        isMon = λ {a} {a'} a≤a' → MonFun.isMon g (reflexive Γ _ , a≤a') } ;

    -- The outer f is monotone in γ
    isMon = λ {γ} {γ'} γ≤γ' → λ a -> MonFun.isMon g (γ≤γ' , reflexive A a) }

Lambda :  ⟨ ((Γ ×p A) ==> B) ==> (Γ ==> A ==> B) ⟩
Lambda {Γ = Γ} {A = A} = record {
  f = Curry ;
  isMon = λ {f1} {f2} f1≤f2 γ a → f1≤f2 ((γ , a)) }



Uncurry : ⟨ Γ ==> A ==> B ⟩ -> ⟨ (Γ ×p A) ==> B ⟩
Uncurry f = record {
    f = λ (γ , a) → MonFun.f (MonFun.f f γ) a ;
    isMon = λ {(γ1 , a1)} {(γ2 , a2)} (γ1≤γ2 , a1≤a2) ->
      let fγ1≤fγ2 = MonFun.isMon f γ1≤γ2 in
        ≤mon→≤mon-het (MonFun.f f γ1) (MonFun.f f γ2) fγ1≤fγ2 a1 a2 a1≤a2 }


App : ⟨ ((A ==> B) ×p A) ==> B ⟩
App = Uncurry Id


Swap : (Γ : Poset ℓ ℓ') -> {A B : Poset ℓ ℓ'} -> ⟨ Γ ==> A ==> B ⟩ -> ⟨ A ==> Γ ==> B ⟩
Swap Γ f = record {
    f = λ a →
      record {
        f = λ γ → MonFun.f (MonFun.f f γ) a ;
        isMon = λ {γ1} {γ2} γ1≤γ2 ->
          let fγ1≤fγ2 = MonFun.isMon f γ1≤γ2 in
          ≤mon→≤mon-het _ _ fγ1≤fγ2 a a (reflexive _ a) } ;
    isMon = λ {a1} {a2} a1≤a2 ->
      λ γ -> {!!} } 


SwapPair : ⟨ (A ×p B) ==> (B ×p A) ⟩
SwapPair = record {
  f = λ { (a , b) -> b , a } ;
  isMon = λ { {a1 , b1} {a2 , b2} (a1≤a2 , b1≤b2) → b1≤b2 , a1≤a2} }


-- Apply a monotone function to the first or second argument of a pair

With1st :
    ⟨ Γ ==> B ⟩ -> ⟨ Γ ×p A ==> B ⟩
-- ArgIntro1 {_} {A} f = Uncurry (Swap A (K A f))
With1st {_} {A} f = mCompU f π1

With2nd :
    ⟨ A ==> B ⟩ -> ⟨ Γ ×p A ==> B ⟩
With2nd f = mCompU f π2
-- ArgIntro2 {Γ} f = Uncurry (K Γ f)


IntroArg' :
    ⟨ Γ ==> B ⟩ -> ⟨ B ==> B' ⟩ -> ⟨ Γ ==> B' ⟩
IntroArg' {Γ = Γ} {B = B} {B' = B'} fΓB fBB' = S Γ (With2nd fBB') fΓB

IntroArg : {Γ B B' : Poset ℓ ℓ'} ->
  ⟨ B ==> B' ⟩ -> ⟨ (Γ ==> B) ==> (Γ ==> B') ⟩
IntroArg f = Curry (mCompU f App)

{-
IntroArg1' : {Γ Γ' B : Poset ℓ ℓ'} ->
    ⟨ Γ' ==> Γ ⟩ -> ⟨ Γ ==> B ⟩ -> ⟨ Γ' ==> B ⟩
IntroArg1' f = {!!}
-}


PairAssocLR :
  ⟨ A ×p B ×p C ==> A ×p (B ×p C) ⟩
PairAssocLR = record {
  f = λ { ((a , b) , c) → a , (b , c) } ;
  isMon = λ { {(a1 , b1) , c1} {(a2 , b2) , c2} ((a1≤a2 , b1≤b2) , c1≤c2) →
    a1≤a2 , (b1≤b2 , c1≤c2)} }

PairAssocRL :
 ⟨ A ×p (B ×p C) ==> A ×p B ×p C ⟩
PairAssocRL = record {
  f =  λ { (a , (b , c)) -> (a , b) , c } ;
  isMon = λ { {a1 , (b1 , c1)} {a2 , (b2 , c2)} (a1≤a2 , (b1≤b2 , c1≤c2)) →
    (a1≤a2 , b1≤b2) , c1≤c2} }

{-
PairCong :
  ⟨ A ==> A' ⟩ -> ⟨ (Γ ×p A) ==> (Γ ×p A') ⟩
PairCong f = {!!}
-}
{-
record {
  f = λ { (γ , a) → γ , (f $ a)} ;
  isMon = λ { {γ1 , a1} {γ2 , a2} (γ1≤γ2 , a1≤a2) → γ1≤γ2 , isMon f a1≤a2 }}
-}

TransformDomain :
    ⟨ Γ ×p A ==> B ⟩ ->
    ⟨ ( A ==> B ) ==> ( A' ==> B ) ⟩ ->
    ⟨ Γ ×p A' ==> B ⟩
TransformDomain fΓ×A->B f = Uncurry (IntroArg' (Curry fΓ×A->B) f)



-- Convenience versions of comp, ext, and ret using combinators

mComp' : (Γ : Poset ℓΓ ℓ'Γ) ->
    ⟨ (Γ ×p B ==> C) ⟩ -> ⟨ (Γ ×p A ==> B) ⟩ -> ⟨ (Γ ×p A ==> C) ⟩
mComp' Γ f g = record {
  f = λ { (γ , a) → MonFun.f f (γ , (MonFun.f g (γ , a)))} ;
  isMon = {!!} }
  {- S {!!} (mCompU f aux) g
    where
      aux : ⟨ Γ ×p A ×p B ==> Γ ×p B ⟩
      aux = mCompU π1 (mCompU (mCompU PairAssocRL (PairCong SwapPair)) PairAssocLR)

      aux2 : ⟨ Γ ×p B ==> C ⟩ -> ⟨ Γ ×p A ×p B ==> C ⟩
      aux2 h = mCompU f aux -}

_∘m_ :
   ⟨ (Γ ×p B ==> C) ⟩ -> ⟨ (Γ ×p A ==> B) ⟩ -> ⟨ (Γ ×p A ==> C) ⟩
_∘m_ {Γ = Γ} = mComp' Γ

_$_∘m_ :  (Γ : Poset ℓ ℓ') -> {A B C : Poset ℓ ℓ'} ->
    ⟨ (Γ ×p B ==> C) ⟩ -> ⟨ (Γ ×p A ==> B) ⟩ -> ⟨ (Γ ×p A ==> C) ⟩
Γ $ f ∘m g = mComp' Γ f g
infixl 20 _∘m_

Comp : (Γ : Poset ℓ ℓ') -> {A B C : Poset ℓ ℓ'} ->
    ⟨ Γ ×p B ==> C ⟩ -> ⟨ Γ ×p A ==> B ⟩ -> ⟨ Γ ×p A ==> C ⟩
Comp Γ f g = {!!}


-- Lifting a monotone function functorially
_~->_ : {A B C D : Poset ℓ ℓ'} ->
    ⟨ A ==> B ⟩ -> ⟨ C ==> D ⟩ -> ⟨ (B ==> C) ==> (A ==> D) ⟩
pre ~-> post = Curry ((mCompU post App) ∘m (With2nd pre))


{-

_^m_ : ⟨ A ==> A ⟩ -> Nat -> ⟨ A ==> A ⟩
g ^m zero = Id
g ^m suc n = mCompU g (g ^m n)

^m-underlying-fn : (g : ⟨ A ==> A ⟩) (n : Nat) ->
  MonFun.f (g ^m n) ≡ (MonFun.f g) ^ n
^m-underlying-fn g zero = refl
^m-underlying-fn g (suc n) = funExt (λ x -> λ i -> MonFun.f g (^m-underlying-fn g n i x))

-}


-- This formulation has better definintional behavior, becasue
-- the underlying function is *definitionally* equal to the
-- normal iterated composition operator (_^_).
_^m_ : ⟨ A ==> A ⟩ -> Nat -> ⟨ A ==> A ⟩
g ^m n = record { f = fun n ; isMon = mon n }
  where
    fun : Nat -> _
    fun m = (MonFun.f g) ^ m

    mon : (m : Nat) -> monotone (fun m)
    mon zero {x} {y} x≤y = x≤y
    mon (suc m) {x} {y} x≤y = isMon g (mon m x≤y)



module ClockedCombinators (k : Clock) where
  private
    ▹_ : Type ℓ → Type ℓ
    ▹_ A = ▹_,_ k A

  open import Semantics.Lift k
  open import Semantics.Concrete.MonotonicityProofs
  open import Semantics.LockStepErrorOrdering k


  open LiftPoset
  open ClockedProofs k
  

  -- map and ap functions for later as monotone functions
  Map▹ :
    ⟨ A ==> B ⟩ -> ⟨ ▸''_ k A ==> ▸''_ k B ⟩
  Map▹ {A} {B} f = record {
    f = map▹ (MonFun.f f) ;
    isMon = λ {a1} {a2} a1≤a2 t → isMon f (a1≤a2 t) }

  Ap▹ :
    ⟨ (▸''_ k (A ==> B)) ==> (▸''_ k A ==> ▸''_ k B) ⟩
  Ap▹ {A = A} {B = B} = record { f = UAp▹ ; isMon = UAp▹-mon }
    where
      UAp▹ :
        ⟨ ▸''_ k (A ==> B) ⟩ -> ⟨ ▸''_ k A ==> ▸''_ k B ⟩
      UAp▹ f~ = record {
        f = _⊛_ λ t → MonFun.f (f~ t) ;
        isMon = λ {a1} {a2} a1≤a2 t → isMon (f~ t) (a1≤a2 t) }

      UAp▹-mon : {f1~ f2~ : ▹ ⟨ A ==> B ⟩} ->
        ▸ (λ t -> rel (A ==> B) (f1~ t) (f2~ t)) ->
        rel ((▸''_ k A) ==> (▸''_ k B)) (UAp▹ f1~) (UAp▹ f2~)
      UAp▹-mon {f1~} {f2~} f1~≤f2~ a~ t = f1~≤f2~ t (a~ t)



  Next : {A : Poset ℓ ℓ'} ->
    ⟨ A ==> ▸''_ k A ⟩
  Next = record { f = next ; isMon = λ {a1} {a2} a1≤a2 t → a1≤a2 }

  mθ : {A : Poset ℓ ℓ'} ->
    ⟨ ▸''_ k (𝕃 A) ==> 𝕃 A ⟩
  mθ {A = A} = record { f = θ ; isMon = ord-θ-monotone {!!} }


  -- 𝕃's return as a monotone function
  mRet : {A : Poset ℓ ℓ'} -> ⟨ A ==> 𝕃 A ⟩
  mRet {A = A} = record { f = ret ; isMon = ord-η-monotone A }


  -- Delay on Lift as a monotone function
  Δ : {A : Poset ℓ ℓ'} -> ⟨ 𝕃 A ==> 𝕃 A ⟩
  Δ {A = A} = record { f = δ ; isMon = λ x≤y → ord-δ-monotone A x≤y }


  -- Extending a monotone function to 𝕃
  mExtU : MonFun A (𝕃 B) -> MonFun (𝕃 A) (𝕃 B)
  mExtU f = record {
      f = λ la -> bind la (MonFun.f f) ;
      isMon = monotone-bind-mon f }

  mExt : ⟨ (A ==> 𝕃 B) ==> (𝕃 A ==> 𝕃 B) ⟩
  mExt {A = A} = record {
      f = mExtU ;
      isMon = λ {f1} {f2} f1≤f2 la →
        ext-monotone (MonFun.f f1) (MonFun.f f2)
          (≤mon→≤mon-het f1 f2 f1≤f2) la la (reflexive (𝕃 A) la) }

  mExt' : (Γ : Poset ℓ ℓ') ->
      ⟨ (Γ ×p A ==> 𝕃 B) ⟩ -> ⟨ (Γ ×p 𝕃 A ==> 𝕃 B) ⟩
  mExt' Γ f = TransformDomain f mExt

  mRet' : (Γ : Poset ℓ ℓ') -> { A : Poset ℓ ℓ'} -> ⟨ Γ ==> A ⟩ -> ⟨ Γ ==> 𝕃 A ⟩
  mRet' Γ f = record { f = λ γ -> ret (MonFun.f f γ) ; isMon = {!!} } -- _ ! K _ mRet <*> a

  Bind : (Γ : Poset ℓ ℓ') ->
      ⟨ Γ ==> 𝕃 A ⟩ -> ⟨ Γ ×p A ==> 𝕃 B ⟩ -> ⟨ Γ ==> 𝕃 B ⟩
  Bind Γ la f = S Γ (mExt' Γ f) la




  -- Mapping a monotone function
  mMap : ⟨ (A ==> B) ==> (𝕃 A ==> 𝕃 B) ⟩
  mMap {A = A} {B = B} = Curry (mExt' (A ==> B) ((With2nd mRet) ∘m App))
  -- Curry (mExt' {!!} {!!}) -- mExt' (mComp' (Curry {!!}) {!!}) -- mExt (mComp mRet f)


  mMap' :
      ⟨ (Γ ×p A ==> B) ⟩ -> ⟨ (Γ ×p 𝕃 A ==> 𝕃 B) ⟩
  mMap' f = record {
    f = λ { (γ , la) -> mapL (λ a -> MonFun.f f (γ , a)) la} ;
    isMon = {!!} }

  Map :
      ⟨ (Γ ×p A ==> B) ⟩ -> ⟨ (Γ ==> 𝕃 A) ⟩ -> ⟨ (Γ ==> 𝕃 B) ⟩
  Map {Γ = Γ} f la = S Γ (mMap' f) la -- Γ ! mMap' f <*> la


  {-
  -- Montone function between function spaces
  mFun : {A A' B B' : Poset ℓ ℓ'} ->
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
  mFunEmb : (A A' B B' : Poset ℓ ℓ') ->
      ⟨ A' ==> 𝕃 A ⟩ ->
      ⟨ B ==> B' ⟩ ->
      ⟨ (A ==> 𝕃 B) ==> (A' ==> 𝕃 B') ⟩
  mFunEmb A A' B B' fA'LA fBB' =
      Curry (Bind ((A ==> 𝕃 B) ×p A')
        (mCompU fA'LA π2)
        (Map (mCompU fBB' π2) ({!!})))
    --  _ $ (mExt' _ (_ $ (mMap' (K _ fBB')) ∘m Id)) ∘m (K _ fA'LA)
    -- mComp' (mExt' (mComp' (mMap' (K fBB')) Id)) (K fA'LA)

  mFunProj : (A A' B B' : Poset ℓ ℓ') ->
     ⟨ A ==> A' ⟩ ->
     ⟨ B' ==> 𝕃 B ⟩ ->
     ⟨ (A' ==> 𝕃 B') ==> 𝕃 (A ==> 𝕃 B) ⟩
  mFunProj A A' B B' fAA' fB'LB = {!!}
    -- mRet' (mExt' (K fB'LB) ∘m Id ∘m (K fAA'))

