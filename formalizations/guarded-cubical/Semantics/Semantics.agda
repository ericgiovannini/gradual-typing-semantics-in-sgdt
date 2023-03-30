{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-} -- Makes type-checking *much* faster
-- (Otherwise, finding the implicit arguments for the definitions in EP-arrow
-- takes a long time)
-- See https://agda.readthedocs.io/en/v2.6.3/language/lossy-unification.html

open import Common.Later

module Semantics.Semantics (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_^_)

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
-- open import SyntacticTermPrecision k
open import Common.Lemmas k
open import Common.MonFuns k

private
  variable
    l : Level
    A B : Set l
    ℓ ℓ' : Level
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A


open LiftPredomain using (𝕃 ; ord-η-monotone ; ord-δ-monotone ; ord-bot )


-- Denotations of Types


data Dyn' (D : ▹ Predomain) : Type where
  nat : Nat -> Dyn' D
  fun : ▸ (λ t → MonFun (D t) (𝕃 (D t))) -> Dyn' D

DynP' : (D : ▹ Predomain) -> Predomain
DynP' D = (Dyn' D) ,
  (posetstr order
    (isposet (λ x y pf1 pf2 → {!!}) {!!} order-refl order-trans {!!}))
  where
    order : Dyn' D → Dyn' D → Type ℓ-zero
    order (nat n1) (nat n2) = n1 ≡ n2
    order (fun f) (fun g) = ▸ λ t ->
      mon-fun-order (D t) (𝕃 (D t)) (f t) (g t)
    order _ _ = ⊥

    {-
    order (fun f) (fun g) = ∀ x y ->
      rel (▸' D) x y ->
      ▸ λ t -> rel (𝕃 (D t)) (MonFun.f (f t) (x t)) (MonFun.f (g t) (y t))
    -}

    order-refl : (d : Dyn' D) -> order d d
    order-refl (nat n) = refl
    order-refl (fun f) = λ t → mon-fun-order-refl (f t)

    order-trans : BinaryRelation.isTrans order
    order-trans (nat n1) (nat n2) (nat n3) n1≡n2 n2≡n3 =
      n1 ≡⟨ n1≡n2 ⟩ n2 ≡⟨ n2≡n3 ⟩ n3 ∎
    order-trans (fun f1) (fun f2) (fun f3) later-f1≤f2 later-f2≤f3 =
      λ t →
        mon-fun-order-trans (f1 t) (f2 t) (f3 t) (later-f1≤f2 t) (later-f2≤f3 t)



----------------------------------------------------------


DynP : Predomain
DynP = fix DynP'

unfold-DynP : DynP ≡ DynP' (next DynP)
unfold-DynP = fix-eq DynP'



unfold-⟨DynP⟩ : ⟨ DynP ⟩ ≡ ⟨ DynP' (next DynP) ⟩
unfold-⟨DynP⟩ = λ i → ⟨ unfold-DynP i ⟩

-- Converting from the underlying set of DynP' to the underlying
-- set of DynP
DynP'-to-DynP : ⟨ DynP' (next DynP) ⟩ -> ⟨ DynP ⟩
DynP'-to-DynP d = transport (sym (λ i -> ⟨ unfold-DynP i ⟩)) d

DynP-to-DynP' : ⟨ DynP ⟩ -> ⟨ DynP' (next DynP) ⟩
DynP-to-DynP' d = transport (λ i → ⟨ unfold-DynP i ⟩) d

DynP-DynP'-iso : (d : ⟨ DynP' (next DynP) ⟩) ->
  DynP-to-DynP' (DynP'-to-DynP d) ≡ d
DynP-DynP'-iso d = {!!}

DynP-DynP'-iso-inv : (d : ⟨ DynP ⟩) ->
  DynP'-to-DynP (DynP-to-DynP' d) ≡ d
DynP-DynP'-iso-inv d = {!!}


-- This basically is a monotonicity result, and could be
-- incorporated as a constant into the combinator language.
DynP-rel : ∀ d1 d2 ->
  rel (DynP' (next DynP)) d1 d2 ->
  rel DynP (DynP'-to-DynP d1) (DynP'-to-DynP d2)
DynP-rel d1 d2 d1≤d2 = transport
  (λ i → rel (unfold-DynP (~ i))
    (transport-filler (λ j -> ⟨ unfold-DynP (~ j) ⟩) d1 i) -- can also just use (sym unfold-⟨DynP⟩) and remove the λ j
    (transport-filler (λ j -> ⟨ unfold-DynP (~ j) ⟩) d2 i))
  d1≤d2

DynP'-rel : ∀ d1 d2 ->
  rel DynP d1 d2 ->
  rel (DynP' (next DynP)) (DynP-to-DynP' d1) (DynP-to-DynP' d2)
DynP'-rel d1 d2 d1≤d2 = transport
  (λ i → rel (unfold-DynP i)
    (transport-filler (λ j -> ⟨ unfold-DynP j ⟩) d1 i) -- can also just use unfold-⟨DynP⟩ and remove the λ j
    (transport-filler (λ j -> ⟨ unfold-DynP j ⟩) d2 i))
  d1≤d2


-------------------------------------
-- *** Embedding-projection pairs ***

-- open MonRel
-- open MonFun
-- open LiftRelation

record EP (A B : Predomain) : Type (ℓ-suc ℓ-zero)  where
  open LiftPredomain using () renaming (_≾_ to _≾hom_)
  open LiftRelation
  open MonRel
  open MonFun
  field
    emb : MonFun A B
    proj : MonFun B (𝕃 A)
    wait-l-e : ⟨ A ==> A ⟩
    wait-l-p : ⟨ A ==> 𝕃 A ⟩
    wait-r-e : ⟨ B ==> B ⟩
    wait-r-p : ⟨ B ==> 𝕃 B ⟩
    R : MonRel A B

    upR     : fun-order-het A A A B          (rel A) (MonRel.R R) (wait-l-e .f) (emb .f)
    upL     : fun-order-het A B B B          (MonRel.R R) (rel B) (emb .f) (wait-r-e .f)
    
    dnL     : fun-order-het B B (𝕃 A) (𝕃 B) (rel B) (_≾_ A B (MonRel.R R)) (proj .f) (wait-r-p .f)
    dnR     : fun-order-het A B (𝕃 A) (𝕃 A) (MonRel.R R) (_≾hom_ A)          (wait-l-p .f) (proj .f)


-- Identity E-P pair

EP-id : (A : Predomain) -> EP A A
EP-id A = record {
  emb = record { f = id ; isMon = λ x≤y → x≤y };
  proj = mCompU Δ mRet ; -- record { f = ret ; isMon = ord-η-monotone A };
  wait-l-e = Id;
  wait-l-p = mCompU Δ mRet;
  wait-r-e = Id;
  wait-r-p = mCompU Δ mRet;
  R = predomain-monrel A;

  upR = λ a a' a≤a' → a≤a';
  upL = λ a a' a≤a' → a≤a';

  dnL = λ a a' a≤a' → ord-δ-monotone A (ord-η-monotone A a≤a') ; -- (ord-η-monotone A a≤a');
  dnR = λ a a' a≤a' → ord-δ-monotone A (ord-η-monotone A a≤a') } -- ord-η-monotone A a≤a'}



-- E-P Pair for nats

≤ℕ-eq : {x y : ⟨ ℕ ⟩} -> (rel ℕ) x y -> x ≡ y
≤ℕ-eq {x} {y} x≤y = x≤y

e-nat : ⟨ ℕ ==> DynP ⟩
e-nat = record {
  f = λ n -> DynP'-to-DynP (nat n) ;  -- transport (sym unfold-⟨DynP⟩) (nat n) ;
  isMon = λ {x} {y} x≤y → DynP-rel (nat x) (nat y) (≤ℕ-eq x≤y) }

p-nat' : ⟨ DynP' (next DynP) ==> 𝕃 ℕ ⟩
p-nat' = record { f = g ; isMon = g-mon }
  where
    g : ⟨ DynP' (next DynP) ⟩ → ⟨ 𝕃 ℕ ⟩ 
    g (nat n) = ret n
    g (fun f) = ℧

    g-mon : {x y : ⟨ DynP' (next DynP) ⟩} →
      (rel (DynP' (next DynP)) x y) →
      (rel (𝕃 ℕ) (g x) (g y))
    g-mon {nat n} {nat m} x≤y = ord-η-monotone ℕ x≤y
    g-mon {fun f} {fun g} x≤y = ord-bot ℕ ℧

p-nat : MonFun DynP (𝕃 ℕ)
p-nat = {!!} -- S DynP (K DynP p-nat') (mTransport unfold-DynP)
  -- or:
  -- mTransportDomain (sym unfold-DynP) p-nat'


-- TODO add in delays for the projection and wait-p functions
EP-nat : EP ℕ DynP
EP-nat = record {
  emb = e-nat;
  proj = p-nat;
  wait-l-e = Id;
  wait-l-p = mRet;
  wait-r-e = Id;
  wait-r-p = mRet;
  R = record {
    R = λ n d -> R' n (DynP-to-DynP' d) ;
    isAntitone = λ {n} {n'} {d} n≤d n'≤n → {!!} ;
    isMonotone = λ {n} {d} {d'} n≤d d≤d' ->
      isMonotone' n≤d (DynP'-rel d d' d≤d') } ;

  upR = λ n n' n≤n' → {!!};
  upL = λ n d n≤d → {!!};

  dnL = λ d d' d≤d' → {!!};
  dnR = λ n d n≤d → {!!}

  }
    where
      R' : ⟨ ℕ ⟩ -> ⟨ DynP' (next DynP) ⟩ -> Type
      R' n (nat n') = n ≡ n'
      R' n (fun _) = ⊥

      R : ⟨ ℕ ⟩ -> ⟨ DynP ⟩ -> Type
      R n d = R' n (DynP-to-DynP' d)

      isMonotone' : {n : ⟨ ℕ ⟩} {d d' : ⟨ DynP' (next DynP) ⟩}  →
        R' n d →
        rel (DynP' (next DynP)) d d' →
        R' n d'
      isMonotone' {n} {nat n1} {nat n2} n≡n1 n1≡n2 =
        n ≡⟨ n≡n1 ⟩ n1 ≡⟨ n1≡n2 ⟩ n2 ∎



-- E-P Pair for monotone functions Dyn to L℧ Dyn
-- This is parameterized by the waiting information of the EP-pair below it,
-- in order for the projection/wait left function to remain in sync with the
-- child's wait-right function (required for composition to be defined)
EP-fun : EP (DynP ==> (𝕃 DynP)) DynP
EP-fun = record {
  emb = e-fun;
  proj = p-fun;

  -- This is equal to the identity!
  wait-l-e = Curry (
    (mMap' (With2nd (EP.wait-l-e (EP-id DynP)))) ∘m
    (Uncurry mExt) ∘m
    (With2nd (EP.wait-l-p (EP-id DynP))) ∘m
    π2
  );
  
  wait-l-p = mRet' (DynP ==> 𝕃 DynP) (Curry (
    With2nd (U mExt (EP.wait-l-p (EP-id DynP))) ∘m
    App ∘m
    With2nd (EP.wait-l-e (EP-id DynP)))) ;
    
  wait-r-e = Id;
  
  wait-r-p = record {
    f = λ d → mapL DynP'-to-DynP (wait-r-p-fun (DynP-to-DynP' d)) ;
    isMon = {!!} } ;

  R = R ;

  upR = λ n n' n≤n' → {!!};
  upL = λ n d n≤d → {!!};

  dnL = λ d d' d≤d' → {!!};
  dnR = λ n d n≤d → {!!}
  
    
  }
    where
      e-fun : MonFun (DynP ==> (𝕃 DynP)) DynP
      e-fun = record { f = e-fun-f ; isMon = e-fun-mon }
        where
          e-fun-f : ⟨ DynP ==> (𝕃 DynP) ⟩ -> ⟨ DynP ⟩
          e-fun-f f = DynP'-to-DynP (fun (next f))

          e-fun-mon :
            {f1 f2 : ⟨ DynP ==> (𝕃 DynP) ⟩} ->
            rel (DynP ==> (𝕃 DynP)) f1 f2 ->
            rel DynP (e-fun-f f1) (e-fun-f f2)
          e-fun-mon {f1} {f2} f1≤f2 =
            DynP-rel (fun (next f1)) (fun (next f2)) (λ t d1 d2 d1≤d2 → {!!})


      p-fun : MonFun DynP (𝕃 (DynP ==> (𝕃 DynP)))
      p-fun = record { f = p-fun-f ; isMon = {!!} }
        where

          p-fun-f' : ⟨ DynP' (next DynP) ⟩ -> ⟨ 𝕃 (DynP ==> (𝕃 DynP)) ⟩
          p-fun-f' (nat n) = ℧
          p-fun-f' (fun f) = θ (λ t → η (f t))

    -- f : ▸ (λ t → MonFun (next DynP t) (𝕃 (next DynP t)))

          p-fun-f : ⟨ DynP ⟩ -> ⟨ 𝕃 (DynP ==> (𝕃 DynP)) ⟩
          -- p-fun-f d = p-fun-f' (transport unfold-⟨DynP⟩ d)
          p-fun-f d = p-fun-f' (transport (λ i -> ⟨ unfold-DynP i ⟩) d)

      wait-l-p-fun : ⟨   ( (DynP' (next DynP)) ==> 𝕃 (DynP' (next DynP)) ) ⟩ ->
                     ⟨ 𝕃 ( (DynP' (next DynP)) ==> 𝕃 (DynP' (next DynP)) ) ⟩
      wait-l-p-fun d = δ (η d) -- is this correct?                   

      wait-r-p-fun : ⟨ DynP' (next DynP) ⟩ -> ⟨ 𝕃 (DynP' (next DynP)) ⟩
      wait-r-p-fun (nat n) = η (nat n)
      wait-r-p-fun (fun f) = θ (next (η (fun f)))


     {-
      R' : ⟨ DynP ==> 𝕃 DynP ⟩ -> ⟨ DynP' (next DynP) ⟩ -> Type
      R' f (nat n) = ⊥
      R' f (fun f') = ▸ λ t ->
        fun-order-het DynP DynP (𝕃 DynP) (𝕃 DynP)
        (rel DynP)
        (LiftRelation._≾_ DynP DynP (rel DynP))
        (MonFun.f f) (MonFun.f (f' t))
      -}

      R' : ⟨ DynP ==> 𝕃 DynP ⟩ -> ⟨ DynP' (next DynP) ⟩ -> Type
      R' f (nat n) = ⊥
      R' f (fun f') = ▸ λ t ->
        mon-fun-order DynP (𝕃 DynP) f (f' t)

      R : MonRel (DynP ==> 𝕃 DynP) DynP
      R = record {
        R = λ f d → R' f (DynP-to-DynP' d) ;
        isAntitone = λ {f} {f'} {d} f≤d f'≤f → {!!} ;
        isMonotone = λ {f} {d} {d'} f≤d d≤d' -> monotone' f≤d (DynP'-rel d d' d≤d') }

        where
          monotone' :  {f : ⟨ DynP ==> 𝕃 DynP ⟩} {d d' : ⟨ DynP' (next DynP) ⟩}  →
            R' f d →
            rel (DynP' (next DynP)) d d' ->
            R' f d'
          monotone' {f} {fun f~} {fun g~} f≤d d≤d' =
            λ t → mon-fun-order-trans f (f~ t) (g~ t) (f≤d t) (d≤d' t)




-- Composing EP pairs

-- We can compose EP pairs provided that the "middle" wait functions
-- satisfy a "coherence" condition.
module EPComp
  {A B C : Predomain}
  (d' : EP B C)
  (d : EP A B)
  (⊑-wait-rl-e : rel (B ==> B)   (EP.wait-r-e d) (EP.wait-l-e d'))
  (⊑-wait-rl-p : rel (B ==> 𝕃 B) (EP.wait-r-p d) (EP.wait-l-p d')) 
  where

  open EP
  open MonFun
  open MonRel

  comp-emb : ⟨ A ==> C ⟩
  comp-emb = mCompU (emb d') (emb d)

  comp-proj : ⟨ C ==> 𝕃 A ⟩
  comp-proj = Bind C (proj d') (mCompU (proj d) π2)


  EP-comp : EP A C
  EP-comp = record {
    emb = comp-emb;
    proj = comp-proj;

    wait-l-e = mCompU (wait-l-e d) (wait-l-e d);
    wait-l-p = mCompU (mExtU (wait-l-p d)) (wait-l-p d);
    wait-r-e = mCompU (wait-r-e d') (wait-r-e d');
    wait-r-p = mCompU (mExtU (wait-r-p d')) (wait-r-p d');
    
    R = CompMonRel (R d') (R d);

    upR = λ a a' a≤a' →
      emb d $ (wait-l-e d $ a)  ,
      upR d (wait-l-e d $ a) (wait-l-e d $ a) (reflexive A _) ,
      isAntitone (R d')
        (upR d' (emb d $ a') (emb d $ a') (reflexive B _))
        (transitive B
           (emb d $ (wait-l-e d $ a))
           (wait-r-e d $ (emb d $ a'))
           (wait-l-e d' $ (emb d $ a'))
           (upL d _ _ (upR d _ _ a≤a'))
           (⊑-wait-rl-e _ _ (reflexive B _)));
   
    upL = λ a c (b , a≤b , b≤c) → {!!};

    dnL = λ c c' c≤c' → {!!};
    dnR = λ a c a≤c → {!!} }



-- Lifting EP pairs to 𝕃
EP-lift : {A B : Predomain} -> EP A B -> EP (𝕃 A) (𝕃 B)
EP-lift {A} {B} d =
  record {
    emb = U mMap (EP.emb d);
    proj = U mMap (EP.proj d);
    wait-l-e = U mMap (EP.wait-l-e d);
    wait-l-p = U mMap (EP.wait-l-p d);
    wait-r-e = U mMap (EP.wait-r-e d);
    wait-r-p = U mMap (EP.wait-r-p d);
    R = LiftRelMon.R A B (EP.R d);

    upR = λ la la' la≤la' → mapL-monotone-het (rel A) (MonRel.R (EP.R d)) (MonFun.f (EP.wait-l-e d)) (MonFun.f (EP.emb d)) (EP.upR d) la la' la≤la' ;
    upL = λ la lb la≤lb   → mapL-monotone-het (MonRel.R (EP.R d)) (rel B) _ _ (EP.upL d) la lb la≤lb ;

    dnL = {!!};
    dnR = {!!}}
      where open MonFun
            open EP


-- Lifting EP pairs to functions

module EPArrow
  {A A' B B' : Predomain}
  (epAA' : EP A A')
  (epBB' : EP B B') where

    e-arrow : ⟨ (A ==> 𝕃 B) ==> (A' ==> 𝕃 B') ⟩
    e-arrow = mFunEmb A A' B B' (EP.proj epAA') (EP.emb epBB')

    p-arrow : ⟨ (A' ==> (𝕃 B')) ==> (𝕃 (A ==> (𝕃 B))) ⟩
    p-arrow = mFunProj A A' B B' (EP.emb epAA') (EP.proj epBB')



EP-arrow : {A A' B B' : Predomain} ->
  EP A A' ->
  EP B B' ->
  EP (A ==> (𝕃 B)) (A' ==> (𝕃 B'))
EP-arrow {A} {A'} {B} {B'} epAA' epBB' = record {
  emb = e-arrow;
  proj = p-arrow;
  

  wait-l-e = Curry (
    (mMap' (With2nd (EP.wait-l-e epBB'))) ∘m
    (Uncurry mExt) ∘m
    (With2nd (EP.wait-l-p epAA')) ∘m
    π2
  ) ;
  
  wait-l-p = mRet' (A ==> 𝕃 B) (Curry (
    With2nd (U mExt (EP.wait-l-p epBB')) ∘m
    App ∘m
    With2nd (EP.wait-l-e epAA'))) ;
  
  wait-r-e = Curry (
    mMap' (With2nd (EP.wait-r-e epBB')) ∘m
    ((Uncurry mExt) ∘m
    (With2nd (EP.wait-r-p epAA') ∘m
    π2))) ;
  
  wait-r-p = mRet' (A' ==> 𝕃 B') (Curry (
    With2nd (U mExt (EP.wait-r-p epBB')) ∘m
    App ∘m
    With2nd (EP.wait-r-e epAA'))) ;

  R = FunRel (EP.R epAA') {!!} ;

  upR = λ p p' x p₁ p'' x₁ → {!!} ;
  upL = {!!} ;
  dnL = {!!} ;
  dnR = {!!}

  }
  
  where open EPArrow epAA' epBB'

{-


-------------------------------------------
-- *** Denotation of types and contexts ***

open EPComp

-- Types are predomains
⟦_⟧ty : Ty -> Predomain
⟦ nat ⟧ty = ℕ
⟦ dyn ⟧ty = DynP
⟦ A => B ⟧ty =  ⟦ A ⟧ty ==> (𝕃 ⟦ B ⟧ty)
-- ⟦ A ⟧ty -> L℧ ⟦ B ⟧ty

-- Contexts are predomains
⟦_⟧ctx : Ctx -> Predomain
⟦ · ⟧ctx = UnitP
⟦ Γ :: A ⟧ctx = ⟦ Γ ⟧ctx ×d ⟦ A ⟧ty -- ⟦ Γ ⟧ctx × ⟦ A ⟧ty

-- Agda can infer that the context is not empty, so
-- ⟦ Γ ⟧ctx must be a product
-- Make A implicit
look : {Γ : Ctx} ->
  (env : ⟨ ⟦ Γ ⟧ctx ⟩) ->
  (A : Ty) ->
  (x : Γ ∋ A) ->
  ⟨ ⟦ A ⟧ty ⟩
look env A vz = proj₂ env
look env A (vs {Γ} {S} {T} x) = look (proj₁ env) A x

look-mon : {Γ : Ctx} ->
  (env1 env2 : ⟨ ⟦ Γ ⟧ctx ⟩) ->
  (A : Ty) ->
  (z : Γ ∋ A) ->
  rel ⟦ Γ ⟧ctx env1 env2 ->
  rel ⟦ A ⟧ty (look env1 A z) (look env2 A z)
look-mon env1 env2 A z env1≤env2 = {!!}

mLook : {Γ : Ctx} ->
  (A : Ty) ->
  (x : Γ ∋ A) ->
  ⟨ ⟦ Γ ⟧ctx ==> ⟦ A ⟧ty ⟩
mLook A vz = π2
mLook A (vs z) = mCompU (mLook A z) π1

mLook-vz : {Γ : Ctx} -> (A : Ty) -> (env : ⟨ ⟦ Γ :: A ⟧ctx ⟩) ->
  MonFun.f (mLook A (vz {Γ})) env ≡ proj₂ env
mLook-vz = {!!}


---------------------------------------
-- *** Denotation of type precision ***

⟦_⟧lt : {A B : Ty} -> A ⊑ B -> EP ⟦ A ⟧ty ⟦ B ⟧ty
-- ⟦_⟧lt = {!!}
⟦ dyn ⟧lt = EP-id DynP
⟦ A⊑A' => B⊑B' ⟧lt = EP-arrow ⟦ A⊑A' ⟧lt ⟦ B⊑B' ⟧lt
⟦ nat ⟧lt = EP-id ℕ
⟦ inj-nat ⟧lt = EP-nat
⟦ inj-arrow (A-dyn => B-dyn) ⟧lt =
  EP-comp (EP-arrow  ⟦ A-dyn ⟧lt  ⟦ B-dyn ⟧lt) EP-fun



------------------------------
-- *** Denotation of terms ***

tm-sem : {A : Ty} {Γ : Ctx} -> Tm Γ A -> ⟨ ⟦ Γ ⟧ctx ==> (𝕃 ⟦ A ⟧ty) ⟩
tm-sem {_} {Γ} (var z) = mRet' ⟦ Γ ⟧ctx (mLook _ z)
tm-sem {_} {Γ} (lda M) = mRet' ⟦ Γ ⟧ctx (Curry (tm-sem M))
--(_ $ K ⟦ Γ ⟧ctx (tm-sem M) ∘m Pair)

-- mRet' ? (K (tm-sem M) ∘m Pair))

{-
record {
  f = λ ⟦Γ⟧ -> ret
    (record {
      f = λ N -> MonFun.f (tm-sem M) (⟦Γ⟧ , N);
      isMon = {!!} }) ;
  isMon = {!!} }
-}
  
tm-sem {A} {Γ} (app {S = B} M1 M2) = {!!}
{-
    let kont = (⟦ Γ ⟧ctx ! K ⟦ Γ ⟧ctx (swap _ {- (⟦ B ⟧ty ==> 𝕃 ⟦ A ⟧ty) -} mExt) <*> tm-sem M2) in
    (⟦ Γ ⟧ctx ! mExt' ⟦ Γ ⟧ctx kont <*> tm-sem M1)
-}

-- mExt :      ⟨ (⟦ B ⟧ty ==> 𝕃 ⟦ A ⟧ty) ==> 𝕃 ⟦ B ⟧ty ==> 𝕃 ⟦ A ⟧ty ⟩
-- swap mExt : ⟨ 𝕃 ⟦ B ⟧ty ==> ( ⟦ B ⟧ty ==> 𝕃 ⟦ A ⟧ty ) ==> 𝕃 ⟦ A ⟧ty ⟩
-- K (swap mExt) : ⟨ ⟦ Γ ⟧ctx ==> 𝕃 ⟦ B ⟧ty ==> ( ⟦ B ⟧ty ==> 𝕃 ⟦ A ⟧ty ) ==> 𝕃 ⟦ A ⟧ty ⟩
-- tm-sem M2 : ⟨ ⟦ Γ ⟧ctx ==> 𝕃 ⟦ B ⟧ty ⟩
-- kont :      ⟨  ⟦ Γ ⟧ctx ==> ( ⟦ B ⟧ty ==> 𝕃 ⟦ A ⟧ty ) ==> 𝕃 ⟦ A ⟧ty ⟩

-- mExt' kont : ⟨ ⟦ Γ ⟧ctx ==> 𝕃 ( ⟦ B ⟧ty ==> 𝕃 ⟦ A ⟧ty ) ==> 𝕃 ⟦ A ⟧ty ⟩
-- tm-sem M1 : ⟨ ⟦ Γ ⟧ctx ==> 𝕃 ( ⟦ B ⟧ty ==> 𝕃 ⟦ A ⟧ty ) ⟩
-- result : ⟨ ⟦ Γ ⟧ctx ==> 𝕃 ⟦ A ⟧ty ⟩

{-
 
Idea:
  
  ext f : 𝕃 ⟦ S1 ⟧ty ==> 𝕃 ⟦ A ⟧ty
 (ext f) (tm-sem M2 ⟦Γ⟧) : 𝕃 ⟦ A ⟧ty

-}


{-
record {
  f = λ ⟦Γ⟧ ->
    bind ((MonFun.f (tm-sem M1)) ⟦Γ⟧)
         (λ f -> bind (MonFun.f (tm-sem M2) ⟦Γ⟧) (MonFun.f f)) ;
    isMon = {!!} }
-}
    
tm-sem {A} {Γ} err = K ⟦ Γ ⟧ctx ℧
-- record { f = λ _ -> ℧ ; isMon = λ _ -> ord-bot ⟦ A ⟧ty ℧ }

tm-sem {_} {Γ} (up A⊑B M) = Map (mCompU (EP.emb ⟦ A⊑B ⟧lt) π2) (tm-sem M)
  -- ⟦ Γ ⟧ctx ! (mMap' (K ⟦ Γ ⟧ctx (EP.emb ⟦ A⊑B ⟧lt))) <*> (tm-sem M)
  -- Map (K ⟦ Γ ⟧ctx (EP.emb ⟦ A⊑B ⟧lt)) (tm-sem M)

{-
record {
  f =  λ ⟦Γ⟧ -> mapL (MonFun.f (EP.emb ⟦ A⊑B ⟧lt)) ((MonFun.f (tm-sem  M)) ⟦Γ⟧) ;
  isMon = {!!} }
-}
  
tm-sem {_} {Γ} (dn A⊑B M) =
  -- ⟦ Γ ⟧ctx ! (mExt' ⟦ Γ ⟧ctx (K ⟦ Γ ⟧ctx (EP.proj ⟦ A⊑B ⟧lt))) <*> (tm-sem M)
  Bind ⟦ Γ ⟧ctx (tm-sem M) (mCompU (EP.proj ⟦ A⊑B ⟧lt) π2)

{-
record { f =
  λ ⟦Γ⟧ -> bind ((MonFun.f (tm-sem M)) ⟦Γ⟧) (MonFun.f (EP.proj ⟦ A⊑B ⟧lt)) ;
  isMon = {!!} }
-}
  
tm-sem {_} {Γ} zro = K ⟦ Γ ⟧ctx (η zero)
-- record { f = λ _ -> η zero ; isMon = λ _ → ord-refl ℕ (η zero) }

tm-sem {_} {Γ} (suc M) = {!!}
-- ⟦ Γ ⟧ctx ! (mExt' ⟦ Γ ⟧ctx (K ⟦ Γ ⟧ctx (mRet' ℕ mSuc))) <*> (tm-sem M)
{-
record {
  f =  λ ⟦Γ⟧ -> bind (MonFun.f (tm-sem M) ⟦Γ⟧) (λ n -> η (suc n)) ;
  isMon = λ _ → {!!} }
-}

-- ⟦_⟧tm : {A : Ty} -> {Γ : Ctx} -> Tm Γ A -> (⟨ ⟦ Γ ⟧ctx ⟩ -> L℧ ⟨ ⟦ A ⟧ty ⟩)
⟦_⟧tm : {A : Ty} -> {Γ : Ctx} -> Tm Γ A -> MonFun ( ⟦ Γ ⟧ctx)  (𝕃 ⟦ A ⟧ty )
⟦ M ⟧tm = tm-sem M





---------------------------------------
-- *** Denotation of term precision ***
--  ⟦ M ⟧ ≲ ⟦ N ⟧

open Bisimilarity

{-
-- Homogeneous term precision relation
lttm-hom : {A : Ty} ->
  (Γ : Ctx) ->
  (M : Tm (lhs (Ctx-ref Γ)) A) ->
  (N : Tm (rhs (Ctx-ref Γ)) A) ->
  (Ctx-ref Γ) |- M ⊑tm N # (⊑ref A) ->
  (⟦ A ⟧ty ≾ ((MonFun.f ⟦ M ⟧tm) {!!} )) ((MonFun.f ⟦ N ⟧tm) {!!})
lttm-hom Γ M N M⊑N = {!!}
-}

{-
mapL-emb : {A A' : Type} -> (epAA' : EP A A') (a : L℧ A) ->
  mapL (EP.emb epAA') a ≡ EP.emb (EP-L epAA') a
mapL-emb epAA' a = refl
-}


------------------------------------------------------------------
-- *** Relational interpretation of type precision derivations ***
-- c : A ⊑ B
-- ⟦c⟧ : relation between ⟦ A ⟧ty and ⟦ B ⟧ty

typrecd-sem : {A B : Ty} ->
  (c : A ⊑ B) -> (⟨ ⟦ A ⟧ty ⟩ -> ⟨ ⟦ B ⟧ty ⟩ -> Type)
typrecd-sem dyn = rel DynP
typrecd-sem {Ain => Aout} {Bin => Bout} (cin => cout) =
  λ f1 f2 -> fun-order-het  ⟦ Ain ⟧ty ⟦ Bin ⟧ty (𝕃 ⟦ Aout ⟧ty) (𝕃 ⟦ Bout ⟧ty)
    (typrecd-sem cin)
    (LiftRelation.ord ⟦ Aout ⟧ty ⟦ Bout ⟧ty (typrecd-sem cout))
    (MonFun.f f1) (MonFun.f f2)
    -- (MonFun.f (MonFun.f (EP.wait-l-e ⟦ cin => cout ⟧lt) f1))
    -- (MonFun.f (MonFun.f (EP.wait-r-e ⟦ cin => cout ⟧lt) f2))
typrecd-sem nat = rel ℕ
typrecd-sem inj-nat = λ n d -> rel' n (DynP-to-DynP' d)
  where
    rel' : ⟨ ℕ ⟩ -> ⟨ DynP' (next DynP) ⟩ -> Type
    rel' n (nat n') = n ≡ n'
    rel' n (fun _) = ⊥
typrecd-sem {Ain => Aout} (inj-arrow (cin => cout)) =
  λ f d -> rel' f (DynP-to-DynP' d)
  where
    rel' : ⟨ ⟦ Ain ⟧ty ==> 𝕃 ⟦ Aout ⟧ty ⟩ -> ⟨ DynP' (next DynP) ⟩ -> Type
    rel' f (nat n) = ⊥
    rel' f (fun f') = ▸ λ t ->
      fun-order-het ⟦ Ain ⟧ty DynP (𝕃 ⟦ Aout ⟧ty) (𝕃 DynP)
      (typrecd-sem cin)
      (LiftRelation.ord ⟦ Aout ⟧ty DynP (typrecd-sem cout))
      (MonFun.f f) (MonFun.f (f' t))

------------------------------------------
-- *** Heterogeneous term precision *** --

tmprec : {Γ : Ctx} -> {A B : Ty} ->
  (c : A ⊑ B) -> Tm Γ A -> Tm Γ B -> Type
tmprec {Γ} {A} {B} c M N =
  fun-order-het ⟦ Γ ⟧ctx ⟦ Γ ⟧ctx (𝕃 ⟦ A ⟧ty) (𝕃 ⟦ B ⟧ty)
  (rel ⟦ Γ ⟧ctx)
    (LiftRelation.ord ⟦ A ⟧ty ⟦ B ⟧ty (typrecd-sem c))
    (MonFun.f ⟦ M ⟧tm) (MonFun.f ⟦ N ⟧tm)



-----------------------------------------


x≤emb : {Γ : Ctx} -> (A B : Ty) -> (x : (· :: A) ∋ A) -> (c : A ⊑ B) ->
  tmprec c (var x) (up c (var x))
x≤emb .dyn .dyn x dyn (_ , d1) (_ , d2) (_ , d1≤d2) =
           transport
             (sym (λ i → LiftRelation.unfold-ord DynP DynP (rel DynP) i
                           (MonFun.f ⟦ var x ⟧tm (tt , d1))
                           (MonFun.f ⟦ up dyn (var x) ⟧tm (tt , d2))))
             {!!}
x≤emb .(_ => _) .(_ => _) x (c => c₁) = {!!}
x≤emb .nat .nat x nat (_ , n1) (_ , n2) (_ , n1≡n2) =
           transport
             (sym (λ i → LiftRelation.unfold-ord ℕ ℕ (rel ℕ) i
                           (MonFun.f ⟦ var x ⟧tm (tt , n1))
                           (MonFun.f ⟦ up nat (var x) ⟧tm (tt , n2))))
             {!!}
x≤emb .nat .dyn x inj-nat = {!!}
x≤emb A .dyn x (inj-arrow c) = {!!}





open EPComp


-- Properties of the wait functions
module WaitProp
  where

  open EP

  wait-l-θ : {A B : Ty} -> (c : A ⊑ B) -> (la~ : ▹ L℧ ⟨ ⟦ A ⟧ty ⟩) ->
    Σ (▹ L℧ ⟨ ⟦ A ⟧ty ⟩) λ la'~ ->
      MonFun.f (wait-l-p ⟦ c ⟧lt) (θ la~) ≡
      θ (λ t -> MonFun.f (wait-l-p ⟦ c ⟧lt) (la'~ t))
  wait-l-θ dyn la~ = la~ , refl
  wait-l-θ {Ai => Ao} {Bi => Bo} (cin => cout) la~ = {!!}
  wait-l-θ nat la~ = la~ , refl
  wait-l-θ inj-nat la~ = la~ , refl
  wait-l-θ {Ai => Ao} (inj-arrow (cin => cout)) la~ = {!!} , {!!}


  wait-r-θ : {A B : Ty} -> (c : A ⊑ B) -> (lb~ : ▹ L℧ ⟨ ⟦ B ⟧ty ⟩) ->
    Σ (▹ L℧ ⟨ ⟦ B ⟧ty ⟩) λ lb'~ ->
      MonFun.f (wait-r-p ⟦ c ⟧lt) (θ lb~) ≡
      θ (λ t -> MonFun.f (wait-r-p ⟦ c ⟧lt) (lb'~ t))
  wait-r-θ dyn la~ = la~ , refl
  wait-r-θ {Ai => Ao} {Bi => Bo} (cin => cout) la~ = {!!}
  wait-r-θ nat la~ = la~ , refl
  wait-r-θ inj-nat la~ = la~ , refl
  wait-r-θ {Ai => Ao} (inj-arrow (cin => cout)) la~ = la~ ,
    transport (λ i -> δ (θ la~) ≡ θ (λ t -> θ (next-Mt≡M la~ t (~ i)))) refl

  -- Goal :  δ (θ la~)        ≡ θ (λ t → δ (la~ t))
  -- i.e.    θ (next (θ la~)) ≡ θ (λ t → θ (next (la~ t)))
  
  -- By tick irr + later extensionality, we have that
  -- ▸ λ t -> (next (la~ t) == la~)

  -- So the goal becomes
  -- θ (next (θ la~)) ≡ θ (λ t → θ (la~))
  -- θ (next (θ la~)) ≡ θ (next (θ la~))
  


-- Universal properties of casts
module UniversalProps where
{-
UpR : {A B C : Ty} ->
  (M1 : ⟨ ⟦ A ⟧ty ⟩) ->
  (M2 : ⟨ ⟦ B ⟧ty ⟩) ->
  (c : A ⊑ B) ->
  (d : B ⊑ C) ->
  typrecd-sem c M1 M2 ->
  typrecd-sem (⊑comp c d)
    (MonFun.f (EP.wait-l-e ⟦ c ⟧lt) M1)
    (MonFun.f (EP.emb ⟦ d ⟧lt) M2)
UpR M1 M2 dyn dyn M1⊑M2 = M1⊑M2

UpR {Ai => Ao} {Bi => Bo} {Ci => Co}
  M1 M2 (cin => cout) (din => dout) M1⊑M2 =
  λ ai ci ai⊑ci → {!!}

UpR {Ai => Ao} {Bi => Bo}
  M1 M2 (cin => cout) (inj-arrow (cin' => cout')) M1⊑M2 =
  {!!}

UpR M1 M2 nat nat M1⊑M2 = M1⊑M2

UpR M1 M2 nat inj-nat M1⊑M2 = {!!}

UpR M1 M2 inj-nat dyn M1⊑M2 = M1⊑M2

UpR {Ai => Ao} M1 M2 (inj-arrow (cin' => cout')) dyn M1⊑M2 = {!!}
-}


  UpR : {A B C : Ty} ->
    (M1 M2 : ⟨ ⟦ A ⟧ty ⟩) ->
    (c : A ⊑ B) ->
    rel ⟦ A ⟧ty M1 M2 ->
    typrecd-sem c
      (MonFun.f (EP.wait-l-e ⟦ c ⟧lt) M1)
      (MonFun.f (EP.emb ⟦ c ⟧lt) M2)
  UpR M1 M2 dyn M1⊑M2 = M1⊑M2
  UpR M1 M2 (cin => cout) M1⊑M2 = {!!}
  UpR M1 M2 nat M1⊑M2 = M1⊑M2
  UpR M1 M2 inj-nat M1⊑M2 = {!!} -- transport stuff
  UpR {Ai => Ao} M1 M2 (inj-arrow (cin' => cout')) M1⊑M2 = {!!}



  UpL : {A B C : Ty} ->
    (M1 : ⟨ ⟦ A ⟧ty ⟩) ->
    (M2 : ⟨ ⟦ B ⟧ty ⟩) ->
    (c : A ⊑ B) ->
    typrecd-sem c M1 M2 ->
    rel ⟦ B ⟧ty
      (MonFun.f (EP.emb ⟦ c ⟧lt) M1)
      (MonFun.f (EP.wait-r-e ⟦ c ⟧lt) M2)
  UpL M1 M2 dyn M1⊑M2 = M1⊑M2
  UpL M1 M2 (cin => cout) M1⊑M2 = {!!}
  UpL M1 M2 nat M1⊑M2 = M1⊑M2
  UpL M1 M2 inj-nat M1⊑M2 = {!!} -- transport stuff
  UpL {Ai => Ao} M1 M2 (inj-arrow (cin' => cout')) M1⊑M2 = {!!}

-- By our assumption that M1 is related to M2,
-- (DynP-to-DynP' M2) must be of the form (fun f') where
-- ▸ (λ t -> M1 ⊑ (f' t)).
-- Thus, we have that emb M1 is related to M2 in the DynP relation
-- which is what we needed to show (since here wait-r-e is the identity)












id≤map : {A B : Predomain} ->
  (la la' : L℧ ⟨ A ⟩) ->
  (f : ⟨ A ⟩ -> ⟨ B ⟩) ->
  (R : ⟨ A ⟩ -> ⟨ B ⟩ -> Type) ->
  ((a a' : ⟨ A ⟩) -> rel A a a' -> R a (f a')) ->
  ord' A (next (ord A)) la la' ->
  LiftRelation.ord' A B R (next (LiftRelation.ord A B R)) la (mapL f la')
id≤map {A} {B} (η x) (η x') f R H la≤la' =
  -- subst {!!} {!!} (H x x' la≤la')  -- (H x x' la≤la')
  transport
    (sym (λ i → LiftRelation.ord' A B R _ (η x) (mapL-eta f x' i)))
    (H x x' la≤la')
id≤map ℧ la' f R H la≤la' = tt
id≤map {A} {B} (θ lx~) (θ ly~) f R H la≤la' =
  transport
    (sym (λ i → LiftRelation.ord' A B R (next (LiftRelation.ord A B R)) (θ lx~) (mapL-theta f ly~ i)))
    λ t → {!!}

-- LiftRelation.ord' A B R (next (LiftRelation.ord A B R)) (η x)
--      (mapL f (η x'))









------------------------------
-- *** Beta/eta properties ***


-- Semantic interpretation of substitution

-- Correct subtitution lemma for values




-- This is incorrect. Counterexample is if N is err and M is a term that
-- doesn't refer to its free variable
sub-lemma : (Γ : Ctx) (A B : Ty) -> (M : Tm (Γ :: A) B) -> (N : Tm Γ A) ->
  rel (⟦ Γ ⟧ctx ==> 𝕃 ⟦ B ⟧ty)
      (⟦ M [ N ] ⟧tm)
      (Bind ⟦ Γ ⟧ctx ⟦ N ⟧tm (⟦ M ⟧tm))
sub-lemma Γ A .A (var vz) N = bind-Ret' (⟦ N ⟧tm) (mLook A vz)
sub-lemma Γ A B (var (vs x)) N = {!!}
sub-lemma Γ A .(_ => _) (lda M) N = {!!}
sub-lemma Γ A B (app M1 M2) N = {!!}
sub-lemma Γ A B err N = bind-K (⟦ N ⟧tm) ℧
sub-lemma Γ A B (up x M) N = {!!}
sub-lemma Γ A B (dn x M) N = {!!}
sub-lemma Γ A .nat zro N = bind-K (⟦ N ⟧tm) (η zero)
sub-lemma Γ A .nat (suc M) N = {!!}

{-
lem1 : ∀ (Γ : Ctx) (A B : Ty) -> (M : Tm (Γ :: A) B) (N : Tm Γ A) ->
   ⟦ app (lda M) N ⟧tm ≡ {!!}
lem1 Γ A B M N =
  let kont = (K (swap mExt) <*> tm-sem N) in
  (mExt' kont <*> tm-sem (lda M))
    ≡⟨ refl ⟩
  let kont = (K (swap mExt) <*> tm-sem N) in
  (mExt' kont <*> (mRet' (K (tm-sem M) ∘m Pair)))
    ≡⟨ {! refl!} ⟩
  mExt' (K (swap mExt) <*> tm-sem N) <*> (mRet' (K (tm-sem M) ∘m Pair))
    ≡⟨ {!!} ⟩
  {!!}
    ≡⟨ {!!} ⟩
  {!!}

-}


beta-lt : (Γ : Ctx) (A B : Ty) -> (M : Tm (Γ :: A) B) -> {!!}
  -- rel {!!} ⟦ app (lda {!!}) (var vz) ⟧tm ⟦ M ⟧tm
beta-lt = {!!}



{-
eta : (Γ : Ctx) (A B : Ty) -> (M : Tm Γ (A => B)) ->
  rel {!!}  ⟦ M ⟧tm ⟦ {!lda!} ⟧tm
eta = {!!}
-}


-}
