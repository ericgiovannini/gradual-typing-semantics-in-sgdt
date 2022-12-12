{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Later

module Semantics (k : Clock) where

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

open import StrongBisimulation k
open import GradualSTLC
open import SyntacticTermPrecision k
open import Lemmas k
open import MonFuns k

private
  variable
    l : Level
    A B : Set l
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A



open 𝕃

-- Denotations of Types

{-

-- First definition of Dyn'

data Dyn' (D : ▹ Type) : Type where
  nat : Nat -> Dyn' D
  fun : (▸ D -> L℧ (Dyn' D)) -> Dyn' D

-- Dyn' is a recursive sum type, so we can
-- define the ordering inductively
-- (same way as you'd define an ordering on lists)

DynP' : (D : ▹ Predomain) -> Predomain
DynP' D = Dyn' (λ t -> ⟨ D t ⟩) ,
          posetstr order {!!}

      where

      order : Dyn' (λ t → ⟨ D t ⟩) → Dyn' (λ t → ⟨ D t ⟩) → Type ℓ-zero
      order (nat n1) (nat n2) = n1 ≡ n2
      order (fun f) (fun g) = ∀ x y ->
        rel (▸' D) x y ->
        cust-order (f x) (g y)
          where
            cust-order' :
             ▹ (L℧ (Dyn' (λ t → ⟨ D t ⟩)) -> L℧ (Dyn' (λ t → ⟨ D t ⟩)) -> Type) ->
                L℧ (Dyn' (λ t → ⟨ D t ⟩)) -> L℧ (Dyn' (λ t → ⟨ D t ⟩)) -> Type
            cust-order' _ ℧ _ = Unit
            cust-order' rec (η x) (η y) = order x y
            cust-order' _ (η _) _ = ⊥
            cust-order' rec (θ lx~) (θ ly~) = {!!}
            cust-order' _ (θ _) _ = ⊥

            cust-order :  L℧ (Dyn' (λ t → ⟨ D t ⟩)) -> L℧ (Dyn' (λ t → ⟨ D t ⟩)) -> Type
            cust-order = fix cust-order'
         
      order _ _ = ⊥
-}

-- Alternate definition of Dyn' (different encoding of function case)

{-
data Dyn' (T : ▹ Type) : Type where
  nat : Nat -> Dyn' T
  fun  : ▸ (λ t → T t -> L℧ (T t)) -> Dyn' T

DynP' : (D : ▹ Predomain) -> Predomain
DynP' D = Dyn' (λ t -> ⟨ D t ⟩) , posetstr order {!!}
  where
    order : Dyn' (λ t → ⟨ D t ⟩) → Dyn' (λ t → ⟨ D t ⟩) → Type ℓ-zero
    order (nat n1) (nat n2) = n1 ≡ n2
    order (fun f) (fun g) = ∀ x y ->
      rel (▸' D) x y ->
      ▸ λ t -> rel (𝕃 (D t)) (f t (x t)) (g t (y t))
    order _ _ = ⊥
-}

----------------------------------------------------------
-- Third definition of DynP, where we build in the requirement that
-- the functions must be monotone

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

--DynP P = (▸ (λ t -> Dyn' (next ⟨ P t ⟩))) , posetstr {!!} {!!}

DynP : Predomain
DynP = fix DynP'

unfold-DynP : DynP ≡ DynP' (next DynP)
unfold-DynP = fix-eq DynP'



-- Equation for the underlying set of DynP
{-
unfold-⟨DynP⟩ : ⟨ DynP ⟩ ≡ Dyn' (next ⟨ DynP ⟩)
unfold-⟨DynP⟩ =
  ⟨ fix DynP' ⟩                    ≡⟨ (λ i → ⟨ unfold-DynP i ⟩ ) ⟩
  ⟨ DynP' (next DynP) ⟩            ≡⟨ refl ⟩
  Dyn' (λ t -> ⟨ (next DynP) t ⟩)  ≡⟨ refl ⟩
  Dyn' (next ⟨ DynP ⟩) ∎
-}


unfold-⟨DynP⟩ : ⟨ DynP ⟩ ≡ ⟨ DynP' (next DynP) ⟩
unfold-⟨DynP⟩ = λ i → ⟨ unfold-DynP i ⟩

-- Converting from the underlying set of DynP' to the underlying
-- set of DynP
DynP'-to-DynP : ⟨ DynP' (next DynP) ⟩ -> ⟨ DynP ⟩
DynP'-to-DynP d = transport (sym (λ i -> ⟨ unfold-DynP i ⟩)) d

DynP-to-DynP' : ⟨ DynP ⟩ -> ⟨ DynP' (next DynP) ⟩
DynP-to-DynP' d = transport (λ i → ⟨ unfold-DynP i ⟩) d


-- This basically is a monotonicity result, and could be
-- incorporated as a constant into the combinator language.
DynP-rel : ∀ d1 d2 ->
  rel (DynP' (next DynP)) d1 d2 ->
  rel DynP (DynP'-to-DynP d1) (DynP'-to-DynP d2)
DynP-rel d1 d2 d1≤d2 = transport
  (λ i → rel (unfold-DynP (~ i))
    (transport-filler (λ j -> ⟨ unfold-DynP (~ j) ⟩) d1 i)
    (transport-filler (λ j -> ⟨ unfold-DynP (~ j) ⟩) d2 i))
  d1≤d2


{-
rel-lemma : ∀ d1 d2 ->
  rel (DynP' (next DynP)) d1 d2 ->
  rel DynP (transport (sym unfold-⟨DynP⟩) d1) (transport (sym unfold-⟨DynP⟩) d2)
rel-lemma d1 d2 d1≤d2 = {!!}
transport
  (λ i -> rel (unfold-DynP (~ i))
    (transport-filler (λ j -> sym unfold-⟨DynP⟩ j ) d1 i)
    {!!}
    --(transport-filler (sym unfold-⟨DynP⟩) d1 i)
    --(transport-filler (sym unfold-⟨DynP⟩) d2 i)
  )
  d1≤d2
-}



-------------------------------------
-- *** Embedding-projection pairs ***


record EP (A B : Predomain) : Set where
  field
    emb : MonFun A B
    proj : MonFun B (𝕃 A)


-- Identity E-P pair

EP-id : (A : Predomain) -> EP A A
EP-id A = record {
  emb = record { f = id ; isMon = λ x≤y → x≤y };
  proj = record { f = ret ; isMon = ord-η-monotone A }}



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
p-nat = S (K p-nat') (mTransport unfold-DynP)
  -- or:
  -- mTransportDomain (sym unfold-DynP) p-nat'


EP-nat : EP ℕ DynP
EP-nat = record {
  emb = e-nat;
  proj = p-nat }


-- E-P Pair for monotone functions Dyn to L℧ Dyn

e-fun : MonFun (arr' DynP (𝕃 DynP)) DynP
e-fun = record { f = e-fun-f ; isMon = e-fun-mon }
  where
    e-fun-f : ⟨ arr' DynP (𝕃 DynP) ⟩ -> ⟨ DynP ⟩
    e-fun-f f = DynP'-to-DynP (fun (next f))

    e-fun-mon :
      {f1 f2 : ⟨ arr' DynP (𝕃 DynP) ⟩} ->
      rel (arr' DynP (𝕃 DynP)) f1 f2 ->
      rel DynP (e-fun-f f1) (e-fun-f f2)
    e-fun-mon {f1} {f2} f1≤f2 =
      DynP-rel (fun (next f1)) (fun (next f2)) (λ t d1 d2 d1≤d2 → {!!})


p-fun : MonFun DynP (𝕃 (arr' DynP (𝕃 DynP)))
p-fun = record { f = p-fun-f ; isMon = {!!} }
  where

    p-fun-f' : ⟨ DynP' (next DynP) ⟩ -> ⟨ 𝕃 (arr' DynP (𝕃 DynP)) ⟩
    p-fun-f' (nat n) = ℧
    p-fun-f' (fun f) = η {!!}

    p-fun-f : ⟨ DynP ⟩ -> ⟨ 𝕃 (arr' DynP (𝕃 DynP)) ⟩
    -- p-fun-f d = p-fun-f' (transport unfold-⟨DynP⟩ d)
    p-fun-f d = p-fun-f' (transport (λ i -> ⟨ unfold-DynP i ⟩) d)


EP-fun : EP (arr' DynP (𝕃 DynP)) DynP
EP-fun = record {
  emb = e-fun;
  proj = p-fun }




-- Composing EP pairs

module EPComp
  {A B C : Predomain}
  (epAB : EP A B)
  (epBC : EP B C) where

  open EP
  open MonFun

  comp-emb : ⟨ A ==> C ⟩
  comp-emb = K (emb epBC) <*> (emb epAB) -- mComp (emb epBC) (emb epAB)

  comp-proj : ⟨ C ==> 𝕃 A ⟩
  comp-proj = (mExt' (K (proj epAB))) <*> (proj epBC) -- mComp (mExt (proj epAB)) (proj epBC)
  --  comp-proj-f =
  --    λ c -> bind (f (proj epBC) c) (f (proj epAB)) ==
  --    λ c -> ext  (f (proj epAB)) (f (proj epBC) c) ==
  --    (ext (f (proj epAB))) ∘ (f (proj epBC c)) 

  EP-comp : EP A C
  EP-comp = record {
    emb = comp-emb;
    proj = comp-proj }


-- Lifting EP pairs to functions

module EPArrow
  {A A' B B' : Predomain}
  (epAA' : EP A A')
  (epBB' : EP B B') where

    e-arrow : ⟨ (A ==> 𝕃 B) ==> (A' ==> 𝕃 B') ⟩
    e-arrow = mFunEmb (EP.proj epAA') (EP.emb epBB')

    p-arrow : ⟨ (A' ==> (𝕃 B')) ==> (𝕃 (A ==> (𝕃 B))) ⟩
    p-arrow = mFunProj (EP.emb epAA') (EP.proj epBB')

{-
    p-lift :
      (A' -> L℧ B') -> L℧ (A -> L℧ B)
    p-lift f =
      ret (λ a → bind (f (EP.emb epAA' a)) (EP.proj epBB'))
-}


EP-arrow : {A A' B B' : Predomain} ->
  EP A A' ->
  EP B B' ->
  EP (arr' A (𝕃 B)) (arr' A' (𝕃 B'))
EP-arrow epAA' epBB' = record {
  emb = e-arrow;
  proj = p-arrow  }
  where open EPArrow epAA' epBB'



-------------------------------------------
-- *** Denotation of types and contexts ***

open EPComp


⟦_⟧ty : Ty -> Predomain
⟦ nat ⟧ty = ℕ
⟦ dyn ⟧ty = DynP
⟦ A => B ⟧ty = arr' ⟦ A ⟧ty (𝕃 ⟦ B ⟧ty)
-- ⟦ A ⟧ty -> L℧ ⟦ B ⟧ty

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
mLook A x = record {
  f = λ env -> look env A x ;
  isMon = λ {env1} {env2} env1≤env2 → look-mon env1 env2 A x env1≤env2 }



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
tm-sem (var z) = mRet' (mLook _ z)
tm-sem (lda M) = mRet' (K (tm-sem M) ∘m Pair)

{-
record {
  f = λ ⟦Γ⟧ -> ret
    (record {
      f = λ N -> MonFun.f (tm-sem M) (⟦Γ⟧ , N);
      isMon = {!!} }) ;
  isMon = {!!} }
-}
  
tm-sem {A} {Γ} (app {S = B} M1 M2) =
    let kont = (K (swap mExt) <*> tm-sem M2) in
    (mExt' kont <*> tm-sem M1)


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
    
tm-sem {A} err = K ℧
-- record { f = λ _ -> ℧ ; isMon = λ _ -> ord-bot ⟦ A ⟧ty ℧ }

tm-sem (up A⊑B M) = (mMap' (K (EP.emb ⟦ A⊑B ⟧lt))) <*> (tm-sem M)

{-
record {
  f =  λ ⟦Γ⟧ -> mapL (MonFun.f (EP.emb ⟦ A⊑B ⟧lt)) ((MonFun.f (tm-sem  M)) ⟦Γ⟧) ;
  isMon = {!!} }
-}
  
tm-sem (dn A⊑B M) = (mExt' (K (EP.proj ⟦ A⊑B ⟧lt))) <*> (tm-sem M)

{-
record { f =
  λ ⟦Γ⟧ -> bind ((MonFun.f (tm-sem M)) ⟦Γ⟧) (MonFun.f (EP.proj ⟦ A⊑B ⟧lt)) ;
  isMon = {!!} }
-}
  
tm-sem zro = K (η zero)
-- record { f = λ _ -> η zero ; isMon = λ _ → ord-refl ℕ (η zero) }

tm-sem (suc M) = (mExt' (K (mRet' mSuc))) <*> (tm-sem M)
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

open WeakRel

-- Homogeneous term precision relation
lttm-hom : {A : Ty} ->
  (Γ : Ctx) ->
  (M : Tm (lhs (Ctx-ref Γ)) A) ->
  (N : Tm (rhs (Ctx-ref Γ)) A) ->
  (Ctx-ref Γ) |- M ⊑tm N # (⊑ref A) ->
  (⟦ A ⟧ty ≾ ((MonFun.f ⟦ M ⟧tm) {!!})) ((MonFun.f ⟦ N ⟧tm) {!!})
lttm-hom Γ M N M⊑N = {!!}


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
  λ f1 f2 -> fun-order-het
    ⟦ Ain ⟧ty ⟦ Bin ⟧ty (𝕃 ⟦ Aout ⟧ty) (𝕃 ⟦ Bout ⟧ty)
    (typrecd-sem cin)
    (LiftRelation.ord ⟦ Aout ⟧ty ⟦ Bout ⟧ty (typrecd-sem cout))
    (MonFun.f f1) (MonFun.f f2)
typrecd-sem nat = rel ℕ
typrecd-sem inj-nat = λ n d -> rel' n (DynP-to-DynP' d)
  where
    rel' : ⟨ ℕ ⟩ -> ⟨ DynP' (next DynP) ⟩ -> Type
    rel' n (nat n') = n ≡ n'
    rel' n (fun _) = ⊥
typrecd-sem (inj-arrow c) = {!!}




------------------------------
-- *** Beta/eta properties ***



-- Semantic meaning of substitution

sub-lemma : (Γ : Ctx) (A B : Ty) -> (M : Tm (Γ :: A) B) -> (N : Tm Γ A) ->
  ⟦ M [ N ] ⟧tm ≡ {!!}
sub-lemma = {!!}

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

-- TODO need to stipulate that N is a value?
beta-lt : (Γ : Ctx) (A B : Ty) -> (M : Tm (Γ :: A) B) -> (N : Tm Γ A) ->
  rel (⟦ Γ ⟧ctx ==> 𝕃 ⟦ B ⟧ty)   ⟦ app (lda M) N ⟧tm   ⟦ M [ N ] ⟧tm
beta-lt Γ A B (var x) N = {!!}
beta-lt Γ A .(_ => _) (lda M) N = {!!}
beta-lt Γ A B (app M M₁) N = {!!}
beta-lt Γ A B err N = {!!}
beta-lt Γ A B (up x M) N = {!!}
beta-lt Γ A B (dn x M) N = {!!}
beta-lt Γ A .nat zro N = {!!}
beta-lt Γ A .nat (suc M) N = {!!}

eta : (Γ : Ctx) (A B : Ty) -> (M : Tm Γ (A => B)) ->
  rel {!!}  ⟦ M ⟧tm ⟦ {!lda!} ⟧tm
eta = {!!}


{-

-}
