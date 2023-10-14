{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}



open import Common.Later

module Semantics.Concrete.DynNew (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport

open import Cubical.Relation.Binary
open import Cubical.Data.Nat renaming (ℕ to Nat)
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma

open import Common.LaterProperties
--open import Common.Preorder.Base
--open import Common.Preorder.Monotone
--open import Common.Preorder.Constructions
open import Semantics.Lift k
-- open import Semantics.Concrete.LiftPreorder k

open import Cubical.Relation.Binary.Poset
open import Common.Poset.Convenience
open import Common.Poset.Constructions
open import Common.Poset.Monotone
open import Common.Poset.MonotoneRelation
open import Semantics.MonotoneCombinators
open import Semantics.Concrete.MonotonicityProofs

open import Semantics.LockStepErrorOrdering k

open BinaryRelation
open LiftPoset
open ClockedCombinators k


private
  variable
    ℓ ℓ' ℓX ℓX' : Level

  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A





-- Can have type Poset ℓ ℓ
DynP' : (D : ▹ Poset ℓ-zero ℓ-zero) -> Poset ℓ-zero ℓ-zero
DynP' D = ℕ ⊎p (▸' k (λ t → D t ==> 𝕃 (D t)))

DynP : Poset ℓ-zero ℓ-zero
DynP = fix DynP'



unfold-DynP : DynP ≡ DynP' (next DynP)
unfold-DynP = fix-eq DynP'

unfold-⟨DynP⟩ : ⟨ DynP ⟩ ≡ ⟨ DynP' (next DynP) ⟩
unfold-⟨DynP⟩ = λ i → ⟨ unfold-DynP i ⟩

DynP-Sum : DynP ≡ ℕ ⊎p ((▸'' k) (DynP ==> 𝕃 DynP))
DynP-Sum = unfold-DynP

⟨DynP⟩-Sum : ⟨ DynP ⟩ ≡ Nat ⊎ (▹ (⟨ DynP ==> 𝕃 DynP ⟩)) -- MonFun DynP (𝕃 DynP)
⟨DynP⟩-Sum i = ⟨ DynP-Sum i ⟩



case : {ℓA ℓB ℓC : Level} -> {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} ->
  (A -> C) -> (B -> C) -> ((A ⊎ B) -> C)
case f g =  λ { (inl a) → f a ; (inr b) → g b }


Rel-DynP-lem : ∀ d d' -> rel DynP d d' ->
      (Σ[ n ∈ ⟨ ℕ ⟩ ]
      (Σ[ n' ∈ ⟨ ℕ ⟩ ]
      (transport ⟨DynP⟩-Sum d ≡ inl n)
      × (transport ⟨DynP⟩-Sum d' ≡ inl n')
      × (n ≡ n'))) ⊎
      (Σ[ f~ ∈ ⟨ ▹' k ((DynP ==> 𝕃 DynP)) ⟩ ]
      (Σ[ g~ ∈ ⟨ ▹' k ((DynP ==> 𝕃 DynP)) ⟩ ]
      (transport ⟨DynP⟩-Sum d ≡ inr f~)
      × (transport ⟨DynP⟩-Sum d' ≡ inr g~)
      × (▸ (λ t → f~ t ≤mon g~ t))))
Rel-DynP-lem d d' d≤d' =
  let dSum = transport ⟨DynP⟩-Sum d in let d'Sum = transport ⟨DynP⟩-Sum d' in
  let dSum≤d'Sum = rel-transport DynP-Sum d≤d' in (rel-sum dSum d'Sum dSum≤d'Sum)


⊎p-rel-lem-l : {ℓA ℓ'A ℓB ℓ'B : Level} {A : Poset ℓA ℓ'A} {B : Poset ℓB ℓ'B} ->
  (a : ⟨ A ⟩) ->
  (x : ⟨ A ⟩ ⊎ ⟨ B ⟩) ->
  rel (A ⊎p B) (inl a) x ->
  Σ[ a' ∈ ⟨ A ⟩ ] (x ≡ inl a') × rel A a a'
⊎p-rel-lem-l a (inl a') H = a' , (refl , (lower H))

⊎p-rel-lem-r : {ℓA ℓ'A ℓB ℓ'B : Level} {A : Poset ℓA ℓ'A} {B : Poset ℓB ℓ'B} ->
  (b : ⟨ B ⟩) ->
  (x : ⟨ A ⟩ ⊎ ⟨ B ⟩) ->
  rel (A ⊎p B) (inr b) x ->
  Σ[ b' ∈ ⟨ B ⟩ ] (x ≡ inr b') × rel B b b'
⊎p-rel-lem-r b (inr b') H = b' , (refl , (lower H))




InjNat : ⟨ ℕ ==> DynP ⟩
InjNat = mCompU (mTransport (sym DynP-Sum)) σ1

InjArr : ⟨ (DynP ==> 𝕃 DynP) ==> DynP ⟩
InjArr = mCompU (mTransport (sym DynP-Sum)) (mCompU σ2 Next)

ProjNat : ⟨ DynP ==> 𝕃 ℕ ⟩
ProjNat = mCompU (Case' mRet (K _ ℧)) (mTransport DynP-Sum)

▹g→g : MonFun ((▸'' k) (DynP ==> 𝕃 DynP)) (𝕃 (DynP ==> 𝕃 DynP))
▹g→g = record {
   f = λ f~ -> θ (λ t -> η (f~ t)) ;
   isMon = λ {f~} {g~} f~≤g~ → ord-θ-monotone _ (λ t -> ord-η-monotone _ (f~≤g~ t)) }

ProjNat-nat : ∀ d n ->
  transport ⟨DynP⟩-Sum d ≡ inl n ->
  MonFun.f ProjNat d ≡ η n
ProjNat-nat d n eq =
  cong₂ (MonFun.f {X = DynP} {Y = 𝕃 ℕ})
        (refl {x = ProjNat})
        ((sym (transport⁻Transport ⟨DynP⟩-Sum d)) ∙ λ i -> transport⁻ ⟨DynP⟩-Sum (eq i))
  ∙ λ i → MonFun.f {!!} (transportTransport⁻ ⟨DynP⟩-Sum (inl n) i)

ProjNat-fun : ∀ d g~ ->
  transport ⟨DynP⟩-Sum d ≡ inr g~ ->
  MonFun.f ProjNat d ≡ ℧
ProjNat-fun d g~ eq =
  cong₂ (MonFun.f {X = DynP} {Y = 𝕃 ℕ})
        (refl {x = ProjNat})
        ((sym (transport⁻Transport ⟨DynP⟩-Sum d)) ∙ λ i -> transport⁻ ⟨DynP⟩-Sum (eq i))
  ∙ λ i → MonFun.f (Case' mRet (K {!𝕃 (DynP ==> 𝕃 DynP)!} ℧)) (transportTransport⁻ ⟨DynP⟩-Sum (inr g~) i)

ProjArr : ⟨ DynP ==> 𝕃 (DynP ==> 𝕃 DynP) ⟩
ProjArr = mCompU (Case' (K _ ℧) ▹g→g) (mTransport DynP-Sum)


ProjArr-nat : ∀ d n ->
  transport ⟨DynP⟩-Sum d ≡ inl n ->
  MonFun.f ProjArr d ≡ ℧
ProjArr-nat d n eq =
  cong₂ (MonFun.f {X = DynP} {Y = 𝕃 (DynP ==> 𝕃 DynP)})
        (refl {x = ProjArr})
        ((sym (transport⁻Transport ⟨DynP⟩-Sum d)) ∙ λ i -> transport⁻ ⟨DynP⟩-Sum (eq i))
  ∙ λ i → MonFun.f (Case' (K ℕ ℧) ▹g→g) (transportTransport⁻ ⟨DynP⟩-Sum (inl n) i)


ProjArr-fun : ∀ d g~ ->
  transport ⟨DynP⟩-Sum d ≡ inr g~ ->
  MonFun.f ProjArr d ≡ θ (λ t -> η (g~ t))
ProjArr-fun d g~ eq =
  cong₂ (MonFun.f {X = DynP} {Y = 𝕃 (DynP ==> 𝕃 DynP)})
        (refl {x = ProjArr})
        ((sym (transport⁻Transport ⟨DynP⟩-Sum d)) ∙ λ i -> transport⁻ ⟨DynP⟩-Sum (eq i))
  ∙ (λ i -> MonFun.f (Case' (K ℕ ℧) ▹g→g) (transportTransport⁻ ⟨DynP⟩-Sum (inr g~) i))

--  MonFun.f ProjArr (transport⁻ ⟨DynP⟩-Sum (inr g~)) ≡ _y_510

  {-{!!} ∙
  -- (λ i -> MonFun.f (mCompU (Case' (K _ ℧) aux) (mTransport DynP-Sum)) d) ∙
  (congS ((λ { (inl a) → MonFun.f (K ℕ ℧) a
             ; (inr b) → MonFun.f ▹g→g b
         })) eq) ∙
  refl -}
-- MonFun.f ProjArr d ≡ θ (λ t → η (g~ t))

-- (transp (λ i → ⟨ DynP-Sum i ⟩) i0 d)
-- transport ⟨DynP⟩-Sum d ≡ inr g~
{-

-- MonFun.f ( mCompU (Case' (K _ ℧) _) (mTransport DynP-Sum)) ?) ∙ ?

data Dyn' (D : ▹ Poset ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  nat : Nat -> Dyn' D
  fun : ▸ (λ t → MonFun (D t) (𝕃 (D t))) -> Dyn' D

Dyn'-iso : (D : ▹ Poset ℓ ℓ') -> Iso (Dyn' D) (Nat ⊎ (▸ (λ t → MonFun (D t) (𝕃 (D t)))))
Dyn'-iso D = iso
  (λ { (nat n) → inl n ; (fun f~) → inr f~})
  (λ { (inl n) → nat n ; (inr f~) → fun f~})
  (λ { (inl n) → refl ;  (inr f~) → refl})
  (λ { (nat x) → refl ;  (fun x) → refl})


DynP' :
    (D : ▹ Poset ℓ-zero ℓ-zero) -> Poset ℓ-zero ℓ-zero
DynP' D = Dyn' D ,
    posetstr order
      (isposet isSetDynP' dyn-ord-prop dyn-ord-refl dyn-ord-trans dyn-ord-antisym)
    where
      order : Dyn' D → Dyn' D → Type
      order (nat n) (nat m) = (n ≡ m)
      order (fun f~) (fun g~) = ▸ λ t → (f~ t) ≤mon (g~ t)
      order _ _ = ⊥

      isSetDynP' : isSet (Dyn' D)
      isSetDynP' = isSetRetract
        (Iso.fun (Dyn'-iso D)) (Iso.inv (Dyn'-iso D)) (Iso.leftInv (Dyn'-iso D))
        (isSet⊎ isSetℕ (isSet▸ λ t -> MonFunIsSet))

      dyn-ord-refl : isRefl order
      dyn-ord-refl (nat n) = refl
      dyn-ord-refl (fun f~) = λ t → ≤mon-refl (f~ t)

      dyn-ord-prop : isPropValued order
      dyn-ord-prop (nat n) (nat m) = isSetℕ n m
      dyn-ord-prop (fun f~) (fun g~) = isProp▸ (λ t -> ≤mon-prop (f~ t) (g~ t))

      dyn-ord-trans : isTrans order
      dyn-ord-trans (nat n1) (nat n2) (nat n3) n1≡n2 n2≡n3 =
        n1≡n2 ∙ n2≡n3
      dyn-ord-trans (fun f1~) (fun f2~) (fun f3~) H1 H2 =
        λ t → ≤mon-trans (f1~ t) (f2~ t) (f3~ t) (H1 t) (H2 t)

      dyn-ord-antisym : isAntisym order
      dyn-ord-antisym (nat n) (nat m) n≡m m≡n = cong nat n≡m
      dyn-ord-antisym (fun f~) (fun g~) d≤d' d'≤d =
        cong fun (eq▸ f~ g~ λ t -> ≤mon-antisym (f~ t) (g~ t) (d≤d' t) (d'≤d t))


DynP : Poset ℓ-zero ℓ-zero
DynP = fix DynP'

unfold-DynP : DynP ≡ DynP' (next DynP)
unfold-DynP = fix-eq DynP'

unfold-⟨DynP⟩ : ⟨ DynP ⟩ ≡ ⟨ DynP' (next DynP) ⟩
unfold-⟨DynP⟩ = λ i → ⟨ unfold-DynP i ⟩

unfold-DynP-rel : PathP (λ i -> {!lift (unfold-⟨DynP⟩ i)!}) (rel DynP) (rel (DynP' (next DynP)))
unfold-DynP-rel = {!!}


-- Converting from the underlying set of DynP' to the underlying
-- set of DynP
DynP'→DynP : ⟨ DynP' (next DynP) ⟩ -> ⟨ DynP ⟩
DynP'→DynP d = transport (sym (λ i -> ⟨ unfold-DynP i ⟩)) d

DynP→DynP' : ⟨ DynP ⟩ -> ⟨ DynP' (next DynP) ⟩
DynP→DynP' d = transport (λ i → ⟨ unfold-DynP i ⟩) d


rel-DynP'→rel-DynP : ∀ d1 d2 ->
  rel (DynP' (next DynP)) d1 d2 ->
  rel DynP (DynP'→DynP d1) (DynP'→DynP d2)
rel-DynP'→rel-DynP d1 d2 d1≤d2 = transport
  (λ i → rel (unfold-DynP (~ i))
    (transport-filler (λ j → ⟨ unfold-DynP (~ j) ⟩) d1 i)
    (transport-filler (λ j → ⟨ unfold-DynP (~ j) ⟩) d2 i))
  d1≤d2

rel-DynP→rel-DynP' : ∀ d1 d2 ->
  rel DynP d1 d2 ->
  rel (DynP' (next DynP)) (DynP→DynP' d1) (DynP→DynP' d2)
rel-DynP→rel-DynP' d1 d2 d1≤d2 = transport
  (λ i → rel (unfold-DynP i)
    (transport-filler (λ j -> ⟨ unfold-DynP j ⟩) d1 i)
    (transport-filler (λ j -> ⟨ unfold-DynP j ⟩) d2 i))
  d1≤d2

DynP-equiv : PosetEquiv DynP (DynP' (next DynP))
DynP-equiv = pathToEquiv unfold-⟨DynP⟩ ,
             makeIsPosetEquiv (pathToEquiv unfold-⟨DynP⟩)
               (λ d1 d2 d1≤d2 -> rel-DynP→rel-DynP' d1 d2 d1≤d2)
               (λ d1 d2 d1≤d2 -> {!rel-DynP'→rel-DynP d1 d2 d1≤d2!})





InjNat : ⟨ ℕ ==> DynP ⟩
InjNat = record {
  f = λ n -> DynP'→DynP (nat n) ;
  isMon = λ {n} {m} n≡m ->
    rel-DynP'→rel-DynP (nat n) (nat m) n≡m }


InjArr : ⟨ (DynP ==> 𝕃 DynP) ==> DynP ⟩
InjArr = record {
  f = λ f -> DynP'→DynP (fun (next f)) ;
  isMon = λ {f1} {f2} f1≤f2 ->
    rel-DynP'→rel-DynP (fun (next f1)) (fun (next f2)) λ t -> f1≤f2 }


-}
