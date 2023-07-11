{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Later

module Semantics.Concrete.Dyn (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Relation.Binary
open import Cubical.Data.Nat renaming (ℕ to Nat)
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty

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


open import Semantics.LockStepErrorOrdering k

open BinaryRelation
open LiftPoset

private
  variable
    ℓ ℓ' : Level

  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


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








{-
-- Poset Structure on Dyn
module DynPoset (ℓ ℓ' : Level) where

  DynP' :
    (D : ▹ Poset ℓ ℓ') -> Poset (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  DynP' D = Dyn' D ,
    posetstr order
      (isposet isSetDynP' dyn-ord-prop dyn-ord-refl dyn-ord-trans dyn-ord-antisym)
    where
      order : Dyn' D → Dyn' D → Type (ℓ-max ℓ ℓ')
      order (nat n) (nat m) = Lift (n ≡ m)
      order (fun f~) (fun g~) = ▸ λ t → (f~ t) ≤mon (g~ t)
      order _ _ = ⊥*

      isSetDynP' : isSet (Dyn' D)
      isSetDynP' = isSetRetract
        (Iso.fun (Dyn'-iso D)) (Iso.inv (Dyn'-iso D)) (Iso.leftInv (Dyn'-iso D))
        (isSet⊎ isSetℕ (isSet▸ λ t -> MonFunIsSet))

      dyn-ord-refl : isRefl order
      dyn-ord-refl (nat n) = lift refl
      dyn-ord-refl (fun f~) = λ t → ≤mon-refl (f~ t)

      dyn-ord-prop : isPropValued order
      dyn-ord-prop (nat n) (nat m) = isOfHLevelLift 1 (isSetℕ n m)
      dyn-ord-prop (fun f~) (fun g~) = isProp▸ (λ t -> ≤mon-prop (f~ t) (g~ t))

      dyn-ord-trans : isTrans order
      dyn-ord-trans (nat n1) (nat n2) (nat n3) (lift n1≡n2) (lift n2≡n3) =
        lift (n1≡n2 ∙ n2≡n3)
      dyn-ord-trans (fun f1~) (fun f2~) (fun f3~) H1 H2 =
        λ t → ≤mon-trans (f1~ t) (f2~ t) (f3~ t) (H1 t) (H2 t)

      dyn-ord-antisym : isAntisym order
      dyn-ord-antisym (nat n) (nat m) (lift n≡m) (lift m≡n) = cong nat n≡m
      dyn-ord-antisym (fun f~) (fun g~) d≤d' d'≤d =
        cong fun (eq▸ f~ g~ λ t -> ≤mon-antisym (f~ t) (g~ t) (d≤d' t) (d'≤d t))


  DynP : Poset ? ?
  DynP = fix DynP'


  
  unfold-DynP : DynP ≡ DynP' (next DynP)
  unfold-DynP = fix-eq DynP'


  unfold-⟨DynP⟩ : {ℓ ℓ' : Level} -> ⟨ DynP ⟩ ≡ ⟨ DynP' (next (DynP {ℓ} {ℓ'})) ⟩
  unfold-⟨DynP⟩ {ℓ} {ℓ'} = λ i → ⟨ unfold-DynP {ℓ} {ℓ'} i ⟩


  -- Converting from the underlying set of DynP' to the underlying
  -- set of DynP
  DynP'→DynP : ⟨ DynP' (next DynP) ⟩ -> ⟨ DynP ⟩
  DynP'→DynP d = transport (sym (λ i -> ⟨ unfold-DynP i ⟩)) d

  DynP→DynP' : ⟨ DynP ⟩ -> ⟨ DynP' (next DynP) ⟩
  DynP→DynP' d = transport (λ i → ⟨ unfold-DynP i ⟩) d


  DynP-rel : ∀ d1 d2 ->
    rel (DynP' (next DynP)) d1 d2 ->
    rel DynP (DynP'→DynP d1) (DynP'→DynP d2)
  DynP-rel d1 d2 d1≤d2 = transport
    (λ i → rel (unfold-DynP (~ i))
      (transport-filler (λ j -> ⟨ unfold-DynP (~ j) ⟩) d1 i)
      (transport-filler (λ j -> ⟨ unfold-DynP (~ j) ⟩) d2 i))
  d1≤d2

  DynP'-rel : ∀ d1 d2 ->
    rel DynP d1 d2 ->
    rel (DynP' (next DynP)) (DynP→DynP' d1) (DynP→DynP' d2)
  DynP'-rel d1 d2 d1≤d2 = transport
    (λ i → rel (unfold-DynP i)
      (transport-filler (λ j -> ⟨ unfold-DynP j ⟩) d1 i)
      (transport-filler (λ j -> ⟨ unfold-DynP j ⟩) d2 i))
    d1≤d2
  

-}

