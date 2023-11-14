{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.WeakBisimilarity (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sum

open import Cubical.Data.Empty as ⊥

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Poset

open import Cubical.HITs.PropositionalTruncation renaming (elim to PTelim)

open import Common.Common
open import Semantics.Lift k

private
  variable
    ℓ ℓ' ℓR : Level

  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


open BinaryRelation

-- Weak bisimilarity on Lift X, parameterized by a relation on X.
-- 
-- If this relation is instantiated with a PER on X, then the
-- properties below can be used to show that the resulting relation
-- on Lift X is also a PER.

module Bisim (X : Type ℓ) (R : X -> X -> Type ℓR) where

  -- We use the propositional truncation in the case where the LHS is η
  -- and RHS is θ or vice versa, so that the relation will be prop-valued
  -- whenever R is.
  module Inductive (rec : ▹ (L X -> L X -> Type (ℓ-max ℓ ℓR))) where

     _≈'_ :  L X -> L X -> Type (ℓ-max ℓ ℓR)
     η x ≈' η y = Lift {i = ℓR} {j = ℓ} (R x y)

     η x ≈' θ ly~ = ∥ Σ[ n ∈ ℕ ] Σ[ y ∈ X ] (θ ly~ ≡ (δL ^ n) (η y)) × R x y ∥₁
     
     θ lx~ ≈' η y = ∥ Σ[ n ∈ ℕ ] Σ[ x ∈ X ] (θ lx~ ≡ (δL ^ n) (η x)) × R x y ∥₁
     
     θ lx~ ≈' θ ly~ = ▸ (λ t -> rec t (lx~ t) (ly~ t))
  
  _≈_ : L X -> L X -> Type (ℓ-max ℓ ℓR)
  _≈_ = fix _≈'_
    where open Inductive

  unfold-≈ : _≈_ ≡ Inductive._≈'_ (next _≈_)
  unfold-≈ = fix-eq Inductive._≈'_

  open Inductive (next _≈_)

  ≈'→≈ : (l l' : L X) -> l ≈' l' -> l ≈ l'
  ≈'→≈ l l' l≈'l' = transport (sym (λ i -> unfold-≈ i l l')) l≈'l'

  ≈→≈' : (l l' : L X) -> l ≈ l' -> l ≈' l'
  ≈→≈' l l' l≈l' = transport (λ i -> unfold-≈ i l l') l≈l'


  -- Properties:
  -- ≈ is a congruence with respect to θ
  -- ≈ is closed under δ on both sides
  -- R is not transitive (follows from the previous two, plus a
  --   general result on relations defined on Lift X)
  -- If R is prop-valued, so is ≈
  -- If R is reflexive, so is ≈
  -- If R is symmetric, so is ≈

  θ-cong : {lx ly : ▹ (L X)} -> ▸ (λ t → (lx t) ≈ (ly t)) -> (θ lx) ≈ (θ ly)
  θ-cong {lx~} {ly~} H-later = ≈'→≈ (θ lx~) (θ ly~) H-later

  module PropValued (isPropValuedR : isPropValued R) where
     lem : ∀ n m (x y : X) -> (δL ^ n) (η x) ≡ (δL ^ m) (η y) -> (n ≡ m) × (x ≡ y)
     lem zero zero x y H = refl , inj-η x y H
     lem zero (suc m) x y H = ⊥.rec (Lη≠Lθ H)
     lem (suc n) zero x y H = ⊥.rec (Lη≠Lθ (sym H))
     lem (suc n) (suc m) x y H = {!!} -- *not provable!!*
     -- let IH = lem n m x y {!!} in {!!}

     prop-≈'→prop-≈ : BinaryRelation.isPropValued _≈'_ -> BinaryRelation.isPropValued _≈_
     prop-≈'→prop-≈ = transport (λ i -> BinaryRelation.isPropValued (sym unfold-≈ i))

     prop-≈→prop-≈' : BinaryRelation.isPropValued _≈_ -> BinaryRelation.isPropValued _≈'_
     prop-≈→prop-≈' = transport (λ i -> BinaryRelation.isPropValued (unfold-≈ i))

     prop' : ▹ (BinaryRelation.isPropValued _≈'_) -> BinaryRelation.isPropValued _≈'_
     prop' IH (η a) (η b) p q =
       let x = (isPropValuedR a b (lower p) (lower q)) in isoInvInjective LiftIso p q x
     prop' IH (η a) (θ lb~) p q = isPropPropTrunc p q --ΣPathP ({!snd q .snd .fst!} , {!!})
     prop' IH (θ la~) (η b) p q = isPropPropTrunc p q
     prop' IH (θ la~) (θ lb~) p q =
       λ i t → prop-≈'→prop-≈ (IH t) (la~ t) (lb~ t) (p t) (q t) i

     prop :  BinaryRelation.isPropValued _≈_
     prop = prop-≈'→prop-≈ (fix prop')


  module Reflexive (isReflR : isRefl R) where

     ≈'-refl : ▹ (isRefl _≈'_) -> isRefl _≈'_
     ≈'-refl _ (η x) = lift (isReflR x)
     ≈'-refl IH (θ lx~) = λ t → ≈'→≈ _ _ (IH t (lx~ t))

     ≈-refl : isRefl _≈_
     ≈-refl lx = ≈'→≈ _ _ (fix ≈'-refl lx)

     x≈'δx : ▹ ((lx : L X) -> lx ≈' (δL lx)) ->
                (lx : L X) -> lx ≈' (δL lx)
     x≈'δx _ (η x) = ∣ 1 , x , refl , isReflR x ∣₁
     x≈'δx IH (θ lx~) =
      λ t → ≈'→≈ (lx~ t) (θ lx~)
      (transport (λ i → (lx~ t) ≈' θ (next-Mt≡M lx~ t i)) (IH t (lx~ t)))

     x≈δx : (lx : L X) -> lx ≈ (δL lx)
     x≈δx lx = ≈'→≈ lx (δL lx) (fix x≈'δx lx)

  module Symmetric (isSymR : isSym R) where

    symmetric' :
      ▹ ((lx ly : L X) -> lx ≈' ly -> ly ≈' lx) ->
         (lx ly : L X) -> lx ≈' ly -> ly ≈' lx
    symmetric' _ (η x) (η y) xRy = lift (isSymR x y (lower xRy)) -- symmetry of the underlying relation
    symmetric' IH (θ lx~) (θ ly~) lx≈'ly =
      λ t → ≈'→≈  _ _ (IH t (lx~ t) (ly~ t) (≈→≈' _ _ (lx≈'ly t)))
    symmetric' _ (θ lx~) (η y) H =
      PTelim (λ _ -> isPropPropTrunc)
             (λ {(n , x , eq , xRy) -> ∣ n , x , eq , isSymR x y xRy ∣₁})
             H
    symmetric' _ (η x) (θ ly~) H =
      PTelim (λ _ -> isPropPropTrunc)
             (λ {(n , y , eq , xRy) -> ∣ n , y , eq , isSymR x y xRy ∣₁})
             H

    symmetric : (lx ly : L X ) -> lx ≈ ly -> ly ≈ lx
    symmetric lx ly lx≈ly =
      ≈'→≈ _ _ (fix symmetric' lx ly (≈→≈' _ _ lx≈ly))


-- A version of weak bisimilarity on Lift X that seems to *not* be
-- propositional. The issue is that in the two cases involving Σ, we cannot
-- prove that the natural number n and the value of type X are unique.
-- To do so seems to require that the function δL is injective,
-- but since δL = θ ∘ next, and next is not injective, then δL is not injective.
module NonPropBisim (X : Type ℓ) (R : X -> X -> Type ℓR) where

  module Inductive (rec : ▹ (L X -> L X -> Type (ℓ-max ℓ ℓR))) where

     _≈'_ :  L X -> L X -> Type (ℓ-max ℓ ℓR)
     η x ≈' η y = Lift {i = ℓR} {j = ℓ} (R x y)

     η x ≈' θ ly~ = Σ[ n ∈ ℕ ] Σ[ y ∈ X ] (θ ly~ ≡ (δL ^ n) (η y)) × R x y
     
     θ lx~ ≈' η y = Σ[ n ∈ ℕ ] Σ[ x ∈ X ] (θ lx~ ≡ (δL ^ n) (η x)) × R x y
     
     θ lx~ ≈' θ ly~ = ▸ (λ t -> rec t (lx~ t) (ly~ t))
  
  _≈_ : L X -> L X -> Type (ℓ-max ℓ ℓR)
  _≈_ = fix _≈'_
    where open Inductive

  unfold-≈ : _≈_ ≡ Inductive._≈'_ (next _≈_)
  unfold-≈ = fix-eq Inductive._≈'_




{-
module BisimSum (X : Type ℓ) (R : X -> X -> Type ℓR) where

  -- Weak bisimilarity as a sum type
  -- We could merge the middle two conditions, but we choose to keep them separate here.
  module Inductive (rec :  ▹ (L X -> L X -> Type (ℓ-max ℓ ℓR))) where 
    _≈'_ : L X -> L X -> Type (ℓ-max ℓ ℓR)
    l ≈' l' =  (Σ[ x ∈ X ] Σ[ y ∈ X ] (l ≡ η x) × (l' ≡ η y) × R x y) ⊎
               ((Σ[ x ∈ X ] Σ[ y ∈ X ] Σ[ n ∈ ℕ ] (l ≡ η x)            × (l' ≡ (δL ^ n) (η y)) × R x y) ⊎
               ((Σ[ x ∈ X ] Σ[ y ∈ X ] Σ[ n ∈ ℕ ] (l ≡ (δL ^ n) (η x)) × (l' ≡ η y)            × R x y) ⊎
               (Σ[ lx~ ∈ ▹ (L X) ] Σ[ ly~ ∈ ▹ (L X) ] (l ≡ θ lx~) × (l' ≡ θ ly~) × (▸ (λ t -> rec t (lx~ t) (ly~ t))))))

  _≈_ : L X → L X → Type (ℓ-max ℓ ℓR)
  _≈_ = fix Inductive._≈'_

  unfold-≈ : _≈_ ≡ Inductive._≈'_ (next _≈_)
  unfold-≈ = fix-eq Inductive._≈'_

  open Inductive (next _≈_)

  ≈'→≈ : (l l' : L X) -> l ≈' l' -> l ≈ l'
  ≈'→≈ l l' l≈'l' = transport (sym (λ i -> unfold-≈ i l l')) l≈'l'

  ≈→≈' : (l l' : L X) -> l ≈ l' -> l ≈' l'
  ≈→≈' l l' l≈l' = transport (λ i -> unfold-≈ i l l') l≈l'


-- Equivalence between the two definitions
module _ (X : Type ℓ) (R : X -> X -> Type ℓR) where

  open module B = Bisim X R
  open module BSum = BisimSum X R renaming (_≈_ to _≈S_)

  open B.Inductive (next _≈_)
  open BSum.Inductive (next _≈S_) renaming (_≈'_ to _≈S'_)

  ≈→≈Sum : (l l' : L X) -> l ≈ l' -> l ≈S l'
  ≈→≈Sum l l' l≈l' = BSum.≈'→≈ _ _(fix lem l l' (B.≈→≈' _ _ l≈l'))
      where
        lem : ▹ ((l l' : L X) -> l ≈' l' -> l ≈S' l') ->
                 (l l' : L X) -> l ≈' l' -> l ≈S' l'
        lem _ (η x) (η y) H = inl (x , (y , (refl , (refl , (lower H)))))
        lem _ (η x) (θ ly~) (n , y , eq , xRy) = inr (inl (x , y , n , refl , eq , xRy))
        lem _ (θ lx~) (η y) (n , x , eq , xRy) = inr (inr (inl (x , y , n , eq , refl , xRy)))
        lem IH (θ lx~) (θ ly~) H =
          inr (inr (inr (lx~ , ly~ , refl , refl ,
                         λ t -> BSum.≈'→≈ (lx~ t) (ly~ t) (IH t (lx~ t) (ly~ t) (B.≈→≈' _ _ (H t))))))
        
  ≈Sum→≈ : (l l' : L X) -> l ≈S l' -> l ≈ l'
  ≈Sum→≈ l l' l≈Sl' = {!!}
    where
      lem :  ▹ ((l l' : L X) -> l ≈S' l' -> l ≈' l') ->
                (l l' : L X) -> l ≈S' l' -> l ≈' l'
      lem _ l l' (inl (x , y , eq1 , eq2 , Rxy)) = (transport (λ i -> (sym eq1 i) ≈' (sym eq2 i)) (lift Rxy))
      lem _ l l' (inr (inl (x , y , n , eq1 , eq2 , Rxy))) = {!!} -- NTS that l' is of the form θ(...)


-}

{-
module _ (X : Type) (R : X -> X -> Type ℓR) where
   _≈^gl_ : L^gl X -> L^gl X -> Type ? where
-}
  

  
