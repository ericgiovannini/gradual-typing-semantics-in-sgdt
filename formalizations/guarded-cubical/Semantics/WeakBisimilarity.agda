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

open import Cubical.HITs.PropositionalTruncation renaming (elim to PTelim ; rec to PTrec)

open import Common.Common
open import Common.LaterProperties
open import Semantics.Lift k

private
  variable
    ℓ ℓ' ℓR : Level

  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


open BinaryRelation

-- If θ l~ is an iterated delay of l for some l, then one time
-- step later, l~ t is also an iterated delay
lem-θ-δ : {X : Type ℓ} -> {l~ : ▹ L X} -> {l : L X} -> (n : ℕ) ->
  (θ l~) ≡ (δL ^ (suc n)) l -> ▸ (λ t -> l~ t ≡ (δL ^ n) l)
lem-θ-δ {l~ = l~} {l = l} n H t = inj-θL l~ (next ((δL ^ n) l)) H t


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


  -- In the definition of the relation, whenever we have a Σ n,
  -- we only require that it is ≥ 0. But in fact we can show that
  -- it must be at least 1.
  -- It seems more convenient to define the ordering as we do
  -- and then prove these lemmas after the fact.
  θ≈η-lem-suc : {lx~ : ▹ L X} -> {y : X} -> θ lx~ ≈' η y ->
    ∥ Σ[ n ∈ ℕ ] Σ[ x ∈ X ] ((θ lx~ ≡ (δL ^ (suc n)) (η x)) × R x y) ∥₁
  θ≈η-lem-suc H = PTrec isPropPropTrunc (λ {
    (zero , y , eq , xRy) → ⊥.rec (Lη≠Lθ (sym eq)) ;
    (suc n , y , eq , xRy) → ∣ n , y , {!!} ∣₁}) H


  -- Bisimilarity when one side is η
  ≈'-η : ∀ lx y → lx ≈' η y →
    ∥ Σ[ n ∈ ℕ ] Σ[ x ∈ X ] (lx ≡ (δL ^ n) (η x)) × (R x y) ∥₁ -- need propositional truncation
  ≈'-η (η x) y Rxy = ∣ 0 , x , refl , lower Rxy ∣₁
  ≈'-η (θ lx~) y H = PTrec isPropPropTrunc (λ
    {(n , x , eq , Rxy) → ∣ n , x , eq , Rxy ∣₁}) H



  module PropValued (isPropValuedR : isPropValued R) where
     -- lem : ∀ n m (x y : X) -> (δL ^ n) (η x) ≡ (δL ^ m) (η y) -> (n ≡ m) × (x ≡ y)
     -- lem zero zero x y H = refl , inj-η x y H
     -- lem zero (suc m) x y H = ⊥.rec (Lη≠Lθ H)
     -- lem (suc n) zero x y H = ⊥.rec (Lη≠Lθ (sym H))
     -- lem (suc n) (suc m) x y H = {!!} -- *not provable!!*
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
     prop' IH (θ la~) (θ lb~) p q = isProp▸ (λ t -> prop-≈'→prop-≈ (IH t) (la~ t) (lb~ t)) p q
       -- or, more explicitly: λ i t → prop-≈'→prop-≈ (IH t) (la~ t) (lb~ t) (p t) (q t) i

     prop :  BinaryRelation.isPropValued _≈_
     prop = prop-≈'→prop-≈ (fix prop')


     absurd : ∀ X -> ▹ (▹ X) → ▹ X
     absurd X llx = λ t -> {!llx t t!}
    

     ≈'-δ^n-η-sufficient : (x y : X) (n : ℕ) →
       R x y → (δL ^ n) (η x) ≈' η y
     ≈'-δ^n-η-sufficient x y zero H = lift H
     ≈'-δ^n-η-sufficient x y (suc n) H = ∣ suc n , x , refl , H ∣₁

     lem : ∀ n x y → δL ((δL ^ n) (η x)) ≈' η y → (δL ^ n) (η x) ≈' η y
     lem n x y H =
       PTrec (prop-≈→prop-≈' prop _ _)
             (λ {(n' , x' , eq) →
               {!!}})
             H


     -- If lx ≈ ly, then lx ≈ δL ly.
     -- This is more general than the corresponding "homogeneous" version
     -- i.e., x ≈ (δL x). This proof is more involved because we need to
     -- consider both lx and ly, which leads to complications in the case
     -- where lx is θ and ly is η, because when we add a θ on the right,
     -- now both sides are a θ and so we change to a different case of
     -- the relation than the one used to prove the assumption lx ≈ ly.
     δ-closed-r : ▹ ((lx ly : L X) -> lx ≈' ly -> lx ≈' (δL ly)) ->
                     (lx ly : L X) -> lx ≈' ly -> lx ≈' (δL ly)
     δ-closed-r _ (η x) (η y) lx≈'ly = ∣ 1 , y , refl , lower lx≈'ly ∣₁ 

     δ-closed-r _ (η x) (θ ly~) lx≈'ly =
       PTrec isPropPropTrunc (λ {(n , y , eq , xRy) -> ∣ suc n , y , cong δL eq  , xRy ∣₁}) lx≈'ly

     δ-closed-r _ (θ lx~) (η y) lx≈'ly =      -- lx≈'ly : θ lx~ ≈' η y
       let lem1 = θ≈η-lem-suc lx≈'ly in
       PTrec (prop-≈→prop-≈' prop _ _)
             (λ {(n , x , eq , xRy) ->              -- eq : θ lx~ ≡ δL ((δL ^ n) (η x))
               let lem2 = lem-θ-δ n eq in
                 λ t -> transport (λ i -> sym (lem2 t) i ≈ (η y)) (≈'→≈ _ _ (≈'-δ^n-η-sufficient x y n xRy)) })
             lem1

       {-
       λ t ->
       PTrec (prop _ _) (λ {(n , x , eq , xRy) ->
         let lem1 = θ≈η-lem-suc lx≈'ly in
         let lem2 = lem-θ-δ n {!!} in
         PTrec (prop _ _) (λ {(n' , x' , eq') -> {!lem-θ-δ n' eq' t!}}) lem1}) lx≈'ly
         -}
    

     δ-closed-r IH (θ lx~) (θ ly~) lx≈'ly =
       λ t -> ≈'→≈ _ _ (transport
         (cong₂ _≈'_ refl (congS θ (next-Mt≡M ly~ t)))
         (IH t (lx~ t) (ly~ t) (≈→≈' _ _ (lx≈'ly t))))


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

     -- The "homogeneous" version of the above property about closure
     -- under δ.
     x≈δx : (lx : L X) -> lx ≈ (δL lx)
     x≈δx lx = ≈'→≈ lx (δL lx) (fix x≈'δx lx)

     x≈δ^nx : (n : ℕ) -> (lx : L X) -> lx ≈ (δL ^ n) lx
     x≈δ^nx zero lx = ≈-refl lx
     x≈δ^nx (suc n) lx = {!!}

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







module BisimSum (X : Type ℓ) (R : X -> X -> Type ℓR) where

  -- Weak bisimilarity as a sum type
  -- We could merge the middle two conditions, but we choose to keep them separate here.
  module Inductive (rec :  ▹ (L X -> L X -> Type (ℓ-max ℓ ℓR))) where 
    _≈'_ : L X -> L X -> Type (ℓ-max ℓ ℓR)
    l ≈' l' =  (Σ[ x ∈ X ] Σ[ y ∈ X ] (l ≡ η x) × (l' ≡ η y) × R x y) ⊎
              ((Σ[ x ∈ X ] ((l  ≡ η x) × ∥ Σ[ n ∈ ℕ ] Σ[ y ∈ X ] ((l' ≡ (δL ^ n) (η y)) × R x y) ∥₁)) ⊎
              ((Σ[ y ∈ X ] ((l' ≡ η y) × ∥ Σ[ n ∈ ℕ ] Σ[ x ∈ X ] ((l  ≡ (δL ^ n) (η x)) × R x y) ∥₁)) ⊎
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
        lem _ (η x) (θ ly~) H = inr (inl (x , refl , H))
        lem _ (θ lx~) (η y) H = inr (inr (inl (y , refl , H)))
        lem IH (θ lx~) (θ ly~) H =
          inr (inr (inr (lx~ , ly~ , refl , refl ,
                         λ t -> BSum.≈'→≈ (lx~ t) (ly~ t) (IH t (lx~ t) (ly~ t) (B.≈→≈' _ _ (H t))))))

{-
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
  

  
-- Global version:
-- lx ≈g ly <-->
-- lx ≡ η^gl x × ly ≡ η^gl y × x ≈ y  +
-- lx ≡ η^gl x × ly ≡ (δ^gl)^n (η^gl y) × x ≈ y   +
-- ly ≡ η^gl y × lx ≡ (δ^gl)^n (η^gl x) × x ≈ y   +
-- lx ≡ δ^gl lx' × ly ≡ δ^gl ly' × lx' ≈g ly'

-- ∀k. Σ[ l1~ ∈ ▹ L k X ] Σ[ l2~ ∈ ▹ L k X ]
--   (l1^g k ≡ θ l1~) × (l2^g k ≡ θ l2~) × (▸k_t [ l1~ t ≈_k l2~ t ])

-- Σ[ l1'^g ∈ ∀k. L k X ] Σ[ l2'^g ∈ ∀k. L k Y ]
--   ∀k. ((l1^g ≡ δ^gl l1'^g) × (l2^g ≡ δ^gl l2'^g) × (▸k_t [ l1'^g k ≈_k l2'^g k ]))






-- Σ[ l1'^g ∈ ∀k. L k X ] Σ[ l2'_g ∈ ∀k. L k Y ]
--   (l1^g ≡ δ^gl l1'^g) × (l2^g ≡ δ^gl l2'^g) × (l1'^g ≈g l2'^g)
--
-- ∀k. Σ[ l1 ∈ L k X ] Σ[ l2 ∈ L k Y]
--   (l1^g k ≡ δ k l1) × (l2^g k ≡ δ k l2) × (l1 ≈_k l2)
--
-- ∀k. ▹ Σ[ l1 ∈ L k X ] Σ[ l2 ∈ L k Y]
--   (l1^g k ≡ δ k l1) × (l2^g k ≡ δ k l2) × (l1 ≈_k l2)
--
-- ∀k. Σ[ l1~ ∈ ▹ L k X ] Σ[ l2~ ∈ ▹ L k X ]
--   ▸_t [ (l1^g k ≡ δ k (l1~ t)) × (l2^g k ≡ δ k (l2~ t)) × (l1~ t ≈_k l2~ t) ]
--
-- ∀k. Σ[ l1~ ∈ ▹ L k X ] Σ[ l2~ ∈ ▹ L k X ]
--   ▸_t [ l1^g k ≡ δ k (l1~ t) ] × ▸_t [ l2^g k ≡ δ k (l2~ t) ] × ▸_t [ l1~ t ≈_k l2~ t ]
--
-- ∀k. Σ[ l1~ ∈ ▹ L k X ] Σ[ l2~ ∈ ▹ L k X ] 
--   (l1^g k ≡ δ k (l1~ ◇)) × (l2^g k ≡ δ k (l2~ ◇)) × ▸_t [ l1~ t ≈_k l2~ t ]
--
-- ∀k. Σ[ l1~ ∈ ▹ L k X ] Σ[ l2~ ∈ ▹ L k X ]
--   (l1^g k ≡ θ k l1~) × (l2^g k ≡ θ k l2~) × ▸_t [ l1~ t ≈_k l2~ t ]
 

-- ∀k. (▸_t [ l1^g k ≡ δ k (l1~ t) ] × ▸_t [ l2^g k ≡ δ k (l2~ t) ] × ▸_t [ l1~ t ≈_k l2~ t ])

-- ∀k. ▸_t [ l1^g k ≡ δ k (l1~ t) ] × ∀k. ▸_t [ l2^g k ≡ δ k (l2~ t) ] × ∀k. ▸_t [ l1~ t ≈_k l2~ t ]

-- ∀k. ▸_t [ l1^g k ≡ θ k l1~ ] × ∀k. ▸_t [ l2^g k ≡ θ k l2~ ] × ∀k. ▸_t [ l1~ t ≈_k l2~ t ]

-- ∀k. (l1^g k ≡ θ k l1~) × ∀k. l2^g k ≡ θ k l2~ × ∀k. ▸_t [ l1~ t ≈_k l2~ t ]



-- ... × (θ l1~) ≈_k (θ l2~)
