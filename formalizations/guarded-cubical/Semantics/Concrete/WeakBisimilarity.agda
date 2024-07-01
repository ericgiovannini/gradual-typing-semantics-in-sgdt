{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.WeakBisimilarity (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.HITs.PropositionalTruncation
  renaming (elim to PTelim ; rec to PTrec ; map to PTmap)

open import Common.Common
open import Common.LaterProperties

open import Semantics.Concrete.GuardedLift k
-- open import Semantics.Concrete.GuardedLiftError k

private
  variable
    ℓ ℓ' ℓR ℓS : Level

  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


open BinaryRelation

-- If θ l~ is an iterated delay of l for some l, then one time
-- step later, l~ t is also an iterated delay
lem-θ-δ : {X : Type ℓ} -> {l~ : ▹ L X} -> {l : L X} -> (n : ℕ) ->
  (θ l~) ≡ (δ ^ (suc n)) l -> ▸ (λ t -> l~ t ≡ (δ ^ n) l)
lem-θ-δ {l~ = l~} {l = l} n H t = inj-θL l~ (next ((δ ^ n) l)) H t


-- Weak bisimilarity on Lift X, parameterized by a relation on X.
-- 
-- If this relation is instantiated with a PER on X, then the
-- properties below can be used to show that the resulting relation
-- on Lift X is also a PER.



{-

  -- In the definition of the relation, whenever we have a Σ n,
  -- we only require that it is ≥ 0. But in fact we can show that
  -- it must be at least 1.
  -- It seems more convenient to define the ordering as we do
  -- and then prove these lemmas after the fact.
  θ≈η-lem-suc : {lx~ : ▹ L X} -> {y : X} -> θ lx~ ≈' η y ->
    Σ[ n ∈ ℕ ] Σ[ x ∈ X ] ((θ lx~ ≡ (δ ^ (suc n)) (η x)) × R x y)
  θ≈η-lem-suc (zero , x , eq , xRy) = ⊥.rec (Lη≠Lθ (sym eq))
  θ≈η-lem-suc (suc n , x , eq , xRy) = n , x , eq , xRy


  -- Bisimilarity when one side is η
  ≈'-η : ∀ lx y → lx ≈' η y →
    Σ[ n ∈ ℕ ] Σ[ x ∈ X ] (lx ≡ (δ ^ n) (η x)) × (R x y)
  ≈'-η (η x) y Rxy = (0 , x , refl , lower Rxy)
  ≈'-η (θ lx~) y H = H
 

  module PropValued (isPropValuedR : isPropValued R) where
   

     prop-≈'→prop-≈ : BinaryRelation.isPropValued _≈p_ -> BinaryRelation.isPropValued _≈_
     prop-≈'→prop-≈ = transport (λ i -> BinaryRelation.isPropValued (sym unfold-≈ i))

     prop :  BinaryRelation.isPropValued _≈_
     prop = prop-≈'→prop-≈ λ lx ly → isPropPropTrunc
    

     ≈'-δ^n-η-sufficient : (x y : X) (n : ℕ) →
       R x y → (δ ^ n) (η x) ≈' η y
     ≈'-δ^n-η-sufficient x y zero H = lift H
     ≈'-δ^n-η-sufficient x y (suc n) H = (suc n , x , refl , H)



     -- If lx ≈ ly, then lx ≈ δ ly.
     -- This is more general than the corresponding "homogeneous" version
     -- i.e., x ≈ (δ x). This proof is more involved because we need to
     -- consider both lx and ly, which leads to complications in the case
     -- where lx is θ and ly is η, because when we add a θ on the right,
     -- now both sides are a θ and so we change to a different case of
     -- the relation than the one used to prove the assumption lx ≈ ly.
     δ-closed-r : ▹ ((lx ly : L X) -> lx ≈p ly -> lx ≈p (δ ly)) ->
                     (lx ly : L X) -> lx ≈p ly -> lx ≈p (δ ly)
     δ-closed-r _ (η x) (η y) lx≈ply = PTrec isPropPropTrunc (λ H → ∣ 1 , y , refl , lower H ∣₁) lx≈ply

     δ-closed-r _ (η x) (θ ly~) lx≈ply =
       PTrec isPropPropTrunc (λ {(n , y , eq , xRy) -> ∣ suc n , y , cong δ eq  , xRy ∣₁}) lx≈ply


     δ-closed-r _ (θ lx~) (η y) lx≈ply =            -- lx≈ply : θ lx~ ≈p η y
       let lem1 = PTmap θ≈η-lem-suc lx≈ply in
        PTrec isPropPropTrunc
             (λ {(n , x , eq , xRy) ->              -- eq : θ lx~ ≡ δ ((δ ^ n) (η x))
               let lem2 = lem-θ-δ n eq in
               ∣ (λ t → transport
                         (λ i → sym (lem2 t) i ≈ η y)
                         (≈'→≈ _ _ (≈'-δ^n-η-sufficient x y n xRy)))
               ∣₁})
          lem1

     δ-closed-r IH (θ lx~) (θ ly~) lx≈ply =
       PTrec isPropPropTrunc (λ H → ∣ aux H ∣₁) lx≈ply
       where
         aux : (H : θ lx~ ≈' θ ly~) → θ lx~ ≈' δ (θ ly~)
         aux H t = ≈p→≈ _ _ (transport
           (cong ∥_∥₁ (cong₂ _≈'_ refl (congS θ (next-Mt≡M ly~ t))))
           (IH t (lx~ t) (ly~ t) (≈→≈p _ _ (H t))))


-}

module LiftBisim (X : Type ℓ) (R : X → X → Type ℓR) where

  data _≈_ : L X → L X → Type (ℓ-max ℓ ℓR) where
    ≈ηη : ∀ (x y : X) → R x y →
      (η x) ≈ (η y)
      
    ≈ηθ : ∀ (x : X) (ly : L X) →
      ∥ Σ[ n ∈ ℕ ] Σ[ y ∈ X ] ((ly ≡ (δ ^ suc n) (η y)) × R x y) ∥₁ →
      (η x) ≈ ly
      
    ≈θη : ∀ (lx : L X) (y : X) →
      ∥ Σ[ n ∈ ℕ ] Σ[ x ∈ X ] ((lx ≡ (δ ^ suc n) (η x)) × R x y) ∥₁ →
      lx ≈ (η y)
      
    ≈θθ : ∀ (lx~ ly~ : ▹ L X) → ▸ (λ t → (lx~ t) ≈ (ly~ t)) →
      (θ lx~) ≈ (θ ly~)



  -- Eliminator for the weak bisimilarity type.  We are given a
  -- dependent type B parameterized by lx, ly, and a proof that lx ≈I
  -- ly.  The eliminator allows us to construct a proof that for any
  -- lx and ly s.t. P : lx ≈I ly, we have B lx ly P.  Note that since
  -- weak bisimilarity is prop-valued given a fixed lx and ly, the
  -- specific proof of weak bisimilarity is irrelevant.
  module Elim {B : ∀ lx ly → lx ≈ ly → Type ℓ'}

    -- In all four of the cases, the user gets to assume that the
    -- eliminator is defined later when constructing an element of B.
    (≈ηη* :
      (IH : ▹ ((lx ly : L X) (lx≈ly : lx ≈ ly) → B lx ly lx≈ly)) →
      (x y : X) →
      (H : R x y) →
      B (η x) (η y) (≈ηη x y H))

    (≈ηθ* :
      (IH : ▹ ((lx ly : L X) (lx≈ly : lx ≈ ly) → B lx ly lx≈ly)) →
      (x : X) (ly : L X) →
      (H : ∥ Σ[ n ∈ ℕ ] Σ[ y ∈ X ] ((ly ≡ (δ ^ suc n) (η y)) × R x y) ∥₁) →
      B  (η x)  ly  (≈ηθ x ly H))
      
    (≈θη* :
      (IH : ▹ ((lx ly : L X) (lx≈ly : lx ≈ ly) → B lx ly lx≈ly)) →
      (lx : L X) (y : X) →
      (H : ∥ Σ[ n ∈ ℕ ] Σ[ x ∈ X ] ((lx ≡ (δ ^ suc n) (η x)) × R x y) ∥₁) →
      B  lx  (η y) (≈θη lx y H))
      
    (≈θθ* :
      (IH : ▹ ((lx ly : L X) (lx≈ly : lx ≈ ly) → B lx ly lx≈ly)) →
      (lx~ ly~ : ▹ L X) →
      (H : ▸ (λ t → (lx~ t) ≈ (ly~ t))) →
      B (θ lx~) (θ ly~) (≈θθ lx~ ly~ H)) where

    f : (lx ly : L X) → (lx≈ly : lx ≈ ly) → B lx ly lx≈ly
    f lx ly lx≈ly = (fix aux lx ly lx≈ly)
      where
       -- To be able to instantiate the first argument of each of
       -- ≈ηη*, ≈ηθ*, ≈θη*, and ≈θθ* we need to assume that the
       -- eliminator is defined later.
        aux : ▹ ((lx ly : L X) (lx≈'ly : lx ≈ ly) → B lx ly lx≈'ly) →
                 (lx ly : L X) (lx≈'ly : lx ≈ ly) → B lx ly lx≈'ly
        aux IH .(η x) .(η y) (≈ηη x y xRy) = ≈ηη* IH x y xRy
        aux IH .(η x) ly (≈ηθ x .ly Hterm) = ≈ηθ* IH x ly Hterm
        aux IH lx .(η y) (≈θη .lx y Hterm) = ≈θη* IH lx y Hterm
        aux IH .(θ lx~) .(θ ly~) (≈θθ lx~ ly~ H~) = ≈θθ* IH lx~ ly~ H~



  -- ≈-η : ∀ lx y → lx ≈' η y →
  --   Σ[ n ∈ ℕ ] Σ[ x ∈ X ] (lx ≡ (δ ^ n) (η x)) × (R x y)
  -- ≈-η (η x) y Rxy = (0 , x , refl , lower Rxy)
  -- ≈-η (θ lx~) y H = H


  module Properties where

    is-prop : isPropValued R → isPropValued _≈_
    is-prop isPropValuedR = fix aux
      where
        aux : ▹ (isPropValued _≈_) → isPropValued _≈_
        aux IH .(η x) .(η y) (≈ηη x y H1) (≈ηη .x .y H2) =
          λ i → ≈ηη x y (isPropValuedR x y H1 H2 i)
        aux IH .(η x) .(η y) (≈ηη x y H1) (≈ηθ .x .(η y) H2) = ⊥.rec (PTrec isProp⊥ (λ (n , y' , eq , _) → Lη≠Lθ eq) H2)
        aux IH .(η x) .(η y) (≈ηη x y H1) (≈θη .(η x) .y H2) = ⊥.rec (PTrec isProp⊥ (λ (n , z , eq , _) → Lη≠Lθ eq) H2)
        aux IH .(η x) .(η y) (≈ηθ x .(η y) H1) (≈ηη .x y H2) = ⊥.rec (PTrec isProp⊥ (λ (n , z , eq , _) → Lη≠Lθ eq) H1)
        aux IH .(η x) ly (≈ηθ x .ly H1) (≈ηθ .x .ly H2) = λ i → ≈ηθ x ly (eq i)
          -- Because the type of H1 and H2 is the same and is a Prop, H1 ≡ H2!
          where
            eq : H1 ≡ H2
            eq = isPropPropTrunc H1 H2
        aux IH .(η x) .(η y) (≈ηθ x .(η y) H1) (≈θη .(η x) y H2) = ⊥.rec (PTrec isProp⊥ (λ (n , z , eq , _) → Lη≠Lθ eq) H1) -- could also use H2 for a contradiction
        aux IH .(η x) .(η y) (≈θη .(η x) y H1) (≈ηη x .y H2) = ⊥.rec (PTrec isProp⊥ (λ (n , z , eq , _) → Lη≠Lθ eq) H1)
        aux IH .(η x) .(η y) (≈θη .(η x) y H1) (≈ηθ x .(η y) H2) = ⊥.rec (PTrec isProp⊥ (λ (n , z , eq , _) → Lη≠Lθ eq) H1) -- could also use H2 for a contradiction
        aux IH lx .(η y) (≈θη .lx y H1) (≈θη .lx .y H2) = λ i → ≈θη lx y ((isPropPropTrunc H1 H2) i)
        aux IH .(θ lx~) .(θ ly~) (≈θθ lx~ ly~ H1~) (≈θθ .lx~ .ly~ H2~) =
          λ i → ≈θθ lx~ ly~ (later-ext eq i)
          where
            eq : ▸ (λ t → H1~ t ≡ H2~ t)
            eq t = IH t (lx~ t) (ly~ t) (H1~ t) (H2~ t)

    ≈-δ^n∘η-δ^m∘η-sufficient : (x y : X) (n : ℕ) (m : ℕ) →
      R x y → (δ ^ n) (η x) ≈ (δ ^ m) (η y)
    ≈-δ^n∘η-δ^m∘η-sufficient x y zero zero xRy = ≈ηη x y xRy
    ≈-δ^n∘η-δ^m∘η-sufficient x y zero (suc m) xRy = ≈ηθ x ((δ ^ suc m) (η y)) ∣ m , y , refl , xRy ∣₁
    ≈-δ^n∘η-δ^m∘η-sufficient x y (suc n) zero xRy = ≈θη ((δ ^ suc n) (η x)) y ∣ n , x , refl , xRy ∣₁
    ≈-δ^n∘η-δ^m∘η-sufficient x y (suc n) (suc m) xRy = ≈θθ _ _ (λ t → ≈-δ^n∘η-δ^m∘η-sufficient x y n m xRy)

    -- ≈θη ((δ ^ suc n) (η x)) y ∣ n , x , refl , H ∣₁


    -- If lx ≈ ly, then lx ≈ δ ly.
    -- This is more general than the corresponding "homogeneous" version
    -- i.e., x ≈ (δ x). This proof is more involved because we need to
    -- consider both lx and ly, which leads to complications in the case
    -- where lx is θ and ly is η, because when we add a θ on the right,
    -- now both sides are a θ and so we change to a different case of
    -- the relation than the one used to prove the assumption lx ≈ ly.
    δ-closed-r' : isPropValued R →
                   ▹ ((lx ly : L X) -> lx ≈ ly -> lx ≈ (δ ly)) ->
                     (lx ly : L X) -> lx ≈ ly -> lx ≈ (δ ly)
    δ-closed-r' isPropValuedR _ lx ly H =
             Elim.f
                {B = λ lx' ly' lx'≈ly' → lx' ≈ (δ ly')}
                (λ _ x y xRy → ≈ηθ _ _ ∣ 0 , y , refl , xRy ∣₁)

                -- In this case and the next case, we need to use that ≈
                -- is prop-valued here so we can remove the truncation
                -- from the hypothesis.
                (λ _ x ly H → PTrec (is-prop isPropValuedR _ _) (λ {(n , y , eq , xRy) →
                  ≈ηθ _ _ ∣ suc n , y , (cong δ eq) , xRy ∣₁}) H)

                (λ _ lx y H → PTrec (is-prop isPropValuedR _ _) (λ {(n , x , eq , xRy) →
                  transport (cong₂ _≈_ (sym eq) refl) (≈-δ^n∘η-δ^m∘η-sufficient x y (suc n) 1 xRy)}) H)

                (λ IH lx~ ly~ H~ → ≈θθ lx~ (next (θ ly~)) (λ t → 
                   -- NTS: lx~ t ≈ (θ ly~)
                   -- Know: ly~ ≡ (next (ly~ t)) (by tick irrelevance + later extensionality)
                   -- ==> θ ly~ ≡ θ (next (ly~ t)) ≡ δ (ly~ t)
                   -- Know: lx~ t ≈ δ (ly~ t) by IH
                   --
                   -- Have: lx~ t ≈ δ (ly~ t)
                   --             ≡ θ (next (ly~ t))
                   --             ≡ θ ly~
                   transport (cong₂ _≈_ refl (congS θ (next-Mt≡M ly~ t))) (IH t (lx~ t) (ly~ t) (H~ t))
                  )) lx ly H

    δ-closed-r : isPropValued R → (lx ly : L X) -> lx ≈ ly -> lx ≈ (δ ly)
    δ-closed-r isPropValuedR = fix (δ-closed-r' isPropValuedR)

              

-- aux : (H : θ lx~ ≈' θ ly~) → θ lx~ ≈' δ (θ ly~)
--          aux H t = ≈p→≈ _ _ (transport
--            (cong ∥_∥₁ (cong₂ _≈'_ refl (congS θ (next-Mt≡M ly~ t))))
--            (IH t (lx~ t) (ly~ t) (≈→≈p _ _ (H t))))


    reflexive : (isReflR : isRefl R) → isRefl _≈_
    reflexive isReflR = fix aux
      where
        aux : ▹ (isRefl _≈_) → isRefl _≈_
        aux _ (η x) = ≈ηη x x (isReflR x)
        aux IH (θ lx~) = ≈θθ lx~ lx~ (λ t → IH t (lx~ t))

    symmetric : (isSymR : isSym R) → isSym _≈_
    symmetric isSymR lx ly lx≈ly =
      Elim.f
      {B = λ lx ly lx≈ly → ly ≈ lx}
      (λ _ x y xRy → (≈ηη y x (isSymR x y xRy)))
      (λ _ x ly' H → (≈θη ly' x (PTrec isPropPropTrunc (λ { (n , y , eq , xRy) → ∣ n , y , eq , isSymR x y xRy ∣₁}) H)))
      (λ _ lx' y H → (≈ηθ y lx' (PTrec isPropPropTrunc (λ { (n , x , eq , xRy) → ∣ n , x , eq , isSymR x y xRy ∣₁ }) H)))
      (λ IH lx~ ly~ H~ → (≈θθ ly~ lx~ (λ t → IH t (lx~ t) (ly~ t) (H~ t))))
      lx ly lx≈ly


    η-pres≈ : {x y : X} → R x y → (η x) ≈ (η y)
    η-pres≈ x≈y = ≈ηη _ _ x≈y
      
    θ-pres≈ : {lx~ ly~ : ▹ L X} →
       ▸ (λ t → lx~ t ≈ ly~ t) → θ lx~ ≈ θ ly~
    θ-pres≈ H~ = ≈θθ _ _ H~

    δ-pres≈ : {lx ly : L X} →
      lx ≈ ly → (δ lx) ≈ (δ ly)
    δ-pres≈ lx≈ly = θ-pres≈ (next lx≈ly)





module _
  (X : Type ℓ)  (R : X → X → Type ℓR)
  (Y : Type ℓ') (S : Y → Y → Type ℓS)
  (isSymS : isSym S)
  (isPropValuedS : isPropValued S)
  (f : X → Y)
  where

  module LX = LiftBisim X R
  module LY = LiftBisim Y S

  private
    id≈δ : TwoCell LY._≈_ LY._≈_ id δ
    id≈δ x y x≈y = LY.Properties.δ-closed-r isPropValuedS (id x) y x≈y

    δ≈id : TwoCell LY._≈_ LY._≈_ δ id
    δ≈id x y x≈y = LY.Properties.symmetric isSymS (id y) (δ x) (id≈δ y x (LY.Properties.symmetric isSymS x y x≈y))

  L-map-preserves-bisim : ((x x' : X) → R x x' → S (f x) (f x')) →
     (lx lx' : L X) → lx LX.≈ lx' → (mapL f lx) LY.≈ (mapL f lx')
  L-map-preserves-bisim R→S = fix aux
    where
      aux :
        ▹ ((lx lx' : L X) → lx LX.≈ lx' → mapL f lx LY.≈ mapL f lx') →
           (lx lx' : L X) → lx LX.≈ lx' → mapL f lx LY.≈ mapL f lx'
      aux IH .(η x) .(η y) (LiftBisim.≈ηη x y xRy) =
        transport
          (sym (λ i → funExt⁻ (unfold-mapL f) (η x) i LY.≈ funExt⁻ (unfold-mapL f) (η y) i))
          (LiftBisim.≈ηη (f x) (f y) (R→S x y xRy))
      aux IH .(η x) lx' (LiftBisim.≈ηθ x .lx' H) =
        PTrec
          (LY.Properties.is-prop isPropValuedS _ _)
          (λ {(n , y , eq , Rxy) →
            transport (sym (λ i →
                    (mapL-η f x i) LY.≈
                    ((λ j → mapL f (eq j)) ∙ mapL-δ^n f (suc n) (η y) ∙ cong (δ ^ (suc n)) (mapL-η f y)) i))
              (TwoCell-iterated-idL LY._≈_ δ id≈δ (suc n) (η (f x)) (η (f y)) (LiftBisim.≈ηη (f x) (f y) (R→S x y Rxy)))})
          H
      aux IH lx .(η y) (LiftBisim.≈θη .lx y H) =
        PTrec
          (LY.Properties.is-prop isPropValuedS _ _)
          (λ {(n , x , eq , Rxy) → transport (sym (λ i →
            (((λ j → mapL f (eq j)) ∙ mapL-δ^n f (suc n) (η x) ∙ cong (δ ^ (suc n)) (mapL-η f x)) i) LY.≈ (mapL-η f y i)))
            (TwoCell-iterated-idR LY._≈_ δ δ≈id (suc n) (η (f x)) (η (f y)) (LiftBisim.≈ηη (f x) (f y) (R→S x y Rxy)))})
          H
      aux IH .(θ lx~) .(θ ly~) (LiftBisim.≈θθ lx~ ly~ H~) =
        transport
          (sym (λ i → funExt⁻ (unfold-mapL f) (θ lx~) i LY.≈ funExt⁻ (unfold-mapL f) (θ ly~) i))
          (LiftBisim.≈θθ _ _ (λ t → IH t (lx~ t) (ly~ t) (H~ t)))
    

module BisimSum (X : Type ℓ) (R : X -> X -> Type ℓR) where

  -- Weak bisimilarity as a sum type
  -- We could merge the middle two conditions, but we choose to keep them separate here.
  module Inductive (rec :  ▹ (L X -> L X -> Type (ℓ-max ℓ ℓR))) where 
    _≈'_ : L X -> L X -> Type (ℓ-max ℓ ℓR)
    l ≈' l' =  (Σ[ x ∈ X ] Σ[ y ∈ X ] (l ≡ η x) × (l' ≡ η y) × R x y) ⊎
              ((Σ[ x ∈ X ] ((l  ≡ η x) × ∥ Σ[ n ∈ ℕ ] Σ[ y ∈ X ] ((l' ≡ (δ ^ n) (η y)) × R x y) ∥₁)) ⊎
              ((Σ[ y ∈ X ] ((l' ≡ η y) × ∥ Σ[ n ∈ ℕ ] Σ[ x ∈ X ] ((l  ≡ (δ ^ n) (η x)) × R x y) ∥₁)) ⊎
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



-- The original definition implies the sum-type definition.

module _ (X : Type ℓ) (R : X -> X -> Type ℓR) where

  open module Bisim = LiftBisim X R
  open module BSum = BisimSum X R renaming (_≈_ to _≈S_)


  open BSum.Inductive (next _≈S_) renaming (_≈'_ to _≈S'_)

  ≈→≈Sum : (l l' : L X) -> l ≈ l' -> l ≈S l'
  ≈→≈Sum l l' l≈l' = BSum.≈'→≈ _ _ (fix lem l l' l≈l')
      where
        lem : ▹ ((l l' : L X) -> l ≈ l' -> l ≈S' l') ->
                 (l l' : L X) -> l ≈ l' -> l ≈S' l'
        lem _ (η x) (η y) (≈ηη x y xRy) = inl (x , (y , (refl , (refl , xRy))))
        lem _ .(η x) .ly (≈ηθ x ly H) =
          inr (inl (x , refl , PTmap (λ {(n , y , eq , xRy) → suc n , y , eq , xRy}) H))
        lem _ .lx .(η y) (≈θη lx y H) =
          inr (inr (inl (y , refl , PTmap (λ {(n , x , eq , xRy) → suc n , x , eq , xRy} ) H)))
        lem IH (θ lx~) (θ ly~) (≈θθ .(lx~) (.ly~) H~) =
          inr (inr (inr (lx~ , ly~ , refl , refl ,
                         λ t -> BSum.≈'→≈ (lx~ t) (ly~ t) (IH t (lx~ t) (ly~ t) (H~ t)))))

{-
  ≈Sum→≈ : (l l' : L X) -> l ≈S l' -> l ≈ l'
  ≈Sum→≈ l l' l≈Sl' = {!!}
    where
      lem :  ▹ ((l l' : L X) -> l ≈S' l' -> l ≈' l') ->
                (l l' : L X) -> l ≈S' l' -> l ≈' l'
      lem _ l l' (inl (x , y , eq1 , eq2 , Rxy)) = (transport (λ i -> (sym eq1 i) ≈' (sym eq2 i)) (lift Rxy))
      lem _ l l' (inr (inl (x , y , n , eq1 , eq2 , Rxy))) = {!!} -- NTS that l' is of the form θ(...)
-}



