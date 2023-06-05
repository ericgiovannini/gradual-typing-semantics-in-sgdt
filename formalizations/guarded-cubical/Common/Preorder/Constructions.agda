{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Common.Preorder.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (ℕ to Nat)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty

open import Common.Later
open import Common.Preorder.Base
open import Common.Preorder.Monotone

open BinaryRelation


private
  variable
    ℓ ℓ' : Level

-- Some common predomains

-- Flat predomain from a set
flat : hSet ℓ -> Preorder ℓ ℓ
flat h = ⟨ h ⟩ ,
         (preorderstr _≡_ (ispreorder (str h) (str h)
           (λ _ → refl)
           (λ a b c a≡b b≡c → a ≡⟨ a≡b ⟩ b ≡⟨ b≡c ⟩ c ∎)))

𝔹 : Preorder ℓ-zero ℓ-zero
𝔹 = flat (Bool , isSetBool)

ℕ : Preorder ℓ-zero ℓ-zero
ℕ = flat (Nat , isSetℕ)

UnitP : Preorder ℓ-zero ℓ-zero
UnitP = flat (Unit , isSetUnit)



-- Product of predomains

-- We can't use Cubical.Data.Prod.Base for products, because this version of _×_
-- is not a subtype of the degenerate sigma type Σ A (λ _ → B), and this is needed
-- when we define the lookup function.
-- So we instead use Cubical.Data.Sigma.

-- These aren't included in Cubical.Data.Sigma, so we copy the
-- definitions from Cubical.Data.Prod.Base.
proj₁ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → A × B → A
proj₁ (x , _) = x

proj₂ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → A × B → B
proj₂ (_ , x) = x


infixl 21 _×p_
_×p_  : Preorder ℓ ℓ' -> Preorder ℓ ℓ' -> Preorder ℓ ℓ'
A ×p B =
  (⟨ A ⟩ × ⟨ B ⟩) ,
  (preorderstr order (ispreorder
    (isSet× (IsPreorder.is-set A.isPreorder) (IsPreorder.is-set B.isPreorder))
    propValued order-refl order-trans))
  where
    module A = PreorderStr (A .snd)
    module B = PreorderStr (B .snd)
   

    order : ⟨ A ⟩ × ⟨ B ⟩ -> ⟨ A ⟩ × ⟨ B ⟩ -> Type _
    order (a1 , b1) (a2 , b2) = (a1 A.≤ a2) × (b1 B.≤ b2)

    propValued : isPropValued order
    propValued (a1 , b1) (a2 , b2) = isProp×
      (IsPreorder.is-prop-valued A.isPreorder a1 a2)
      (IsPreorder.is-prop-valued B.isPreorder b1 b2)

    order-refl : BinaryRelation.isRefl order
    order-refl = λ (a , b) → reflexive A a , reflexive B b

    order-trans : BinaryRelation.isTrans order
    order-trans (a1 , b1) (a2 , b2) (a3 , b3) (a1≤a2 , b1≤b2) (a2≤a3 , b2≤b3) =
      (IsPreorder.is-trans A.isPreorder a1 a2 a3 a1≤a2 a2≤a3) ,
       IsPreorder.is-trans B.isPreorder b1 b2 b3 b1≤b2 b2≤b3


π1 : {A B : Preorder ℓ ℓ'} -> ⟨ (A ×p B) ==> A ⟩
π1 {A = A} {B = B} = record {
  f = g;
  isMon = g-mon }
  where
    g : ⟨ A ×p B ⟩ -> ⟨ A ⟩
    g (a , b) = a

    g-mon  : {p1 p2 : ⟨ A ×p B ⟩} → rel (A ×p B) p1 p2 → rel A (g p1) (g p2)
    g-mon {γ1 , a1} {γ2 , a2} (a1≤a2 , b1≤b2) = a1≤a2


π2 : {A B : Preorder ℓ ℓ'} -> ⟨ (A ×p B) ==> B ⟩
π2 {A = A} {B = B} = record {
  f = g;
  isMon = g-mon }
  where
    g : ⟨ A ×p B ⟩ -> ⟨ B ⟩
    g (a , b) = b

    g-mon  : {p1 p2 : ⟨ A ×p B ⟩} → rel (A ×p B) p1 p2 → rel B (g p1) (g p2)
    g-mon {γ1 , a1} {γ2 , a2} (a1≤a2 , b1≤b2) = b1≤b2




-- Sum of preorders

_⊎p_ : Preorder ℓ ℓ' -> Preorder ℓ ℓ' -> Preorder ℓ ℓ'
A ⊎p B =
  (⟨ A ⟩ ⊎ ⟨ B ⟩) ,
  preorderstr order (ispreorder
    (isSet⊎ ((IsPreorder.is-set A.isPreorder)) ((IsPreorder.is-set B.isPreorder)))
    propValued order-refl order-trans)
  where
    module A = PreorderStr (A .snd)
    module B = PreorderStr (B .snd)

    order : ⟨ A ⟩ ⊎ ⟨ B ⟩ -> ⟨ A ⟩ ⊎ ⟨ B ⟩ -> Type _
    order (inl a1) (inl a2) = a1 A.≤ a2
    order (inl a1) (inr b1) = ⊥*
    order (inr b1) (inl a1) = ⊥*
    order (inr b1) (inr b2) = b1 B.≤ b2

    propValued : isPropValued order
    propValued (inl a1) (inl a2) = IsPreorder.is-prop-valued A.isPreorder a1 a2
    propValued (inr b1) (inr b2) = IsPreorder.is-prop-valued B.isPreorder b1 b2

    order-refl : BinaryRelation.isRefl order
    order-refl (inl a) = reflexive A a
    order-refl (inr b) = reflexive B b

    order-trans : BinaryRelation.isTrans order
    order-trans (inl a1) (inl a2) (inl a3) = transitive A a1 a2 a3
    order-trans (inr b1) (inr b2) (inr b3) = transitive B b1 b2 b3

σ1 : {A B : Preorder ℓ ℓ'} -> ⟨ A ==> (A ⊎p B) ⟩
σ1 = record { f = λ a -> inl a ; isMon = λ {x} {y} x≤y → x≤y }

σ2 : {A B : Preorder ℓ ℓ'} -> ⟨ B ==> (A ⊎p B) ⟩
σ2 = record { f = λ b -> inr b ; isMon = λ {x} {y} x≤y → x≤y }




-- Functions from clocks into preorders inherit the preorder structure of the codomain.
-- (Note: Nothing here is specific to clocks.)
𝔽 : (Clock -> Preorder ℓ ℓ') -> Preorder ℓ ℓ'
𝔽 A = (∀ k -> ⟨ A k ⟩) ,
  preorderstr (λ x y → ∀ k -> rel (A k) (x k) (y k))
  (ispreorder
    (λ f g pf1 pf2 → λ i1 i2 k → isSet-preorder (A k) (f k) (g k) (λ i' -> pf1 i' k) (λ i' -> pf2 i' k) i1 i2)
    (λ f g pf1 pf2 i k → isPropValued-preorder (A k) (f k) (g k) (pf1 k) (pf2 k) i )
    (λ f k → reflexive (A k) (f k))
    (λ f g h f≤g g≤h k → transitive (A k) (f k) (g k) (h k) (f≤g k) (g≤h k)))


-- Later structure on preorders

module _ (k : Clock) where

  private
    variable
      l : Level
    
    ▹_ : Set l → Set l
    ▹_ A = ▹_,_ k A


  ▹' : Preorder ℓ ℓ' -> Preorder ℓ ℓ'
  ▹' X = (▹ ⟨ X ⟩) ,
         (preorderstr ord (ispreorder isset propValued ord-refl ord-trans))
    where
      ord : ▹ ⟨ X ⟩ → ▹ ⟨ X ⟩ → Type _
      ord = λ x1~ x2~ → ▸ (λ t -> PreorderStr._≤_ (str X) (x1~ t) (x2~ t))

      isset : isSet (▹ ⟨ X ⟩)
      isset = λ x y p1 p2 i j t → isSet-preorder X (x t) (y t) (λ i' -> p1 i' t) (λ i' -> p2 i' t) i j

      propValued : isPropValued ord
      propValued = {!!}

      ord-refl : (a : ▹ ⟨ X ⟩) -> ord a a
      ord-refl a = λ t → reflexive X (a t)

      ord-trans : BinaryRelation.isTrans ord
      ord-trans = λ a b c a≤b b≤c t → transitive X (a t) (b t) (c t) (a≤b t) (b≤c t)

      
 
  -- Theta for preorders
  ▸' : ▹ Preorder ℓ ℓ' → Preorder ℓ ℓ'
  ▸' X = (▸ (λ t → ⟨ X t ⟩)) ,
         preorderstr ord
                  (ispreorder isset-later {!!} ord-refl ord-trans)
     where

       ord : ▸ (λ t → ⟨ X t ⟩) → ▸ (λ t → ⟨ X t ⟩) → Type _
       -- ord x1~ x2~ =  ▸ (λ t → (str (X t) PosetStr.≤ (x1~ t)) (x2~ t))
       ord x1~ x2~ =  ▸ (λ t → (PreorderStr._≤_ (str (X t)) (x1~ t)) (x2~ t))
     

       isset-later : isSet (▸ (λ t → ⟨ X t ⟩))
       isset-later = λ x y p1 p2 i j t →
         isSet-preorder (X t) (x t) (y t) (λ i' → p1 i' t) (λ i' → p2 i' t) i j

       ord-refl : (a : ▸ (λ t → ⟨ X t ⟩)) -> ord a a
       ord-refl a = λ t ->
         IsPreorder.is-refl (PreorderStr.isPreorder (str (X t))) (a t)

       ord-trans : BinaryRelation.isTrans ord
       ord-trans = λ a b c ord-ab ord-bc t →
         IsPreorder.is-trans
           (PreorderStr.isPreorder (str (X t))) (a t) (b t) (c t) (ord-ab t) (ord-bc t)


  -- This is the analogue of the equation for types that says that
  -- ▸ (next A) ≡ ▹ A
  ▸'-next : (X : Preorder ℓ ℓ') -> ▸' (next X) ≡ ▹' X
  ▸'-next X = refl


  -- Delay for predomains
  ▸''_ : Preorder ℓ ℓ' → Preorder ℓ ℓ'
  ▸'' X = ▸' (next X)

