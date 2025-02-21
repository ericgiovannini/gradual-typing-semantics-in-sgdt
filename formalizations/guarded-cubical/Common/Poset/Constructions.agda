{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Common.Poset.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (ℕ to Nat)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Common.Later
open import Common.Poset.Monotone
open import Common.Poset.Convenience
open import Common.LaterProperties

open BinaryRelation
open MonFun

private
  variable
    ℓ ℓ' : Level
    ℓA ℓ'A ℓB ℓ'B : Level

-- Some common posets

-- Flat poset from a set
flat : hSet ℓ -> Poset ℓ ℓ
flat h = ⟨ h ⟩ ,
         (posetstr _≡_ (isposet (str h) (str h)
           (λ _ → refl)
           (λ a b c a≡b b≡c → a ≡⟨ a≡b ⟩ b ≡⟨ b≡c ⟩ c ∎)
           λ x y p q → p))


𝔹 : Poset ℓ-zero ℓ-zero
𝔹 = flat (Bool , isSetBool)

ℕ : Poset ℓ-zero ℓ-zero
ℕ = flat (Nat , isSetℕ)

-- Any function defined on Nat as a flat poset is monotone
flatNatFun : (f : Nat -> Nat) -> monotone {X = ℕ} {Y = ℕ} f
flatNatFun f {n} {m} n≡m = cong f n≡m


UnitP : Poset ℓ-zero ℓ-zero
UnitP = flat (Unit , isSetUnit)


-- unique monotone function into UnitP
UnitP! : {A : Poset ℓ ℓ'} -> MonFun A UnitP
UnitP! = record { f = λ _ -> tt ; isMon = λ _ → refl }


-- Lifting a poset to higher universe level
LiftPoset : {ℓ1 ℓ1' : Level} (X : Poset ℓ1 ℓ1') ->
  (ℓ2 ℓ2' : Level) -> Poset (ℓ-max ℓ1 ℓ2) (ℓ-max ℓ1' ℓ2')
LiftPoset {ℓ1 = ℓ1} {ℓ1' = ℓ1'} X ℓ2 ℓ2' =
  (Lift {i = ℓ1} {j = ℓ2} ⟨ X ⟩) ,
  posetstr (λ {(lift x) (lift y) -> Lift {j = ℓ2'} (x X.≤ y) })
  (isposet
    (isOfHLevelLift 2 X.is-set)
    (λ {(lift x) (lift y) (lift p) (lift q) →
      cong lift (X.is-prop-valued x y p q)})
    (λ {(lift x) → lift (X.is-refl x)})
    (λ {(lift x) (lift y) (lift z) (lift x≤y) (lift y≤z) ->
      lift (X.is-trans x y z x≤y y≤z)})
    (λ {(lift x) (lift y) (lift x≤y) (lift y≤x) ->
      cong lift (X.is-antisym x y x≤y y≤x)}))
    where
      module X = PosetStr (X .snd)



-- Product of posets

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
_×p_  : Poset ℓA ℓ'A -> Poset ℓB ℓ'B -> Poset (ℓ-max ℓA ℓB) (ℓ-max ℓ'A ℓ'B)
A ×p B =
  (⟨ A ⟩ × ⟨ B ⟩) ,
  (posetstr order (isposet
    (isSet× A.is-set (B.is-set))
    propValued order-refl order-trans
      λ ab a'b' ab≦a'b' a'b'≦ab →
        ΣPathP ( A.is-antisym _ _ (ab≦a'b' .fst) (a'b'≦ab .fst)
               , B.is-antisym _ _ (ab≦a'b' .snd) (a'b'≦ab .snd))))
  where
    module A = PosetStr (A .snd)
    module B = PosetStr (B .snd)
   

    order : ⟨ A ⟩ × ⟨ B ⟩ -> ⟨ A ⟩ × ⟨ B ⟩ -> Type _
    order (a1 , b1) (a2 , b2) = (a1 A.≤ a2) × (b1 B.≤ b2)

    propValued : isPropValued order
    propValued (a1 , b1) (a2 , b2) = isProp×
      (IsPoset.is-prop-valued A.isPoset a1 a2)
      (IsPoset.is-prop-valued B.isPoset b1 b2)

    order-refl : BinaryRelation.isRefl order
    order-refl = λ (a , b) → reflexive A a , reflexive B b

    order-trans : BinaryRelation.isTrans order
    order-trans (a1 , b1) (a2 , b2) (a3 , b3) (a1≤a2 , b1≤b2) (a2≤a3 , b2≤b3) =
      (IsPoset.is-trans A.isPoset a1 a2 a3 a1≤a2 a2≤a3) ,
       IsPoset.is-trans B.isPoset b1 b2 b3 b1≤b2 b2≤b3

    


π1 : {A : Poset ℓA ℓ'A} {B : Poset ℓB ℓ'B} -> MonFun (A ×p B) A
π1 {A = A} {B = B} = record {
  f = g;
  isMon = g-mon }
  where
    g : ⟨ A ×p B ⟩ -> ⟨ A ⟩
    g (a , b) = a

    g-mon  : {p1 p2 : ⟨ A ×p B ⟩} → rel (A ×p B) p1 p2 → rel A (g p1) (g p2)
    g-mon {γ1 , a1} {γ2 , a2} (a1≤a2 , b1≤b2) = a1≤a2


π2 : {A : Poset ℓA ℓ'A} {B : Poset ℓB ℓ'B} -> ⟨ (A ×p B) ==> B ⟩
π2 {A = A} {B = B} = record {
  f = g;
  isMon = g-mon }
  where
    g : ⟨ A ×p B ⟩ -> ⟨ B ⟩
    g (a , b) = b

    g-mon  : {p1 p2 : ⟨ A ×p B ⟩} → rel (A ×p B) p1 p2 → rel B (g p1) (g p2)
    g-mon {γ1 , a1} {γ2 , a2} (a1≤a2 , b1≤b2) = b1≤b2



MonCurry' : {X Y Z : Poset ℓ ℓ'} ->
  MonFun (Z ×p X) Y -> ⟨ Z ⟩ -> MonFun X Y
MonCurry' {Z = Z} g z = record {
  f = λ x -> g $ (z , x) ;
  isMon = λ {x1} {x2} x1≤x2 → isMon g (reflexive Z z , x1≤x2) }

MonCurry : {X Y Z : Poset ℓ ℓ'} ->
  MonFun (Z ×p X) Y -> MonFun Z (IntHom X Y)
MonCurry {X = X} {Y = Y} {Z = Z} g = record {
  f = λ z -> MonCurry' {X = X} {Y = Y} {Z = Z} g z ;
  isMon = λ {z} {z'} z≤z' -> λ x → isMon g (z≤z' , reflexive X x)  }




-- Sum of posets

_⊎p_ : Poset ℓA ℓ'A -> Poset ℓB ℓ'B -> Poset (ℓ-max ℓA ℓB) (ℓ-max ℓ'A ℓ'B)
_⊎p_ {ℓ'A = ℓ'A} {ℓ'B = ℓ'B} A B =
  (⟨ A ⟩ ⊎ ⟨ B ⟩) ,
  posetstr order (isposet
    (isSet⊎ ((IsPoset.is-set A.isPoset)) ((IsPoset.is-set B.isPoset)))
    propValued order-refl order-trans order-antisym)
  where
    module A = PosetStr (A .snd)
    module B = PosetStr (B .snd)

    order : ⟨ A ⟩ ⊎ ⟨ B ⟩ -> ⟨ A ⟩ ⊎ ⟨ B ⟩ -> Type (ℓ-max ℓ'A ℓ'B)
    order (inl a1) (inl a2) = Lift {j = ℓ'B} (a1 A.≤ a2)
    order (inl a1) (inr b1) = ⊥*
    order (inr b1) (inl a1) = ⊥*
    order (inr b1) (inr b2) = Lift {j = ℓ'A} (b1 B.≤ b2)

    propValued : isPropValued order
    propValued (inl a1) (inl a2) = isOfHLevelLift 1 (IsPoset.is-prop-valued A.isPoset a1 a2)
    propValued (inr b1) (inr b2) = isOfHLevelLift 1 (IsPoset.is-prop-valued B.isPoset b1 b2)

    order-refl : BinaryRelation.isRefl order
    order-refl (inl a) = lift (reflexive A a)
    order-refl (inr b) = lift (reflexive B b)

    order-trans : BinaryRelation.isTrans order
    order-trans (inl a1) (inl a2) (inl a3) a1≤a2 a2≤a3 =
      lift (transitive A a1 a2 a3 (lower a1≤a2) (lower a2≤a3))
    order-trans (inr b1) (inr b2) (inr b3) b1≤b2 b2≤b3 =
      lift (transitive B b1 b2 b3 (lower b1≤b2) (lower b2≤b3))

    order-antisym : BinaryRelation.isAntisym order
    order-antisym (inl a) (inl a') ≤ ≥ = cong inl (A.is-antisym a a' (≤ .lower) (≥ .lower))
    order-antisym (inr b) (inr b') ≤ ≥ = cong inr (B.is-antisym b b' (≤ .lower) (≥ .lower))

σ1 : {A : Poset ℓA ℓ'A} {B : Poset ℓB ℓ'B} -> ⟨ A ==> (A ⊎p B) ⟩
σ1 = record { f = λ a -> inl a ; isMon = λ {x} {y} x≤y → lift x≤y }

σ2 : {A : Poset ℓA ℓ'A} {B : Poset ℓB ℓ'B} -> ⟨ B ==> (A ⊎p B) ⟩
σ2 = record { f = λ b -> inr b ; isMon = λ {x} {y} x≤y → lift x≤y }




-- Functions from clocks into posets inherit the poset structure of the codomain.
-- (Note: Nothing here is specific to clocks.)
-- 𝔽 : (Clock -> Poset ℓ ℓ') -> Poset ℓ ℓ'
-- 𝔽 A = (∀ k -> ⟨ A k ⟩) ,
--   posetstr (λ x y → ∀ k -> rel (A k) (x k) (y k))
--   (isposet
--     (λ f g pf1 pf2 → λ i1 i2 k → isSet-poset (A k) (f k) (g k) (λ i' -> pf1 i' k) (λ i' -> pf2 i' k) i1 i2)
--     (λ f g pf1 pf2 i k → isPropValued-poset (A k) (f k) (g k) (pf1 k) (pf2 k) i )
--     (λ f k → reflexive (A k) (f k))
--     (λ f g h f≤g g≤h k → transitive (A k) (f k) (g k) (h k) (f≤g k) (g≤h k))
--     {!!})


-- Later structure on posets

module _ (k : Clock) where

  private
    variable
      l : Level
    
    ▹_ : Set l → Set l
    ▹_ A = ▹_,_ k A


  ▹' : Poset ℓ ℓ' -> Poset ℓ ℓ'
  ▹' X = (▹ ⟨ X ⟩) ,
         (posetstr ord (isposet isset propValued ord-refl ord-trans ord-antisym))
    where
      ord : ▹ ⟨ X ⟩ → ▹ ⟨ X ⟩ → Type _
      ord = λ x1~ x2~ → ▸ (λ t -> PosetStr._≤_ (str X) (x1~ t) (x2~ t))

      isset : isSet (▹ ⟨ X ⟩)
      isset = λ x y p1 p2 i j t → isSet-poset X (x t) (y t) (λ i' -> p1 i' t) (λ i' -> p2 i' t) i j

      propValued : isPropValued ord
      propValued = λ a b p q → isProp▸ (λ t -> isPropValued-poset X (a t) (b t)) p q

      ord-refl : (a : ▹ ⟨ X ⟩) -> ord a a
      ord-refl a = λ t → reflexive X (a t)

      ord-trans : BinaryRelation.isTrans ord
      ord-trans = λ a b c a≤b b≤c t → transitive X (a t) (b t) (c t) (a≤b t) (b≤c t)

      ord-antisym : BinaryRelation.isAntisym ord
      ord-antisym = λ a b a≤b b≤a i t -> antisym X (a t) (b t) (a≤b t) (b≤a t) i

      
 
  -- Theta for posets
  ▸' : ▹ Poset ℓ ℓ' → Poset ℓ ℓ'
  ▸' X = (▸ (λ t → ⟨ X t ⟩)) ,
         posetstr ord
                  (isposet isset-later propValued ord-refl ord-trans ord-antisym)
     where

       ord : ▸ (λ t → ⟨ X t ⟩) → ▸ (λ t → ⟨ X t ⟩) → Type _
       ord x1~ x2~ =  ▸ (λ t → (PosetStr._≤_ (str (X t)) (x1~ t)) (x2~ t))

       isset-later : isSet (▸ (λ t → ⟨ X t ⟩))
       isset-later = λ x y p1 p2 i j t →
         isSet-poset (X t) (x t) (y t) (λ i' → p1 i' t) (λ i' → p2 i' t) i j

       propValued : isPropValued ord
       propValued = λ a b p q → isProp▸ (λ t -> isPropValued-poset (X t) (a t) (b t)) p q

       ord-refl : (a : ▸ (λ t → ⟨ X t ⟩)) -> ord a a
       ord-refl a = λ t ->
         IsPoset.is-refl (PosetStr.isPoset (str (X t))) (a t)

       ord-trans : BinaryRelation.isTrans ord
       ord-trans = λ a b c ord-ab ord-bc t →
         IsPoset.is-trans
           (PosetStr.isPoset (str (X t))) (a t) (b t) (c t) (ord-ab t) (ord-bc t)

       ord-antisym : BinaryRelation.isAntisym ord
       ord-antisym = λ a b ord-ab ord-ba i t ->
         IsPoset.is-antisym
           (PosetStr.isPoset (str (X t))) (a t) (b t) (ord-ab t) (ord-ba t) i


  -- This is the analogue of the equation for types that says that
  -- ▸ (next A) ≡ ▹ A
  ▸'-next : (X : Poset ℓ ℓ') -> ▸' (next X) ≡ ▹' X
  ▸'-next X = refl


  -- Delay for posets
  ▸''_ : Poset ℓ ℓ' → Poset ℓ ℓ'
  ▸'' X = ▸' (next X)


-- Zero and successor as monotone functions
Zero : MonFun UnitP ℕ
Zero = record { f = λ _ -> zero ; isMon = λ _ → refl }

Suc : MonFun (UnitP ×p ℕ) ℕ
Suc = record {
  f = λ (_ , n) -> suc n ;
  isMon = λ { {_ , n} {_ , m} (_ , n≡m) → cong suc n≡m} }


-- Isomorphisms
Unit-×L : {X : Type ℓ} -> Unit × X ≃ X
Unit-×L = isoToEquiv
  (iso (λ {(_ , x) -> x}) (λ x -> (tt , x)) (λ x → refl) (λ p → refl))

UnitP-×L-equiv : {X : Poset ℓ ℓ'} -> PosetEquiv (UnitP ×p X) X
UnitP-×L-equiv .fst = Unit-×L
UnitP-×L-equiv .snd = makeIsPosetEquiv Unit-×L is-mon is-mon-inv
  where
    is-mon : _
    is-mon (_ , x) (_ , x') (_ , x≤x') = x≤x'

    is-mon-inv : _
    is-mon-inv x x' x≤x' = refl , x≤x'

UnitP-×L : {X : Poset ℓ ℓ'} -> (UnitP ×p X) ≡ X
UnitP-×L {X = X} = equivFun (PosetPath (UnitP ×p X) X) UnitP-×L-equiv
