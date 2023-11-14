{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Predomains where

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

open import Common.Later

open BinaryRelation

-- Define predomains as posets
Predomain : Set₁
Predomain = Poset ℓ-zero ℓ-zero


-- The relation associated to a predomain d
rel : (d : Predomain) -> (⟨ d ⟩ -> ⟨ d ⟩ -> Type)
rel d = PosetStr._≤_ (d .snd)

reflexive : (d : Predomain) -> (x : ⟨ d ⟩) -> (rel d x x)
reflexive d x = IsPoset.is-refl (PosetStr.isPoset (str d)) x

transitive : (d : Predomain) -> (x y z : ⟨ d ⟩) ->
  rel d x y -> rel d y z -> rel d x z
transitive d x y z x≤y y≤z =
  IsPoset.is-trans (PosetStr.isPoset (str d)) x y z x≤y y≤z

antisym : (d : Predomain) -> (x y : ⟨ d ⟩) ->
  rel d x y -> rel d y x -> x ≡ y
antisym d x y x≤y y≤x = IsPoset.is-antisym (PosetStr.isPoset (str d)) x y x≤y y≤x

isSet-poset : {ℓ ℓ' : Level} -> (P : Poset ℓ ℓ') -> isSet ⟨ P ⟩
isSet-poset P = IsPoset.is-set (PosetStr.isPoset (str P))

isPropValued-poset : {ℓ ℓ' : Level} -> (P : Poset ℓ ℓ') -> isPropValued (PosetStr._≤_ (str P))
isPropValued-poset P = IsPoset.is-prop-valued (PosetStr.isPoset (str P))


-- Some common predomains

-- Flat predomain from a set
flat : hSet ℓ-zero -> Predomain
flat h = ⟨ h ⟩ ,
         (posetstr _≡_ (isposet (str h) (str h)
           (λ _ → refl)
           (λ a b c a≡b b≡c → a ≡⟨ a≡b ⟩ b ≡⟨ b≡c ⟩ c ∎)
           λ a b a≡b _ → a≡b))

𝔹 : Predomain
𝔹 = flat (Bool , isSetBool)

ℕ : Predomain
ℕ = flat (Nat , isSetℕ)

UnitP : Predomain
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


infixl 21 _×d_
_×d_  : Predomain -> Predomain -> Predomain
A ×d B =
  (⟨ A ⟩ × ⟨ B ⟩) ,
  (posetstr order (isposet isSet-prod {!!} order-refl order-trans {!!}))
  where
    module A = PosetStr (A .snd)
    module B = PosetStr (B .snd)
   

    prod-eq : {a1 a2 : ⟨ A ⟩} -> {b1 b2 : ⟨ B ⟩} ->
      (a1 , b1) ≡ (a2 , b2) -> (a1 ≡ a2) × (b1 ≡ b2)
    prod-eq p = (λ i → proj₁ (p i)) , λ i -> proj₂ (p i)

    isSet-prod : isSet (⟨ A ⟩ × ⟨ B ⟩)
    isSet-prod (a1 , b1) (a2 , b2) p1 p2 =
      let (p-a1≡a2 , p-b1≡b2) = prod-eq p1 in
      let (p'-a1≡a2 , p'-b1≡b2) = prod-eq p2 in
      {!!}

    order : ⟨ A ⟩ × ⟨ B ⟩ -> ⟨ A ⟩ × ⟨ B ⟩ -> Type ℓ-zero
    order (a1 , b1) (a2 , b2) = (a1 A.≤ a2) × (b1 B.≤ b2)

    order-refl : BinaryRelation.isRefl order
    order-refl = λ (a , b) → reflexive A a , reflexive B b

    order-trans : BinaryRelation.isTrans order
    order-trans (a1 , b1) (a2 , b2) (a3 , b3) (a1≤a2 , b1≤b2) (a2≤a3 , b2≤b3) =
      (IsPoset.is-trans A.isPoset a1 a2 a3 a1≤a2 a2≤a3) ,
       IsPoset.is-trans B.isPoset b1 b2 b3 b1≤b2 b2≤b3


-- Sum of predomains

_⊎d_ : Predomain -> Predomain -> Predomain
A ⊎d B =
  (⟨ A ⟩ ⊎ ⟨ B ⟩) ,
  posetstr order (isposet {!!} {!!} order-refl order-trans order-antisym)
  where
    module A = PosetStr (A .snd)
    module B = PosetStr (B .snd)

    order : ⟨ A ⟩ ⊎ ⟨ B ⟩ -> ⟨ A ⟩ ⊎ ⟨ B ⟩ -> Type ℓ-zero
    order (inl a1) (inl a2) = a1 A.≤ a2
    order (inl a1) (inr b1) = ⊥
    order (inr b1) (inl a1) = ⊥
    order (inr b1) (inr b2) = b1 B.≤ b2

    order-refl : BinaryRelation.isRefl order
    order-refl (inl a) = reflexive A a
    order-refl (inr b) = reflexive B b

    order-trans : BinaryRelation.isTrans order
    order-trans (inl a1) (inl a2) (inl a3) = transitive A a1 a2 a3
    order-trans (inr b1) (inr b2) (inr b3) = transitive B b1 b2 b3

    order-antisym : BinaryRelation.isAntisym order
    order-antisym (inl a1) (inl a2) a1≤a2 a2≤a1 = cong inl (antisym A a1 a2 a1≤a2 a2≤a1)
    order-antisym (inr b1) (inr b2) b1≤b2 b2≤b1 = cong inr (antisym B b1 b2 b1≤b2 b2≤b1)


-- Functions from clocks into predomains inherit the predomain structure of the codomain.
-- (Note: Nothing here is specific to clocks.)
𝔽 : (Clock -> Predomain) -> Predomain
𝔽 A = (∀ k -> ⟨ A k ⟩) ,
  posetstr (λ x y → ∀ k -> rel (A k) (x k) (y k))
  (isposet
    (λ f g pf1 pf2 → λ i1 i2 k → isSet-poset (A k) (f k) (g k) (λ i' -> pf1 i' k) (λ i' -> pf2 i' k) i1 i2)
    (λ f g pf1 pf2 i k → isPropValued-poset (A k) (f k) (g k) (pf1 k) (pf2 k) i )
    (λ f k → reflexive (A k) (f k))
    (λ f g h f≤g g≤h k → transitive (A k) (f k) (g k) (h k) (f≤g k) (g≤h k))
    λ f g f≤g g≤f i k → antisym (A k) (f k) (g k) (f≤g k) (g≤f k) i)


-- Later structure on predomains

module _ (k : Clock) where

  private
    variable
      l : Level
    
    ▹_ : Set l → Set l
    ▹_ A = ▹_,_ k A


  ▹' : Predomain -> Predomain
  ▹' X = (▹ ⟨ X ⟩) ,
         (posetstr ord (isposet isset {!!} ord-refl ord-trans ord-antisym))
    where
      ord : ▹ ⟨ X ⟩ → ▹ ⟨ X ⟩ → Type ℓ-zero
      ord = λ x1~ x2~ → ▸ (λ t -> PosetStr._≤_ (str X) (x1~ t) (x2~ t))

      isset : isSet (▹ ⟨ X ⟩)
      isset = λ x y p1 p2 i j t → isSet-poset X (x t) (y t) (λ i' -> p1 i' t) (λ i' -> p2 i' t) i j

      ord-refl : (a : ▹ ⟨ X ⟩) -> ord a a
      ord-refl a = λ t → reflexive X (a t)

      ord-trans : BinaryRelation.isTrans ord
      ord-trans = λ a b c a≤b b≤c t → transitive X (a t) (b t) (c t) (a≤b t) (b≤c t)

      ord-antisym : BinaryRelation.isAntisym ord
      ord-antisym = λ a b a≤b b≤a i t -> antisym X (a t) (b t) (a≤b t) (b≤a t) i
      
 
  -- Theta for predomains
  ▸' : ▹ Predomain → Predomain
  ▸' X = (▸ (λ t → ⟨ X t ⟩)) ,
         posetstr ord
                  (isposet isset-later {!!} ord-refl ord-trans ord-antisym)
     where

       ord : ▸ (λ t → ⟨ X t ⟩) → ▸ (λ t → ⟨ X t ⟩) → Type ℓ-zero
       -- ord x1~ x2~ =  ▸ (λ t → (str (X t) PosetStr.≤ (x1~ t)) (x2~ t))
       ord x1~ x2~ =  ▸ (λ t → (PosetStr._≤_ (str (X t)) (x1~ t)) (x2~ t))
     

       isset-later : isSet (▸ (λ t → ⟨ X t ⟩))
       isset-later = λ x y p1 p2 i j t →
         isSet-poset (X t) (x t) (y t) (λ i' → p1 i' t) (λ i' → p2 i' t) i j

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
  ▸'-next : (X : Predomain) -> ▸' (next X) ≡ ▹' X
  ▸'-next X = refl


  -- Delay for predomains
  ▸''_ : Predomain → Predomain
  ▸'' X = ▸' (next X)

