{-# OPTIONS --guarded --rewriting #-}


module Semantics.Concrete.DoublePoset.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (ℕ to Nat)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Sum.Base
open import Cubical.Data.Sum.Properties
open import Cubical.Data.Empty.Base

open import Cubical.Relation.Binary.Base

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Convenience

open import Common.Later
open import Common.LaterProperties

open BinaryRelation

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓ'X ℓ''X : Level
    ℓY ℓ'Y ℓ''Y : Level
    ℓ1 ℓ'1 ℓ''1 : Level
    ℓ2 ℓ'2 ℓ''2 : Level
    ℓA ℓ'A ℓ''A : Level
    ℓB ℓ'B ℓ''B : Level

    X : DoublePoset ℓX ℓ'X ℓ''X
    Y : DoublePoset ℓY ℓ'Y ℓ''Y


-- Constructions not involving later

flat : hSet ℓ -> DoublePoset ℓ ℓ ℓ
flat h = ⟨ h ⟩ , (dblposetstr
                   (str h) _≡_
                   (isorderingrelation (str h) (λ _ → refl)
                     (λ a b c a≡b b≡c → a ≡⟨ a≡b ⟩ b ≡⟨ b≡c ⟩ c ∎)
                     λ x y p q → p)
                   _≡_ (isper (λ _ → refl) (λ a b x → sym x) (str h)))


𝔹 : DoublePoset ℓ-zero ℓ-zero ℓ-zero
𝔹 = flat (Bool , isSetBool)

ℕ : DoublePoset ℓ-zero ℓ-zero ℓ-zero
ℕ = flat (Nat , isSetℕ)

-- Any function defined on Nat as a flat dbposet is monotone
flatNatFun-monotone : (f : Nat -> Nat) -> monotone {X = ℕ} {Y = ℕ} f
flatNatFun-monotone f {n} {m} n≡m = cong f n≡m


flatNatFun-preserve≈ : (f : Nat -> Nat) -> preserve≈ {X = ℕ} {Y = ℕ} f
flatNatFun-preserve≈ f {n} {m} n≈m = cong f n≈m


UnitDP : DoublePoset ℓ-zero ℓ-zero ℓ-zero
UnitDP = flat (Unit , isSetUnit)


-- unique morphism into UnitP
UnitDP! : {A : DoublePoset ℓ ℓ' ℓ''} -> DPMor A UnitDP
UnitDP! = record { f = λ _ → tt ; isMon = λ _ → refl ; pres≈ = λ _ → refl }


LiftDoublePoset : {ℓ1 ℓ'1 ℓ''1 : Level} (X : DoublePoset ℓ1 ℓ'1 ℓ''1) ->
  (ℓ2 ℓ'2 ℓ''2 : Level) -> DoublePoset (ℓ-max ℓ1 ℓ2) (ℓ-max ℓ'1 ℓ'2) (ℓ-max ℓ''1 ℓ''2)
LiftDoublePoset {ℓ1 = ℓ1} {ℓ'1 = ℓ'1} {ℓ''1 = ℓ''1} X ℓ2 ℓ'2 ℓ''2 =
  (Lift {i = ℓ1} {j = ℓ2} ⟨ X ⟩) ,
  dblposetstr
    (isOfHLevelLift 2 X.is-set )
    (λ {(lift x) (lift y) → Lift {i = ℓ'1} {j = ℓ'2} (x X.≤ y)})
    (isorderingrelation
      (λ {(lift x) (lift y) (lift p) (lift q) → cong lift (X.is-prop-valued x y p q)})
      (λ {(lift x) → lift (X.is-refl x)})
      (λ {(lift x) (lift y) (lift z) (lift x≤y) (lift y≤z) ->
      lift (X.is-trans x y z x≤y y≤z)})
      λ {(lift x) (lift y) (lift x≤y) (lift y≤x) ->
      cong lift (X.is-antisym x y x≤y y≤x)})
    (λ {(lift x) (lift y) → Lift {i = ℓ''1} {j = ℓ''2} (x X.≈ y)})
    (isper
      (λ {(lift x) → lift (X.is-refl-PER x)})
      (λ {(lift x) (lift y) (lift (x≈y)) → lift (X.is-sym x y x≈y)})
      λ {(lift x) (lift y) (lift p) (lift q) →
        cong lift (X.is-prop-valued-PER x y p q)})
  where
    module X = DblPosetStr (X .snd)

-- Product of double posets

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

infixl 21 _×dp_
_×dp_ : DoublePoset ℓA ℓ'A ℓ''A  -> DoublePoset ℓB ℓ'B ℓ''B -> DoublePoset (ℓ-max ℓA ℓB) (ℓ-max ℓ'A ℓ'B) (ℓ-max ℓ''A ℓ''B)
_×dp_ {ℓ'A = ℓ'A} {ℓ''A = ℓ''A} {ℓ'B = ℓ'B} {ℓ''B = ℓ''B} A B  =
  ⟨ A ⟩ × ⟨ B ⟩ ,
  dblposetstr
    (isSet× A.is-set B.is-set)
    order
    (isorderingrelation order-prop-valued order-refl order-trans order-antisym)
    bisim
    (isper bisim-refl bisim-sym bisim-prop-valued)
  where
    module A = DblPosetStr (A .snd)
    module B = DblPosetStr (B .snd)
    
    order : ⟨ A ⟩ × ⟨ B ⟩ -> ⟨ A ⟩ × ⟨ B ⟩ -> Type (ℓ-max ℓ'A ℓ'B)
    order (a1 , b1) (a2 , b2) = (a1 A.≤ a2) × (b1 B.≤ b2)

    order-prop-valued : isPropValued order
    order-prop-valued (a1 , b1) (a2 , b2) = isProp×
      (prop-valued-≤ A a1 a2)
      (prop-valued-≤ B b1 b2)

    order-refl : isRefl order
    order-refl = λ (a , b) → reflexive-≤ A a , reflexive-≤ B b

    order-trans : isTrans order
    order-trans (a1 , b1) (a2 , b2) (a3 , b3) (a1≤a2 , b1≤b2) (a2≤a3 , b2≤b3) =
      (transitive-≤ A a1 a2 a3 a1≤a2 a2≤a3) ,
      (transitive-≤ B b1 b2 b3 b1≤b2 b2≤b3)

    order-antisym : isAntisym order
    order-antisym (a1 , b1) (a2 , b2) (a1≤a2 , b1≤b2) (a2≤a1 , b2≤b1) =
      ≡-× (antisym-≤ A a1 a2 a1≤a2 a2≤a1)
          (antisym-≤ B b1 b2 b1≤b2 b2≤b1)

    bisim : ⟨ A ⟩ × ⟨ B ⟩ -> ⟨ A ⟩ × ⟨ B ⟩ -> Type (ℓ-max ℓ''A ℓ''B)
    bisim (a1 , b1) (a2 , b2) = (a1 A.≈ a2) × (b1 B.≈ b2)
    
    bisim-refl : isRefl bisim
    bisim-refl = λ (a , b) → (reflexive-≈ A a) , reflexive-≈ B b

    bisim-sym : isSym bisim
    bisim-sym = λ (a1 , b1) (a2 , b2) (a1≈a2 , b1≈b2) →
      sym-≈ A a1 a2 a1≈a2 , sym-≈ B b1 b2 b1≈b2

    bisim-prop-valued : isPropValued bisim
    bisim-prop-valued (a1 , b1) (a2 , b2) = isProp×
      (prop-valued-≈ A a1 a2) (prop-valued-≈ B b1 b2)

π1 : {A : DoublePoset ℓA ℓ'A ℓ''A} {B : DoublePoset ℓB ℓ'B ℓ''B} -> DPMor (A ×dp B) A
π1 {A = A} {B = B} = record {
  f = g ;
  isMon = g-mon ;
  pres≈ = g-bisim }
  where
    g : ⟨ A ×dp B ⟩ -> ⟨ A ⟩
    g (a , b) = a

    g-mon  : {p1 p2 : ⟨ A ×dp B ⟩} → rel-≤ (A ×dp B) p1 p2 → rel-≤ A (g p1) (g p2)
    g-mon {γ1 , a1} {γ2 , a2} (a1≤a2 , b1≤b2) = a1≤a2

    g-bisim : {p1 p2 : ⟨ A ×dp B ⟩} → rel-≈ (A ×dp B) p1 p2 → rel-≈ A (g p1) (g p2)
    g-bisim {γ1 , a1} {γ2 , a2} (a1≈a2 , b1≈b2) = a1≈a2

π2 : {A : DoublePoset ℓA ℓ'A ℓ''A} {B : DoublePoset ℓB ℓ'B ℓ''B} -> DPMor (A ×dp B) B
π2 {A = A} {B = B} = record {
  f = g ;
  isMon = g-mon ;
  pres≈ = g-bisim }
  where
    g : ⟨ A ×dp B ⟩ -> ⟨ B ⟩
    g (a , b) = b

    g-mon  : {p1 p2 : ⟨ A ×dp B ⟩} → rel-≤ (A ×dp B) p1 p2 → rel-≤ B (g p1) (g p2)
    g-mon {γ1 , a1} {γ2 , a2} (a1≤a2 , b1≤b2) = b1≤b2

    g-bisim : {p1 p2 : ⟨ A ×dp B ⟩} → rel-≈ (A ×dp B) p1 p2 → rel-≈ B (g p1) (g p2)
    g-bisim {γ1 , a1} {γ2 , a2} (a1≈a2 , b1≈b2) = b1≈b2


DPMorCurry' : {X Y Z : DoublePoset ℓ ℓ' ℓ''} ->
  DPMor (Z ×dp X) Y -> ⟨ Z ⟩ -> DPMor X Y
DPMorCurry' {Z = Z} g z = record {
  f = λ x → g $ (z , x) ;
  isMon = λ {x1} {x2} x1≤x2 → DPMor.isMon g (reflexive-≤ Z z , x1≤x2) ;
  pres≈ = λ {x1} {x2} x1≈x2 → DPMor.pres≈ g (reflexive-≈ Z z , x1≈x2)  }

DPMorCurry : {X Y Z : DoublePoset ℓ ℓ' ℓ''} ->
  DPMor (Z ×dp X) Y -> DPMor Z (IntHom X Y)
DPMorCurry {X = X} {Y = Y} {Z = Z} g = record {
  f = λ z → DPMorCurry' {X = X} {Y = Y} {Z = Z} g z ;
  isMon = λ {z} {z'} z≤z' → λ x → DPMor.isMon g (z≤z' , reflexive-≤ X x) ;
  pres≈ = λ {z} {z'} z≈z' x x' x≈x' → DPMor.pres≈ g (z≈z' , x≈x') }


_⊎p_ : DoublePoset ℓA ℓ'A ℓ''A  -> DoublePoset ℓB ℓ'B ℓ''B -> DoublePoset (ℓ-max ℓA ℓB) (ℓ-max ℓ'A ℓ'B) (ℓ-max ℓ''A ℓ''B)
_⊎p_ {ℓ'A = ℓ'A} {ℓ''A = ℓ''A} {ℓ'B = ℓ'B}  {ℓ''B = ℓ''B} A B =
  (⟨ A ⟩ ⊎ ⟨ B ⟩) ,
  dblposetstr
    (isSet⊎ (is-set-DblPoset A) (is-set-DblPoset B))
    order (isorderingrelation order-prop-valued order-refl order-trans order-antisym)
    bisim (isper bisim-refl bisim-sym bisim-prop-valued)
  where
    module A = DblPosetStr (A .snd)
    module B = DblPosetStr (B .snd)

    order : ⟨ A ⟩ ⊎ ⟨ B ⟩ -> ⟨ A ⟩ ⊎ ⟨ B ⟩ -> Type (ℓ-max ℓ'A ℓ'B)
    order (inl a1) (inl a2) = Lift {j = ℓ'B} (a1 A.≤ a2)
    order (inl a1) (inr b1) = ⊥*
    order (inr b1) (inl a1) = ⊥*
    order (inr b1) (inr b2) = Lift {j = ℓ'A} (b1 B.≤ b2)

    order-prop-valued : isPropValued order
    order-prop-valued (inl a1) (inl a2) = isOfHLevelLift 1 (prop-valued-≤ A a1 a2)
    order-prop-valued (inr b1) (inr b2) = isOfHLevelLift 1 (prop-valued-≤ B b1 b2)

    order-refl : isRefl order
    order-refl (inl a) = lift (reflexive-≤ A a)
    order-refl (inr b) = lift (reflexive-≤ B b)

    order-trans : isTrans order
    order-trans (inl a1) (inl a2) (inl a3) a1≤a2 a2≤a3 =
      lift (transitive-≤ A a1 a2 a3 (lower a1≤a2) (lower a2≤a3))
    order-trans (inr b1) (inr b2) (inr b3) b1≤b2 b2≤b3 =
      lift (transitive-≤ B b1 b2 b3 (lower b1≤b2) (lower b2≤b3))

    order-antisym : isAntisym order
    order-antisym (inl a1) (inl a2) a≤b b≤a =
      cong inl (antisym-≤ A _ _ (lower a≤b) (lower b≤a))
    order-antisym (inr b1) (inr b2) a≤b b≤a =
      cong inr (antisym-≤ B _ _ (lower a≤b) (lower b≤a))

    bisim : ⟨ A ⟩ ⊎ ⟨ B ⟩ -> ⟨ A ⟩ ⊎ ⟨ B ⟩ -> Type (ℓ-max ℓ''A ℓ''B)
    bisim (inl a1) (inl a2) = Lift {j = ℓ''B} (a1 A.≈ a2)
    bisim (inl a1) (inr b1) = ⊥*
    bisim (inr b1) (inl a1) = ⊥*
    bisim (inr b1) (inr b2) = Lift {j = ℓ''A} (b1 B.≈ b2)

    bisim-refl : isRefl bisim
    bisim-refl = λ { (inl a) → lift (reflexive-≈ A a) ;
                     (inr b) → lift (reflexive-≈ B b) }

    bisim-sym : isSym bisim
    bisim-sym = λ { (inl a1) (inl a2) a1≈a2 → lift (sym-≈ A a1 a2 (lower a1≈a2)) ;
                    (inr b1) (inr b2) b1≈b2 → lift (sym-≈ B b1 b2 (lower b1≈b2))}

    bisim-prop-valued : isPropValued bisim
    bisim-prop-valued (inl a1) (inl a2) = isOfHLevelLift 1 (prop-valued-≈ A a1 a2)
    bisim-prop-valued (inr b1) (inr b2) = isOfHLevelLift 1 (prop-valued-≈ B b1 b2)
    

σ1 : {A : DoublePoset ℓA ℓ'A ℓ''A} {B : DoublePoset ℓB ℓ'B ℓ''B} -> ⟨ A ==> (A ⊎p B) ⟩
σ1 = record {
  f = λ a → inl a ;
  isMon = λ {x} {y} x≤y → lift x≤y ;
  pres≈ = λ {x} {y} x≈y → lift x≈y }

σ2 : {A : DoublePoset ℓA ℓ'A ℓ''A} {B : DoublePoset ℓB ℓ'B ℓ''B} -> ⟨ B ==> (A ⊎p B) ⟩
σ2 = record {
  f = λ a → inr a ;
  isMon = λ {x} {y} x≤y → lift x≤y ;
  pres≈ = λ {x} {y} x≈y → lift x≈y }


𝔽 : (Clock -> DoublePoset ℓ ℓ' ℓ'') -> DoublePoset ℓ ℓ' ℓ''
𝔽 {ℓ' = ℓ'} {ℓ'' = ℓ''} A = (∀ k -> ⟨ A k ⟩) ,
  (dblposetstr
    (λ f g pf1 pf2 i1 i2 k →
      is-set-DblPoset (A k) (f k) (g k) (λ i' → pf1 i' k) (λ i' -> pf2 i' k) i1 i2)
    order (isorderingrelation
      (λ f g pf1 pf2 i k → prop-valued-≤ (A k) (f k) (g k) (pf1 k) (pf2 k) i )
      (λ f k → reflexive-≤ (A k) (f k))
      (λ f g h f≤g g≤h k → transitive-≤ (A k) (f k) (g k) (h k) (f≤g k) (g≤h k))
      λ f g f≤g g≤f i k → antisym-≤ (A k) (f k) (g k) (f≤g k) (g≤f k) i)
    bisim (isper
      (λ f k → reflexive-≈ (A k) (f k))
      (λ f g f≈g k → sym-≈ (A k) (f k) (g k) (f≈g k))
      λ f g pf1 pf2 i k → prop-valued-≈ (A k) (f k) (g k) (pf1 k) (pf2 k) i))
    where
      order : ((k : Clock) → ⟨ A k ⟩) -> ((k : Clock) → ⟨ A k ⟩) -> Type ℓ'
      order a a' = ∀ k -> rel-≤ (A k) (a k) (a' k)

      bisim : ((k : Clock) → ⟨ A k ⟩) -> ((k : Clock) → ⟨ A k ⟩) -> Type ℓ''
      bisim a a' = ∀ k -> rel-≈ (A k) (a k) (a' k)
    

    
-- Contructions involving later
module _ (k : Clock) where

  private
    ▹_ : Type ℓ -> Type ℓ
    ▹ A = ▹_,_ k A

    -- Theta for double posets
  DP▸ : ▹ DoublePoset ℓ ℓ' ℓ'' → DoublePoset ℓ ℓ' ℓ''
  DP▸ X = (▸ (λ t → ⟨ X t ⟩)) ,
            (dblposetstr
              is-set-later ord
              (isorderingrelation ord-prop-valued ord-refl ord-trans ord-antisym)
              bisim
              (isper bisim-refl bisim-sym bisim-prop-valued))

        where
          ord : ▸ (λ t → ⟨ X t ⟩) → ▸ (λ t → ⟨ X t ⟩) → Type _
          ord x1~ x2~ =  ▸ (λ t → (DblPosetStr._≤_ (str (X t)) (x1~ t)) (x2~ t))

          is-set-later : isSet (▸ (λ t → ⟨ X t ⟩))
          is-set-later = λ x y p1 p2 i j t →
            is-set-DblPoset (X t) (x t) (y t) (λ i' → p1 i' t) (λ i' → p2 i' t) i j

          ord-prop-valued : isPropValued ord
          ord-prop-valued = λ a b p q →
            isProp▸ (λ t -> prop-valued-≤ (X t) (a t) (b t)) p q

          ord-refl : (a : ▸ (λ t → ⟨ X t ⟩)) -> ord a a
          ord-refl a = λ t -> reflexive-≤ (X t) (a t)

          ord-trans : isTrans ord
          ord-trans = λ a b c a≤b b≤c t →
            transitive-≤ (X t) (a t) (b t) (c t) (a≤b t) (b≤c t)

          ord-antisym : isAntisym ord
          ord-antisym = λ a b a≤b b≤a i t ->
            antisym-≤ (X t) (a t) (b t) (a≤b t) (b≤a t) i

          bisim : ▸ (λ t → ⟨ X t ⟩) → ▸ (λ t → ⟨ X t ⟩) → Type _
          bisim x1~ x2~ = ▸ (λ t → (DblPosetStr._≈_ (str (X t)) (x1~ t)) (x2~ t))

          bisim-refl : (a : ▸ (λ t → ⟨ X t ⟩)) -> bisim a a
          bisim-refl a = λ t → reflexive-≈ (X t) (a t)

          bisim-sym : isSym bisim
          bisim-sym = λ a b a≈b t → sym-≈ (X t) (a t) (b t) (a≈b t)

          bisim-prop-valued : isPropValued bisim
          bisim-prop-valued = λ a b pf1 pf2 →
            isProp▸ (λ t → prop-valued-≈ (X t) (a t) (b t)) pf1 pf2

  DP▸'_ : DoublePoset ℓ ℓ' ℓ'' → DoublePoset ℓ ℓ' ℓ''
  DP▸' X = DP▸ (next X) 

  -- DP▸-next : (X : DoublePoset ℓ ℓ' ℓ'') -> DP▸ (next X) ≡ DP▹ X
  -- DP▸-next = {!refl!}

Zero : DPMor UnitDP ℕ
Zero = record {
  f = λ _ → zero ;
  isMon = λ _ → refl ;
  pres≈ = λ _ → refl }

Suc : DPMor (UnitDP ×dp ℕ) ℕ
Suc = record {
  f = λ (_ , n) → suc n ;
  isMon = λ { {_ , n} {_ , m} (_ , n≡m) → cong suc n≡m} ;
  pres≈ = λ { {_ , n} {_ , m} (_ , n≡m) → cong suc n≡m} }

Unit-×L : {X : Type ℓ} -> Unit × X ≃ X
Unit-×L = isoToEquiv
  (iso (λ {(_ , x) -> x}) (λ x -> (tt , x)) (λ x → refl) (λ p → refl))



{-
UnitP-×L-equiv : {X : Poset ℓ ℓ'} -> PosetEquiv (UnitP ×p X) X
UnitP-×L-equiv .fst = Unit-×L
UnitP-×L-equiv .snd = makeIsPosetEquiv Unit-×L is-mon is-mon-inv
  where
    is-mon : _
    is-mon (_ , x) (_ , x') (_ , x≤x') = x≤x'

    is-mon-inv : _
    is-mon-inv x x' x≤x' = refl , x≤x'

UnitP-×L : {X : Poset ℓ ℓ'} -> (UnitP ×p X) ≡ X
UnitP-×L {X = X} = equivFun (PosetPath (UnitP ×p X) X) UnitP-×L-equiv-}


