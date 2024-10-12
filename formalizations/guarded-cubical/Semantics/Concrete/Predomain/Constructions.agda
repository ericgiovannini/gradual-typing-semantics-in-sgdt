{-# OPTIONS --guarded --rewriting #-}

{-# OPTIONS --allow-unsolved-metas #-}


module Semantics.Concrete.Predomain.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport

open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (ℕ to Nat)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Sum.Base as Sum
open import Cubical.Data.Sum.Properties
open import Cubical.Data.Empty.Base

open import Cubical.Relation.Binary.Base

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Convenience
open import Semantics.Concrete.Predomain.Proofs

open import Common.Later
open import Common.LaterProperties

open BinaryRelation

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓ'X ℓ''X : Level
    ℓY ℓ'Y ℓ''Y : Level
    ℓZ ℓ'Z ℓ''Z : Level
    ℓ1 ℓ'1 ℓ''1 : Level
    ℓ2 ℓ'2 ℓ''2 : Level
    ℓA ℓ'A ℓ''A : Level
    ℓB ℓ'B ℓ''B : Level

    ℓ≤A ℓ≈A : Level
    ℓA' ℓ≤A' ℓ≈A' : Level
    ℓ≤B ℓ≈B : Level
    ℓC ℓ'C ℓ''C : Level
    ℓ≤ ℓ≈ : Level
    ℓX₁ ℓX₂ : Level
    ℓX' : Level

    X : Predomain ℓX ℓ'X ℓ''X
    Y : Predomain ℓY ℓ'Y ℓ''Y
    Z : Predomain ℓZ ℓ'Z ℓ''Z


-- Constructions not involving later


-- Turning a Set into a predomain with ordering and bisimilarity given by equality.

flat : hSet ℓ -> Predomain ℓ ℓ ℓ
flat h = ⟨ h ⟩ , (predomainstr
                   (str h) _≡_
                   (isorderingrelation (str h) (λ _ → refl)
                     (λ a b c a≡b b≡c → a ≡⟨ a≡b ⟩ b ≡⟨ b≡c ⟩ c ∎)
                     λ x y p q → p)
                   _≡_ (isbisim (λ _ → refl) (λ a b x → sym x) (str h)))


𝔹 : Predomain ℓ-zero ℓ-zero ℓ-zero
𝔹 = flat (Bool , isSetBool)

ℕ : Predomain ℓ-zero ℓ-zero ℓ-zero
ℕ = flat (Nat , isSetℕ)

flatRec : (X : hSet ℓ) (A : Predomain ℓA ℓ≤A ℓ≈A) → (⟨ X ⟩ → ⟨ A ⟩) →
  PMor (flat X) A
flatRec X A f .PMor.f = f
flatRec X A f .PMor.isMon {x = x} {y = y} x≡y =
  subst (λ z → A .snd .PredomainStr._≤_ (f x) z) (cong f x≡y) (A .snd .PredomainStr.is-refl (f x))
flatRec X A f .PMor.pres≈ {x = x} {y = y} x≡y =
  subst (λ z → A .snd .PredomainStr._≈_ (f x) z) (cong f x≡y) (A .snd .PredomainStr.is-refl-Bisim (f x))

-- Any function defined on Nat as a flat dbposet is monotone
flatNatFun-monotone : (f : Nat -> Nat) -> monotone {X = ℕ} {Y = ℕ} f
flatNatFun-monotone f {n} {m} n≡m = cong f n≡m


flatNatFun-preserve≈ : (f : Nat -> Nat) -> preserve≈ {X = ℕ} {Y = ℕ} f
flatNatFun-preserve≈ f {n} {m} n≈m = cong f n≈m



-- Constant functions induce morphisms of predomains
Const : (Y : Predomain ℓY ℓ'Y ℓ''Y) → (y : ⟨ Y ⟩) → {X : Predomain ℓX ℓ'X ℓ''X} → PMor X Y
Const Y y .PMor.f = λ _ → y
Const Y y .PMor.isMon = λ x1≤x2 → (Y .snd .PredomainStr.is-refl) y
Const Y y .PMor.pres≈ = λ x1≈x2 → (Y .snd .PredomainStr.is-refl-Bisim) y


-- The terminal object in the category of predomains

UnitP : Predomain ℓ-zero ℓ-zero ℓ-zero
UnitP = flat (Unit , isSetUnit)


-- unique morphism into UnitP
UnitP! : {A : Predomain ℓ ℓ' ℓ''} -> PMor A UnitP
UnitP! = record { f = λ _ → tt ; isMon = λ _ → refl ; pres≈ = λ _ → refl }

recUnitP : {A : Predomain ℓ ℓ' ℓ''} → ⟨ A ⟩ → PMor UnitP A
recUnitP {A = A} x =
  record {
    f = λ _ → x
  ; isMon = λ _ → A .snd .PredomainStr.is-refl x
  ; pres≈ = λ _ → A .snd .PredomainStr.is-refl-Bisim x}


LiftPredomain : {ℓ1 ℓ'1 ℓ''1 : Level} (X : Predomain ℓ1 ℓ'1 ℓ''1) ->
  (ℓ2 ℓ'2 ℓ''2 : Level) -> Predomain (ℓ-max ℓ1 ℓ2) (ℓ-max ℓ'1 ℓ'2) (ℓ-max ℓ''1 ℓ''2)
LiftPredomain {ℓ1 = ℓ1} {ℓ'1 = ℓ'1} {ℓ''1 = ℓ''1} X ℓ2 ℓ'2 ℓ''2 =
  (Lift {i = ℓ1} {j = ℓ2} ⟨ X ⟩) ,
  predomainstr
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
    (isbisim
      (λ {(lift x) → lift (X.is-refl-Bisim x)})
      (λ {(lift x) (lift y) (lift (x≈y)) → lift (X.is-sym x y x≈y)})
      λ {(lift x) (lift y) (lift p) (lift q) →
        cong lift (X.is-prop-valued-Bisim x y p q)})
  where
    module X = PredomainStr (X .snd)


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

infixl 21 _×dp_
_×dp_ : Predomain ℓA ℓ'A ℓ''A  -> Predomain ℓB ℓ'B ℓ''B -> Predomain (ℓ-max ℓA ℓB) (ℓ-max ℓ'A ℓ'B) (ℓ-max ℓ''A ℓ''B)
_×dp_ {ℓ'A = ℓ'A} {ℓ''A = ℓ''A} {ℓ'B = ℓ'B} {ℓ''B = ℓ''B} A B  =
  ⟨ A ⟩ × ⟨ B ⟩ ,
  predomainstr
    (isSet× A.is-set B.is-set)
    order
    (isorderingrelation order-prop-valued order-refl order-trans order-antisym)
    bisim
    (isbisim bisim-refl bisim-sym bisim-prop-valued)
  where
    module A = PredomainStr (A .snd)
    module B = PredomainStr (B .snd)

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

π1 : {A : Predomain ℓA ℓ'A ℓ''A} {B : Predomain ℓB ℓ'B ℓ''B} -> PMor (A ×dp B) A
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

π2 : {A : Predomain ℓA ℓ'A ℓ''A} {B : Predomain ℓB ℓ'B ℓ''B} -> PMor (A ×dp B) B
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

×-intro : PMor X Y → PMor X Z → PMor X (Y ×dp Z)
×-intro g h = record {
  f = λ x → g.f x , h.f x
  ; isMon = λ x≤y → (g.isMon x≤y) , (h.isMon x≤y)
  ; pres≈ = λ x≈y → (g.pres≈ x≈y) , (h.pres≈ x≈y)
  } where
  module g = PMor g
  module h = PMor h

PMorCurry' : {X Y Z : Predomain ℓ ℓ' ℓ''} ->
  PMor (Z ×dp X) Y -> ⟨ Z ⟩ -> PMor X Y
PMorCurry' {Z = Z} g z = record {
  f = λ x → g $ (z , x) ;
  isMon = λ {x1} {x2} x1≤x2 → PMor.isMon g (reflexive-≤ Z z , x1≤x2) ;
  pres≈ = λ {x1} {x2} x1≈x2 → PMor.pres≈ g (reflexive-≈ Z z , x1≈x2)  }

PMorCurry : {X Y Z : Predomain ℓ ℓ' ℓ''} ->
  PMor (Z ×dp X) Y -> PMor Z (IntHom X Y)
PMorCurry {X = X} {Y = Y} {Z = Z} g = record {
  f = λ z → PMorCurry' {X = X} {Y = Y} {Z = Z} g z ;
  isMon = λ {z} {z'} z≤z' → λ x → PMor.isMon g (z≤z' , reflexive-≤ X x) ;
  pres≈ = λ {z} {z'} z≈z' x x' x≈x' → PMor.pres≈ g (z≈z' , x≈x') }


-- Coproduct of predomains

module _ {A : Type ℓA} {B : Type ℓB} where

  module _ (_≤A_ : Rel A A ℓ≤A) (_≤B_ : Rel B B ℓ≤B) where
   
    ⊎-ord : A ⊎ B -> A ⊎ B -> Type (ℓ-max ℓ≤A ℓ≤B)
    ⊎-ord (inl a1) (inl a2) = Lift {j = ℓ≤B} (a1 ≤A a2)
    ⊎-ord (inl a1) (inr b1) = ⊥*
    ⊎-ord (inr b1) (inl a1) = ⊥*
    ⊎-ord (inr b1) (inr b2) = Lift {j = ℓ≤A} (b1 ≤B b2)

    ⊎-ord-prop-valued : isPropValued _≤A_ → isPropValued _≤B_ → isPropValued ⊎-ord
    ⊎-ord-prop-valued HA HB (inl a1) (inl a2) = isOfHLevelLift 1 (HA a1 a2)
    ⊎-ord-prop-valued HA HB (inr b1) (inr b2) = isOfHLevelLift 1 (HB b1 b2)

    ⊎-ord-refl : isRefl _≤A_ → isRefl _≤B_ → isRefl ⊎-ord
    ⊎-ord-refl HA HB (inl a) = lift (HA a)
    ⊎-ord-refl HA HB (inr b) = lift (HB b)

    ⊎-ord-trans : isTrans _≤A_ → isTrans _≤B_ → isTrans ⊎-ord
    ⊎-ord-trans HA HB (inl a1) (inl a2) (inl a3) a1≤a2 a2≤a3 =
      lift (HA a1 a2 a3 (lower a1≤a2) (lower a2≤a3))
    ⊎-ord-trans HA HB (inr b1) (inr b2) (inr b3) b1≤b2 b2≤b3 =
      lift (HB b1 b2 b3 (lower b1≤b2) (lower b2≤b3))

    ⊎-ord-antisym : isAntisym _≤A_ → isAntisym _≤B_ → isAntisym ⊎-ord
    ⊎-ord-antisym HA HB (inl a1) (inl a2) a≤b b≤a =
      cong inl (HA _ _ (lower a≤b) (lower b≤a))
    ⊎-ord-antisym HA HB (inr b1) (inr b2) a≤b b≤a =
      cong inr (HB _ _ (lower a≤b) (lower b≤a))

  module _ (_≈A_ : Rel A A ℓ≈A) (_≈B_ : Rel B B ℓ≈B) where

    ⊎-bisim : A ⊎ B -> A ⊎ B -> Type (ℓ-max ℓ≈A ℓ≈B)
    ⊎-bisim (inl a1) (inl a2) = Lift {j = ℓ≈B} (a1 ≈A a2)
    ⊎-bisim (inl a1) (inr b1) = ⊥*
    ⊎-bisim (inr b1) (inl a1) = ⊥*
    ⊎-bisim (inr b1) (inr b2) = Lift {j = ℓ≈A} (b1 ≈B b2)

    ⊎-bisim-refl : isRefl _≈A_ → isRefl _≈B_ → isRefl ⊎-bisim
    ⊎-bisim-refl HA HB = λ { (inl a) → lift (HA a) ;
                             (inr b) → lift (HB b) }

    ⊎-bisim-sym : isSym _≈A_ → isSym _≈B_ → isSym ⊎-bisim
    ⊎-bisim-sym HA HB = λ { (inl a1) (inl a2) a1≈a2 → lift (HA a1 a2 (lower a1≈a2)) ;
                            (inr b1) (inr b2) b1≈b2 → lift (HB b1 b2 (lower b1≈b2))}

    ⊎-bisim-prop-valued : isPropValued _≈A_ → isPropValued _≈B_ → isPropValued ⊎-bisim
    ⊎-bisim-prop-valued HA HB (inl a1) (inl a2) = isOfHLevelLift 1 (HA a1 a2)
    ⊎-bisim-prop-valued HA HB (inr b1) (inr b2) = isOfHLevelLift 1 (HB b1 b2)

_⊎p_ : (A : Predomain ℓA ℓ'A ℓ''A) (B : Predomain ℓB ℓ'B ℓ''B) →
    Predomain (ℓ-max ℓA ℓB) (ℓ-max ℓ'A ℓ'B) (ℓ-max ℓ''A ℓ''B)
_⊎p_ A B = (⟨ A ⟩ ⊎ ⟨ B ⟩) ,
  predomainstr (isSet⊎ A.is-set B.is-set)
  (⊎-ord A._≤_ B._≤_)
  (isorderingrelation
    (⊎-ord-prop-valued _ _ A.is-prop-valued B.is-prop-valued)
    (⊎-ord-refl _ _ A.is-refl B.is-refl)
    (⊎-ord-trans _ _ A.is-trans B.is-trans)
    (⊎-ord-antisym _ _ A.is-antisym B.is-antisym))
  (⊎-bisim A._≈_ B._≈_)
  (isbisim
    (⊎-bisim-refl _ _ A.is-refl-Bisim B.is-refl-Bisim)
    (⊎-bisim-sym _ _ A.is-sym B.is-sym)
    (⊎-bisim-prop-valued _ _ A.is-prop-valued-Bisim B.is-prop-valued-Bisim))
  where
    module A = PredomainStr (A .snd)
    module B = PredomainStr (B .snd)

{- predomainstr
    (isSet⊎ (A.is-set) (B.is-set))
    ⊎-ord (isorderingrelation ⊎-ord-prop-valued ⊎-ord-refl ⊎-ord-trans ⊎-ord-antisym)
    ⊎-bisim (isbisim ⊎-bisim-refl ⊎-bisim-sym ⊎-bisim-prop-valued)
    where
      module A = PredomainStr (A .snd)
      module B = PredomainStr (B .snd)
  -}

{-
_⊎p_ : Predomain ℓA ℓ'A ℓ''A  -> Predomain ℓB ℓ'B ℓ''B -> Predomain (ℓ-max ℓA ℓB) (ℓ-max ℓ'A ℓ'B) (ℓ-max ℓ''A ℓ''B)
_⊎p_ {ℓ'A = ℓ'A} {ℓ''A = ℓ''A} {ℓ'B = ℓ'B}  {ℓ''B = ℓ''B} A B =
  (⟨ A ⟩ ⊎ ⟨ B ⟩) ,
  predomainstr
    (isSet⊎ (A.is-set) (B.is-set))
    order (isorderingrelation order-prop-valued order-refl order-trans order-antisym)
    bisim (isbisim bisim-refl bisim-sym bisim-prop-valued)
  where
    module A = PredomainStr (A .snd)
    module B = PredomainStr (B .snd)

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
-}

σ1 : {A : Predomain ℓA ℓ'A ℓ''A} {B : Predomain ℓB ℓ'B ℓ''B} -> ⟨ A ==> (A ⊎p B) ⟩
σ1 = record {
  f = λ a → inl a ;
  isMon = λ {x} {y} x≤y → lift x≤y ;
  pres≈ = λ {x} {y} x≈y → lift x≈y }

σ2 : {A : Predomain ℓA ℓ'A ℓ''A} {B : Predomain ℓB ℓ'B ℓ''B} -> ⟨ B ==> (A ⊎p B) ⟩
σ2 = record {
  f = λ a → inr a ;
  isMon = λ {x} {y} x≤y → lift x≤y ;
  pres≈ = λ {x} {y} x≈y → lift x≈y }

⊎p-rec :
  {A : Predomain ℓA ℓ'A ℓ''A} {B : Predomain ℓB ℓ'B ℓ''B} {C : Predomain ℓC ℓ'C ℓ''C} →
  ⟨ A ==> C ⟩ -> ⟨ B ==> C ⟩ -> ⟨ (A ⊎p B) ==> C ⟩
⊎p-rec f g = record {
  f = λ { (inl a) → PMor.f f a ; (inr b) → PMor.f g b} ;
  isMon = λ { {inl a1} {inl a2} a1≤a2 → PMor.isMon f (lower a1≤a2) ;
              {inr b1} {inr b2} b1≤b2 → PMor.isMon g (lower b1≤b2) }  ;
  pres≈ = λ { {inl a1} {inl a2} a1≤a2 → PMor.pres≈ f (lower a1≤a2) ;
              {inr b1} {inr b2} b1≤b2 → PMor.pres≈ g (lower b1≤b2) } }


open PredomainStr

module _ (X : Type ℓX) (B : X → Type ℓ)
 
  where

  private
    Pi : Type (ℓ-max ℓX ℓ)
    Pi = (x : X) → B x

  module _ (ord-B : ∀ x → Rel (B x) (B x) ℓ≤) where
  
    Π-ord : Rel Pi Pi (ℓ-max ℓX ℓ≤)
    Π-ord as bs = ∀ x → ord-B x (as x) (bs x)

    Π-ord-prop-valued : (∀ x → isPropValued (ord-B x)) → isPropValued Π-ord
    Π-ord-prop-valued H as bs p q = funExt (λ x → H x (as x) (bs x) (p x) (q x))

    Π-ord-refl : (∀ x → isRefl (ord-B x)) → isRefl Π-ord
    Π-ord-refl H as x = H x (as x)

    Π-ord-trans : (∀ x → isTrans (ord-B x)) → isTrans Π-ord
    Π-ord-trans H as bs cs as≤bs bs≤cs x = H x (as x) (bs x) (cs x) (as≤bs x) (bs≤cs x)

    Π-ord-antisym : (∀ x → isAntisym (ord-B x)) → isAntisym Π-ord
    Π-ord-antisym H as bs as≤bs bs≤as =
     funExt (λ x → H x (as x) (bs x) (as≤bs x) (bs≤as x))

    isOrderingΠ : (∀ x → IsOrderingRelation (ord-B x)) → IsOrderingRelation Π-ord
    isOrderingΠ H = isorderingrelation
      (Π-ord-prop-valued (IsOrderingRelation.is-prop-valued ∘ H))
      (Π-ord-refl (IsOrderingRelation.is-refl ∘ H))
      (Π-ord-trans (IsOrderingRelation.is-trans ∘ H))
      (Π-ord-antisym (IsOrderingRelation.is-antisym ∘ H))

  module _ (bisim-B : ∀ x → Rel (B x) (B x) ℓ≈) where

    Π-bisim : Rel Pi Pi (ℓ-max ℓX ℓ≈)
    Π-bisim as bs = ∀ x → bisim-B x (as x) (bs x)

    Π-bisim-prop-valued : (∀ x → isPropValued (bisim-B x)) → isPropValued Π-bisim
    Π-bisim-prop-valued H as bs p q =
      funExt (λ x → H x (as x) (bs x) (p x) (q x))

    Π-bisim-refl : (∀ x → isRefl (bisim-B x)) → isRefl Π-bisim
    Π-bisim-refl H as x = H x (as x)

    Π-bisim-sym : (∀ x → isSym (bisim-B x)) → isSym Π-bisim
    Π-bisim-sym H as bs as≈bs x = H x (as x) (bs x) (as≈bs x)

    isBisimΠ : (∀ x → IsBisim (bisim-B x)) → IsBisim Π-bisim
    isBisimΠ H = isbisim
      (Π-bisim-refl (IsBisim.is-refl ∘ H))
      (Π-bisim-sym (IsBisim.is-sym ∘ H))
      (Π-bisim-prop-valued (IsBisim.is-prop-valued ∘ H))
   


-- Indexed product of predomains (must be at the same universe levels)
ΠP : (X : Type ℓX){ℓ ℓ≤ ℓ≈ : Level} → (A : X → Predomain ℓ ℓ≤ ℓ≈) →
  Predomain (ℓ-max ℓX ℓ) (ℓ-max ℓX ℓ≤) (ℓ-max ℓX ℓ≈)
ΠP X A = (∀ (x : X) → ⟨ A x ⟩) ,
  predomainstr (isSetΠ λ x → A x .snd .is-set) ord isOrdering bisim isBisimilarity

  where
    ord : _ → _ → Type _
    ord as bs = ∀ x → A x .snd  .PredomainStr._≤_ (as x) (bs x)

    ord-prop-valued : isPropValued ord
    ord-prop-valued as bs p q =
      funExt (λ x → A x .snd .is-prop-valued (as x) (bs x) (p x) (q x))

    ord-refl : isRefl ord
    ord-refl as x = A x .snd .is-refl (as x)

    ord-trans : isTrans ord
    ord-trans as bs cs as≤bs bs≤cs x =
      A x .snd .is-trans (as x) (bs x) (cs x) (as≤bs x) (bs≤cs x)

    ord-antisym : isAntisym ord
    ord-antisym as bs as≤bs bs≤as =
      funExt (λ x → A x .snd .is-antisym (as x) (bs x) (as≤bs x) (bs≤as x))

    isOrdering = isorderingrelation ord-prop-valued ord-refl ord-trans ord-antisym

    bisim : _ → _ → Type _
    bisim as bs = ∀ x → A x .snd .PredomainStr._≈_ (as x) (bs x)

    bisim-prop-valued : isPropValued bisim
    bisim-prop-valued as bs p q =
      funExt (λ x → A x .snd .is-prop-valued-Bisim (as x) (bs x) (p x) (q x))

    bisim-refl : isRefl bisim
    bisim-refl as x = A x .snd .is-refl-Bisim (as x)

    bisim-sym : isSym bisim
    bisim-sym as bs as≈bs x = A x .snd .is-sym (as x) (bs x) (as≈bs x)

    isBisimilarity = isbisim bisim-refl bisim-sym bisim-prop-valued


-- Intro and elim for Π
module _ {X : Type ℓX} {ℓ ℓ≤ ℓ≈ : Level} {B : X → Predomain ℓ ℓ≤ ℓ≈} where

  Π-intro : {A : Predomain ℓA ℓ≤A ℓ≈A} →
    ((x : X) → PMor A (B x)) →
    PMor A (ΠP X B)
  Π-intro fs .PMor.f a x = PMor.f (fs x) a
  Π-intro fs .PMor.isMon a₁≤a₂ x = PMor.isMon (fs x) a₁≤a₂
  Π-intro fs .PMor.pres≈ a₁≈a₂ x = PMor.pres≈ (fs x) a₁≈a₂

  Π-elim : (x : X) → PMor (ΠP X B) (B x)
  Π-elim x .PMor.f bs = bs x
  Π-elim x .PMor.isMon {x = as} {y = bs} as≤bs = as≤bs x
  Π-elim x .PMor.pres≈ {x = as} {y = bs} as≈bs = as≈bs x

-- Action of Π on a family of morphisms
Π-mor :
  (X : Type ℓX) →
  (A : X → Predomain ℓA ℓ≤A ℓ≈A) →
  (B : X → Predomain ℓB ℓ≤B ℓ≈B) →
  ((x : X) → PMor (A x) (B x)) →
  PMor (ΠP X A) (ΠP X B)
Π-mor X A B fs = Π-intro (λ y → (fs y) ∘p (Π-elim {B = A} y))
  


module _ (X : hSet ℓX) (B : ⟨ X ⟩ → Type ℓ) where

  private
    Sigma : Type (ℓ-max ℓX ℓ)
    Sigma = (Σ[ x ∈ ⟨ X ⟩ ] B x)

  module _ (ord-B : ∀ x → Rel (B x) (B x) ℓ≤) where
  
    Σ-ord : Rel Sigma Sigma (ℓ-max ℓX ℓ≤)
    Σ-ord (x₁ , b₁) (x₂ , b₂) =
        Σ[ eq ∈ (x₁ ≡ x₂) ] (ord-B x₂ (subst (λ x → B x ) eq b₁) b₂)

    Σ-ord-prop-valued : (∀ x → isPropValued (ord-B x)) → isPropValued Σ-ord
    Σ-ord-prop-valued H (x₁ , b₁) (x₂ , b₂) (eq , b₁≤b₂) (eq' , b₁≤b₂') =
      ΣPathP ((X .snd x₁ x₂ eq eq') ,
              (isProp→PathP (λ i → H x₂ _ _) b₁≤b₂ b₁≤b₂'))

    Σ-ord-refl : (∀ x → isRefl (ord-B x)) → isRefl Σ-ord
    Σ-ord-refl H (x , b) = refl ,
      subst
        (λ y → ord-B x y b)
        (sym (substRefl {B = B} b))
        (H x b)

    Σ-ord-trans : (∀ x → isTrans (ord-B x)) → isTrans Σ-ord
    Σ-ord-trans H (x₁ , b₁) (x₂ , b₂) (x₃ , b₃) (x₁≡x₂ , b₁₂≤b₂) (x₂≡x₃ , b₂₃≤b₃) =
      (x₁≡x₂ ∙ x₂≡x₃) ,
      transport (λ i → ord-B x₃ (sym (substComposite T x₁≡x₂ x₂≡x₃ b₁) i) b₃) lem
        where
          T : ⟨ X ⟩ → Type _
          T = λ x → B x
        
          b₁₃  = subst T (x₁≡x₂ ∙ x₂≡x₃) b₁
          b₁₂  = subst T x₁≡x₂ b₁
          b₁₂₃ = subst T x₂≡x₃ b₁₂
          b₂₃  = subst T x₂≡x₃ b₂
          
          b₁₂₃≤b₂₃ : ord-B x₃ b₁₂₃ b₂₃
          b₁₂₃≤b₂₃ = transport-rel (cong B x₂≡x₃) (ord-B x₂) (ord-B x₃) (cong ord-B x₂≡x₃) b₁₂≤b₂
          -- rel-transport-≤ (cong B x₂≡x₃) b₁₂≤b₂

          -- Goal: b₁₃ (B x₃).≤ b₃
          -- Know: b₁₃ = b₁₂₃ by substComposite
          --
          -- STS b₁₂₃ (B x₃).≤ b₃
          -- By transitivity STS b₁₂₃ ≤ b₂₃ ≤ b₃.
          -- The latter is true by assumption, and the former
          -- follows by assumption b₁₂≤b₂ and the fact that B x₂ ≡ B x₃.
          lem : ord-B x₃ b₁₂₃ b₃
          lem = H x₃  b₁₂₃ b₂₃ b₃ b₁₂₃≤b₂₃ b₂₃≤b₃
         
    
    Σ-ord-antisym : (∀ x → isAntisym (ord-B x)) → isAntisym Σ-ord
    Σ-ord-antisym H (x₁ , b₁) (x₂ , b₂) (x₁≡x₂ , b₁₂≤b₂) (x₂≡x₁ , b₂₁≤b₁) =
      ΣPathP (x₁≡x₂ , toPathP eq)
        where
          T : ⟨ X ⟩ → Type _
          T = λ x → B x
          
          b₁₂  = subst T x₁≡x₂ b₁
          b₁₂₁ = subst T x₂≡x₁ b₁₂
          b₂₁  = subst T x₂≡x₁ b₂
          b₂₁₂ = subst T x₁≡x₂ b₂₁

          pf-inverse : x₁≡x₂ ≡ sym x₂≡x₁
          pf-inverse = X .snd x₁ x₂ x₁≡x₂ (sym x₂≡x₁)

          b₂₁₂≤b₁₂ : ord-B x₂ b₂₁₂ b₁₂
          b₂₁₂≤b₁₂ = transport-rel (cong B x₁≡x₂) (ord-B x₁) (ord-B x₂) (cong ord-B x₁≡x₂) b₂₁≤b₁
          -- rel-transport-≤ (cong B x₁≡x₂) b₂₁≤b₁

          b₂₁₂≡b₂ : b₂₁₂ ≡ b₂
          b₂₁₂≡b₂ = let e1 = (λ i → subst T (pf-inverse i) b₂₁) in
                    let e2 = subst⁻Subst T x₂≡x₁ b₂ in
                    e1 ∙ e2
          
          eq : b₁₂ ≡ b₂
          eq = H x₂ b₁₂ b₂ b₁₂≤b₂
            (subst (λ z → ord-B x₂ z b₁₂) b₂₁₂≡b₂ b₂₁₂≤b₁₂)


  module _ (bisim-B : ∀ x → Rel (B x) (B x) ℓ≈) where

    Σ-bisim : Rel Sigma Sigma (ℓ-max ℓX ℓ≈)
    Σ-bisim (x₁ , b₁) (x₂ , b₂) =
      Σ[ eq ∈ (x₁ ≡ x₂) ] ((bisim-B x₂) (subst (λ x → B x) eq b₁) b₂)

    Σ-bisim-refl : (∀ x → isRefl (bisim-B x)) → isRefl Σ-bisim
    Σ-bisim-refl H (x , b) = refl ,
      subst
        (λ y → (bisim-B x) y b)
        (sym (substRefl {B = λ x → B x} b))
        (H x b)

    Σ-bisim-sym : (∀ x → isSym (bisim-B x)) → isSym Σ-bisim
    Σ-bisim-sym H (x₁ , b₁) (x₂ , b₂) (x₁≡x₂ , b₁₂≈b₂) =
      (sym x₁≡x₂) ,
      transport-rel-lemma (cong B (sym x₁≡x₂)) (bisim-B x₂) (bisim-B x₁)
      (cong bisim-B (sym x₁≡x₂)) (H x₂ _ _ b₁₂≈b₂) -- rel-transport-≈-lemma (cong B (sym x₁≡x₂)) (H x₂ _ _ b₁₂≈b₂)

    Σ-bisim-prop-valued : (∀ x → isPropValued (bisim-B x)) → isPropValued Σ-bisim
    Σ-bisim-prop-valued H (x₁ , b₁) (x₂ , b₂) (eq , b₁≈b₂) (eq' , b₁≈b₂') =
      ΣPathP ((X .snd x₁ x₂ eq eq') ,
              (isProp→PathP (λ i → H x₂ _ _) b₁≈b₂ b₁≈b₂'))
  

-- Σ for predomains (i.e. a Type-indexed coproduct of predomains)
ΣP : (X : hSet ℓX) → {ℓ ℓ≤ ℓ≈ : Level} →
  (B : ⟨ X ⟩ → Predomain ℓ ℓ≤ ℓ≈) →
  Predomain (ℓ-max ℓX ℓ) (ℓ-max ℓX ℓ≤) (ℓ-max ℓX ℓ≈)
ΣP X B = (Σ[ x ∈ ⟨ X ⟩ ] ⟨ B x ⟩) ,
  (predomainstr (isSetΣ (X .snd) (λ x → B x .snd .is-set))
    ord (isorderingrelation ord-prop-valued ord-refl ord-trans ord-antisym)
    bisim (isbisim bisim-refl bisim-sym bisim-prop-valued))

  where

    ord : _ → _ → Type _
    ord (x₁ , b₁) (x₂ , b₂) =
      Σ[ eq ∈ (x₁ ≡ x₂) ] (rel-≤ (B x₂) (subst (λ x → ⟨ B x ⟩) eq b₁) b₂)

    ord-prop-valued : isPropValued ord
    ord-prop-valued (x₁ , b₁) (x₂ , b₂) (eq , b₁≤b₂) (eq' , b₁≤b₂') =
      ΣPathP ((X .snd x₁ x₂ eq eq') ,
              (isProp→PathP (λ i → B x₂ .snd .is-prop-valued _ _) b₁≤b₂ b₁≤b₂'))

    ord-refl : isRefl ord
    ord-refl (x , b) = refl ,
      subst
        (λ y → rel-≤ (B x) y b)
        (sym (substRefl {B = λ x → ⟨ B x ⟩} b))
        (B x .snd .is-refl b)

    ord-trans : isTrans ord
    ord-trans (x₁ , b₁) (x₂ , b₂) (x₃ , b₃) (x₁≡x₂ , b₁₂≤b₂) (x₂≡x₃ , b₂₃≤b₃) =
      (x₁≡x₂ ∙ x₂≡x₃) ,
      transport (λ i → rel-≤ (B x₃) (sym (substComposite T x₁≡x₂ x₂≡x₃ b₁) i) b₃) lem
        where
          T : ⟨ X ⟩ → Type _
          T = λ x → ⟨ B x ⟩
        
          b₁₃  = subst T (x₁≡x₂ ∙ x₂≡x₃) b₁
          b₁₂  = subst T x₁≡x₂ b₁
          b₁₂₃ = subst T x₂≡x₃ b₁₂
          b₂₃  = subst T x₂≡x₃ b₂
          
          b₁₂₃≤b₂₃ : rel-≤ (B x₃) b₁₂₃ b₂₃
          b₁₂₃≤b₂₃ = rel-transport-≤ (cong B x₂≡x₃) b₁₂≤b₂

          -- Goal: b₁₃ (B x₃).≤ b₃
          -- Know: b₁₃ = b₁₂₃ by substComposite
          --
          -- STS b₁₂₃ (B x₃).≤ b₃
          -- By transitivity STS b₁₂₃ ≤ b₂₃ ≤ b₃.
          -- The latter is true by assumption, and the former
          -- follows by assumption b₁₂≤b₂ and the fact that B x₂ ≡ B x₃.
          lem : rel-≤ (B x₃) b₁₂₃ b₃
          lem = B x₃ .snd .is-trans b₁₂₃ b₂₃ b₃ b₁₂₃≤b₂₃ b₂₃≤b₃
         
    
    ord-antisym : isAntisym ord
    ord-antisym (x₁ , b₁) (x₂ , b₂) (x₁≡x₂ , b₁₂≤b₂) (x₂≡x₁ , b₂₁≤b₁) =
      ΣPathP (x₁≡x₂ , toPathP eq)
        where
          T : ⟨ X ⟩ → Type _
          T = λ x → ⟨ B x ⟩
          
          b₁₂  = subst T x₁≡x₂ b₁
          b₁₂₁ = subst T x₂≡x₁ b₁₂
          b₂₁  = subst T x₂≡x₁ b₂
          b₂₁₂ = subst T x₁≡x₂ b₂₁

          pf-inverse : x₁≡x₂ ≡ sym x₂≡x₁
          pf-inverse = X .snd x₁ x₂ x₁≡x₂ (sym x₂≡x₁)

          b₂₁₂≤b₁₂ : rel-≤ (B x₂) b₂₁₂ b₁₂
          b₂₁₂≤b₁₂ = rel-transport-≤ (cong B x₁≡x₂) b₂₁≤b₁

          b₂₁₂≡b₂ : b₂₁₂ ≡ b₂
          b₂₁₂≡b₂ = let e1 = (λ i → subst T (pf-inverse i) b₂₁) in
                    let e2 = subst⁻Subst T x₂≡x₁ b₂ in
                    e1 ∙ e2
          
          eq : b₁₂ ≡ b₂
          eq = B x₂ .snd .is-antisym b₁₂ b₂ b₁₂≤b₂
            (subst (λ z → rel-≤ (B x₂) z b₁₂) b₂₁₂≡b₂ b₂₁₂≤b₁₂) 

    bisim : _ → _ → Type _
    bisim (x₁ , b₁) (x₂ , b₂) =
      Σ[ eq ∈ (x₁ ≡ x₂) ] (rel-≈ (B x₂) (subst (λ x → ⟨ B x ⟩) eq b₁) b₂)

    bisim-refl : isRefl bisim
    bisim-refl (x , b) = refl ,
      subst
        (λ y → rel-≈ (B x) y b)
        (sym (substRefl {B = λ x → ⟨ B x ⟩} b))
        (B x .snd .is-refl-Bisim b)

    bisim-sym : isSym bisim
    bisim-sym (x₁ , b₁) (x₂ , b₂) (x₁≡x₂ , b₁₂≈b₂) =
      (sym x₁≡x₂) , rel-transport-≈-lemma (cong B (sym x₁≡x₂)) (B x₂ .snd .is-sym _ _ b₁₂≈b₂)

    bisim-prop-valued : isPropValued bisim
    bisim-prop-valued (x₁ , b₁) (x₂ , b₂) (eq , b₁≈b₂) (eq' , b₁≈b₂') =
      ΣPathP ((X .snd x₁ x₂ eq eq') ,
              (isProp→PathP (λ i → B x₂ .snd .is-prop-valued-Bisim _ _) b₁≈b₂ b₁≈b₂'))



-- Intro and elim for Σ
module _ {X : hSet ℓX} {ℓ ℓ≤ ℓ≈ : Level} {B : ⟨ X ⟩ → Predomain ℓ ℓ≤ ℓ≈} where

  Σ-intro : (x : ⟨ X ⟩) → PMor (B x) (ΣP X B)
  Σ-intro x .PMor.f b = x , b
  Σ-intro x .PMor.isMon {x = b₁} {y = b₂} b₁≤b₂ =
    refl , subst (λ b → rel-≤ (B x) b b₂) (sym (transportRefl b₁)) b₁≤b₂
  Σ-intro x .PMor.pres≈ {x = b₁} {y = b₂} b₁≈b₂ =
    refl , subst (λ b → rel-≈ (B x) b b₂) (sym (transportRefl b₁)) b₁≈b₂

  -- Σ-intro' : {A : Predomain ℓA ℓ≤A ℓ≈A} →
  --   (g : ⟨ A ⟩ → ⟨ X ⟩) → ((a : ⟨ A ⟩) → PMor A (B (g a))) → PMor A (ΣP X B)
  -- Σ-intro' g h .PMor.f a = (g a) , h a .PMor.f a
  -- Σ-intro' g h .PMor.isMon {x = a₁} {y = a₂} a₁≤a₂ = {!!} , {!!}
  -- Σ-intro' g h .PMor.pres≈ = {!!}
    -- record {
    -- f = λ x → g.f x , h.f x
    -- ; isMon = λ x≤y → (g.isMon x≤y) , (h.isMon x≤y)
    -- ; pres≈ = λ x≈y → (g.pres≈ x≈y) , (h.pres≈ x≈y)
    -- } where
    -- module g = PMor g
    -- module h = PMor h

  Σ-elim₁ : ⟨ (ΣP X B) ⟩ → ⟨ X ⟩
  Σ-elim₁ = fst

  Σ-elim₂ : (p : ⟨ ΣP X B ⟩) → ⟨ B (Σ-elim₁ p) ⟩
  Σ-elim₂ = snd

  Σ-elim : {A : Predomain ℓA ℓ≤A ℓ≈A} →
    ((x : ⟨ X ⟩) → PMor (B x) A) →
    PMor (ΣP X B) A
  Σ-elim fs .PMor.f (x , b) = fs x .PMor.f b
  Σ-elim {A = A} fs .PMor.isMon {x = (x₁ , b₁)} {y = (x₂ , b₂)} (x₁≡x₂ , b₁≤b₂) =
    transport
      (λ i → rel-≤ A
        (fs (sym x₁≡x₂ i) .PMor.f (path i))
        (fs x₂ .PMor.f b₂))
      (fs x₂ .PMor.isMon b₁≤b₂)
      where
        path : PathP (λ i → ⟨ B (x₁≡x₂ (~ i)) ⟩) (subst (λ x → ⟨ B x ⟩) x₁≡x₂ b₁) b₁
        path = symP (subst-filler (λ x → ⟨ B x ⟩) x₁≡x₂ b₁)
  Σ-elim {A = A} fs .PMor.pres≈ {x = (x₁ , b₁)} {y = (x₂ , b₂)} (x₁≡x₂ , b₁≈b₂) =
     transport
      (λ i → rel-≈ A
        (fs (sym x₁≡x₂ i) .PMor.f (path i))
        (fs x₂ .PMor.f b₂))
      (fs x₂ .PMor.pres≈ b₁≈b₂)
      where
        path : PathP (λ i → ⟨ B (x₁≡x₂ (~ i)) ⟩) (subst (λ x → ⟨ B x ⟩) x₁≡x₂ b₁) b₁
        path = symP (subst-filler (λ x → ⟨ B x ⟩) x₁≡x₂ b₁)


module _
  (X : hSet ℓX)
  (X' : hSet ℓX')
  (f : ⟨ X ⟩ → ⟨ X' ⟩)
  (A : ⟨ X ⟩ → Predomain ℓA ℓ≤A ℓ≈A)
  (A' : ⟨ X' ⟩ → Predomain ℓA' ℓ≤A' ℓ≈A')
  (g : (x : ⟨ X ⟩) → PMor (A x) (A' (f x)))
  where

  Σ-mor' : PMor (ΣP X A) (ΣP X' A')
  Σ-mor' = Σ-elim {B = A} {A = (ΣP X' A')} (λ x → (Σ-intro {B = A'} (f x)) ∘p (g x))
  -- Σ-mor' .PMor.f (x , a) = (f x) , g x .PMor.f a
  -- Σ-mor' .PMor.isMon {x = (x₁ , a₁)} {y = (x₂ , a₂)} (x₁≡x₂ , a₁≤a₂) =
  --   (cong f x₁≡x₂) , {!!}
  -- Σ-mor' .PMor.pres≈ {x = (x₁ , a₁)} {y = (x₂ , a₂)} (x₁≡x₂ , a₁≈a₂) =
  --   {!!}

-- Action of Σ on a family of morphisms
Σ-mor :
  (X : hSet ℓX) →
  (A : ⟨ X ⟩ → Predomain ℓA ℓ≤A ℓ≈A) →
  (B : ⟨ X ⟩ → Predomain ℓB ℓ≤B ℓ≈B) →
  ((x : ⟨ X ⟩) → PMor (A x) (B x)) →
  PMor (ΣP X A) (ΣP X B)
-- Σ-mor X A B fs = {!!}
Σ-mor X A B fs = Σ-mor' X X (λ x → x) A B fs

{-
Σ-mor X A B fs .PMor.f (x , a) = (x , fs x .PMor.f a)

Σ-mor X A B fs .PMor.isMon {x = (x₁ , a₁)} {y = (x₂ , a₂)} (x₁≡x₂ , a₁₂≤a₂) = x₁≡x₂ , aux
  where
    open PMor 
    TA : ⟨ X ⟩ → Type _
    TA = λ x → ⟨ A x ⟩

    TB : ⟨ X ⟩ → Type _
    TB = λ x → ⟨ B x ⟩

    a₁₂ = subst TA x₁≡x₂ a₁

    -- fs x₂ a₁₂ ≤ fs x₂ a₂
    lem1 : rel-≤ (B x₂) (fs x₂ .f a₁₂) (fs x₂ .f a₂)
    lem1 = fs x₂ .isMon a₁₂≤a₂

    lem2 : PathP (λ i → ⟨ B (x₁≡x₂ i) ⟩) (fs x₁ .f a₁) (fs x₂ .f a₁₂)
    lem2 i = fs (x₁≡x₂ i) .f (subst-filler TA x₁≡x₂ a₁ i)

    lem3 : (subst TB x₁≡x₂ (fs x₁ .f a₁)) ≡ fs x₂ .f a₁₂
    lem3 = fromPathP lem2
    
    -- lem2 : (fs x₂ .f a₁₂) ≡ (subst TB x₁≡x₂ (fs x₁ .f a₁))
    -- lem2 =
    --   fs x₂ .f a₁₂
    --   ≡⟨ cong (fs x₂ .f) (sym {!subst-filler TA ? a₂!}) ⟩ fs x₂ .f a₂
    --   ≡⟨ (subst-filler (λ _ → B x₂ .fst) x₁≡x₂ (fs x₂ .f a₂)) ⟩ _
    --   ≡⟨ {!!} ⟩
    --   _ ∎
 
    aux : rel-≤ (B x₂) (subst TB x₁≡x₂ (fs x₁ .f a₁)) (fs x₂ .f a₂)
    aux = subst (λ z → rel-≤ (B x₂) z (fs x₂ .f a₂)) (sym lem3) lem1

  
Σ-mor X A B fs .PMor.pres≈ = {!!}
-- Π-intro (λ y → (fs y) ∘p (Π-elim {B = A} y))
-}


module _
  (X₁ : hSet ℓX₁)
  (X₂ : hSet ℓX₂)
  (A₁ : ⟨ X₁ ⟩ → Predomain ℓA ℓ≤A ℓ≈A)
  (A₂ : ⟨ X₂ ⟩ → Predomain ℓA ℓ≤A ℓ≈A)
  where

  private
    X₁⊎X₂ : hSet (ℓ-max ℓX₁ ℓX₂)
    X₁⊎X₂ = (⟨ X₁ ⟩ ⊎ ⟨ X₂ ⟩) , isSet⊎ (X₁ .snd) (X₂ .snd)

    A₁⊎A₂ : ⟨ X₁⊎X₂ ⟩ → Predomain ℓA ℓ≤A ℓ≈A
    A₁⊎A₂ = Sum.rec A₁ A₂
  
  Iso-⊎Σ-Σ⊎ : PredomIso
    (ΣP X₁⊎X₂ (Sum.rec A₁ A₂))
    ((ΣP X₁ A₁) ⊎p (ΣP X₂ A₂))
  Iso-⊎Σ-Σ⊎ .PredomIso.fun =
    Σ-elim {B = A₁⊎A₂} {A = (ΣP X₁ A₁) ⊎p (ΣP X₂ A₂)}
      (Sum.elim (λ x₁ → (σ1 {B = ΣP X₂ A₂}) ∘p (Σ-intro {B = A₁} x₁))
                (λ x₂ → (σ2 {A = ΣP X₁ A₁}) ∘p (Σ-intro {B = A₂} x₂)))
  Iso-⊎Σ-Σ⊎ .PredomIso.inv =
    ⊎p-rec {A = ΣP X₁ A₁} {B = ΣP X₂ A₂}
      (Σ-mor' X₁ X₁⊎X₂ inl A₁ A₁⊎A₂ (λ x₁ → Id))
      (Σ-mor' X₂ X₁⊎X₂ inr A₂ A₁⊎A₂ (λ x₂ → Id))
  Iso-⊎Σ-Σ⊎ .PredomIso.invRight (inl _) = refl
  Iso-⊎Σ-Σ⊎ .PredomIso.invRight (inr _) = refl
  Iso-⊎Σ-Σ⊎ .PredomIso.invLeft (inl _ , _) = refl
  Iso-⊎Σ-Σ⊎ .PredomIso.invLeft (inr _ , _) = refl


module _ {ℓY : Level}
  (X₁ : hSet ℓX₁)
  (X₂ : hSet ℓX₂)
  (Y₁ : ⟨ X₁ ⟩ → Type ℓY)
  (Y₂ : ⟨ X₂ ⟩ → Type ℓY)
  (A₁ : (x₁ : ⟨ X₁ ⟩) → Y₁ x₁ → Predomain ℓA ℓ≤A ℓ≈A)
  (A₂ : (x₂ : ⟨ X₂ ⟩) → Y₂ x₂ → Predomain ℓA ℓ≤A ℓ≈A)

  where

  private
    X₁⊎X₂ : hSet (ℓ-max ℓX₁ ℓX₂)
    X₁⊎X₂ = (⟨ X₁ ⟩ ⊎ ⟨ X₂ ⟩) , isSet⊎ (X₁ .snd) (X₂ .snd)

    A₁⊎A₂ : (s : ⟨ X₁⊎X₂ ⟩) (z : Sum.rec Y₁ Y₂ s) → Predomain ℓA ℓ≤A ℓ≈A
    A₁⊎A₂ = Sum.elim {C = λ s → Sum.rec Y₁ Y₂ s → Predomain ℓA ℓ≤A ℓ≈A} A₁ A₂

    Π-s : ∀ (s : ⟨ X₁⊎X₂ ⟩) → Predomain (ℓ-max ℓA ℓY) (ℓ-max ℓY ℓ≤A) (ℓ-max ℓY ℓ≈A)
    Π-s s = ΠP (Sum.rec Y₁ Y₂ s)
      (Sum.elim {C = λ s' → Sum.rec Y₁ Y₂ s' → Predomain ℓA ℓ≤A ℓ≈A} A₁ A₂ s)

    LHS = (ΣP X₁⊎X₂ Π-s)
                
    RHS = ((ΣP X₁ (λ x₁ → ΠP (Y₁ x₁) (A₁ x₁))) ⊎p
           (ΣP X₂ (λ x₂ → ΠP (Y₂ x₂) (A₂ x₂))))

  Predom-Iso-ΣΠ-⊎ : PredomIso LHS RHS
  Predom-Iso-ΣΠ-⊎ .PredomIso.fun = Σ-elim {B = Π-s} {A = RHS}
    (Sum.elim
      (λ x₁ →
           σ1 {B = ΣP X₂ (λ x₂ → ΠP (Y₂ x₂) (A₂ x₂))}
        ∘p Σ-intro {B = λ x → ΠP (Y₁ x) (A₁ x)} x₁)
      (λ x₂ →
           σ2 {A = ΣP X₁ λ x₁ → ΠP (Y₁ x₁) (A₁ x₁)}
       ∘p Σ-intro {B = λ x → ΠP (Y₂ x) (A₂ x)} x₂))
  Predom-Iso-ΣΠ-⊎ .PredomIso.inv = ⊎p-rec
    {A = ΣP X₁ (λ x₁ → ΠP (Y₁ x₁) (A₁ x₁))} {B = ΣP X₂ (λ x₂ → ΠP (Y₂ x₂) (A₂ x₂))}
    (Σ-mor' X₁ X₁⊎X₂ inl (λ x₁ → ΠP (Y₁ x₁) (A₁ x₁)) Π-s (λ x₁ → Id))
    (Σ-mor' X₂ X₁⊎X₂ inr (λ x₂ → ΠP (Y₂ x₂) (A₂ x₂)) Π-s (λ x₂ → Id))
  
  Predom-Iso-ΣΠ-⊎ .PredomIso.invRight (inl _) = refl
  Predom-Iso-ΣΠ-⊎ .PredomIso.invRight (inr _) = refl
  
  Predom-Iso-ΣΠ-⊎ .PredomIso.invLeft (inl _ , _) = refl
  Predom-Iso-ΣΠ-⊎ .PredomIso.invLeft (inr _ , _) = refl
    

{-
module _ {ℓY₁ ℓY₂ : Level}
  (X₁ : Type ℓX₁)
  (X₂ : Type ℓX₂)
  (Y₁ : X₁ → Type ℓY₁)
  (Y₂ : X₂ → Type ℓY₂)
  (A₁ : (x₁ : X₁) → Y₁ x₁ → Predomain ℓA ℓ≤A ℓ≈A)
  (A₂ : (x₂ : X₂) → Y₂ x₂ → Predomain ℓA ℓ≤A ℓ≈A) 
  where

  test : (s : X₁ ⊎ X₂) → PredomIso
    (Sum.rec
      (λ x₁ → ΠP (Lift {j = ℓY₂} (Y₁ x₁)) (A₁ x₁ ∘ lower))
      (λ x₂ → ΠP (Lift {j = ℓY₁} (Y₂ x₂)) (A₂ x₂ ∘ lower)) s)
      
    (ΠP (Sum.rec ((Lift {j = ℓY₂}) ∘ Y₁) ((Lift {j = ℓY₁}) ∘ Y₂) s)
      (Sum.elim
        {C = λ s' → Sum.rec (Lift ∘ Y₁) (Lift ∘ Y₂) s' → Predomain ℓA ℓ≤A ℓ≈A}
        (λ x₁ y₁ → A₁ x₁ (lower y₁) ) (λ x₂ y₂ → A₂ x₂ (lower y₂)) s))
  test (inl x) = {!!}
  test (inr x) = {!!}
-}

-- Given types A and A' and a retraction g : A' → A, if A has a
-- predomain structure then we can define a predomain structure on A'

module _
  {ℓA ℓA' ℓ≤A' ℓ≈A' : Level}
  (A : Type ℓA)
  (A' : Type ℓA')
  (f : A → A')
  (g : A' → A)
  (retr : retract f g)
  (isPredomA' : PredomainStr ℓ≤A' ℓ≈A' A') where

  private
    module A' = PredomainStr isPredomA'

  isInjectivef : ∀ x₁ x₂ → f x₁ ≡ f x₂ → x₁ ≡ x₂
  isInjectivef x₁ x₂ eq = sym (retr x₁) ∙ cong g eq ∙ retr x₂

  predomRetractStr : PredomainStr ℓ≤A' ℓ≈A' A
  predomRetractStr .is-set = isSetRetract f g retr A'.is-set
  predomRetractStr .PredomainStr._≤_ x₁ x₂ = f x₁ A'.≤ f x₂
  predomRetractStr .isOrderingRelation =
    isorderingrelation
      (λ x₁ x₂ → A'.is-prop-valued (f x₁) (f x₂))
      (λ x → A'.is-refl (f x))
      (λ x₁ x₂ x₃ fx₁≤fx₂ fx₂≤fx₃ → A'.is-trans (f x₁) (f x₂) (f x₃) fx₁≤fx₂ fx₂≤fx₃)
      (λ x₁ x₂ fx₁≤fx₂ fx₂≤fx₁ → isInjectivef x₁ x₂ (A'.is-antisym (f x₁) (f x₂) fx₁≤fx₂ fx₂≤fx₁))
  predomRetractStr ._≈_ x₁ x₂ = f x₁ A'.≈ f x₂
  predomRetractStr .isBisim =
    isbisim
      (λ x → A'.is-refl-Bisim (f x))
      (λ x₁ x₂ fx₁≈fx₂ → A'.is-sym (f x₁) (f x₂) fx₁≈fx₂)
      (λ x₁ x₂ → A'.is-prop-valued-Bisim (f x₁) (f x₂))

  predomRetract : Predomain ℓA ℓ≤A' ℓ≈A'
  predomRetract = A , predomRetractStr

  retractMorphism : PMor predomRetract (A' , isPredomA')
  retractMorphism .PMor.f = f
  retractMorphism .PMor.isMon fx₁≤fx₂ = fx₁≤fx₂
  retractMorphism .PMor.pres≈ fx₁≈fx₂ = fx₁≈fx₂



𝔽 : (Clock -> Predomain ℓ ℓ' ℓ'') -> Predomain ℓ ℓ' ℓ''
𝔽 {ℓ' = ℓ'} {ℓ'' = ℓ''} A = (∀ k -> ⟨ A k ⟩) ,
  (predomainstr
    (λ f g pf1 pf2 i1 i2 k →
      is-set-Predomain (A k) (f k) (g k) (λ i' → pf1 i' k) (λ i' -> pf2 i' k) i1 i2)
    order (isorderingrelation
      (λ f g pf1 pf2 i k → prop-valued-≤ (A k) (f k) (g k) (pf1 k) (pf2 k) i )
      (λ f k → reflexive-≤ (A k) (f k))
      (λ f g h f≤g g≤h k → transitive-≤ (A k) (f k) (g k) (h k) (f≤g k) (g≤h k))
      λ f g f≤g g≤f i k → antisym-≤ (A k) (f k) (g k) (f≤g k) (g≤f k) i)
    bisim (isbisim
      (λ f k → reflexive-≈ (A k) (f k))
      (λ f g f≈g k → sym-≈ (A k) (f k) (g k) (f≈g k))
      λ f g pf1 pf2 i k → prop-valued-≈ (A k) (f k) (g k) (pf1 k) (pf2 k) i))
    where
      order : ((k : Clock) → ⟨ A k ⟩) -> ((k : Clock) → ⟨ A k ⟩) -> Type ℓ'
      order a a' = ∀ k -> rel-≤ (A k) (a k) (a' k)

      bisim : ((k : Clock) → ⟨ A k ⟩) -> ((k : Clock) → ⟨ A k ⟩) -> Type ℓ''
      bisim a a' = ∀ k -> rel-≈ (A k) (a k) (a' k)



-- Contructions involving later
module Clocked (k : Clock) where

  private
    ▹_ : Type ℓ -> Type ℓ
    ▹ A = ▹_,_ k A

    -- Theta for predomains
  P▸ : ▹ Predomain ℓ ℓ' ℓ'' → Predomain ℓ ℓ' ℓ''
  P▸ X = (▸ (λ t → ⟨ X t ⟩)) ,
            (predomainstr
              is-set-later ord
              (isorderingrelation ord-prop-valued ord-refl ord-trans ord-antisym)
              bisim
              (isbisim bisim-refl bisim-sym bisim-prop-valued))

        where
          ord : ▸ (λ t → ⟨ X t ⟩) → ▸ (λ t → ⟨ X t ⟩) → Type _
          ord x1~ x2~ =  ▸ (λ t → (PredomainStr._≤_ (str (X t)) (x1~ t)) (x2~ t))

          is-set-later : isSet (▸ (λ t → ⟨ X t ⟩))
          is-set-later = λ x y p1 p2 i j t →
            is-set-Predomain (X t) (x t) (y t) (λ i' → p1 i' t) (λ i' → p2 i' t) i j

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
          bisim x1~ x2~ = ▸ (λ t → (PredomainStr._≈_ (str (X t)) (x1~ t)) (x2~ t))

          bisim-refl : (a : ▸ (λ t → ⟨ X t ⟩)) -> bisim a a
          bisim-refl a = λ t → reflexive-≈ (X t) (a t)

          bisim-sym : isSym bisim
          bisim-sym = λ a b a≈b t → sym-≈ (X t) (a t) (b t) (a≈b t)

          bisim-prop-valued : isPropValued bisim
          bisim-prop-valued = λ a b pf1 pf2 →
            isProp▸ (λ t → prop-valued-≈ (X t) (a t) (b t)) pf1 pf2

  P▸'_ : Predomain ℓ ℓ' ℓ'' → Predomain ℓ ℓ' ℓ''
  P▸' X = P▸ (next X)

  P▹_ : Predomain ℓ ℓ' ℓ'' → Predomain ℓ ℓ' ℓ''
  P▹ X = P▸ (next X)

  -- P▸-next : (X : Predomain ℓ ℓ' ℓ'') -> P▸ (next X) ≡ P▹ X
  -- P▸-next = {!refl!}


  -- We can turn a "later" morphism f : ▸_t ((X~ t) → (Y~ t))
  -- into a morphism ▸f : (P▸ X~) → (P▸ Y~).
  PMor▸ : {X~ : ▹ Predomain ℓX ℓ'X ℓ''X} {Y~ : ▹ Predomain ℓY ℓ'Y ℓ''Y} ->
    (▸ (λ t -> PMor (X~ t) (Y~ t))) →
    (PMor (P▸ X~) (P▸ Y~))
  PMor▸ {X~ = X~} f~ .PMor.f x~ =
    λ t -> PMor.f (f~ t) (x~ t) -- or : map▹ MonFun.f f~ ⊛ x~
  PMor▸ {X~ = X~} f~ .PMor.isMon {x~} {y~} x~≤y~ =
    λ t -> PMor.isMon (f~ t) (x~≤y~ t)
  PMor▸ {X~ = X~} f~ .PMor.pres≈ {x~} {y~} x~≤y~ =
    λ t -> PMor.pres≈ (f~ t) (x~≤y~ t)


Zero : PMor UnitP ℕ
Zero = record {
  f = λ _ → zero ;
  isMon = λ _ → refl ;
  pres≈ = λ _ → refl }

Suc : PMor (UnitP ×dp ℕ) ℕ
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




