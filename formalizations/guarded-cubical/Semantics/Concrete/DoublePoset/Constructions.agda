{-# OPTIONS --guarded --rewriting #-}

{-# OPTIONS --allow-unsolved-metas #-}


module Semantics.Concrete.DoublePoset.Constructions where

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
open import Cubical.Data.Sum.Base
open import Cubical.Data.Sum.Properties
open import Cubical.Data.Empty.Base

open import Cubical.Relation.Binary.Base

open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Convenience
open import Semantics.Concrete.DoublePoset.DPMorProofs

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

    X : PosetBisim ℓX ℓ'X ℓ''X
    Y : PosetBisim ℓY ℓ'Y ℓ''Y
    Z : PosetBisim ℓZ ℓ'Z ℓ''Z


-- Constructions not involving later


-- Turning a Set into a predomain with ordering and bisimilarity given by equality.

flat : hSet ℓ -> PosetBisim ℓ ℓ ℓ
flat h = ⟨ h ⟩ , (posetbisimstr
                   (str h) _≡_
                   (isorderingrelation (str h) (λ _ → refl)
                     (λ a b c a≡b b≡c → a ≡⟨ a≡b ⟩ b ≡⟨ b≡c ⟩ c ∎)
                     λ x y p q → p)
                   _≡_ (isbisim (λ _ → refl) (λ a b x → sym x) (str h)))


𝔹 : PosetBisim ℓ-zero ℓ-zero ℓ-zero
𝔹 = flat (Bool , isSetBool)

ℕ : PosetBisim ℓ-zero ℓ-zero ℓ-zero
ℕ = flat (Nat , isSetℕ)

-- Any function defined on Nat as a flat dbposet is monotone
flatNatFun-monotone : (f : Nat -> Nat) -> monotone {X = ℕ} {Y = ℕ} f
flatNatFun-monotone f {n} {m} n≡m = cong f n≡m


flatNatFun-preserve≈ : (f : Nat -> Nat) -> preserve≈ {X = ℕ} {Y = ℕ} f
flatNatFun-preserve≈ f {n} {m} n≈m = cong f n≈m



-- Constant functions induce morphisms of predomains
Const : (Y : PosetBisim ℓY ℓ'Y ℓ''Y) → (y : ⟨ Y ⟩) → {X : PosetBisim ℓX ℓ'X ℓ''X} → PBMor X Y
Const Y y .PBMor.f = λ _ → y
Const Y y .PBMor.isMon = λ x1≤x2 → (Y .snd .PosetBisimStr.is-refl) y
Const Y y .PBMor.pres≈ = λ x1≈x2 → (Y .snd .PosetBisimStr.is-refl-Bisim) y


-- The terminal object in the category of predomains

UnitPB : PosetBisim ℓ-zero ℓ-zero ℓ-zero
UnitPB = flat (Unit , isSetUnit)


-- unique morphism into UnitP
UnitPB! : {A : PosetBisim ℓ ℓ' ℓ''} -> PBMor A UnitPB
UnitPB! = record { f = λ _ → tt ; isMon = λ _ → refl ; pres≈ = λ _ → refl }


LiftPosetBisim : {ℓ1 ℓ'1 ℓ''1 : Level} (X : PosetBisim ℓ1 ℓ'1 ℓ''1) ->
  (ℓ2 ℓ'2 ℓ''2 : Level) -> PosetBisim (ℓ-max ℓ1 ℓ2) (ℓ-max ℓ'1 ℓ'2) (ℓ-max ℓ''1 ℓ''2)
LiftPosetBisim {ℓ1 = ℓ1} {ℓ'1 = ℓ'1} {ℓ''1 = ℓ''1} X ℓ2 ℓ'2 ℓ''2 =
  (Lift {i = ℓ1} {j = ℓ2} ⟨ X ⟩) ,
  posetbisimstr
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
    module X = PosetBisimStr (X .snd)


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
_×dp_ : PosetBisim ℓA ℓ'A ℓ''A  -> PosetBisim ℓB ℓ'B ℓ''B -> PosetBisim (ℓ-max ℓA ℓB) (ℓ-max ℓ'A ℓ'B) (ℓ-max ℓ''A ℓ''B)
_×dp_ {ℓ'A = ℓ'A} {ℓ''A = ℓ''A} {ℓ'B = ℓ'B} {ℓ''B = ℓ''B} A B  =
  ⟨ A ⟩ × ⟨ B ⟩ ,
  posetbisimstr
    (isSet× A.is-set B.is-set)
    order
    (isorderingrelation order-prop-valued order-refl order-trans order-antisym)
    bisim
    (isbisim bisim-refl bisim-sym bisim-prop-valued)
  where
    module A = PosetBisimStr (A .snd)
    module B = PosetBisimStr (B .snd)

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

π1 : {A : PosetBisim ℓA ℓ'A ℓ''A} {B : PosetBisim ℓB ℓ'B ℓ''B} -> PBMor (A ×dp B) A
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

π2 : {A : PosetBisim ℓA ℓ'A ℓ''A} {B : PosetBisim ℓB ℓ'B ℓ''B} -> PBMor (A ×dp B) B
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

×-intro : PBMor X Y → PBMor X Z → PBMor X (Y ×dp Z)
×-intro g h = record {
  f = λ x → g.f x , h.f x
  ; isMon = λ x≤y → (g.isMon x≤y) , (h.isMon x≤y)
  ; pres≈ = λ x≈y → (g.pres≈ x≈y) , (h.pres≈ x≈y)
  } where
  module g = PBMor g
  module h = PBMor h

PBMorCurry' : {X Y Z : PosetBisim ℓ ℓ' ℓ''} ->
  PBMor (Z ×dp X) Y -> ⟨ Z ⟩ -> PBMor X Y
PBMorCurry' {Z = Z} g z = record {
  f = λ x → g $ (z , x) ;
  isMon = λ {x1} {x2} x1≤x2 → PBMor.isMon g (reflexive-≤ Z z , x1≤x2) ;
  pres≈ = λ {x1} {x2} x1≈x2 → PBMor.pres≈ g (reflexive-≈ Z z , x1≈x2)  }

PBMorCurry : {X Y Z : PosetBisim ℓ ℓ' ℓ''} ->
  PBMor (Z ×dp X) Y -> PBMor Z (IntHom X Y)
PBMorCurry {X = X} {Y = Y} {Z = Z} g = record {
  f = λ z → PBMorCurry' {X = X} {Y = Y} {Z = Z} g z ;
  isMon = λ {z} {z'} z≤z' → λ x → PBMor.isMon g (z≤z' , reflexive-≤ X x) ;
  pres≈ = λ {z} {z'} z≈z' x x' x≈x' → PBMor.pres≈ g (z≈z' , x≈x') }


-- Coproduct of predomains

_⊎p_ : PosetBisim ℓA ℓ'A ℓ''A  -> PosetBisim ℓB ℓ'B ℓ''B -> PosetBisim (ℓ-max ℓA ℓB) (ℓ-max ℓ'A ℓ'B) (ℓ-max ℓ''A ℓ''B)
_⊎p_ {ℓ'A = ℓ'A} {ℓ''A = ℓ''A} {ℓ'B = ℓ'B}  {ℓ''B = ℓ''B} A B =
  (⟨ A ⟩ ⊎ ⟨ B ⟩) ,
  posetbisimstr
    (isSet⊎ (A.is-set) (B.is-set))
    order (isorderingrelation order-prop-valued order-refl order-trans order-antisym)
    bisim (isbisim bisim-refl bisim-sym bisim-prop-valued)
  where
    module A = PosetBisimStr (A .snd)
    module B = PosetBisimStr (B .snd)

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


σ1 : {A : PosetBisim ℓA ℓ'A ℓ''A} {B : PosetBisim ℓB ℓ'B ℓ''B} -> ⟨ A ==> (A ⊎p B) ⟩
σ1 = record {
  f = λ a → inl a ;
  isMon = λ {x} {y} x≤y → lift x≤y ;
  pres≈ = λ {x} {y} x≈y → lift x≈y }

σ2 : {A : PosetBisim ℓA ℓ'A ℓ''A} {B : PosetBisim ℓB ℓ'B ℓ''B} -> ⟨ B ==> (A ⊎p B) ⟩
σ2 = record {
  f = λ a → inr a ;
  isMon = λ {x} {y} x≤y → lift x≤y ;
  pres≈ = λ {x} {y} x≈y → lift x≈y }


open PosetBisimStr


-- Indexed product of predomains (must be at the same universe levels)


ΠP : (X : Type ℓX){ℓ ℓ≤ ℓ≈ : Level} → (A : X → PosetBisim ℓ ℓ≤ ℓ≈) →
  PosetBisim (ℓ-max ℓX ℓ) (ℓ-max ℓX ℓ≤) (ℓ-max ℓX ℓ≈)
ΠP X A = (∀ (x : X) → ⟨ A x ⟩) ,
  posetbisimstr (isSetΠ λ x → A x .snd .is-set) ord isOrdering bisim isBisimilarity

  where
    ord : _ → _ → Type _
    ord as bs = ∀ x → A x .snd  .PosetBisimStr._≤_ (as x) (bs x)

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
    bisim as bs = ∀ x → A x .snd .PosetBisimStr._≈_ (as x) (bs x)

    bisim-prop-valued : isPropValued bisim
    bisim-prop-valued as bs p q =
      funExt (λ x → A x .snd .is-prop-valued-Bisim (as x) (bs x) (p x) (q x))

    bisim-refl : isRefl bisim
    bisim-refl as x = A x .snd .is-refl-Bisim (as x)

    bisim-sym : isSym bisim
    bisim-sym as bs as≈bs x = A x .snd .is-sym (as x) (bs x) (as≈bs x)

    isBisimilarity = isbisim bisim-refl bisim-sym bisim-prop-valued


-- Intro and elim for Π
module _ {X : Type ℓX} {ℓ ℓ≤ ℓ≈ : Level} {B : X → PosetBisim ℓ ℓ≤ ℓ≈} where

  Π-intro : {A : PosetBisim ℓA ℓ≤A ℓ≈A} →
    ((x : X) → PBMor A (B x)) →
    PBMor A (ΠP X B)
  Π-intro fs .PBMor.f a x = PBMor.f (fs x) a
  Π-intro fs .PBMor.isMon a₁≤a₂ x = PBMor.isMon (fs x) a₁≤a₂
  Π-intro fs .PBMor.pres≈ a₁≈a₂ x = PBMor.pres≈ (fs x) a₁≈a₂

  Π-elim : (x : X) → PBMor (ΠP X B) (B x)
  Π-elim x .PBMor.f bs = bs x
  Π-elim x .PBMor.isMon {x = as} {y = bs} as≤bs = as≤bs x
  Π-elim x .PBMor.pres≈ {x = as} {y = bs} as≈bs = as≈bs x

-- Action of Π on a family of morphisms
Π-mor : ∀ {ℓ ℓ≤ ℓ≈}
  (X : Type ℓX) →
  (A B : X → PosetBisim ℓ ℓ≤ ℓ≈) →
  ((x : X) → PBMor (A x) (B x)) →
  PBMor (ΠP X A) (ΠP X B)
Π-mor X A B fs = Π-intro (λ y → (fs y) ∘p (Π-elim {B = A} y))
  


-- Σ for predomains (i.e. a Type-indexed coproduct of predomains)

ΣP : (X : hSet ℓX) → {ℓ ℓ≤ ℓ≈ : Level} →
  (B : ⟨ X ⟩ → PosetBisim ℓ ℓ≤ ℓ≈) →
  PosetBisim (ℓ-max ℓX ℓ) (ℓ-max ℓX ℓ≤) (ℓ-max ℓX ℓ≈)
ΣP X B = (Σ[ x ∈ ⟨ X ⟩ ] ⟨ B x ⟩) ,
  (posetbisimstr (isSetΣ (X .snd) (λ x → B x .snd .is-set))
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
module _ {X : hSet ℓX} {ℓ ℓ≤ ℓ≈ : Level} {B : ⟨ X ⟩ → PosetBisim ℓ ℓ≤ ℓ≈} where

  Σ-intro : (x : ⟨ X ⟩) → PBMor (B x) (ΣP X B)
  Σ-intro x .PBMor.f b = x , b
  Σ-intro x .PBMor.isMon {x = b₁} {y = b₂} b₁≤b₂ =
    refl , subst (λ b → rel-≤ (B x) b b₂) (sym (transportRefl b₁)) b₁≤b₂
  Σ-intro x .PBMor.pres≈ {x = b₁} {y = b₂} b₁≈b₂ =
    refl , subst (λ b → rel-≈ (B x) b b₂) (sym (transportRefl b₁)) b₁≈b₂

  Σ-intro' : {A : PosetBisim ℓA ℓ≤A ℓ≈A} →
    (g : ⟨ A ⟩ → ⟨ X ⟩) → ((a : ⟨ A ⟩) → PBMor A (B (g a))) → PBMor A (ΣP X B)
  Σ-intro' g h .PBMor.f a = (g a) , h a .PBMor.f a
  Σ-intro' g h .PBMor.isMon {x = a₁} {y = a₂} a₁≤a₂ = {!!} , {!!}
  Σ-intro' g h .PBMor.pres≈ = {!!}
    -- record {
    -- f = λ x → g.f x , h.f x
    -- ; isMon = λ x≤y → (g.isMon x≤y) , (h.isMon x≤y)
    -- ; pres≈ = λ x≈y → (g.pres≈ x≈y) , (h.pres≈ x≈y)
    -- } where
    -- module g = PBMor g
    -- module h = PBMor h

  Σ-elim₁ : ⟨ (ΣP X B) ⟩ → ⟨ X ⟩
  Σ-elim₁ = fst

  Σ-elim₂ : (p : ⟨ ΣP X B ⟩) → ⟨ B (Σ-elim₁ p) ⟩
  Σ-elim₂ = snd

-- Action of Σ on a family of morphisms
Σ-mor : ∀ {ℓ ℓ≤ ℓ≈}
  (X : hSet ℓX) →
  (A B : ⟨ X ⟩ → PosetBisim ℓ ℓ≤ ℓ≈) →
  ((x : ⟨ X ⟩) → PBMor (A x) (B x)) →
  PBMor (ΣP X A) (ΣP X B)
-- Σ-mor X A B fs = {!!}
Σ-mor X A B fs .PBMor.f (x , a) = (x , fs x .PBMor.f a)

Σ-mor X A B fs .PBMor.isMon {x = (x₁ , a₁)} {y = (x₂ , a₂)} (x₁≡x₂ , a₁₂≤a₂) = x₁≡x₂ , aux
  where
    open PBMor 
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
  
Σ-mor X A B fs .PBMor.pres≈ = {!!}
-- Π-intro (λ y → (fs y) ∘p (Π-elim {B = A} y))





𝔽 : (Clock -> PosetBisim ℓ ℓ' ℓ'') -> PosetBisim ℓ ℓ' ℓ''
𝔽 {ℓ' = ℓ'} {ℓ'' = ℓ''} A = (∀ k -> ⟨ A k ⟩) ,
  (posetbisimstr
    (λ f g pf1 pf2 i1 i2 k →
      is-set-PosetBisim (A k) (f k) (g k) (λ i' → pf1 i' k) (λ i' -> pf2 i' k) i1 i2)
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

    -- Theta for double posets
  PB▸ : ▹ PosetBisim ℓ ℓ' ℓ'' → PosetBisim ℓ ℓ' ℓ''
  PB▸ X = (▸ (λ t → ⟨ X t ⟩)) ,
            (posetbisimstr
              is-set-later ord
              (isorderingrelation ord-prop-valued ord-refl ord-trans ord-antisym)
              bisim
              (isbisim bisim-refl bisim-sym bisim-prop-valued))

        where
          ord : ▸ (λ t → ⟨ X t ⟩) → ▸ (λ t → ⟨ X t ⟩) → Type _
          ord x1~ x2~ =  ▸ (λ t → (PosetBisimStr._≤_ (str (X t)) (x1~ t)) (x2~ t))

          is-set-later : isSet (▸ (λ t → ⟨ X t ⟩))
          is-set-later = λ x y p1 p2 i j t →
            is-set-PosetBisim (X t) (x t) (y t) (λ i' → p1 i' t) (λ i' → p2 i' t) i j

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
          bisim x1~ x2~ = ▸ (λ t → (PosetBisimStr._≈_ (str (X t)) (x1~ t)) (x2~ t))

          bisim-refl : (a : ▸ (λ t → ⟨ X t ⟩)) -> bisim a a
          bisim-refl a = λ t → reflexive-≈ (X t) (a t)

          bisim-sym : isSym bisim
          bisim-sym = λ a b a≈b t → sym-≈ (X t) (a t) (b t) (a≈b t)

          bisim-prop-valued : isPropValued bisim
          bisim-prop-valued = λ a b pf1 pf2 →
            isProp▸ (λ t → prop-valued-≈ (X t) (a t) (b t)) pf1 pf2

  PB▸'_ : PosetBisim ℓ ℓ' ℓ'' → PosetBisim ℓ ℓ' ℓ''
  PB▸' X = PB▸ (next X)

  PB▹_ : PosetBisim ℓ ℓ' ℓ'' → PosetBisim ℓ ℓ' ℓ''
  PB▹ X = PB▸ (next X)

  -- PB▸-next : (X : PosetBisim ℓ ℓ' ℓ'') -> PB▸ (next X) ≡ PB▹ X
  -- PB▸-next = {!refl!}


  -- We can turn a "later" morphism f : ▸_t ((X~ t) → (Y~ t))
  -- into a morphism ▸f : (PB▸ X~) → (PB▸ Y~).
  PBMor▸ : {X~ : ▹ PosetBisim ℓX ℓ'X ℓ''X} {Y~ : ▹ PosetBisim ℓY ℓ'Y ℓ''Y} ->
    (▸ (λ t -> PBMor (X~ t) (Y~ t))) →
    (PBMor (PB▸ X~) (PB▸ Y~))
  PBMor▸ {X~ = X~} f~ .PBMor.f x~ =
    λ t -> PBMor.f (f~ t) (x~ t) -- or : map▹ MonFun.f f~ ⊛ x~
  PBMor▸ {X~ = X~} f~ .PBMor.isMon {x~} {y~} x~≤y~ =
    λ t -> PBMor.isMon (f~ t) (x~≤y~ t)
  PBMor▸ {X~ = X~} f~ .PBMor.pres≈ {x~} {y~} x~≤y~ =
    λ t -> PBMor.pres≈ (f~ t) (x~≤y~ t)


Zero : PBMor UnitPB ℕ
Zero = record {
  f = λ _ → zero ;
  isMon = λ _ → refl ;
  pres≈ = λ _ → refl }

Suc : PBMor (UnitPB ×dp ℕ) ℕ
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
