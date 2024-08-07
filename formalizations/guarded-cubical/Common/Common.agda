{-# OPTIONS --cubical #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


module Common.Common where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat hiding (_^_) renaming (ℕ to Nat)
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.FreeCommProduct
open import Cubical.Algebra.CommMonoid.Base
open import Cubical.Algebra.Monoid.More


private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓX ℓY ℓZ : Level
    ℓA ℓB ℓC ℓD : Level
    ℓR ℓS : Level

id : {ℓ : Level} -> {A : Type ℓ} -> A -> A
id x = x

_^_ : {ℓ : Level} -> {A : Type ℓ} -> (A -> A) -> Nat -> A -> A
f ^ zero = id
f ^ suc n = f ∘ (f ^ n)

⊥*→⊥ : {ℓ : Level} -> ⊥* {ℓ} -> ⊥
⊥*→⊥ ()


inl≠inr : ∀ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} ->
  (a : A) (b : B) -> inl a ≡ inr b -> ⊥
inl≠inr {_} {_} {A} {B} a b eq = transport (cong (diagonal ⊤ ⊥) eq) tt
  where
    diagonal : (Left Right : Type) -> (A ⊎ B) -> Type
    diagonal Left Right (inl a) = Left
    diagonal Left Right (inr b) = Right


{- From Cubical.Data.Sigma.Properties:
Σ-cong-iso-fst : {A A' : Type ℓ} {B : (a : A') → Type ℓ}
  (isom : Iso A A') → Iso (Σ A (B ∘ Iso.fun isom)) (Σ A' B)
-}

-- This is analogous to the above, but allows us to use the *inverse*
-- function instead.
-- A  = ∀ k. ▹ k , L k X
-- A' = ∀ k.       L k X
Σ-cong-iso-fst' : {A A' : Type ℓ} {B : (a : A) → Type ℓ'}
  (isom : Iso A A') → Iso (Σ A B) (Σ A' (B ∘ Iso.inv isom))
Σ-cong-iso-fst' isom = invIso (Σ-cong-iso-fst (invIso isom))


isoFun→isIso : {A : Type ℓ} {B : Type ℓ'} →
  (isom : Iso A B) → isIso (Iso.fun isom)
isoFun→isIso isom = (Iso.inv isom) , ((Iso.rightInv isom) , (Iso.leftInv isom))

isoInv→isIso : {A : Type ℓ} {B : Type ℓ'} →
  (isom : Iso A B) → isIso (Iso.inv isom)
isoInv→isIso isom = (Iso.fun isom) , ((Iso.leftInv isom) , (Iso.rightInv isom))


-- Definitions about relations and two-cells

compRel : {ℓR1 ℓR2 : Level} ->
  {X : Type ℓX} {Y : Type ℓY} {Z : Type ℓZ}
  (R1 : X -> Y -> Type ℓR1) ->
  (R2 : Y -> Z -> Type ℓR2) ->
  (X -> Z -> Type (ℓ-max ℓY (ℓ-max ℓR1 ℓR2)))
compRel {X = X} {Y = Y} {Z = Z} R1 R2 x z = Σ[ y ∈ Y ] R1 x y × R2 y z

isPropValuedRel : {A : Type ℓA} {B : Type ℓB} ->
  (R : A -> B -> Type ℓR) -> Type (ℓ-max (ℓ-max ℓA ℓB) ℓR)
isPropValuedRel {A = A} {B = B} R =
  (x : A) -> (y : B) -> isProp (R x y)

TwoCell : {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} {D : Type ℓD} ->
-- {A C : Type ℓ} -> {B D : Type ℓ'}
  (R : A -> B -> Type ℓR) ->
  (S : C -> D -> Type ℓS)
  (f : A -> C) ->
  (g : B -> D) ->
  Type (ℓ-max (ℓ-max (ℓ-max ℓA ℓB) ℓR) ℓS)
-- Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓR) ℓS)
TwoCell R S f g = ∀ a b -> R a b -> S (f a) (g b)

isPropTwoCell : {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} {D : Type ℓD} ->
  {R : A -> B -> Type ℓR} ->
  {S : C -> D -> Type ℓS}
  {f : A -> C} ->
  {g : B -> D} ->
  isPropValuedRel S ->
  isProp (TwoCell R S f g)
isPropTwoCell isPropValuedS =
  isPropΠ3 (λ a b aRb -> isPropValuedS _ _)


TwoCell→TwoCell : {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} {D : Type ℓD}
  {R R' : A -> B -> Type ℓR}
  {S S' : C -> D -> Type ℓS} ->
  (R'→R : ∀ a b -> R' a b -> R a b) ->
  (S→S' : ∀ c d -> S c d -> S' c d) ->
  {f : A -> C} ->
  {g : B -> D} ->
  TwoCell R S f g ->
  TwoCell R' S' f g
TwoCell→TwoCell R'→R S→S' {f = f} {g = g} f≤g =
  λ a b aR'b → S→S' (f a) (g b) (f≤g a b (R'→R a b aR'b))

TwoCell-VertComp :
  {ℓA₁ ℓA₁' ℓA₂ ℓA₂' ℓA₃ ℓA₃' ℓR₁ ℓR₂ ℓR₃ : Level}
  {A₁  : Type ℓA₁ }
  {A₁' : Type ℓA₁'}
  {A₂  : Type ℓA₂ }
  {A₂' : Type ℓA₂'}
  {A₃  : Type ℓA₃ }
  {A₃' : Type ℓA₃'}
  {R₁  : A₁ → A₁' → Type ℓR₁}
  {R₂  : A₂ → A₂' → Type ℓR₂}
  {R₃  : A₃ → A₃' → Type ℓR₃}
  {f₁  : A₁ →  A₂ }
  {g₁  : A₁' → A₂'}
  {f₂  : A₂ →  A₃ }
  {g₂  : A₂' → A₃'} →
  TwoCell R₁ R₂ f₁ g₁ →
  TwoCell R₂ R₃ f₂ g₂ →
  TwoCell R₁ R₃ (f₂ ∘ f₁) (g₂ ∘ g₁)
TwoCell-VertComp α₁ α₂ x y xR₁y = α₂ _ _ (α₁ _ _ xR₁y)
  


isSplitMono : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} ->
  (f : A -> B) -> Type (ℓ-max ℓA ℓB)
isSplitMono {A = A} {B = B} f =
 Σ[ g ∈ (B -> A) ] (∀ a -> g (f a) ≡ a)


InjectiveMonoidHom : {ℓm ℓn : Level} ->
  (M : Monoid ℓm) (N : Monoid ℓn) -> Type (ℓ-max ℓm ℓn)
InjectiveMonoidHom M N =
  Σ[ f ∈ MonoidHom M N ] isSplitMono (fst f)



TwoCell-iterated : {X : Type ℓ'} {Y : Type ℓ''} →
  (R : X → Y → Type ℓR) →
  (f : X → X) (g : Y → Y) →
  (TwoCell R R f g) →
  (n : Nat) → TwoCell R R (f ^ n) (g ^ n)
TwoCell-iterated R f g α zero = λ _ _ → id
TwoCell-iterated R f g α (suc n) = λ x y Rxy →
  α ((f ^ n) x)
    ((g ^ n) y)
    (TwoCell-iterated R f g α n x y Rxy)

id^n≡id : {X : Type ℓ'} →
  ∀ n → (id {A = X}) ^ n ≡ id
id^n≡id zero = refl
id^n≡id (suc n) = id^n≡id n

TwoCell-iterated-idL : {X : Type ℓ'} →
  (R : X → X → Type ℓR) →
  (g : X → X) →
  (TwoCell R R id g) →
  (n : Nat) → TwoCell R R id (g ^ n)
TwoCell-iterated-idL R g α n =
  transport (λ i → TwoCell R R (id^n≡id n i) (g ^ n)) (TwoCell-iterated R id g α n)

TwoCell-iterated-idR : {X : Type ℓ'} →
  (R : X → X → Type ℓ'') →
  (f : X → X) →
  (TwoCell R R f id) →
  (n : Nat) → TwoCell R R (f ^ n) id
TwoCell-iterated-idR R f α n =
  transport (λ i → TwoCell R R (f ^ n) (id^n≡id n i)) (TwoCell-iterated R f id α n)
