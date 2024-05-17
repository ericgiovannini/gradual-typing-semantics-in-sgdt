{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Common.ClockProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Cubical.Foundations.Isomorphism

open import Common.Common
open import Common.Later

open import Agda.Builtin.Equality renaming (_≡_ to _≣_) hiding (refl)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.Data.Equality.Conversion hiding (Iso ; funExt)
-- open import Cubical.Data.Prod

private
  variable
    ℓ ℓ' ℓ'' : Level



--------------------------------------------------------------------------
-- Rewrites used in the proofs.
-- Note that only one of these actually involves an axiom: rewrite-force

path-clock-irrel-bool-1 : {k k' : Clock} -> (b : Bool) ->
  bool-clock-irrel (λ _ -> b) k k' ≡ refl
path-clock-irrel-bool-1 b = isSetBool b b _ refl

rewrite-clock-irrel-bool-1 : {k k' : Clock} -> (b : Bool) ->
  bool-clock-irrel (λ _ -> b) k k' ≣ refl
rewrite-clock-irrel-bool-1 {k = k} {k' = k'} b =
  pathToEq (path-clock-irrel-bool-1 b)


path-clock-irrel-bool-2 :
    (M : Clock -> Bool) -> bool-clock-irrel M k0 k0 ≡ refl
path-clock-irrel-bool-2 M =
  isSetBool (M k0) (M k0) (bool-clock-irrel M k0 k0) refl

rewrite-clock-irrel-bool-2 :
    (M : Clock -> Bool) -> bool-clock-irrel M k0 k0 ≣ refl
rewrite-clock-irrel-bool-2 M =
  pathToEq (path-clock-irrel-bool-2 M)


rewrite-force : ∀ {ℓ : Level} -> {A : Clock -> Type ℓ} (f : ∀ k -> A k) →
  force' (λ k -> next (f k)) ≣ f
rewrite-force f = pathToEq (force'-beta f)


rewrite-transp : ∀ {ℓ : Level} {X : Type ℓ} →
  transp (λ i → X) i0 ≣ id
rewrite-transp = pathToEq (funExt (λ x -> transportRefl x))

{-# REWRITE rewrite-clock-irrel-bool-1 #-}

{-# REWRITE rewrite-clock-irrel-bool-2 #-}

{-# REWRITE rewrite-force #-}

{-# REWRITE rewrite-transp #-}
--------------------------------------------------------------------------


{- Iso definitions used in this file:

 _Iso⟨_⟩_  : {ℓ ℓ' ℓ'' : Level} {B : Type ℓ'} {C : Type ℓ''}
              (X : Type ℓ) →
              Iso X B → Iso B C → Iso X C
  _∎Iso     : {ℓ : Level} (A : Type ℓ) → Iso A A


   Σ-Π-Iso   : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : A → Type ℓ'}
              {C : (a : A) → B a → Type ℓ''} →
              Iso ((a : A) → Σ-syntax (B a) (C a))
                  (Σ-syntax ((a : A) → B a) (λ f → (a : A) → C a (f a)))

   codomainIsoDep
            : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : A → Type ℓ'}
              {C : A → Type ℓ''} →
              ((a : A) → Iso (B a) (C a)) → Iso ((a : A) → B a) ((a : A) → C a)

   ⊎Iso      : {A.ℓa : Level} {A : Type A.ℓa} {C.ℓc : Level}
              {C : Type C.ℓc} {B.ℓb : Level} {B : Type B.ℓb} {D.ℓd : Level}
              {D : Type D.ℓd} →
              Iso A C → Iso B D → Iso (A ⊎ B) (C ⊎ D)

  Σ-cong-iso-fst
            : {A.ℓ : Level} {A : Type A.ℓ} {B..1 : Level} {A' : Type B..1}
              {B.ℓ : Level} {B : A' → Type B.ℓ} (isom : Iso A A') →
              Iso (Σ A (B ∘ Iso.fun isom)) (Σ A' B)

  Σ-cong-iso-snd
            : {B'..1 : Level} {A : Type B'..1} {B.ℓ : Level} {B : A → Type B.ℓ}
              {B'.ℓ : Level} {B' : A → Type B'.ℓ} →
              ((x : A) → Iso (B x) (B' x)) → Iso (Σ A B) (Σ A B')

-}

-- Turn an equality into an iso.
Eq-Iso : {A B : Type ℓ} ->
  A ≡ B -> Iso A B
Eq-Iso {A = A} {B = B} H-eq = subst (Iso A) H-eq idIso
-- same as: transport (cong (Iso A) H-eq) idIso


-- The unit type is clock-irrelevant.
Unit-clock-irrel : clock-irrel Unit
Unit-clock-irrel M k k' with M k | M k'
...  | tt | tt = refl

-- The empty type is clock-irrelevant.
⊥-clock-irrel : clock-irrel ⊥
⊥-clock-irrel M k k' = isProp⊥ (M k) (M k')

⊥*-clock-irrel : clock-irrel {ℓ = ℓ} ⊥*
⊥*-clock-irrel M k k' = isProp⊥* (M k) (M k')


Π-Path : ∀ {A : Type ℓ} {B : Type ℓ'} {x y : B} →
  Iso (A → Path B x y) (Path (A → B) (λ a → x) (λ a → y))
Π-Path = iso
  (λ f → funExt (λ a → f a))
  (λ eq a → funExt⁻ eq a)
  (λ _ → refl)
  (λ _ → refl)


∀k-path : ∀ {A : Type ℓ} {x y : A} →
  clock-irrel A →
  Iso (∀ (k : Clock) → Path A x y) (Path A x y)
∀k-path {A = A} {x = x} {y = y}  H =
  ((k : Clock) → Path A x y)
    Iso⟨ Π-Path ⟩
  Path (∀ (k : Clock) → A) (λ k → x) (λ k → y)
    Iso⟨ congPathIso {!!} ⟩
  Path A x y
  ∎Iso

path-clock-irrel : ∀ {A : Type ℓ} {x y : A} →
  clock-irrel A → clock-irrel (Path A x y)
path-clock-irrel {A = A} {x = x} {y = y} H =
  iso-appk0→clk-irrel (isoFun→isIso (∀k-path {x = x} {y = y} H))




--------------------------------------------------------------------------------


-- Lifting inside a Π type is equal to lifting outside the Π
--
-- It's not enough to set j = ℓ3 in the RHS.
-- This would typecheck, but is not sufficient for use in bool2ty-eq.
-- There, it is crucial that j is ℓ-max ℓ1 ℓ3, not just ℓ3.
lift-Π-eq : ∀ {ℓ1 ℓ2 ℓ3 : Level} → (X : Type ℓ1) {A : X → Type ℓ2} →
  ((x : X) → Lift {i = ℓ2} {j = ℓ3} (A x)) ≡
  Lift {i = ℓ-max ℓ1 ℓ2} {j = ℓ-max ℓ1 ℓ3} ((x : X) → A x)
lift-Π-eq X = isoToPath
  (_ Iso⟨ codomainIsoDep (λ x → invIso LiftIso) ⟩
   _ Iso⟨ LiftIso ⟩
   _ ∎Iso)

testing : ∀ {ℓ ℓ' ℓ'' : Level} (X : Type ℓ) {A : X → Type ℓ'} →
  _≡_ {ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')}
      {Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')}
      ((x : X) → Lift {ℓ'} {ℓ''} (A x))
      (Lift {ℓ-max ℓ ℓ'} {ℓ-max ℓ ℓ''} ((x : X) → A x))
testing X = isoToPath
  (_ Iso⟨ codomainIsoDep (λ x → invIso LiftIso) ⟩
   _ Iso⟨ LiftIso ⟩
   _ ∎Iso)

-- Auxiliary deifnition used for the iso between ⊎ and Σ Bool.
bool2ty : {ℓ ℓ' : Level} -> Type ℓ -> Type ℓ' -> Bool -> Type (ℓ-max ℓ ℓ')
bool2ty {ℓ' = ℓ'} A B true = Lift {j = ℓ'} A
bool2ty {ℓ = ℓ} A B false = Lift {j = ℓ} B

bool2ty-eq : ∀ {ℓ ℓ' ℓ'' : Level} → {X : Type ℓ} {A : X -> Type ℓ'} {B : X -> Type ℓ''} ->
  (b : Bool) ->
  (∀ (x : X) -> bool2ty (A x) (B x) b) ≡
  bool2ty (∀ x -> A x) (∀ x -> B x) b
bool2ty-eq {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} {X = X} {A = A} {B = B} true =
  lift-Π-eq {ℓ1 = ℓ} {ℓ2 = ℓ'}  {ℓ3 = ℓ''} X {A = A}
  
bool2ty-eq {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} {X = X} {A = A} {B = B} false =
  lift-Π-eq {ℓ1 = ℓ} {ℓ2 = ℓ''} {ℓ3 = ℓ'}  X {A = B}

bool2ty-A-A : (A : Type ℓ) (b : Bool) -> bool2ty A A b ≡ Lift {j = ℓ} A
bool2ty-A-A A true = refl
bool2ty-A-A A false = refl


Iso-⊎-ΣBool : {A : Type ℓ} {B : Type ℓ'} -> Iso (A ⊎ B) (Σ Bool (λ b -> bool2ty A B b))
Iso-⊎-ΣBool {A = A} {B = B} = iso to inv sec retr
  where
    to : A ⊎ B → Σ Bool (λ b -> bool2ty A B b)
    to (inl a) = true , lift a
    to (inr b) = false , lift b

    inv : Σ Bool (bool2ty A B) → A ⊎ B
    inv (true , a) = inl (lower a)
    inv (false , b) = inr (lower b)

    sec : section to inv
    sec (true , a) = refl
    sec (false , b) = refl

    retr : retract to inv
    retr (inl a) = refl
    retr (inr b) = refl


∀clock-Σ : {A : Type} -> {B : A -> Clock -> Type} ->
    clock-irrel A ->
    (∀ (k : Clock) -> Σ A (λ a -> B a k)) ->
    Σ A (λ a -> ∀ (k : Clock) -> B a k)
∀clock-Σ {A} {B} H-clk-irrel p =
    let a = fst (p k0) in
      a , (λ k -> transport
                   (λ i → B (H-clk-irrel (fst ∘ p) k k0 i) k)
                   (snd (p k)))
  -- NTS:  B (fst (p k)) k ≡ B (fst (p k0)) k
  -- i.e. essentially need to show that fst (p k) ≡ fst (p k0)
  -- This follows from clock irrelevance for A, with M = fst ∘ p of type Clock -> A




Dist-Pi-Sigma : {S : Type} -> {A : S -> Type} -> {B : (s : S) -> A s -> Type} ->
  Iso (∀ (s : S) -> (Σ[ x ∈ A s ] B s x))
      (Σ[ x ∈ (∀ s -> A s) ] ( ∀ s -> B s (x s) ))
Dist-Pi-Sigma = Σ-Π-Iso



-- Clock quantification distributes over products.
Iso-∀clock-× : {A : Clock → Type ℓ} {B : Clock → Type ℓ'} →
  Iso (∀ k → A k × B k) ((∀ k → A k) × (∀ k → B k))
Iso.fun Iso-∀clock-× f = (λ k → f k .fst) , (λ k → f k .snd)
Iso.inv Iso-∀clock-× (f , g) = λ k → f k , g k
Iso.rightInv Iso-∀clock-× (f , g) = refl
Iso.leftInv Iso-∀clock-× f = refl



-- Clock quantification distributes over sigma types.
-- This is simply an instance of the usual distributivity
-- of pi-types over sigma types.
∀k-Σ : {A : Clock → Type ℓ} → {B : (k : Clock) → A k → Type ℓ'} →
  Iso
    (∀ (k : Clock) → Σ (A k) (λ a → B k a))
    (Σ (∀ k → A k) (λ f → ∀ k → B k (f k)))
∀k-Σ {A = A} {B = B} = Σ-Π-Iso {A = Clock} {B = A} {C = B}


-- Special case where the first type in the sigma is
-- clock-irrelevant.
Iso-∀clock-Σ : {A : Type ℓ} -> {B : A -> Clock -> Type ℓ'} ->
  clock-irrel A ->
  Iso
    (∀ (k : Clock) -> Σ A (λ a -> B a k))
    (Σ A (λ a -> ∀ (k : Clock) -> B a k))
Iso-∀clock-Σ {A = A} {B = B} H-clk-irrel =
  (∀ (k : Clock) -> Σ A (λ a -> B a k))
     Iso⟨ Σ-Π-Iso {A = Clock} {B = λ k -> A} {C = λ k a -> B a k} ⟩
     
  (Σ ((k : Clock) → A) (λ f → (k : Clock) → B (f k) k))
     Iso⟨ ( Σ-cong-iso-snd (λ f → codomainIsoDep (λ k → Eq-Iso (λ i → B (H-clk-irrel f k k0 i) k)))) ⟩

  (Σ ((k : Clock) → A) (λ f → (k : Clock) → B (f k0) k))
     Iso⟨ Σ-cong-iso-fst {B = λ a -> ∀ k' -> B a k'} (Iso-∀kA-A H-clk-irrel) ⟩
     
  (Σ A (λ a -> ∀ (k : Clock) -> B a k)) ∎Iso

{- Note:
          Σ-cong-iso-fst
            : {A.ℓ : Level} {A : Type A.ℓ} {B..1 : Level} {A' : Type B..1}
              {B.ℓ : Level} {B : A' → Type B.ℓ} (isom : Iso A A') →
              Iso (Σ A (B ∘ Iso.fun isom)) (Σ A' B)

    In this case, the isomorphism function associated with Iso-∀kA-A
    takes f : (∀ (k : Clock) -> A) to A by applying f to k0.
    This is why we need the intermediate step of transforming B (f k) k
    into B (f k0) k.

-}


-- Action of the above isomorphism
Iso-∀clock-Σ-fun : {A : Type ℓ} {B : A -> Clock -> Type ℓ'} ->
  (H : clock-irrel A) ->
  (f : (k : Clock) -> Σ A (λ a -> B a k)) ->
  Iso.fun (Iso-∀clock-Σ {A = A} {B = B} H) f ≡ (fst (f k0) , λ k -> {!f k .snd!})
Iso-∀clock-Σ-fun {A = A} {B = B} H f = ΣPathP (refl , (funExt (λ k -> {!!} ∙ {!!})))


-- Clock quantification distributes over coproducts.
Iso-Π-⊎-clk : {ℓ ℓ' : Level} {A : Clock -> Type ℓ} {B : Clock -> Type ℓ'} ->
  Iso
    ((k : Clock) -> (A k ⊎ B k))
    (((k : Clock) -> A k) ⊎ ((k : Clock) -> B k))
Iso-Π-⊎-clk {A = A} {B = B} =
  (∀ (k : Clock) -> (A k ⊎ B k))
    Iso⟨ codomainIsoDep (λ k -> Iso-⊎-ΣBool) ⟩
  (∀ (k : Clock) -> Σ[ b ∈ Bool ] bool2ty (A k) (B k) b )
    Iso⟨ Iso-∀clock-Σ bool-clock-irrel ⟩
  (Σ[ b ∈ Bool ] ∀ k -> bool2ty (A k) (B k) b)
    Iso⟨ Σ-cong-iso-snd (λ b → Eq-Iso (bool2ty-eq b)) ⟩
    --  (cong (Iso ((x : Clock) → bool2ty (A x) (B x) b)) (bool2ty-eq b))
  (Σ[ b ∈ Bool ] bool2ty (∀ k -> A k) (∀ k -> B k) b)
    Iso⟨ invIso Iso-⊎-ΣBool ⟩
  (∀ k -> A k) ⊎ (∀ k -> B k) ∎Iso

-- Action of the above isomorphism
Iso-Π-⊎-clk-fun : {A B : Clock -> Type} -> {f : (k : Clock) -> (A k ⊎ B k) } ->
  (H : ∀ k -> Σ[ a ∈ A k ] f k ≡ inl a) ->
  Iso.fun Iso-Π-⊎-clk f ≡ inl λ k -> H k .fst
Iso-Π-⊎-clk-fun {A} {B} {f} H = {!!}

Iso-Π-⊎-clk-inv-inl : {A B : Clock -> Type} ->
  {f : (k : Clock) → A k} ->
  Iso.inv (Iso-Π-⊎-clk {B = B}) (inl f) ≡ λ k -> inl (f k)
Iso-Π-⊎-clk-inv-inl {A = A} {B = B} {f = f} = funExt (λ k → cong inl {!!})
-- (s : ((k : Clock) → A k) ⊎ ((k : Clock) → B k)) ->

-- transport p a = transp (λ i → p i) i0 a
--
-- transp (λ i → A (transp (λ j → Clock) i k)) i0 (transp (λ i → A (transp (λ j → Clock) i k)) i0 (f k))

-- transport (λ i → A (transp (λ j → Clock) i k))

test :  {A B : Clock -> Type ℓ} → (((k : Clock) -> A k) ⊎ ((k : Clock) -> B k)) → ((k : Clock) -> (A k ⊎ B k))
test (inl f) k = inl (f k)
test (inr g) k = inr (g k)

test' :  {A B : Clock -> Type ℓ} → ((k : Clock) -> (A k ⊎ B k)) → (((k : Clock) -> A k) ⊎ ((k : Clock) -> B k))
test' {A = A} {B = B} f = aux (f k0)
  where
    aux : A k0 ⊎ B k0 → _
    aux (inl a) = inl (λ k → {!!})
    aux (inr b) = inr (λ k → {!!})
