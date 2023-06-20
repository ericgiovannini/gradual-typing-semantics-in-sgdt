{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Lift (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Transport

open import Common.Common
open import Common.LaterProperties

private
  variable
    ℓ ℓ' : Level
    A B : Set ℓ
private
  ▹_ : Set ℓ → Set ℓ
  ▹_ A = ▹_,_ k A


-- Lift + Error monad
data L℧ (X : Type ℓ) : Type ℓ where
  η : X → L℧ X
  ℧ : L℧ X
  θ : ▹ (L℧ X) → L℧ X

-- Lift monad (no error)
data L (X : Type ℓ) : Type ℓ where
  η : X -> L X
  θ : ▹ (L X) -> L X

-- Delay function
δ : {X : Type ℓ} -> L℧ X -> L℧ X
δ = L℧.θ ∘ (next {k = k})


L℧→sum : {X : Type ℓ} -> L℧ X → (X ⊎ ⊤) ⊎ (▹ L℧ X)
L℧→sum (η x) = inl (inl x)
L℧→sum ℧ = inl (inr tt)
L℧→sum (θ lx~) = inr lx~

sum→L℧ : {X : Type ℓ} -> (X ⊎ ⊤) ⊎ (▹ L℧ X) -> L℧ X
sum→L℧ (inl (inl x)) = η x
sum→L℧ (inl (inr tt)) = ℧
sum→L℧ (inr lx~) = θ lx~

L℧-iso : {X : Type ℓ} -> Iso (L℧ X) ((X ⊎ ⊤) ⊎ (▹ (L℧ X)))
L℧-iso {X = X} = iso L℧→sum sum→L℧ sec retr
  where
   
    sec : section L℧→sum sum→L℧
    sec (inl (inl x)) = refl
    sec (inl (inr tt)) = refl
    sec (inr lx~) = refl

    retr : retract L℧→sum sum→L℧
    retr (η x) = refl
    retr ℧ = refl
    retr (θ x) = refl

-- isSet for Lift
isSetL℧ : {X : Type ℓ} -> isSet X -> isSet (L℧ X)
isSetL℧ {X = X} isSetX = fix isSetL℧'
  where
    isSetL℧' : ▹ (isSet (L℧ X)) -> isSet (L℧ X)
    isSetL℧' IH = isSetRetract L℧→sum sum→L℧ (Iso.leftInv L℧-iso)
      (isSet⊎ (isSet⊎ isSetX isSetUnit) (isSet▹ IH))



Iso-L : {X : Type ℓ} -> Iso (L X) (X ⊎ (▹ (L X)))
Iso-L {X = X} = iso to inv sec retr
  where
    to : L X → X ⊎ (▹ L X)
    to (η x) = inl x
    to (θ l~) = inr l~

    inv : X ⊎ (▹ L X) → L X
    inv (inl x) = η x
    inv (inr l~) = θ l~

    sec : section to inv
    sec (inl x) = refl
    sec (inr l~) = refl

    retr : retract to inv
    retr (η x) = refl
    retr (θ l~) = refl

L-unfold : {X : Type ℓ} -> L X ≡ X ⊎ (▹ (L X))
L-unfold = isoToPath Iso-L


-- Defining L using a guarded fixpoint
L-fix : Type ℓ -> Type ℓ
L-fix X = fix {k} λ L' -> X ⊎ (▸ λ t -> L' t)

-- L-fixpoint-iso : {X : Type ℓ} -> Iso (L-fixpoint X) 
L-fix-unfold : {X : Type ℓ} -> L-fix X ≡ (X ⊎ (▹ (L-fix X)))
L-fix-unfold = fix-eq _


L-fix-eq' : {X : Type ℓ} -> ▸ (λ t -> (L-fix X ≡ L X)) -> L-fix X ≡ L X
L-fix-eq' {X = X} IH = L-fix X ≡⟨ L-fix-unfold ⟩
  ((X ⊎ (▹ (L-fix X)))) ≡⟨ (λ i -> X ⊎ (▸ λ t -> IH t i)) ⟩
  ((X ⊎ (▹ (L X)))) ≡⟨ sym L-unfold ⟩
  L X ∎

-- Note: ▸ (λ t -> L-fix X ≡ L X) is equivalent to ▸ (next (L-fix X ≡ L X))
-- which is equivalent to ▹ (L-fix X ≡ L X)

-- IH : ▸ (λ t' → L-fix X ≡ L X)  a.k.a. ▹ (L-fix X ≡ L X)
-- So λ i -> X ⊎ (▸ λ t -> IH t i) has type
-- (X ⊎ (▸ λ t -> L-fix X)) ≡ (X ⊎ (▸ λ t -> L X)) i.e.
-- (X ⊎ (▹ L-fix X)) ≡ (X ⊎ (▹ L X))

L-fix-eq : {X : Type ℓ} -> L-fix X ≡ L X
L-fix-eq = fix L-fix-eq'

L-fix-iso : {X : Type ℓ} -> Iso (L-fix X) (L X)
L-fix-iso = pathToIso L-fix-eq




    

{-
Iso-L-fix : {X : Type ℓ} -> Iso (L-fix X) (L X)
Iso-L-fix {X = X} = iso to inv sec {!!}
  where
    to' : ▹ ((X ⊎ (▹ (L-fix X))) -> L X) -> (X ⊎ (▹ (L-fix X))) -> L X
    to' _   (inl x) = η x
    to' rec (inr l~) = θ λ t -> rec t (inr l~)

    to : L-fix X -> L X
    to lx = fix to' (transport L-fix-unfold lx)

    inv : L X -> L-fix X
    inv' : L X -> (X ⊎ (▹ (L-fix X)))

    inv lx = transport (sym L-fix-unfold) (inv' lx)
    inv' (η x) = inl x
    inv' (θ l~) = inr (λ t -> inv (l~ t))

    sec' : ▹ ((y : L X) -> to' (next (fix to')) (inv' y) ≡ y) ->
              (y : L X) -> to' (next (fix to')) (inv' y) ≡ y
    sec' _ (η x) = refl
    sec' IH (θ l~) = {!!}

    sec : section to inv
    sec (η x) = {!!}
    sec (θ l~) = {!!}
-}
  





-- Similar to caseNat,
-- defined at https://agda.github.io/cubical/Cubical.Data.Nat.Base.html#487
caseL℧ : {X : Type ℓ} -> {A : Type ℓ'} -> (aη a℧ aθ : A) → L℧ X → A
caseL℧ aη a℧ aθ (η x) = aη
caseL℧ aη a℧ aθ ℧ = a℧
caseL℧ a0 a℧ aθ (θ lx~) = aθ


-- Similar to znots and snotz, defined at
-- https://agda.github.io/cubical/Cubical.Data.Nat.Properties.html
℧≠θ : {X : Type ℓ} -> {lx~ : ▹ (L℧ X)} -> ¬ (℧ ≡ θ lx~)
℧≠θ {X = X} {lx~ = lx~} eq =
  rec* (subst (caseL℧ X (L℧ X) ⊥*) eq ℧) -- subst (caseL℧ X (L℧ X) ⊥) eq ℧

η≠℧ : {X : Type ℓ} -> {x : X} -> ¬ (η x ≡ ℧)
η≠℧ {X = X} {x = x} eq =
  rec* (subst (caseL℧ X ⊥* ⊥*) eq x) -- subst (caseL℧ X ⊥ ⊥) eq x

η≠θ : {X : Type ℓ} -> {x : X} -> {lx~ : ▹ (L℧ X)} -> ¬ (L℧.η x ≡ θ lx~)
η≠θ {X = X} {x = x} {lx~ = lx~} eq =
  rec* (subst (caseL℧ X ⊥* ⊥*) eq x) -- subst (caseL℧ X ⊥ ⊥) eq x




-- TODO: Does this make sense?
pred : {X : Type ℓ} -> (lx : L℧ X) -> ▹ (L℧ X)
pred (η x) = next ℧
pred ℧ = next ℧
pred (θ lx~) = lx~

pred-def : {X : Type ℓ} -> (def : ▹ (L℧ X)) -> (lx : L℧ X) -> ▹ (L℧ X)
pred-def def (η x) = def
pred-def def ℧ = def
pred-def def (θ lx~) = lx~


-- TODO: This uses the pred function above, and I'm not sure whether that
-- function makes sense.
inj-θ : {X : Type ℓ} -> (lx~ ly~ : ▹ (L℧ X)) ->
  θ lx~ ≡ θ ly~ ->
  ▸ (λ t -> lx~ t ≡ ly~ t)
inj-θ lx~ ly~ H = let lx~≡ly~ = cong pred H in
  λ t i → lx~≡ly~ i t


-- Monadic structure

ret : {X : Type ℓ} -> X -> L℧ X
ret = η


ext' : (A -> L℧ B) -> ▹ (L℧ A -> L℧ B) -> L℧ A -> L℧ B
ext' f rec (η x) = f x
ext' f rec ℧ = ℧
ext' f rec (θ l-la) = θ (rec ⊛ l-la)

ext : (A -> L℧ B) -> L℧ A -> L℧ B
ext f = fix (ext' f)


bind : L℧ A -> (A -> L℧ B) -> L℧ B
bind {A} {B} la f = ext f la


unfold-ext : (f : A -> L℧ B) -> ext f ≡ ext' f (next (ext f))
unfold-ext f = fix-eq (ext' f)


ext-eta : ∀ (a : A) (f : A -> L℧ B) ->
  ext f (η a) ≡ f a
ext-eta a f =
  fix (ext' f) (ret a)            ≡⟨ (λ i → unfold-ext f i (ret a)) ⟩
  (ext' f) (next (ext f)) (ret a) ≡⟨ refl ⟩
  f a ∎

ext-err : (f : A -> L℧ B) ->
  bind ℧ f ≡ ℧
ext-err f =
  fix (ext' f) ℧            ≡⟨ (λ i → unfold-ext f i ℧) ⟩
  (ext' f) (next (ext f)) ℧ ≡⟨ refl ⟩
  ℧ ∎


ext-theta : (f : A -> L℧ B)
            (l : ▹ (L℧ A)) ->
            bind (θ l) f ≡ θ (ext f <$> l)
ext-theta f l =
  (fix (ext' f)) (θ l)            ≡⟨ (λ i → unfold-ext f i (θ l)) ⟩
  (ext' f) (next (ext f)) (θ l)   ≡⟨ refl ⟩
  θ (fix (ext' f) <$> l) ∎



monad-unit-l : ∀ (a : A) (f : A -> L℧ B) -> ext f (ret a) ≡ f a
monad-unit-l = ext-eta

monad-unit-r : (la : L℧ A) -> ext ret la ≡ la
monad-unit-r = fix lem
  where
    lem : ▹ ((la : L℧ A) -> ext ret la ≡ la) ->
          (la : L℧ A) -> ext ret la ≡ la
    lem IH (η x) = monad-unit-l x ret
    lem IH ℧ = ext-err ret
    lem IH (θ x) = fix (ext' ret) (θ x)
                     ≡⟨ ext-theta ret x ⟩
                   θ (fix (ext' ret) <$> x)
                     ≡⟨ refl ⟩
                   θ ((λ la -> ext ret la) <$> x)
                     ≡⟨ (λ i → θ λ t → IH t (x t) i) ⟩
                   θ (id <$> x)
                     ≡⟨ refl ⟩
                   θ x ∎


mapL : (A -> B) -> L℧ A -> L℧ B
mapL f la = bind la (λ a -> ret (f a))

mapL-eta : (f : A -> B) (a : A) ->
  mapL f (η a) ≡ η (f a)
mapL-eta f a = ext-eta a λ a → ret (f a)

mapL-theta : (f : A -> B) (la~ : ▹ (L℧ A)) ->
  mapL f (θ la~) ≡ θ (mapL f <$> la~)
mapL-theta f la~ = ext-theta (ret ∘ f) la~


mapL-id : (la : L℧ A) -> mapL id la ≡ la
mapL-id la = monad-unit-r la

