{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Lift (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty hiding (rec)

open import Common.Common

private
  variable
    l : Level
    A B : Set l
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A


  -- Lift monad

data L℧ (X : Set) : Set where
  η : X → L℧ X
  ℧ : L℧ X
  θ : ▹ (L℧ X) → L℧ X


-- Delay function
δ : {X : Type} -> L℧ X -> L℧ X
δ = θ ∘ next

-- Similar to caseNat,
-- defined at https://agda.github.io/cubical/Cubical.Data.Nat.Base.html#487
caseL℧ : {X : Set} -> {ℓ : Level} -> {A : Type ℓ} ->
  (aη a℧ aθ : A) → (L℧ X) → A
caseL℧ aη a℧ aθ (η x) = aη
caseL℧ aη a℧ aθ ℧ = a℧
caseL℧ a0 a℧ aθ (θ lx~) = aθ

-- Similar to znots and snotz, defined at
-- https://agda.github.io/cubical/Cubical.Data.Nat.Properties.html
℧≠θ : {X : Set} -> {lx~ : ▹ (L℧ X)} -> ¬ (℧ ≡ θ lx~)
℧≠θ {X} {lx~} eq = subst (caseL℧ X (L℧ X) ⊥) eq ℧

θ≠℧ : {X : Set} -> {lx~ : ▹ (L℧ X)} -> ¬ (θ lx~ ≡ ℧)
θ≠℧ {X} {lx~} eq = subst (caseL℧ X ⊥ (L℧ X)) eq (θ lx~)


-- TODO: Does this make sense?
pred : {X : Set} -> (lx : L℧ X) -> ▹ (L℧ X)
pred (η x) = next ℧
pred ℧ = next ℧
pred (θ lx~) = lx~

pred-def : {X : Set} -> (def : ▹ (L℧ X)) -> (lx : L℧ X) -> ▹ (L℧ X)
pred-def def (η x) = def
pred-def def ℧ = def
pred-def def (θ lx~) = lx~


-- TODO: This uses the pred function above, and I'm not sure whether that
-- function makes sense.
inj-θ : {X : Set} -> (lx~ ly~ : ▹ (L℧ X)) ->
  θ lx~ ≡ θ ly~ ->
  ▸ (λ t -> lx~ t ≡ ly~ t)
inj-θ lx~ ly~ H = let lx~≡ly~ = cong pred H in
  λ t i → lx~≡ly~ i t


-- Monadic structure

ret : {X : Set} -> X -> L℧ X
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

