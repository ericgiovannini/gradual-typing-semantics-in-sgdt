{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Common
open import Common.Later

module Semantics.Concrete.GuardedLift (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma

open import Common.Common
open import Common.LaterProperties

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ
private
  ▹_ : Set ℓ → Set ℓ
  ▹_ A = ▹_,_ k A


-- The guarded lift monad.
data L (X : Type ℓ) : Type ℓ where
  η : X -> L X
  θ : ▹ (L X) -> L X


δ : {X : Type ℓ} -> L X -> L X
δ = L.θ ∘ next


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

isSetL : {X : Type ℓ} → isSet X → isSet (L X)
isSetL {X = X} isSetX = fix isSetL'
  where
    isSetL' : ▹ (isSet (L X)) → isSet (L X)
    isSetL' IH = isSetRetract (Iso.fun Iso-L ) (Iso.inv Iso-L) (Iso.leftInv Iso-L)
      (isSet⊎ isSetX (isSet▹ IH))


L-unfold : {X : Type ℓ} -> L X ≡ X ⊎ (▹ (L X))
L-unfold = isoToPath Iso-L

L-unfold-η : {X : Type ℓ} (x : X) ->
  transport L-unfold (η x) ≡ inl x
L-unfold-η x = cong inl (transportRefl x)

L-unfold-θ : {X : Type ℓ} (l~ : ▹ (L X)) ->
  transport L-unfold (θ l~) ≡ inr l~
L-unfold-θ l~ = cong inr (transportRefl l~)


-- Defining L using a guarded fixpoint
L-fix : Type ℓ -> Type ℓ
L-fix X = fix {k} λ L' -> X ⊎ (▸ λ t -> L' t)

-- L-fixpoint-iso : {X : Type ℓ} -> Iso (L-fixpoint X) 
L-fix-unfold : {X : Type ℓ} -> L-fix X ≡ (X ⊎ (▹ (L-fix X)))
L-fix-unfold = fix-eq _


-- Note: ▸ (λ t -> L-fix X ≡ L X) is equivalent to ▸ (next (L-fix X ≡ L X))
-- which is equivalent to ▹ (L-fix X ≡ L X)

-- IH : ▸ (λ t' → L-fix X ≡ L X)  a.k.a. ▹ (L-fix X ≡ L X)
-- So λ i -> X ⊎ (▸ λ t -> IH t i) has type
-- (X ⊎ (▸ λ t -> L-fix X)) ≡ (X ⊎ (▸ λ t -> L X)) i.e.
-- (X ⊎ (▹ L-fix X)) ≡ (X ⊎ (▹ L X))

L-fix-eq' : {X : Type ℓ} ->  ▸ (λ t -> (L-fix X ≡ L X)) -> L-fix X ≡ L X
L-fix-eq' {X = X} IH =
  L-fix-unfold ∙
  (λ i -> X ⊎ (▸ λ t → IH t i)) ∙
  sym L-unfold
  

L-fix-eq : {X : Type ℓ} -> L-fix X ≡ L X
L-fix-eq = fix L-fix-eq'

L-fix-iso : {X : Type ℓ} -> Iso (L-fix X) (L X)
L-fix-iso = pathToIso L-fix-eq

-- Action of the above isomorphism
L-fix-iso-η : {X : Type ℓ} (x : X) ->
  transport L-fix-unfold (transport⁻ L-fix-eq (η x)) ≡ inl x
L-fix-iso-η {X = X} x =
  let eq = (λ i -> X ⊎ (▸_ {k = k} λ t → L-fix-eq {X = X} i)) in 
  transport L-fix-unfold (transport⁻ L-fix-eq (η x))
  
    ≡⟨ (λ i -> transport L-fix-unfold (transport⁻ (fix-eq L-fix-eq' i) (η x))) ⟩
    
  transport L-fix-unfold (transport⁻ (L-fix-eq' (next L-fix-eq)) (η x))
  
    ≡⟨ refl ⟩
    
  transport L-fix-unfold
    (transport⁻ (L-fix-unfold ∙ eq ∙ sym L-unfold) (η x))
    
    ≡⟨ ((λ i -> transport L-fix-unfold {!!})) ⟩
    
  transport L-fix-unfold
    ((transport⁻ L-fix-unfold ∘
      transport⁻ eq ∘
      transport⁻ (sym L-unfold)) (η x))
      
    ≡⟨ transportTransport⁻ L-fix-unfold _ ⟩
    
  (transport⁻ eq ∘ transport⁻ (sym L-unfold)) (η x)
  
    ≡⟨ sym (transportComposite L-unfold (sym eq) (η x)) ⟩
    
  (transport⁻ (eq ∙ (sym L-unfold))) (η x)
  
    ≡⟨ refl ⟩
    
  (transport (L-unfold ∙ sym eq)) (η x)
  
    ≡⟨ transportComposite L-unfold (sym eq) (η x) ⟩
    
  ((transport (sym eq)) ∘ (transport L-unfold)) (η x)
  
    ≡⟨ {!!} ⟩
    
  (transport (sym (λ i -> X ⊎ (▸_ {k = k} λ t → L-fix-eq {X = X} i)))) (inl x)
  
    ≡⟨ {!!} ⟩
    
  inl x ∎


-- Similar to caseNat,
-- defined at https://agda.github.io/cubical/Cubical.Data.Nat.Base.html#487
caseL : {X : Type ℓ} -> {A : Type ℓ'} -> (aη aθ : A) → L X → A
caseL aη aθ (η x) = aη
caseL a0 aθ (θ lx~) = aθ

-- Similar to znots and snotz, defined at
-- https://agda.github.io/cubical/Cubical.Data.Nat.Properties.html
Lη≠Lθ : {X : Type ℓ} -> {x : X} -> {lx~ : ▹ (L X)} -> ¬ (L.η x ≡ θ lx~)
Lη≠Lθ {X = X} {x = x} {lx~ = lx~} eq =
  rec* (subst (caseL X ⊥*) eq x) -- subst (caseL℧ X ⊥ ⊥) eq x



-- Injectivity results

ηL-inv : {X : Type ℓ} -> L X -> X -> X
ηL-inv (η x) y = x
ηL-inv (θ lx~) y = y

θL-inv : {X : Type ℓ} -> L X -> ▹ (L X)
θL-inv (η x) = next (η x)
θL-inv (θ lx~) = lx~


inj-ηL : {X : Type ℓ} (x y : X) ->
  L.η x ≡ L.η y ->
  x ≡ y
inj-ηL x y H = λ i -> ηL-inv (H i) x -- also works:  η-inv (H i) y

inj-θL : {X : Type ℓ} (lx~ ly~ : ▹ (L X)) ->
  L.θ lx~ ≡ L.θ ly~ ->
  ▸ (λ t -> lx~ t ≡ ly~ t)
inj-θL lx~ ly~ H = let lx~≡ly~ = cong θL-inv H in
  λ t i -> lx~≡ly~ i t

inj-θL' : {X : Type ℓ} (lx~ ly~ : ▹ (L X)) →
  L.θ lx~ ≡ L.θ ly~ →
  lx~ ≡ ly~
inj-θL' lx~ ly~ H = later-ext (λ t → inj-θL lx~ ly~ H t)





-----------------------
-- Monadic structure --
-----------------------

retL : {X : Type ℓ} -> X -> L X
retL = η

extL' : (A -> L B) -> ▹ (L A -> L B) -> L A -> L B
extL' f rec (η a) = f a
extL' f rec (θ la~) = θ (rec ⊛ la~)

extL : (A -> L B) -> L A -> L B
extL f = fix (extL' f)

bindL : L A -> (A -> L B) -> L B
bindL {A} {B} la f = extL f la

unfold-extL : (f : A -> L B) -> extL f ≡ extL' f (next (extL f))
unfold-extL f = fix-eq (extL' f)

extL-eta : ∀ (a : A) (f : A -> L B) ->
  extL f (η a) ≡ f a
extL-eta a f =
  fix (extL' f) (η a)            ≡⟨ (λ i → unfold-extL f i (η a)) ⟩
  (extL' f) (next (extL f)) (η a) ≡⟨ refl ⟩
  f a ∎


extL-theta : (f : A -> L B)
            (l : ▹ (L A)) ->
            bindL (θ l) f ≡ θ (extL f <$> l)
extL-theta f l = 
  (fix (extL' f)) (θ l)            ≡⟨ (λ i → unfold-extL f i (θ l)) ⟩
  (extL' f) (next (extL f)) (θ l)   ≡⟨ refl ⟩
  θ (fix (extL' f) <$> l) ∎ 

extL-delay : (f : A -> L B) (la : L A) (n : ℕ) ->
  extL f ((δ ^ n) la) ≡ (δ ^ n) (extL f la)
extL-delay f la zero = refl
extL-delay f la (suc n) =
  extL f (δ ((δ ^ n) la))
    ≡⟨ refl ⟩
  extL f (θ (next ((δ ^ n) la)))
    ≡⟨ extL-theta f _ ⟩
  θ (extL f <$> next ((δ ^ n) la))
    ≡⟨ refl ⟩
  θ (λ t -> extL f ((δ ^ n) la))
    ≡⟨ ((λ i -> θ λ t -> extL-delay f la n i)) ⟩
  δ ((δ ^ n) (extL f la)) ∎

