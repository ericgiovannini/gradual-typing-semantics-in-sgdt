{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Common.LaterProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path


open import Common.Later



-- Cubical.Foundations.GroupoidLaws
-- assoc : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
--  p ∙ q ∙ r ≡ (p ∙ q) ∙ r

-- rUnit : (p : x ≡ y) → p ≡ p ∙ refl
-- lUnit : (p : x ≡ y) → p ≡ refl ∙ p

-- lCancel : (p : x ≡ y) → p ⁻¹ ∙ p ≡ refl
-- rCancel : (p : x ≡ y) → p ∙ p ⁻¹ ≡ refl

-- Cubical.Foundations.Path
-- compPathl-cancel : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → p ∙ (sym p ∙ q) ≡ q
-- compPathr-cancel : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : z ≡ y) (q : x ≡ y) → (q ∙ sym p) ∙ p ≡ q

-- PathP≡doubleCompPathˡ : ∀ {A : Type ℓ} {w x y z : A} (p : w ≡ y) (q : w ≡ x) (r : y ≡ z) (s : x ≡ z)
--                        → (PathP (λ i → p i ≡ s i) q r) ≡ (p ⁻¹ ∙∙ q ∙∙ s ≡ r)

-- compPathL→PathP : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
--  → sym p ∙ r ∙ q ≡ s
--  → PathP (λ i → p i ≡ q i) r s

-- Cubical.Foundations.Prelude
--doubleCompPath≡compPath : {x y z w : A}
--    (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
--  → p ∙∙ q ∙∙ r ≡ p ∙ q ∙ r

path-x-f-next-x : {ℓ : Level} -> {k : Clock} {A : Type ℓ} -> {f : ▹ k , A -> A} ->
  isContr (Σ[ x ∈ A ] x ≡ f (next x) )
path-x-f-next-x {k = k} {A = A} {f = f} = (fix f , fix-eq f) , unique
  where
    unique : (y : Σ[ x ∈ A ] (x ≡ f (next x))) → (fix f , fix-eq f) ≡ y
    unique (h , p-h) = ΣPathP (q , eq)
      where
        q' = λ r ->      
          fix f ≡⟨ fix-eq f ⟩
          f (next (fix f)) ≡⟨ cong f (λ i -> λ t -> r t i) ⟩ -- or: ≡⟨ (λ i -> f (λ t -> r t i)) ⟩
          f (next h) ≡⟨ sym p-h ⟩
          h ∎

       -- r : ▹ (fix f ≡ h), so (λ i -> f (λ t -> r t i)) has type
       -- f (λ t -> fix f) ≡ f (λ t -> h) i.e.
       -- f (next (fix f)) ≡ f (next h)

        q : fix f ≡ h
        q = fix q'

        lem : sym (fix-eq f) ∙ (q' (next q)) ∙ p-h ≡ cong f (λ i -> λ t -> q i)
        lem =
          sym (fix-eq f) ∙ (q' (next q)) ∙ p-h                                       ≡⟨ {!!} ⟩
          sym (fix-eq f) ∙ (fix-eq f ∙ cong f (λ i -> λ t -> q i) ∙ sym p-h) ∙ p-h   ≡⟨ {!!} ⟩
          (sym (fix-eq f) ∙ fix-eq f) ∙ cong f (λ i -> λ t -> q i) ∙ (sym p-h ∙ p-h) ≡⟨ {!!} ⟩
          {!!} ≡⟨ {!!} ⟩
          {!!} ≡⟨ {!!} ⟩
          (cong f λ i -> λ t -> q i) ∎
         
        eq : PathP (λ i → q i ≡ f (next (q i))) (fix-eq f) p-h
        eq = transport (sym (PathP≡doubleCompPathˡ q (fix-eq f) p-h (cong f (λ i -> λ t -> q i))))
          (doubleCompPath≡compPath (sym q) (fix-eq f) (cong f (λ i -> λ t -> q i)) ∙ {!!})
        



-- The pair (dfix^k f, pfix^k f) is uniquely determined up to path
-- since it witnesses that dfix^k f is the fixed point of λ x. λ t. f x


fixpoints-unique : {!!}
fixpoints-unique = {!!}




isSet▹ : {k : Clock} {ℓ : Level} {X : Type ℓ} ->
  ▹ k , (isSet X) -> isSet (▹ k ,  X)
isSet▹ H x~ y~ p1 p2 i j t =
  H t (x~ t) (y~ t) (λ l -> p1 l t) (λ l -> p2 l t) i j

-- Dependent version
isSet▸ : {k : Clock} {ℓ : Level} {X : ▹ k , Type ℓ} ->
  ▸ (λ t -> isSet (X t)) -> isSet (▸ λ t -> X t)
isSet▸ H x~ y~ p1 p2 i j t = H t (x~ t) (y~ t) (λ l -> p1 l t) (λ l -> p2 l t) i j




-- Distributing clock quantification over arrow (dependent version)
∀k→ : {ℓ : Level} -> {X Y : Clock -> Type ℓ} ->
  (∀ (k : Clock) -> (X k -> Y k)) ->
  (∀ (k : Clock) -> X k) -> (∀ (k : Clock) -> Y k)
∀k→ f g k = f k (g k)

-- ∀ k distributes over functions where the domain is clock irrelevant
∀k-dist-fun' : {ℓ : Level} -> {X Y : Type ℓ} ->
  clock-irrel X ->
  Iso (∀ (k : Clock) -> (X -> Y)) (∀ (k : Clock) -> X -> ∀ (k : Clock) -> Y)
∀k-dist-fun' {X = X} {Y = Y} H-irrel = iso to inv {!!} {!!} 
  where
    to : ((k : Clock) (x : X) → Y) → (k : Clock) (x : X) → Clock → Y
    to f k x k' = f k x

    inv : (Clock → X → Clock → Y) → Clock → X → Y
    inv f k x = f k x k
    
    sec : section to inv
    sec f = funExt (λ k -> funExt λ x -> funExt (λ k' -> {!!}))

    retr : retract to inv
    retr f = {!!}


-- ∀ k distributes over functions where the domain is clock irrelevant
∀k-dist-fun : {ℓ : Level} -> {X Y : Type ℓ} ->
  clock-irrel X ->
  Iso (∀ (k : Clock) -> (X -> Y)) (X -> ∀ (k : Clock) -> Y)
∀k-dist-fun {X = X} {Y = Y} H-irrel = iso to inv sec retr
  where
    to : (Clock → X → Y) → (X → Clock → Y)
    to f x k = f k x

    inv : (X → Clock → Y) → (Clock → X → Y)
    inv f k x  = f x k

    sec : section to inv
    sec f = funExt (λ x -> funExt (λ k -> refl))

    retr : retract to inv
    retr f = funExt (λ k -> funExt λ x → refl)
