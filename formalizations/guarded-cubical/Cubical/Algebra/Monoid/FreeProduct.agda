-- {-# OPTIONS --safe #-}

{-# OPTIONS --allow-unsolved-metas #-}


module Cubical.Algebra.Monoid.FreeProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More

open import Cubical.Data.Sum
open import Cubical.Data.Sigma


private
  variable
    ℓ ℓ' ℓ'' : Level


open IsMonoidHom



-- Free monoid on two generators as a HIT, similar to
-- Cubical.HITs.FreeComMonoids.Base.html
data FreeMonoidProd (M : Monoid ℓ) (N : Monoid ℓ') : Type (ℓ-max ℓ ℓ') where

  ⟦_⟧₁ : ⟨ M ⟩ -> FreeMonoidProd M N
  ⟦_⟧₂ : ⟨ N ⟩ -> FreeMonoidProd M N

  ε         : FreeMonoidProd M N
  _·_       : FreeMonoidProd M N -> FreeMonoidProd M N -> FreeMonoidProd M N


  id₁ : ⟦ MonoidStr.ε (M .snd) ⟧₁ ≡ ε
  id₂ : ⟦ MonoidStr.ε (N .snd) ⟧₂ ≡ ε

  comp₁ : ∀ m m' -> ⟦ MonoidStr._·_ (M .snd) m m' ⟧₁ ≡ (⟦ m ⟧₁ · ⟦ m' ⟧₁)
  comp₂ : ∀ n n' -> ⟦ MonoidStr._·_ (N .snd) n n' ⟧₂ ≡ (⟦ n ⟧₂ · ⟦ n' ⟧₂)

  identityᵣ  : ∀ x → x · ε ≡ x
  identityₗ   :  ∀ x → ε · x ≡ x
  assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z

  trunc : isSet (FreeMonoidProd M N)


-- Maps out of the free product
module Elim {ℓ''} {M : Monoid ℓ} {N : Monoid ℓ'}
  {B : FreeMonoidProd M N -> Type ℓ''}
  (⟦_⟧₁* : (m : ⟨ M ⟩) -> B ⟦ m ⟧₁)
  (⟦_⟧₂* : (n : ⟨ N ⟩) -> B ⟦ n ⟧₂)
  (ε*    : B ε)
  (_·*_ : ∀ {x y} -> B x -> B y -> B (x · y))

  (id₁*  : PathP (λ i -> B (id₁ i)) ⟦ MonoidStr.ε (M .snd) ⟧₁* ε*)
  (id₂*  : PathP (λ i -> B (id₂ i)) ⟦ MonoidStr.ε (N .snd) ⟧₂* ε*)
  (comp₁* : ∀ m m' -> PathP (λ i -> B (comp₁ m m' i))
    ⟦ MonoidStr._·_ (M .snd) m m' ⟧₁* (⟦ m ⟧₁* ·* ⟦ m' ⟧₁*))
  (comp₂* : ∀ n n' -> PathP (λ i -> B (comp₂ n n' i))
    ⟦ MonoidStr._·_ (N .snd) n n' ⟧₂* (⟦ n ⟧₂* ·* ⟦ n' ⟧₂*))
  

  (identityᵣ* : ∀ {x} -> (xs : B x) ->
    PathP (λ i -> B (identityᵣ x i)) (xs ·* ε*) xs)
  (identityₗ* : ∀ {x} -> (xs : B x) ->
    PathP (λ i -> B (identityₗ x i)) (ε* ·* xs) xs)
  (assoc* : ∀ {x y z} -> (xs : B x) (ys : B y) (zs : B z) ->
    PathP (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs)) ((xs ·* ys) ·* zs))
  (trunc* : ∀ xs -> isSet (B xs))
  
  where

  f : (x : FreeMonoidProd M N) -> B x
  f ⟦ m ⟧₁ = ⟦ m ⟧₁*
  f ⟦ n ⟧₂ = ⟦ n ⟧₂*
  f ε = ε*
  f (x · y) = f x ·* f y
  f (id₁ i) = id₁* i
  f (id₂ i) = id₂* i
  f (comp₁ m m' i) = comp₁* m m' i
  f (comp₂ n n' i) = comp₂* n n' i
  f (identityᵣ x i) = identityᵣ* (f x) i
  f (identityₗ x i) = identityₗ* (f x) i
  f (assoc x y z i) = assoc* (f x) (f y) (f z) i
  f (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2 trunc*
    (f x) (f y) (cong f p) (cong f q) (trunc x y p q) i j
  

module Rec {ℓ''} {M : Monoid ℓ} {N : Monoid ℓ'}
  {B : Type ℓ''}
  (⟦_⟧₁* : (m : ⟨ M ⟩) -> B)
  (⟦_⟧₂* : (n : ⟨ N ⟩) -> B)
  (ε*    : B)
  (_·*_  : B -> B -> B)

  (id₁*  :  ⟦ MonoidStr.ε (M .snd) ⟧₁* ≡ ε*)
  (id₂*  :  ⟦ MonoidStr.ε (N .snd) ⟧₂* ≡ ε*)
  (comp₁* : ∀ m m' ->
    ⟦ MonoidStr._·_ (M .snd) m m' ⟧₁* ≡ (⟦ m ⟧₁* ·* ⟦ m' ⟧₁*))
  (comp₂* : ∀ n n' ->
    ⟦ MonoidStr._·_ (N .snd) n n' ⟧₂* ≡ (⟦ n ⟧₂* ·* ⟦ n' ⟧₂*))
  

  (identityᵣ* : (x : B) -> (x ·* ε*) ≡ x)
  (identityₗ* : (x : B) -> (ε* ·* x) ≡ x)
  (assoc* : ∀ (x y z : B) -> x ·* (y ·* z) ≡ (x ·* y) ·* z)
  (trunc* : isSet B) where

  f : FreeMonoidProd M N -> B
  f = Elim.f
    ⟦_⟧₁* ⟦_⟧₂* ε* _·*_ id₁* id₂* comp₁* comp₂*
    identityᵣ* identityₗ* assoc* (λ _ -> trunc*)

  
_⊕_ : Monoid ℓ -> Monoid ℓ' -> Monoid (ℓ-max ℓ ℓ')
M ⊕ N = makeMonoid {M = FreeMonoidProd M N} ε _·_ trunc assoc identityᵣ identityₗ



-- isSetMonoidHom : (M : Monoid ℓ) (N : Monoid ℓ') → isSet (MonoidHom M N)
-- isSetMonoidHom M N = {!!}


-- Injecting a pair of elements into the free product

pair : {M : Monoid ℓ} {N : Monoid ℓ'} → ⟨ M ⟩ → ⟨ N ⟩ → ⟨ M ⊕ N ⟩
pair m n = ⟦ m ⟧₁ · ⟦ n ⟧₂

-- Universal property of the free product

module _ {M : Monoid ℓ} {N : Monoid ℓ'} where

  open MonoidStr

  i₁ : MonoidHom M (M ⊕ N)
  i₁ = ⟦_⟧₁ , (monoidequiv id₁ comp₁)

  i₂ : MonoidHom N (M ⊕ N)
  i₂ = ⟦_⟧₂ , (monoidequiv id₂ comp₂)

  case : (P : Monoid ℓ'') (f : MonoidHom M P) (g : MonoidHom N P) ->
    isContr (Σ[ h ∈ MonoidHom (M ⊕ N) P ] (f ≡ h ∘hom i₁) × (g ≡ h ∘hom i₂))
  case P f g .fst .fst .fst =
    Rec.f (f .fst) (g .fst) P.ε P._·_ (f .snd .presε) (g .snd .presε)
          (f .snd .pres·) (g .snd .pres·) P.·IdR P.·IdL P.·Assoc P.is-set
    where
      module P = MonoidStr (P .snd)
  case P f g .fst .fst .snd = monoidequiv refl (λ x y -> refl)
  case P f g .fst .snd = (eqMonoidHom _ _ refl) , (eqMonoidHom _ _ refl)
  case P f g .snd (h , eq1 , eq2) =
    ΣPathPProp
      (λ h' → isProp× (isSetMonoidHom M P f (h' ∘hom i₁))
                       {!!})
      (eqMonoidHom _ _ (funExt aux))
        where
          aux : (x : ⟨ M ⊕ N ⟩) → _
          aux x = {!!} -- can use the eliminator!

  [_,hom_] : {P : Monoid ℓ''} (f : MonoidHom M P) (g : MonoidHom N P) ->
    MonoidHom (M ⊕ N) P
  [_,hom_] {P = P} f g = fst (fst (case P f g))


-- Eliminating from M ⊕ N into a type A parameterized by elements of
-- M ⊕ N and elements of an arbitrary monoid P.
module Elim2
  {ℓM ℓN ℓP ℓA : Level}
  (M : Monoid ℓM)
  (N : Monoid ℓN)
  (P : Monoid ℓP)
  (A : ⟨ M ⊕ N ⟩ → ⟨ P ⟩ → Type ℓA)
  (AProp : ∀ {x y} → isProp (A x y))
  (f : MonoidHom M P) (g : MonoidHom N P)
  -- (isMon : MonoidStr (Σ[ x ∈ ⟨ M ⊕ N ⟩ ] A x ([ f ,hom g ] .fst x)))
  where

  module M = MonoidStr (M .snd)
  module N = MonoidStr (N .snd)

  hom : MonoidHom (M ⊕ N) P
  hom =  [ f ,hom g ]

  h = hom .fst

   -- e.g. A x y = Sq c c (ptbA x) (ptbA' y)
   -- Σ x . A x (push x) = Σ x . Sq c c (ptbA x) (ptbA' (push x))
  
  --module Mon = MonoidStr isMon

 --   (_·*_ : ∀ {x y} -> B x -> B y -> B (x · y))
  elim2 : (⟦_⟧₁* : (m : ⟨ M ⟩) → A ⟦ m ⟧₁ (h ⟦ m ⟧₁)) →
          (⟦_⟧₂* : (n : ⟨ N ⟩) → A ⟦ n ⟧₂ (h ⟦ n ⟧₂)) →
          (ε* : A ε (h ε)) →
          (_·*_ : {x y : ⟨ M ⊕ N ⟩} → A x (h x) → A y (h y) → A (x · y) (h (x · y))) →
          (∀ (x : ⟨ M ⊕ N ⟩) → A x (h x))
  elim2 ⟦_⟧₁* ⟦_⟧₂* ε* _·*_ = Elim.f {B = λ x → A x (h x)}
          (λ m → ⟦ m ⟧₁*)
          (λ n → ⟦ n ⟧₂*)
          ε*
          _·*_
          (isProp→PathP (λ i → AProp) ⟦ M.ε ⟧₁* ε*)
          (toPathP (AProp (transport (λ i → A (id₂ i) (h (id₂ i))) _) ε*))
          (λ m m' → toPathP (AProp _ _))
          (λ n n' → toPathP (AProp _ _))
          (λ xs → toPathP (AProp _ _))
          (λ xs → toPathP (AProp _ _))
          (λ xs ys zx → toPathP (AProp _ _))
          (λ _ → isProp→isSet AProp)



          -- Elim.f {B = λ x → Σ[ h ∈ MonoidHom (M ⊕ N) P ] (∀ (x : ⟨ M ⊕ N ⟩) → A (h .fst x))}
          -- (λ m → {!!} , {!!})
          -- {!!}
          -- {!!}
          -- {!!}
          -- {!!}
          -- {!!}
          -- {!!}
          -- {!!}
          -- {!!}
          -- {!!}
          -- {!!}
          -- {!!}
          -- {!!}
    -- Σ[ h ∈ MonoidHom (M ⊕ N) P ] (∀ (x : ⟨ M ⊕ N ⟩) → A (h .fst x))
  
  
 
