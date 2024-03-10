-- {-# OPTIONS --safe #-}

{-# OPTIONS --allow-unsolved-metas #-}


module Cubical.Algebra.Monoid.FreeCommProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.CommMonoid.Base
open import Cubical.Algebra.Monoid.Submonoid

open import Cubical.Data.Sum
open import Cubical.Data.Sigma

import Cubical.Algebra.Monoid.FreeProduct as FP
open FP using (_⋆_)


private
  variable
    ℓ ℓ' ℓ'' : Level


open IsMonoidHom



-- Free commutative monoid on two generators as a HIT, similar to
-- Cubical.HITs.FreeComMonoids.Base.html
data FreeCommMonoidProd (M : Monoid ℓ) (N : Monoid ℓ') : Type (ℓ-max ℓ ℓ') where

  ⟦_⟧₁ : ⟨ M ⟩ -> FreeCommMonoidProd M N
  ⟦_⟧₂ : ⟨ N ⟩ -> FreeCommMonoidProd M N

  ε         : FreeCommMonoidProd M N
  _·_       : FreeCommMonoidProd M N -> FreeCommMonoidProd M N -> FreeCommMonoidProd M N


  id₁ : ⟦ MonoidStr.ε (M .snd) ⟧₁ ≡ ε
  id₂ : ⟦ MonoidStr.ε (N .snd) ⟧₂ ≡ ε

  comp₁ : ∀ m m' -> ⟦ MonoidStr._·_ (M .snd) m m' ⟧₁ ≡ (⟦ m ⟧₁ · ⟦ m' ⟧₁)
  comp₂ : ∀ n n' -> ⟦ MonoidStr._·_ (N .snd) n n' ⟧₂ ≡ (⟦ n ⟧₂ · ⟦ n' ⟧₂)

  comm : ∀ x y -> x · y ≡ y · x
  identity  : ∀ x → x · ε ≡ x
  assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z

  trunc : isSet (FreeCommMonoidProd M N)


-- Maps out of the free product
module Elim {ℓ''} {M : Monoid ℓ} {N : Monoid ℓ'}
  {B : FreeCommMonoidProd M N -> Type ℓ''}
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
  
  (comm*      : ∀ {x y}   → (xs : B x) (ys : B y)
    → PathP (λ i → B (comm x y i)) (xs ·* ys) (ys ·* xs))
  (identity* : ∀ {x} -> (xs : B x) ->
    PathP (λ i -> B (identity x i)) (xs ·* ε*) xs)
  (assoc* : ∀ {x y z} -> (xs : B x) (ys : B y) (zs : B z) ->
    PathP (λ i → B (assoc x y z i)) (xs ·* (ys ·* zs)) ((xs ·* ys) ·* zs))
  (trunc* : ∀ xs -> isSet (B xs))
  
  where

  f : (x : FreeCommMonoidProd M N) -> B x
  f ⟦ m ⟧₁ = ⟦ m ⟧₁*
  f ⟦ n ⟧₂ = ⟦ n ⟧₂*
  f ε = ε*
  f (x · y) = f x ·* f y
  f (id₁ i) = id₁* i
  f (id₂ i) = id₂* i
  f (comp₁ m m' i) = comp₁* m m' i
  f (comp₂ n n' i) = comp₂* n n' i
  f (comm x y i) = comm* (f x) (f y) i
  f (identity x i) = identity* (f x) i
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
  
  (comm*      : (x y : B) → x ·* y ≡ y ·* x)
  (identity* : (x : B) -> (x ·* ε*) ≡ x)
  (assoc* : ∀ (x y z : B) -> x ·* (y ·* z) ≡ (x ·* y) ·* z)
  (trunc* : isSet B) where

  f : FreeCommMonoidProd M N -> B
  f = Elim.f
    ⟦_⟧₁* ⟦_⟧₂* ε* _·*_ id₁* id₂* comp₁* comp₂*
    comm* identity* assoc* (λ _ -> trunc*)

  
_⊕_ : Monoid ℓ -> Monoid ℓ' -> CommMonoid (ℓ-max ℓ ℓ')
M ⊕ N = makeCommMonoid {M = FreeCommMonoidProd M N}
  ε _·_ trunc assoc identity comm

-- The free commutative product of M and N is isomorphic to
-- the product of M and N.







-- Universal property of the free product

module _ {M : Monoid ℓ} {N : Monoid ℓ'} where

  open MonoidStr

  i₁ : MonoidHom M (CommMonoid→Monoid (M ⊕ N))
  i₁ = ⟦_⟧₁ , (monoidequiv id₁ comp₁)

  i₂ : MonoidHom N (CommMonoid→Monoid (M ⊕ N))
  i₂ = ⟦_⟧₂ , (monoidequiv id₂ comp₂)

{-
  case : (P : Monoid ℓ'') (f : MonoidHom M P) (g : MonoidHom N P) ->
    isContr (Σ[ h ∈ MonoidHom (CommMonoid→Monoid (M ⊕ N)) P ] (f ≡ h ∘hom i₁) × (g ≡ h ∘hom i₂))
  case P f g .fst .fst .fst =
    Rec.f (f .fst) (g .fst) P.ε P._·_ (f .snd .presε) (g .snd .presε)
          (f .snd .pres·) (g .snd .pres·) P.·IdR P.·IdL P.·Assoc P.is-set
    where
      module P = MonoidStr (P .snd)
  case P f g .fst .fst .snd = monoidequiv refl (λ x y -> refl)
  case P f g .fst .snd = (eqMonoidHom _ _ refl) , (eqMonoidHom _ _ refl)
  case P f g .snd = {!!}

  [_,hom_] : {P : Monoid ℓ''} (f : MonoidHom M P) (g : MonoidHom N P) ->
    MonoidHom (M ⋆ N) P
  [_,hom_] {P = P} f g = fst (fst (case P f g))
-}


{-
test : {M : Monoid ℓ} {N : Monoid ℓ'} -> CommMonoid→Monoid (M ⊕ N) ≡ (M ⋆ N)
test {M = M} {N = N} = {!!}
  where
    equiv : MonoidEquiv (M ⋆ N) (CommMonoid→Monoid (M ⊕ N))
    equiv .fst .fst = FP.[_,hom_] i₁ i₂ .fst
      -- FPRec.f ⟦_⟧₁ ⟦_⟧₂ {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
    equiv .fst .snd .equiv-proof y = ({!y!} , {!!}) , {!!}
    equiv .snd = {!!}
-}
