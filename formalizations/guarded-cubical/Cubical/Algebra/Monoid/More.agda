{-# OPTIONS --allow-unsolved-metas #-}


module Cubical.Algebra.Monoid.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Unit



open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.CommMonoid.Base


open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' : Level


open IsMonoidHom

-- Composition of monoid homomorphisms

_∘hom_ : {M : Monoid ℓ} {N : Monoid ℓ'} {P : Monoid ℓ''} ->
  MonoidHom N P -> MonoidHom M N -> MonoidHom M P
g ∘hom f = fst g ∘ fst f  ,
           monoidequiv
             ((cong (fst g) (snd f .presε)) ∙ (snd g .presε))
             λ m m' -> {!!}

-- Equality of monoid homomorphisms
eqMonoidHom : {M : Monoid ℓ} {N : Monoid ℓ'} ->
  (f g : MonoidHom M N) ->
  fst f ≡ fst g -> f ≡ g
eqMonoidHom = {!!}


isSetMonoid : (M : Monoid ℓ) -> isSet ⟨ M ⟩
isSetMonoid M = M .snd .isMonoid .isSemigroup .is-set
  where
    open MonoidStr
    open IsMonoid
    open IsSemigroup

monoidId : (M : Monoid ℓ) -> ⟨ M ⟩
monoidId M = M .snd .ε
  where open MonoidStr

commMonoidId : (M : CommMonoid ℓ) -> ⟨ M ⟩
commMonoidId M = M .snd .ε
  where open CommMonoidStr


_×M_ : Monoid ℓ -> Monoid ℓ' -> Monoid (ℓ-max ℓ ℓ')
M1 ×M M2 = makeMonoid
  {M = ⟨ M1 ⟩ × ⟨ M2 ⟩}
  (M1.ε , M2.ε)
  (λ { (m1 , m2) (m1' , m2') -> (m1 M1.· m1') , (m2 M2.· m2')  })
  (isSet× M1.is-set M2.is-set)
  (λ  { (m1 , m2) (m1' , m2') (m1'' , m2'') ->
    ≡-× (M1.·Assoc m1 m1' m1'') (M2.·Assoc m2 m2' m2'') } )
  (λ { (m1 , m2) -> ≡-× (M1.·IdR m1) (M2.·IdR m2) })
  (λ { (m1 , m2) -> ≡-× (M1.·IdL m1) (M2.·IdL m2) })
    where
      open MonoidStr
      open IsMonoid
      open IsSemigroup
      module M1 = MonoidStr (M1 .snd)
      module M2 = MonoidStr (M2 .snd)
      _·M1_ = M1 .snd ._·_
      _·M2_ = M2 .snd ._·_



_×CM_ : CommMonoid ℓ -> CommMonoid ℓ' -> CommMonoid (ℓ-max ℓ ℓ')
M1 ×CM M2 = makeCommMonoid
  {M = ⟨ M1 ⟩ × ⟨ M2 ⟩}
  (commMonoidId M1 , commMonoidId M2)
  (λ { (m1 , m2) (m1' , m2') -> (m1 ·M1 m1') , (m2 ·M2 m2')})
  (isSet× M1.is-set M2.is-set)
  (λ { (m1 , m2) (m1' , m2') (m1'' , m2'') ->
    ≡-× (M1 .snd .isMonoid .isSemigroup .·Assoc m1 m1' m1'')
        (M2 .snd .isMonoid .isSemigroup .·Assoc m2 m2' m2'') })
  (λ { (m1 , m2) -> ≡-×
    (M1 .snd .isMonoid .·IdR m1) ((M2 .snd .isMonoid .·IdR m2)) })
  λ { (m1 , m2) (m1' , m2') -> ≡-×
    (M1 .snd .·Comm m1 m1') (M2 .snd .·Comm m2 m2') }
    where
      module M1 = CommMonoidStr (M1 .snd)
      module M2 = CommMonoidStr (M2 .snd)
      open CommMonoidStr
      open IsMonoid
      open IsSemigroup
      _·M1_ = M1 .snd ._·_
      _·M2_ = M2 .snd ._·_


{-
CM→M-× : (M1 : CommMonoid ℓ) (M2 : CommMonoid ℓ') ->
    (CommMonoid→Monoid (M1 ×CM M2)) ≡
    (CommMonoid→Monoid M1 ×M CommMonoid→Monoid M2)
CM→M-× M1 M2 = equivFun (MonoidPath _ _) CM→M-×'
  where
    CM→M-×' :
      MonoidEquiv
        (CommMonoid→Monoid (M1 ×CM M2))
        (CommMonoid→Monoid M1 ×M CommMonoid→Monoid M2)
    CM→M-×' .fst = idEquiv ⟨ CommMonoid→Monoid (M1 ×CM M2) ⟩
    CM→M-×' .snd .presε = refl
    CM→M-×' .snd .pres· p p' = refl
-}

CM→M-× : (M1 : CommMonoid ℓ) (M2 : CommMonoid ℓ') ->
    MonoidHom
      (CommMonoid→Monoid (M1 ×CM M2))
      (CommMonoid→Monoid M1 ×M CommMonoid→Monoid M2)
CM→M-× M1 M2 .fst x = x
CM→M-× M1 M2 .snd .presε = refl
CM→M-× M1 M2 .snd .pres· p p' = refl



-- "Product" of homomorphisms between two fixed monoids
_·hom_[_] : {M : Monoid ℓ} -> {N : Monoid ℓ'} ->
  (f g : MonoidHom M N) ->
  (commutes : ∀ x y ->
    N .snd .MonoidStr._·_ (fst f y) (fst g x) ≡
    N .snd .MonoidStr._·_ (fst g x) (fst f y)) ->
  MonoidHom M N
_·hom_[_] {M = M} {N = N} f g commutes =
  (λ a -> fst f a ·N fst g a) ,
  monoidequiv
  -- (f ε_M) ·N (g ε_M) = ε_N
  ((λ i -> (f .snd .presε i) ·N (g .snd .presε i)) ∙
  (N .snd .isMonoid .·IdR (N .snd .ε)))

  -- f (x ·M y) ·N g (x ·M y) = ((f x) ·N (g x)) ·N ((f y) ·N (g y))
  pres-mult
  where
    open MonoidStr
    open IsSemigroup
    open IsMonoid
    open IsMonoidHom
    _·M_ = M .snd ._·_
    _·N_ = N .snd ._·_

    f-fun : ⟨ M ⟩ → ⟨ N ⟩
    f-fun = fst f

    g-fun : ⟨ M ⟩ → ⟨ N ⟩
    g-fun = fst g

    N-assoc :  (x y z : ⟨ N ⟩) → x ·N (y ·N z) ≡ (x ·N y) ·N z
    N-assoc = N .snd .isMonoid .isSemigroup .·Assoc

    pres-mult : (x y : fst M) →
                (fst f ((M .snd · x) y) ·N fst g ((M .snd · x) y)) ≡
                (N .snd · (fst f x ·N fst g x)) (fst f y ·N fst g y)           
    pres-mult x y =
           (f-fun (x ·M y) ·N g-fun (x ·M y))
           ≡⟨ (λ i → f .snd .pres· x y i ·N g .snd .pres· x y i) ⟩
    
           ((f-fun x ·N f-fun y) ·N (g-fun x ·N g-fun y))
           ≡⟨ (N-assoc (f-fun x ·N f-fun y) (g-fun x) (g-fun y)) ⟩
           
           (((f-fun x ·N f-fun y) ·N g-fun x) ·N g-fun y)
           ≡⟨ (λ i -> (sym (N-assoc (f-fun x) (f-fun y) (g-fun x)) i) ·N g-fun y) ⟩
           
           ((f-fun x ·N ((f-fun y ·N g-fun x))) ·N g-fun y)
           ≡⟨ ((λ i -> (f-fun x ·N commutes x y i) ·N g-fun y)) ⟩
           
           ((f-fun x ·N ((g-fun x ·N f-fun y))) ·N g-fun y)
           ≡⟨ ((λ i -> (N-assoc (f-fun x) (g-fun x) (f-fun y) i) ·N g-fun y)) ⟩
           
           (((f-fun x ·N g-fun x) ·N f-fun y) ·N g-fun y)
           ≡⟨ sym (N-assoc (f-fun x ·N g-fun x) (f-fun y) (g-fun y)) ⟩
           
           ((f-fun x ·N g-fun x)) ·N (f-fun y ·N g-fun y) ∎




-- Extending the domain of a homomorphism, i.e.
-- If f is a homomorphism from N to P, then f is also
-- a homomorphism from M ×M N to P for any monoid M
extend-domain-l : {N : Monoid ℓ} {P : Monoid ℓ''} ->
  (M : Monoid ℓ') (f : MonoidHom N P) ->
  MonoidHom (M ×M N) P
extend-domain-l M f .fst (m , n) = f .fst n
extend-domain-l M f .snd .presε = f.presε
  where module f = IsMonoidHom (f .snd)
extend-domain-l M f .snd .pres· (m , n) (m' , n') = f.pres· n n'
  where module f = IsMonoidHom (f .snd)

-- This could be defined by composing extend-domain-l
-- with the "swap" homomorphism
extend-domain-r : {M : Monoid ℓ} {P : Monoid ℓ''} ->
  (N : Monoid ℓ') (f : MonoidHom M P) ->
  MonoidHom (M ×M N) P
extend-domain-r N f .fst (m , n) = f .fst m
extend-domain-r N f .snd .presε = f.presε
  where module f = IsMonoidHom (f .snd)
extend-domain-r N f .snd .pres· (m , n) (m' , n') = f.pres· m m'
  where module f = IsMonoidHom (f .snd)



-- Monoid of natural numbers with addition
nat-monoid : CommMonoid ℓ-zero
nat-monoid = makeCommMonoid {M = ℕ} zero _+_ isSetℕ +-assoc +-zero +-comm


-- Trivial monoid
trivial-monoid : CommMonoid ℓ-zero
trivial-monoid = makeCommMonoid
  tt (λ _ _ -> tt) isSetUnit (λ _ _ _ -> refl) (λ _ -> refl) (λ _ _ -> refl)

-- (unique) homomorphism out of the trivial monoid
trivial-monoid-hom : (M : Monoid ℓ) ->
  MonoidHom (CommMonoid→Monoid trivial-monoid) M
trivial-monoid-hom M .fst tt = ε
  where open MonoidStr (M .snd)
trivial-monoid-hom M .snd .presε = refl
trivial-monoid-hom M .snd .pres· tt tt = sym (·IdR ε)
  where open MonoidStr (M .snd)
