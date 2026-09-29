{-# OPTIONS --safe #-}
module Cubical.Algebra.Monoid.PointedMonoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Algebra.Semigroup

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.Monoid.Base

open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level


record PointedMonoidStr (A : Type ℓ) : Type ℓ where
  constructor pointedmonoidstr

  field
    ε        : A
    _·_      : A → A → A
    isMonoid : IsMonoid ε _·_
    -- monoidStr : MonoidStr A
    pt : A

  infixl 7 _·_

  open IsMonoid isMonoid public
  -- open MonoidStr monoidStr public

PointedMonoid : ∀ ℓ → Type (ℓ-suc ℓ)
PointedMonoid ℓ = TypeWithStr ℓ PointedMonoidStr

pointedmonoid : (A : Type ℓ) (ε : A) (_·_ : A → A → A) (h : IsMonoid ε _·_) (x : A) → PointedMonoid ℓ
pointedmonoid A ε _·_ h x = A , pointedmonoidstr ε _·_ h x

-- Easier to use constructors

makePointedMonoid : {M : Type ℓ} (ε : M) (_·_ : M → M → M) (x : M)
             (is-setM : isSet M)
             (·Assoc : (x y z : M) → x · (y · z) ≡ (x · y) · z)
             (·IdR : (x : M) → x · ε ≡ x)
             (·IdL : (x : M) → ε · x ≡ x)             
           → PointedMonoid ℓ
makePointedMonoid ε _·_ x is-setM ·Assoc ·IdR ·IdL =
  pointedmonoid _ ε _·_ (makeIsMonoid is-setM ·Assoc ·IdR ·IdL) x


Monoid→PointedMonoid : (M : Monoid ℓ) → (x : ⟨ M ⟩) → PointedMonoid ℓ
Monoid→PointedMonoid M x .fst = ⟨ M ⟩
Monoid→PointedMonoid M x .snd = pointedmonoidstr M.ε M._·_ M.isMonoid x
  where module M = MonoidStr (M .snd)



record IsPointedMonoidWkHom {A : Type ℓ} {B : Type ℓ'}
  (M : PointedMonoidStr A) (f : A → B) (N : PointedMonoidStr B)
  : Type (ℓ-max ℓ ℓ')
  where

  constructor pointedmonoidwkhom

  -- Shorter qualified names
  private
    module M = PointedMonoidStr M
    module N = PointedMonoidStr N

  field
    presPt : f M.pt ≡ N.pt
    pres· : (x y : A) → f (x M.· M.pt M.· y) ≡ f x N.· N.pt N.· f y

PointedMonoidWkHom : (L : PointedMonoid ℓ) (M : PointedMonoid ℓ') → Type (ℓ-max ℓ ℓ')
PointedMonoidWkHom L M = Σ[ f ∈ (⟨ L ⟩ → ⟨ M ⟩) ] IsPointedMonoidWkHom (L .snd) f (M .snd)

open IsPointedMonoidWkHom

idPtHom : (M : PointedMonoid ℓ) → PointedMonoidWkHom M M
idPtHom M .fst x = x
idPtHom M .snd .presPt = refl
idPtHom M .snd .pres· x y = refl

module _ {M : PointedMonoid ℓ} {N : PointedMonoid ℓ'} {P : PointedMonoid ℓ''} where

  private
    module N = PointedMonoidStr (N .snd)
    module P = PointedMonoidStr (P .snd)

  _∘pthom_ :  PointedMonoidWkHom N P
            → PointedMonoidWkHom M N
            → PointedMonoidWkHom M P
  (g ∘pthom f) .fst x = g .fst (f .fst x)
  (g ∘pthom f) .snd .presPt = cong (g .fst) (f .snd .presPt) ∙ g .snd .presPt
  (g ∘pthom f) .snd .pres· x y =
      (cong (g .fst) (f .snd .pres· x y))
    ∙ (g .snd .pres· (f .fst x) (f .fst y))
     
