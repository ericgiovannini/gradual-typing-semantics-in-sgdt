{-# OPTIONS --safe #-}
module Cubical.Algebra.Monoid.Instances.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.HITs.SetQuotients as SQ hiding (elim)

open import Cubical.Data.Empty as Empty hiding (elim; rec)

private variable
  ℓ ℓ' ℓ'' ℓ''' ℓᴰ : Level

module _ (M : Monoid ℓ) where
  private
    module M = MonoidStr (M .snd)
    open MonoidStr
  module _ 
    (_~_ : ⟨ M ⟩ → ⟨ M ⟩ → Type ℓ')
    (~congl : ∀ {a b c} → a ~ b → (a M.· c) ~ (b M.· c))
    (~congr : ∀ {a b c} → b ~ c → (a M.· b) ~ (a M.· c))
    where
    private
      |M/~| = ⟨ M ⟩ / _~_

    QuotientMonoid : Monoid (ℓ-max ℓ ℓ')
    QuotientMonoid .fst = |M/~|
    QuotientMonoid .snd .ε = [ M.ε ]
    QuotientMonoid .snd ._·_ =
      rec2 squash/ (λ x y → [ x M.· y ])
        (λ a b c a~b → eq/ _ _ (~congl a~b))
        λ a b c b~c → eq/ _ _ (~congr b~c)
    QuotientMonoid .snd .isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set =
      squash/
    QuotientMonoid .snd .isMonoid .IsMonoid.isSemigroup .IsSemigroup.·Assoc =
      elimProp3 (λ _ _ _ → squash/ _ _)
        (λ a b c → cong [_] (M .snd .·Assoc a b c))
    QuotientMonoid .snd .isMonoid .IsMonoid.·IdR =
      elimProp (λ _ → squash/ _ _) (λ a → cong [_] (M .snd .·IdR a))
    QuotientMonoid .snd .isMonoid .IsMonoid.·IdL =
      elimProp (λ _ → squash/ _ _) (λ a → cong [_] (M .snd .·IdL a))

    σ : MonoidHom M QuotientMonoid
    σ .fst = [_]
    σ .snd .IsMonoidHom.presε = refl
    σ .snd .IsMonoidHom.pres· x y = refl

    module _ (Mᴰ : Monoidᴰ QuotientMonoid ℓᴰ)
      (s : LocalSection σ Mᴰ)
      where
      private
        module Mᴰ = Monoidᴰ Mᴰ

      module _ (resp~ : ∀ {a b} → (p : a ~ b)
               → s .fst a Mᴰ.≡[ eq/ a b p ] s .fst b)
        where
        elim : Section Mᴰ
        elim .fst = SQ.elim (λ _ → Mᴰ.isSetEltᴰ) (s .fst) (λ a b → resp~)
        elim .snd .fst = s .snd .fst
        elim .snd .snd = elimProp2 (λ _ _ → Mᴰ.isSetEltᴰ _ _) (s .snd .snd)
