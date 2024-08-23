{- Basic theory about transport:

- transport is invertible
- transport is an equivalence ([pathToEquiv])

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Transport.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv as Equiv hiding (transpEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function using (_∘_)

-- transporting over (λ i → B (p i) → C (p i)) divides the transport into
-- transports over (λ i → C (p i)) and (λ i → B (p (~ i)))
funDomTransp : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ}{C : Type ℓ''} (B : A → Type ℓ') {x y : A} (p : x ≡ y) (f : B x → C)
         → PathP (λ i → B (p i) → C) f (f ∘ subst B (sym p))
funDomTransp B {x = x} p f i b =
  f ((transp (λ j → B (p (i ∧ ~ j))) (~ i) b))

