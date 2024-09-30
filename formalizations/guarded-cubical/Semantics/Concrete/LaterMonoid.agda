{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Common.Later

module Semantics.Concrete.LaterMonoid (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Algebra.Monoid.Base

open import Common.LaterProperties

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓM : Level


private
  ▹_ : Type ℓ -> Type ℓ
  ▹ A = ▹_,_ k A




-- Theta for monoids
module _ (M~ : ▹ Monoid ℓM) where

  private module _ (@tick t : Tick k) where
    module M = MonoidStr (M~ t .snd)
    M = M~ t

    ε : ⟨ M ⟩
    ε = M.ε

    compose : ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
    compose m1 m2 = M._·_ m1 m2

    isSetM = M.is-set
    ·AssocM = M.·Assoc
    ·IdRM = M.·IdR
    ·IdLM = M.·IdL

  Monoid▸ :  Monoid ℓM
  Monoid▸ = makeMonoid
    {M = ▸ (λ t → ⟨ M~ t ⟩)}
    ε
    (λ m1~ m2~ t → compose t (m1~ t) (m2~ t))
    (isSet▸ (λ t → isSetM t))
    (λ m1~ m2~ m3~ → later-ext λ t → ·AssocM t (m1~ t) (m2~ t) (m3~ t))
    (λ m → later-ext (λ t → ·IdRM t (m t)))
    (λ m → later-ext (λ t → ·IdLM t (m t)))


-- Later for monoids
Monoid▹ : Monoid ℓM → Monoid ℓM
Monoid▹ M = Monoid▸ (next M)


open IsMonoidHom

-- Turning a "later" homomorphism of monoids h : (▸_t (M~ t) → (N~ t))
-- into a homomorphism ▸h : (Monoid▸ M~) (Monoid▸ N~)
monoidhom▸ : {M~ : ▹ Monoid ℓ} {N~ : ▹ Monoid ℓ'}
  (f~ : ▸ (λ t -> MonoidHom (M~ t) (N~ t))) ->
  MonoidHom (Monoid▸ M~) (Monoid▸ N~)
monoidhom▸ {M~ = M~} {N~ = N~} f~ .fst = λ m~ -> λ t -> (f~ t .fst) (m~ t)
monoidhom▸ {M~ = M~} {N~ = N~} f~ .snd .presε =
  later-ext (λ t -> f~ t .snd .presε)
monoidhom▸ {M~ = M~} {N~ = N~} f~ .snd .pres· x~ y~ =
  later-ext (λ t -> f~ t .snd .pres· (x~ t) (y~ t))

monoidhom▹ : {M : Monoid ℓ} {N : Monoid ℓ'}
  (f : MonoidHom M N) →
  MonoidHom (Monoid▹ M) (Monoid▹ N)
monoidhom▹ f = monoidhom▸ (next f)


record MonoidWithLaterAlg (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    M : Monoid ℓ
    θM : MonoidHom (Monoid▹ M) M

open MonoidWithLaterAlg
  
-- Free monoid with later algebra on one generator

data FreeMonoidLater : Type ℓ-zero where

  pt        : FreeMonoidLater
  ε         : FreeMonoidLater
  _·_       : FreeMonoidLater → FreeMonoidLater → FreeMonoidLater
  θₑ        : ▹ FreeMonoidLater → FreeMonoidLater

  identityᵣ  : ∀ x → x · ε ≡ x
  identityₗ   :  ∀ x → ε · x ≡ x
  assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z

  θ-ε : θₑ (next ε) ≡ ε
  θ-· : ∀ (x~ y~ : ▹ FreeMonoidLater) →
    θₑ (λ t → (x~ t)· (y~ t)) ≡ (θₑ x~ · θₑ y~)

  trunc : isSet FreeMonoidLater

lemma : fix θₑ ≡ ε
lemma = fix (λ IH → fix-eq θₑ ∙ cong θₑ (later-ext (λ t → IH t)) ∙ θ-ε)

FMLater : MonoidWithLaterAlg ℓ-zero
FMLater .M = makeMonoid ε _·_ trunc assoc identityᵣ identityₗ
FMLater .θM .fst = θₑ
FMLater .θM .snd .presε = θ-ε
FMLater .θM .snd .pres· = θ-·

-- Coproduct of monoids with later algebra
