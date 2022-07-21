{-# OPTIONS --cubical --rewriting --guarded #-}

open import Later

module ErrorDomains(k : Clock) where

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Cubical.Data.Sigma

private
  variable
    l : Level
    A B : Set l
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A 

Predomain : Set₁
Predomain = Poset ℓ-zero ℓ-zero
record MonFun (X Y : Predomain) : Set where
  module X = PosetStr (X .snd)
  module Y = PosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    f : (X .fst) → (Y .fst)
    isMon : ∀ {x y} → x ≤X y → f x ≤Y f y

▸' : ▹ Predomain → Predomain
▸' X = ((@tick x : Tick k) → (X x) .fst) ,
       posetstr (fix {k = k} (λ _,_≤_ x₁ x₂ → ▸ λ x → x , x₁ ≤ x₂))
                (fix {k = k} λ proofs → isposet {!!} {!!} {!!} {!!} {!!})

▸''_ : Predomain → Predomain
▸'' X = ▸' (next X)

record ErrorDomain : Set₁ where
  field
    X : Predomain
  module X = PosetStr (X .snd)
  _≤_ = X._≤_
  field
    ℧ : X .fst
    ℧⊥ : ∀ x → ℧ ≤ x

    θ : MonFun (▸'' X) X

data L℧₀ (X : Set) : Set where
  η₀ : X → L℧₀ X
  ℧ : L℧₀ X
  θ₀ : ▹ (L℧₀ X) → L℧₀ X

L℧ : Predomain → ErrorDomain
L℧ X = record { X = L℧X ; ℧ = ℧ ; ℧⊥ = {!!} ; θ = record { f = θ₀ ; isMon = {!!} } }
  where
    L℧X : Predomain
    L℧X = L℧₀ (X .fst) , {!!}

-- | TODO:
-- | 1. monotone monad structure
-- | 2. strict functions
-- | 3. UMP?
-- | 4. show that later preserves domain structures
-- | 5. Solve some example recursive domain equations
-- | 6. Program in shallow embedded lambda calculus
-- | 7. Embedding-Projection pairs!
-- | 8. GLTC Syntax, Inequational theory
-- | 9. Model of terms & inequational theory
