{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later


module Semantics.DynTypGen.WorldTag (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
-- open import Cubical.Data.Fin as Fin
open import Cubical.Data.FinData as FinData

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Preorder

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Preorder
open import Cubical.Categories.Instances.Sets

open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Bifunctor.Redundant

open import Common.LaterProperties
open import Semantics.DynTypGen.Impred.Set

open BinaryRelation


private
  variable
    ℓ ℓ' : Level
    A : hSet ℓ-zero

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


lookup : {A : Type ℓ}
  → (xs : List A)
  → Fin (length xs)
  → A
lookup (x ∷ xs) zero = x
lookup (x ∷ xs) (suc n) = lookup xs n


upgrade : ∀ n m → n ≤ m → Fin n → Fin m
upgrade n m (zero , H) x  = subst Fin H x
upgrade n m (one , H) x   = subst Fin H (weakenFin x)
upgrade n m (suc (suc l) , H) x = {!!}
  -- subst Fin H (weakenFin (upgrade n (suc (l + n)) (suc l , refl) x))


-- Underlying type of worlds on an hSet A

⟨World⟩ : hSet ℓ-zero → Type ℓ-zero
⟨World⟩ A = List ⟨ A ⟩

isSetWorld : ∀ A → isSet (⟨World⟩ A)
isSetWorld (A , isSetA) = isOfHLevelList 0 isSetA


-- The domain of a world
domain : ⟨World⟩ A → Type
domain w = Fin (length w)

-- The size of a world
size : ⟨World⟩ A → ℕ
size w = length w

-- Lookup in a world
_!!_ : (w : ⟨World⟩ A) → (i : domain w) → ⟨ A ⟩
w !! i = lookup w i

-- Renaming
ren : (w₁ w₂ : ⟨World⟩ A) → size w₁ ≤ size w₂ → domain w₁ → domain w₂
ren w₁ w₂ H i = upgrade (size w₁) (size w₂) H i



-- Prefix ordering on worlds:

_≤world_ : ⟨World⟩ A → ⟨World⟩ A → Type ℓ-zero
[] ≤world ys = ⊤
(x ∷ xs) ≤world [] = ⊥
(x ∷ xs) ≤world (y ∷ ys) = (x ≡ y) × (xs ≤world ys)

_≤world'_ : ⟨World⟩ A → ⟨World⟩ A → Type ℓ-zero
w ≤world' w' =
  Σ[ H ∈ (size w ≤ size w') ]
    (∀ (i : domain w) → w !! i ≡ (w' !! ren w w' H i))


-- Properties of the prefix ordering:

≤world-prop : isPropValued (_≤world_ {A = A})
≤world-prop [] w₂ p q = refl
≤world-prop {A} (x ∷ xs) (y ∷ ys) p q =
  ≡-× (A .snd x y (p .fst) (q .fst))
      (≤world-prop xs ys (p .snd) (q .snd))

≤world-refl : ∀ (w : ⟨World⟩ A) → w ≤world w
≤world-refl [] = tt
≤world-refl (x ∷ xs) = refl , ≤world-refl xs

≤world-trans : ∀ (w₁ w₂ w₃ : ⟨World⟩ A)
  → w₁ ≤world w₂
  → w₂ ≤world w₃
  → w₁ ≤world w₃
≤world-trans w₁ w₂ w₃ = {!!}


-- Definition of Worlds as a Preorder

World : hSet ℓ-zero → Preorder ℓ-zero ℓ-zero
World A .fst = ⟨World⟩ A
World A .snd = preorderstr
  _≤world_
  (ispreorder (isSetWorld A) ≤world-prop ≤world-refl ≤world-trans)


data Ty : Type where
  nat   : Ty
  prod  : Ty → Ty → Ty
  arrow : Ty → Ty → Ty
  dyn   : Ty

isSetTy : isSet Ty
isSetTy = {!!}


W : Preorder ℓ-zero ℓ-zero
W = World (Ty , isSetTy)




open Functor

i' : ▹ (Ty → Functor (PreorderCategory W) (SET ℓ-zero))
     → (Ty → Functor (PreorderCategory W) (SET ℓ-zero))
i' _ nat = Constant _ _ (ℕ , isSetℕ)
i' rec (prod t t') = PshProd .Bifunctor.Bif-ob (i' rec t) (i' rec t') -- product of presheaves
i' _ (arrow t t') = {!!} -- CBV functions (involves the monad)
i' rec dyn = f
  where
    f : Functor _ (SET _)

    f .Functor.F-ob w .fst =
      Σ[ tag ∈ Fin (length w) ] (▸ (λ t → rec t (lookup w tag) .F-ob w .fst)) -- i' rec (lookup w t) .F-ob w .fst 

    f .Functor.F-ob w .snd =
      isSetΣ isSetFin (λ tag → isSet▸ (λ t → rec t (lookup w tag) .F-ob w .snd))


    f .Functor.F-hom {w₁} {w₂} w₁≤w₂ (tag , z~) =
        upgrade _ _ {!!} tag
      , (λ t → {!!})
    f .Functor.F-id = {!!}
    f .Functor.F-seq = {!!}



