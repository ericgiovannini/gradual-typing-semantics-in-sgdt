{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Predomains where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Common.Later

-- Define predomains as posets
Predomain : Set₁
Predomain = Poset ℓ-zero ℓ-zero


-- The relation associated to a predomain d
rel : (d : Predomain) -> (⟨ d ⟩ -> ⟨ d ⟩ -> Type)
rel d = PosetStr._≤_ (d .snd)

reflexive : (d : Predomain) -> (x : ⟨ d ⟩) -> (rel d x x)
reflexive d x = IsPoset.is-refl (PosetStr.isPoset (str d)) x

transitive : (d : Predomain) -> (x y z : ⟨ d ⟩) ->
  rel d x y -> rel d y z -> rel d x z
transitive d x y z x≤y y≤z =
  IsPoset.is-trans (PosetStr.isPoset (str d)) x y z x≤y y≤z



-- Theta for predomains

module _ (k : Clock) where

  private
    variable
      l : Level
    
    ▹_ : Set l → Set l
    ▹_ A = ▹_,_ k A


  
  isSet-poset : {ℓ ℓ' : Level} -> (P : Poset ℓ ℓ') -> isSet ⟨ P ⟩
  isSet-poset P = IsPoset.is-set (PosetStr.isPoset (str P))


  ▸' : ▹ Predomain → Predomain
  ▸' X = (▸ (λ t → ⟨ X t ⟩)) ,
         posetstr ord
                  (isposet isset-later {!!} ord-refl ord-trans ord-antisym)
     where

       ord : ▸ (λ t → ⟨ X t ⟩) → ▸ (λ t → ⟨ X t ⟩) → Type ℓ-zero
       -- ord x1~ x2~ =  ▸ (λ t → (str (X t) PosetStr.≤ (x1~ t)) (x2~ t))
       ord x1~ x2~ =  ▸ (λ t → (PosetStr._≤_ (str (X t)) (x1~ t)) (x2~ t))
     

       isset-later : isSet (▸ (λ t → ⟨ X t ⟩))
       isset-later = λ x y p1 p2 i j t →
         isSet-poset (X t) (x t) (y t) (λ i' → p1 i' t) (λ i' → p2 i' t) i j

       ord-refl : (a : ▸ (λ t → ⟨ X t ⟩)) -> ord a a
       ord-refl a = λ t ->
         IsPoset.is-refl (PosetStr.isPoset (str (X t))) (a t)

       ord-trans : BinaryRelation.isTrans ord
       ord-trans = λ a b c ord-ab ord-bc t →
         IsPoset.is-trans
           (PosetStr.isPoset (str (X t))) (a t) (b t) (c t) (ord-ab t) (ord-bc t)

       ord-antisym : BinaryRelation.isAntisym ord
       ord-antisym = λ a b ord-ab ord-ba i t ->
         IsPoset.is-antisym
           (PosetStr.isPoset (str (X t))) (a t) (b t) (ord-ab t) (ord-ba t) i


  -- Delay for predomains
  ▸''_ : Predomain → Predomain
  ▸'' X = ▸' (next X)

