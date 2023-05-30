

module Cubical.Categories.Coalgebra where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Data.Sigma


private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') (F : Functor C C) where

  open Category

  record Coalgebra : Type (ℓ-max ℓ ℓ') where
    field
      V : C .ob
      un : C [ V , F ⟅ V ⟆ ]

  open Coalgebra

  record CoalgMorphism (c d : Coalgebra) : Type ℓ' where
    field
      f : C [ c .V , d .V ]
      com : d .un ∘⟨ C ⟩ f ≡ F ⟪ f ⟫ ∘⟨ C ⟩ c .un

  open CoalgMorphism

  is-final : Coalgebra -> Type (ℓ-max ℓ ℓ')
  is-final d = ∀ (c : Coalgebra) -> isContr (CoalgMorphism c d)

  FinalCoalg : Type (ℓ-max ℓ ℓ')
  FinalCoalg = Σ[ c ∈ Coalgebra ] is-final c


  -- Final coalgebras are unique up to unique isomorphism
  final-unique : (c c' : FinalCoalg) ->
    isContr (Σ[ α ∈ CoalgMorphism (fst c) (fst c') ] (isIso C (α .f)))
    -- CatIso C (fst c .V) (fst c' .V)
  final-unique c c' = (!c' , {!!}) , {!!}
    where
      !c : CoalgMorphism (fst c') (fst c)
      !c = fst (snd c (fst c'))

      !c' : CoalgMorphism (fst c) (fst c')
      !c' = fst (snd c' (fst c))

      isom : isIso C (!c' .f)
      isom = isiso (!c .f) {!!} {!!}

     


