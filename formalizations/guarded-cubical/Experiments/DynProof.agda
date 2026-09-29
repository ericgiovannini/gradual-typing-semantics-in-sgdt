
module Semantics.Concrete.DynProof where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path

open import Cubical.Relation.Binary.Base


private
  variable
    ℓ ℓ' : Level

open BinaryRelation

module _ {ℓ : Level}
  (S : Type ℓ-zero) (P : S → Type ℓ-zero)
  (isSetS : isSet S)
  where
  
  data |D| : Type ℓ where
    Foo : ∀ s → (P s → |D|) → |D|

  data _⊑d_ : |D| → |D| → Type ℓ where
    ⊑Foo : ∀ s s' ds es →
        (eq : s ≡ s') →
        (∀ (p : P s) (p' : P s') (path : PathP (λ i → P (eq i)) p p') → (ds p ⊑d es p')) →
        Foo s ds ⊑d Foo s' es

  ⊑d-prop : isPropValued _⊑d_
  ⊑d-prop .(Foo s ds) .(Foo s' es)
            (⊑Foo s s' ds es eq ds⊑es) (⊑Foo s s' ds es eq' ds⊑es') i =
    ⊑Foo s s' ds es (eq≡eq' i) (goalPath i)
      where
        eq≡eq' : eq ≡ eq'
        eq≡eq' = isSetS s s' eq eq'

        goalPath : PathP
                (λ i →
                  (p : P s) (p' : P s') (path : PathP (λ j → P (eq≡eq' i j)) p p') → ds p ⊑d es p')
               ds⊑es ds⊑es'
        lem i' p p' path = ⊑d-prop (ds p) (es p') (ds⊑es p p' goal1) (ds⊑es' p p' goal2) i'
          where
            lemma : eq≡eq' i' ≡ eq
            lemma = isSetS s s' (eq≡eq' i') eq

            goal1 : PathP (λ j → P (eq j)) p p'
            goal1 = let x = transport (λ k → PathP (λ j → P (lemma k j)) p p') path
                    in {!x!} -- Giving `x` here doesn't work

            goal2 : PathP (λ j → P (eq' j)) p p'
            goal2 = {!!}
           
        



