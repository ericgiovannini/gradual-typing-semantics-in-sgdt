{-# OPTIONS --guarded --rewriting #-}


-- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.Predomain.Relation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Binary
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (elim)
open import Cubical.Data.Empty hiding (elim)

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.PropositionalTruncation renaming (rec to PTrec)


open import Common.Common
open import Common.LaterProperties
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Convenience
open import Semantics.Concrete.Predomain.Constructions as Predomain
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Proofs
open import Semantics.Concrete.Predomain.Combinators

open import Common.Later

open BinaryRelation

private
  variable
    ℓX ℓ'X ℓ''X ℓY ℓ'Y ℓ''Y ℓZ ℓ'Z ℓ''Z : Level
    ℓX' ℓ'X' ℓY' ℓ'Y' ℓZ' ℓ'Z' : Level
    ℓ ℓ' ℓ'' ℓR ℓR' ℓR'' : Level
    ℓo : Level
    ℓc ℓc' : Level
    ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  : Level
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' : Level
    ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  : Level
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' : Level
    ℓcᵢ ℓcₒ : Level

    ℓA  ℓ≤A  ℓ≈A  : Level
    ℓA' ℓ≤A' ℓ≈A' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ : Level
    ℓA₁' ℓ≤A₁' ℓ≈A₁' : Level
    ℓA₂ ℓ≤A₂ ℓ≈A₂ : Level
    ℓA₂' ℓ≤A₂' ℓ≈A₂' : Level
    ℓA₃ ℓ≤A₃ ℓ≈A₃ : Level
    ℓc₁ ℓc₂ : Level

    X : Predomain ℓX ℓ'X ℓ''X
    Y : Predomain ℓY ℓ'Y ℓ''Y


-- Horizontal morphisms
record PRel (X : Predomain ℓX ℓ'X ℓ''X) (Y : Predomain ℓY ℓ'Y ℓ''Y) (ℓR : Level) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) (ℓ-suc ℓR)) where
  module X = PredomainStr (X .snd)
  module Y = PredomainStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    R : ⟨ X ⟩ -> ⟨ Y ⟩ -> Type ℓR
    is-prop-valued : (x : ⟨ X ⟩) -> (y : ⟨ Y ⟩) -> isProp (R x y)
    is-antitone : ∀ {x' x y} -> x' ≤X x -> R x y -> R x' y
    is-monotone : ∀ {x y y'} -> R x y -> y ≤Y y' -> R x y'

  _rel_ : ⟨ X ⟩ → ⟨ Y ⟩ → Type ℓR
  _rel_ = R

{-
opaque
  PRel : (A : Predomain ℓA ℓ≤A ℓ≈A) (A' : Predomain ℓA' ℓ≤A' ℓ≈A') (ℓc : Level)
    → Type (ℓ-max (ℓ-max (ℓ-max ℓA ℓ≤A) (ℓ-max ℓA' ℓ≤A')) (ℓ-suc ℓc))
  PRel = PRel

module _ {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  (c : PRel A A' ℓc)
  where

  private
    |A| = ⟨ A ⟩
    |A'| = ⟨ A' ⟩
    _≤A_ = A .snd .PredomainStr._≤_
    _≤A'_ = A' .snd .PredomainStr._≤_

  opaque
    unfolding PRel

    PRel→Record : PRel A A' ℓc
    PRel→Record = c

    |PRel| : |A| → |A'| → Type ℓc
    |PRel| = c .PRel.R

    PRelIsPropValued : ∀ x y → isProp (|PRel| x y)
    PRelIsPropValued = c .PRel.is-prop-valued

    PRelIsAntitone : ∀ {x' x y} -> x' ≤A x -> |PRel| x y -> |PRel| x' y
    PRelIsAntitone = c .PRel.is-antitone

    PRelIsMonotone : ∀ {x y y'} -> |PRel| x y -> y ≤A' y' -> |PRel| x y'
    PRelIsMonotone = c .PRel.is-monotone

⟨_⟩PRel : {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'} →
  (c : PRel A A' ℓc) → _
⟨ c ⟩PRel = |PRel| c
-}

open PRel hiding (module X ; module Y ; _≤X_ ; _≤Y_)

record PRel' (X : Predomain ℓX ℓ'X ℓ''X) (Y : Predomain ℓY ℓ'Y ℓ''Y) (ℓR : Level) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) (ℓ-suc ℓR)) where
  module X = PredomainStr (X .snd)
  module Y = PredomainStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    R : ⟨ X ⟩ -> ⟨ Y ⟩ -> hProp ℓR
    is-antitone : ∀ x' x y -> x' ≤X x -> ⟨ R x y ⟩ -> ⟨ R x' y ⟩
    is-monotone : ∀ x y y' -> ⟨ R x y ⟩ -> y ≤Y y' -> ⟨ R x y' ⟩


-- Iso between PRel and PRel'
PRelIsoPRel' : ∀ {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'} →
  Iso (PRel A A' ℓc) (PRel' A A' ℓc)
PRelIsoPRel' = iso
  (λ S -> record {
    R = λ x y -> S .PRel.R x y , S .PRel.is-prop-valued x y ;
    is-antitone = λ x' x y x'≤x xSy → S .PRel.is-antitone x'≤x xSy ;
    is-monotone = λ x y y' xSy y≤y' → S .PRel.is-monotone xSy y≤y' })

  (λ S → record {
    R = λ x y -> fst (S .PRel'.R x y) ;
    is-prop-valued = λ x y -> snd (S .PRel'.R x y) ;
    is-antitone = λ {x'} {x} {y} x'≤x xSy →
      S .PRel'.is-antitone x' x y x'≤x xSy ;
    is-monotone = λ {x} {y} {y'} xSy y≤y' ->
      S .PRel'.is-monotone x y y' xSy y≤y' })

  (λ b → refl)

  (λ a → refl)


  -- Equivalence between PRel' record and a sigma type   
unquoteDecl PRel'IsoΣ = declareRecordIsoΣ PRel'IsoΣ (quote (PRel'))


-- PRel' is a Set
isSetPRel' : {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'} → isSet (PRel' A A' ℓc)
isSetPRel' = isSetRetract
  (Iso.fun PRel'IsoΣ) (Iso.inv PRel'IsoΣ)
  (Iso.leftInv PRel'IsoΣ)
    (isSetΣSndProp
      (isSetΠ2 (λ _ _ -> isSetHProp))
      (λ R -> isProp× (isPropΠ5 (λ _ _ _ _ _ -> snd (R _ _)))
                      (isPropΠ5 (λ _ _ _ _ _ -> snd (R _ _)))))


-- PRel is a Set
isSetPRel : {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'} → isSet (PRel X Y ℓR)
isSetPRel = isSetRetract
  (Iso.fun PRelIsoPRel') (Iso.inv PRelIsoPRel')
  (Iso.leftInv PRelIsoPRel') isSetPRel'

-- Equality of horizontal morphisms follows from equality of the underlying relations.

eqPRel : {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'} -> (c c' : PRel A A' ℓc) ->
  PRel.R c ≡ PRel.R c' -> c ≡ c'
eqPRel {A = A} {A' = A'} c c' eq =
  isoFunInjective PRelIsoPRel' c c' (eqPRel' _ _  eq1)
  where
    eq1 : (λ x y → c .R x y , c .is-prop-valued x y) ≡ (λ x y → c' .R x y , c' .is-prop-valued x y)
    eq1 = funExt (λ x → funExt (λ y → Σ≡Prop (λ _ → isPropIsProp) ((funExt⁻ (funExt⁻ eq x) y))))

    eqPRel' : (c c' : PRel' A A' ℓc) -> PRel'.R c ≡ PRel'.R c' -> c ≡ c'
    eqPRel' c c' eq =
      isoFunInjective PRel'IsoΣ c c'
        (Σ≡Prop (λ R → isProp× (isPropΠ5 (λ _ _ _ _ _ → snd (R _ _)))
                               (isPropΠ5 (λ _ _ _ _ _ → snd (R _ _))))
                 eq)


-- Identity relation
posetbisim-monrel : {ℓo : Level} -> (X : Predomain ℓ ℓ' ℓ'') -> PRel X X (ℓ-max ℓ' ℓo)
posetbisim-monrel {ℓ' = ℓ'} {ℓo = ℓo} X = record {
  R = λ x x' -> Lift {i = ℓ'} {j = ℓo} (rel-≤ X x x') ;
  is-prop-valued = λ x x' -> isOfHLevelLift 1 (prop-valued-≤ X x x') ;
  is-antitone = λ {x'} {x} {y}  x'≤x x≤y -> lift (transitive-≤ X x' x y x'≤x (lower x≤y)) ;
  is-monotone = λ {x}  {y} {y'} x≤y y≤y' -> lift (transitive-≤ X x y y' (lower x≤y) y≤y') }


idPRel : (X : Predomain ℓ ℓ' ℓ'') -> PRel X X ℓ'
idPRel {ℓ' = ℓ'}  X = record {
  R = λ x x' -> (rel-≤ X x x') ;
  is-prop-valued = λ x x' -> (prop-valued-≤ X x x') ;
  is-antitone = λ {x'} {x} {y}  x'≤x x≤y -> (transitive-≤ X x' x y x'≤x x≤y) ;
  is-monotone = λ {x}  {y} {y'} x≤y y≤y' -> (transitive-≤ X x y y' x≤y y≤y') }


-- idRel : (ℓo : Level) -> (X : Predomain ℓ ℓ' ℓ'') -> PRel X X (ℓ-max ℓ' ℓo)
-- idRel ℓo = posetbisim-monrel {ℓo = ℓo}



-- Composition of relations

-- Composing pedomain relations
-- Note that becasue of the quantification over elements of Y,
-- the universe level of the resulting relation involves an
-- ℓ-max with ℓA₂ (i.e. the level of the elements in A₂)
_⊙_ : 
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₃ : Predomain ℓA₃ ℓ≤A₃ ℓ≈A₃} ->
  PRel A₁ A₂ ℓc₁ ->
  PRel A₂ A₃ ℓc₂ ->
  PRel A₁ A₃ (ℓ-max ℓA₂ (ℓ-max ℓc₁ ℓc₂))
_⊙_ {A₁ = A₁} {A₂ = A₂} {A₃ = A₃} c₁ c₂ = record {
  R = λ x z -> ∥ compRel (PRel.R c₁) (PRel.R c₂) x z ∥₁ ;
  is-prop-valued = λ x z -> isPropPropTrunc ;
  is-antitone = λ x'≤x H -> elim (λ _ -> isPropPropTrunc) (λ p -> ∣ comp-antitone x'≤x p ∣₁) H ;
  is-monotone = λ H y≤y' -> PTrec isPropPropTrunc (λ p → ∣ comp-monotone p y≤y' ∣₁) H }
    where

      module A₁ = PredomainStr (A₁ .snd)
      module A₃ = PredomainStr (A₃ .snd)
      
      module c₁ = PRel c₁
      module c₂ = PRel c₂

      comp-antitone : {x' x : ⟨ A₁ ⟩} {z : ⟨ A₃ ⟩} ->
         x' A₁.≤ x ->
        compRel (PRel.R c₁) (PRel.R c₂) x z ->
        compRel (PRel.R c₁) (PRel.R c₂) x' z 
      comp-antitone x'≤x (y , xc₁y , yc₂z) = y , (PRel.is-antitone c₁ x'≤x xc₁y) , yc₂z

      comp-monotone : {x : ⟨ A₁ ⟩} {z z' : ⟨ A₃ ⟩} ->
        compRel (PRel.R c₁) (PRel.R c₂) x z ->
        z A₃.≤ z' ->
        compRel (PRel.R c₁) (PRel.R c₂) x z'
      comp-monotone (y , xc₁y , yc₂z) z≤z' = y , xc₁y , (PRel.is-monotone c₂ yc₂z z≤z')





-- Exponential of relations

_==>pbmonrel_ :
  {Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aᵢ' : Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
  {Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} {Aₒ' : Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'} ->
  PRel Aᵢ Aᵢ' ℓcᵢ ->
  PRel Aₒ Aₒ' ℓcₒ ->
  PRel (Aᵢ ==> Aₒ) (Aᵢ' ==> Aₒ') (ℓ-max (ℓ-max ℓAᵢ ℓAᵢ') (ℓ-max ℓcᵢ ℓcₒ))
cᵢ ==>pbmonrel cₒ = record {
  R = λ f g ->
    TwoCell (PRel.R cᵢ) (PRel.R cₒ) (PMor.f f) (PMor.f g)  ;
  is-prop-valued = λ f g -> isPropTwoCell (cₒ .PRel.is-prop-valued) ;
  is-antitone = λ {f1} {f2} {g} f1≤f2 f1≤g  a b aRb →
    cₒ .PRel.is-antitone (f1≤f2 a) (f1≤g a b aRb) ;
  is-monotone = λ {f} {g1} {g2} f≤g1 g1≤g2 a b aRb →
    cₒ .PRel.is-monotone (f≤g1 a b aRb) (g1≤g2 b) }

_×pbmonrel_ :   {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁'}
  {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : Predomain ℓA₂' ℓ≤A₂' ℓ≈A₂'} ->
  PRel A₁ A₁' ℓc₁ ->
  PRel A₂ A₂' ℓc₂ ->
  PRel (A₁ ×dp A₂) (A₁' ×dp A₂') _
c₁ ×pbmonrel c₂ = record
  { R = λ p q → c₁ .R (p .fst) (q .fst) × c₂ .R (p .snd) (q .snd)
  ; is-prop-valued = λ _ _ → isProp× (c₁ .is-prop-valued _ _) (c₂ .is-prop-valued _ _)
  ; is-antitone = λ x x₁ → (c₁ .is-antitone (x .fst) (x₁ .fst)) , c₂ .is-antitone (x .snd) (x₁ .snd)
  ; is-monotone = λ x x₁ → (c₁ .is-monotone (x .fst) (x₁ .fst)) , c₂ .is-monotone (x .snd) (x₁ .snd) }


_⊎-rel_ :
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : Predomain ℓA₁' ℓ≤A₁' ℓ≈A₁'}
  {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : Predomain ℓA₂' ℓ≤A₂' ℓ≈A₂'} →
  PRel A₁ A₁' ℓc₁ →
  PRel A₂ A₂' ℓc₂ →
  PRel (A₁ ⊎p A₂) (A₁' ⊎p A₂') (ℓ-max ℓc₁ ℓc₂)
_⊎-rel_ {ℓc₁ = ℓc₁} {ℓc₂ = ℓc₂} {A₁ = A₁} {A₁' = A₁'} {A₂ = A₂} {A₂' = A₂'} c₁ c₂ = record
  { R = rel
  ; is-prop-valued = prop-valued
  ; is-antitone = anti
  ; is-monotone = mon }
  where
    module A₁⊎A₂ = PredomainStr ((A₁ ⊎p A₂) .snd)
    module A₁'⊎A₂' = PredomainStr ((A₁' ⊎p A₂') .snd)
    
    rel : ⟨ (A₁ ⊎p A₂) ⟩ → ⟨ (A₁' ⊎p A₂') ⟩ → Type (ℓ-max ℓc₁ ℓc₂)
    rel (inl x₁) (inl x₁') = Lift {j = ℓc₂} (c₁ .R x₁ x₁')
    rel (inl x₁) (inr x₂') = ⊥*
    rel (inr x₂) (inl x₁') = ⊥*
    rel (inr x₂) (inr x₂') = Lift {j = ℓc₁} (c₂ .R x₂ x₂')

    prop-valued : ∀ x y → isProp (rel x y)
    prop-valued (inl x₁) (inl x₁') = isOfHLevelLift 1 (c₁ .is-prop-valued x₁ x₁')
    prop-valued (inr x₂) (inr x₂') = isOfHLevelLift 1 (c₂ .is-prop-valued x₂ x₂')

    anti : {x' x : (A₁ ⊎p A₂) .fst} {y : ⟨ A₁' ⊎p A₂' ⟩} →
      x' A₁⊎A₂.≤ x → rel x y → rel x' y
    anti {x' = inl x} {x = inl y} {y = inl z} x≤y H = lift (c₁ .is-antitone (lower x≤y) (lower H))
    anti {x' = inr x} {x = inr y} {y = inr z} x≤y H = lift (c₂ .is-antitone (lower x≤y) (lower H))

    mon : {x : ⟨ A₁ ⊎p A₂ ⟩} {y : ⟨ A₁' ⊎p A₂' ⟩}
      {y' : (A₁' ⊎p A₂') .fst} →
      rel x y → y A₁'⊎A₂'.≤ y' → rel x y'
    mon {x = inl x} {y = inl y} {y' = inl z} H x≤y = lift (c₁ .is-monotone (lower H) (lower x≤y))
    mon {x = inr x} {y = inr y} {y' = inr z} H x≤y = lift (c₂ .is-monotone (lower H) (lower x≤y))

-- Composing with vertical morphisms on either side

functionalRel :
  {Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ}
  {Aᵢ' : Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'} {Aₒ' : Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'} 
  (f : PMor Aᵢ  Aₒ) →
  (g : PMor Aᵢ' Aₒ') →
  (c : PRel Aₒ Aₒ' ℓc) →
  PRel Aᵢ Aᵢ' ℓc
functionalRel f g c = record {
  R = λ x' y' -> PRel.R c (PMor.f f x') (PMor.f g y') ;
  is-prop-valued = λ x' y' -> PRel.is-prop-valued c (PMor.f f x') (PMor.f g y') ;
  is-antitone = λ {x'1} {x'2} {y}   x'1≤x'2 H → PRel.is-antitone c (PMor.isMon f x'1≤x'2) H ;
  is-monotone = λ {x'}  {y'1} {y'2} H y'1≤y'2 → PRel.is-monotone c H (PMor.isMon g y'1≤y'2) }

-- Lifting a P relation to a higher universe level
LiftPRel : {ℓc ℓc' : Level} {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} (R : PRel A₁ A₂ ℓc) ->
  PRel A₁ A₂ (ℓ-max ℓc ℓc')
LiftPRel {ℓc' = ℓc'} R = record {
  R = λ x y → Lift {j = ℓc'} (R .PRel.R x y) ;
  is-prop-valued = λ x y -> isOfHLevelLift 1 (R .PRel.is-prop-valued x y) ;
  is-antitone = λ x'≤x xRy -> lift (R .PRel.is-antitone x'≤x (lower xRy)) ;
  is-monotone = λ xRy y≤y' -> lift (R .PRel.is-monotone (lower xRy) y≤y') }




predomrel-transport : {A₁ A₁' : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ A₂' : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} →
  {c : PRel A₁ A₂ ℓc} →
  {c' : PRel A₁' A₂' ℓc} →
  (eq₁ : A₁ ≡ A₁') →
  (eq₂ : A₂ ≡ A₂') →
  (PathP (λ i → PRel (eq₁ i) (eq₂ i) ℓc) c c') →
  ∀ x y →
  c  .R x y →
  c' .R (transport (cong fst eq₁) x) (transport (cong fst eq₂) y)
predomrel-transport eq₁ eq₂ path x y xRy =
  transport
    (λ i → (path i) .R
      (transport-filler (λ j → ⟨ eq₁ j ⟩) x i)
      (transport-filler (λ j → ⟨ eq₂ j ⟩) y i))
    xRy



-- Action of transport on predomain relations
relTransport :
  {A₁ A₁' : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁}
  {A₂ A₂' : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} →
  (eq₁ : A₁ ≡ A₁') →
  (eq₂ : A₂ ≡ A₂') →
  (c : PRel A₁ A₂ ℓc) →
  PRel A₁' A₂' ℓc
relTransport eq₁ eq₂ c =
  functionalRel (mTransport (sym eq₁)) (mTransport (sym eq₂)) c

{-
-- Isomorphism induces a relation
module _ (A : Predomain ℓA ℓ≤A ℓ≈A) (A' : Predomain ℓA' ℓ≤A' ℓ≈A')
         (isom : Iso ⟨ A ⟩ ⟨ A' ⟩)
  where

  open Iso
  private
    module isom = Iso isom
    module A' = PredomainStr (A' .snd)

  Iso→Rel : PRel A A' {!!}
  Iso→Rel = functionalRel {!!} {!!} {!!}

  -- Iso→Rel : PRel A A' {!!}
  -- Iso→Rel .R x y = (isom.fun x) A'.≤ y
  -- Iso→Rel .is-prop-valued x y = {!A'.is!}
  -- Iso→Rel .is-antitone = {!!}
  -- Iso→Rel .is-monotone = {!!}
-}

-- Action of Σ on predomain relations
ΣR : (X : hSet ℓX) → {ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓc : Level} →
  (A₁ : ⟨ X ⟩ → Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁) →
  (A₂ : ⟨ X ⟩ → Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) →
  (rs : (x : ⟨ X ⟩) → PRel (A₁ x) (A₂ x) ℓc) →
  PRel (ΣP X A₁) (ΣP X A₂) (ℓ-max ℓX ℓc)
  
ΣR X A₁ A₂ rs .R (x₁ , a₁) (x₂ , a₂) =
  Σ[ eq ∈ (x₁ ≡ x₂) ] (rs x₂ .R (subst (λ x → ⟨ A₁ x ⟩) eq a₁) a₂)
  
ΣR X A₁ A₂ rs .is-prop-valued (x₁ , a₁) (x₂ , a₂) =
  isPropΣ (X .snd x₁ x₂) (λ eq → rs x₂ .is-prop-valued _ _)
  
ΣR X A₁ A₂ rs .is-antitone
  {x' = (x₁' , a₁')} {x = (x₁ , a₁)} {y = (x₂ , a₂)}
  (eq , a₁'≤a₁) (eq' , a₁Ra₂) =
  (eq ∙ eq') ,
  rs x₂ .is-antitone lem a₁Ra₂

  where
    T₁ : ⟨ X ⟩ → Type _
    T₁ x = ⟨ A₁ x ⟩

    T₂ : ⟨ X ⟩ → Type _
    T₂ x = ⟨ A₂ x ⟩

    _⊑Ax₂_ = A₁ x₂ .snd .PredomainStr._≤_

    lem : (subst T₁ (eq ∙ eq') a₁') ⊑Ax₂ (subst T₁ eq' a₁)
    lem = subst
      (λ z → z ⊑Ax₂ subst T₁ eq' a₁)
      (sym (substComposite T₁ eq eq' a₁'))
      (rel-transport-≤ {A = A₁ x₁} {B = A₁ x₂} (cong A₁ eq') a₁'≤a₁)
      -- NTS (subst T₁ eq' (subst T₁ eq a₁'))  ⊑Ax₂  (subst T₁ eq' a₁)
      -- STS               (subst T₁ eq a₁')   ⊑Ax₁  a₁

ΣR X A₁ A₂ rs .is-monotone
  {x = (x₁ , a₁)} {y = (x₂ , a₂)} {y' = (x₂' , a₂')}
  (eq , a₁Ra₂) (eq' , a₁≤a₂') =
  (eq ∙ eq') ,
  rs x₂' .is-monotone lem a₁≤a₂'

  where
    T₁ : ⟨ X ⟩ → Type _
    T₁ x = ⟨ A₁ x ⟩

    T₂ : ⟨ X ⟩ → Type _
    T₂ x = ⟨ A₂ x ⟩

    lem : rs x₂' .R (subst T₁ (eq ∙ eq') a₁) (subst T₂ eq' a₂)
    lem = subst
      (λ z → rs x₂' .R z (subst T₂ eq' a₂))
      (sym (substComposite T₁ eq eq' a₁))
      (predomrel-transport {c = rs x₂} {c' = rs x₂'} (cong A₁ eq') (cong A₂ eq') (cong rs eq') (subst T₁ eq a₁) a₂ a₁Ra₂)   


-- Action of Π on predomain relations
ΠR : (X : Type ℓX) {ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓc : Level} →
  (A₁ : X → Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁) →
  (A₂ : X → Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) →
  (rs : (x : X) → PRel (A₁ x) (A₂ x) ℓc) →
  PRel (ΠP X A₁) (ΠP X A₂) (ℓ-max ℓX ℓc)
ΠR X A₁ A₂ rs .R as bs =
  ∀ x → rs x .R (as x) (bs x)
ΠR X A₁ A₂ rs .is-prop-valued as bs =
  isPropΠ (λ x → rs x .is-prop-valued _ _)
ΠR X A₁ A₂ rs .is-antitone {x' = as'} {x = as} {y = bs} as'≤as as-R-bs =
  λ x → rs x .is-antitone (as'≤as x) (as-R-bs x)
ΠR X A₁ A₂ rs .is-monotone {x = as} {y = bs} {y' = bs'} as-R-bs bs≤bs' =
  λ x → rs x .is-monotone (as-R-bs x) (bs≤bs' x)


-- Relations induced by inl and inr
⊎-inl :
  (A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁) 
  (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) →
  PRel A₁ (A₁ ⊎p A₂) (ℓ-max ℓ≤A₁ ℓ≤A₂)
⊎-inl A₁ A₂ = functionalRel (σ1 {B = A₂}) Id (idPRel (A₁ ⊎p A₂))

⊎-inr :
  (A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁) 
  (A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂) →
  PRel A₂ (A₁ ⊎p A₂) (ℓ-max ℓ≤A₁ ℓ≤A₂)
⊎-inr A₁ A₂ = functionalRel (σ2 {A = A₁}) Id (idPRel (A₁ ⊎p A₂))


module _ {k : Clock} (A : Predomain ℓA ℓ≤A ℓ≈A) where

  open Clocked k
  open ClockedCombinators k

  -- Relation between A and ▹ A defined by
  -- x  (relNext A)  y~  iff  (next x)  r(▹A)  y~
  -- i.e. ▸ₜ[ x  r(A)  (y~ t) ]
  relNext : PRel A (P▹ A) ℓ≤A
  relNext = functionalRel Next Id (idPRel (P▹ A))
