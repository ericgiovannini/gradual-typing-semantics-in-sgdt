{-# OPTIONS --guarded --rewriting #-}


-- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Concrete.DoublePoset.DPMorRelation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Binary
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.PropositionalTruncation renaming (rec to PTrec)


open import Common.Common
open import Common.LaterProperties
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Convenience
open import Semantics.Concrete.DoublePoset.Constructions as Predomain
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.DPMorProofs
open import Semantics.Concrete.DoublePoset.DblPosetCombinators

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

    X : PosetBisim ℓX ℓ'X ℓ''X
    Y : PosetBisim ℓY ℓ'Y ℓ''Y


-- Horizontal morphisms
record PBRel (X : PosetBisim ℓX ℓ'X ℓ''X) (Y : PosetBisim ℓY ℓ'Y ℓ''Y) (ℓR : Level) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) (ℓ-suc ℓR)) where
  module X = PosetBisimStr (X .snd)
  module Y = PosetBisimStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    R : ⟨ X ⟩ -> ⟨ Y ⟩ -> Type ℓR
    is-prop-valued : (x : ⟨ X ⟩) -> (y : ⟨ Y ⟩) -> isProp (R x y)
    is-antitone : ∀ {x' x y} -> x' ≤X x -> R x y -> R x' y
    is-monotone : ∀ {x y y'} -> R x y -> y ≤Y y' -> R x y'

  _rel_ : ⟨ X ⟩ → ⟨ Y ⟩ → Type ℓR
  _rel_ = R

open PBRel hiding (module X ; module Y ; _≤X_ ; _≤Y_)

record PBRel' (X : PosetBisim ℓX ℓ'X ℓ''X) (Y : PosetBisim ℓY ℓ'Y ℓ''Y) (ℓR : Level) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓ'X) (ℓ-max ℓY ℓ'Y)) (ℓ-suc ℓR)) where
  module X = PosetBisimStr (X .snd)
  module Y = PosetBisimStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    R : ⟨ X ⟩ -> ⟨ Y ⟩ -> hProp ℓR
    is-antitone : ∀ x' x y -> x' ≤X x -> ⟨ R x y ⟩ -> ⟨ R x' y ⟩
    is-monotone : ∀ x y y' -> ⟨ R x y ⟩ -> y ≤Y y' -> ⟨ R x y' ⟩


-- Iso between PBRel and PBRel'
PBRelIsoPBRel' : ∀ {A : PosetBisim ℓA ℓ≤A ℓ≈A} {A' : PosetBisim ℓA' ℓ≤A' ℓ≈A'} →
  Iso (PBRel A A' ℓc) (PBRel' A A' ℓc)
PBRelIsoPBRel' = iso
  (λ S -> record {
    R = λ x y -> S .PBRel.R x y , S .PBRel.is-prop-valued x y ;
    is-antitone = λ x' x y x'≤x xSy → S .PBRel.is-antitone x'≤x xSy ;
    is-monotone = λ x y y' xSy y≤y' → S .PBRel.is-monotone xSy y≤y' })

  (λ S → record {
    R = λ x y -> fst (S .PBRel'.R x y) ;
    is-prop-valued = λ x y -> snd (S .PBRel'.R x y) ;
    is-antitone = λ {x'} {x} {y} x'≤x xSy →
      S .PBRel'.is-antitone x' x y x'≤x xSy ;
    is-monotone = λ {x} {y} {y'} xSy y≤y' ->
      S .PBRel'.is-monotone x y y' xSy y≤y' })

  (λ b → refl)

  (λ a → refl)


  -- Equivalence between PBRel' record and a sigma type   
unquoteDecl PBRel'IsoΣ = declareRecordIsoΣ PBRel'IsoΣ (quote (PBRel'))


-- PBRel' is a Set
isSetPBRel' : {A : PosetBisim ℓA ℓ≤A ℓ≈A} {A' : PosetBisim ℓA' ℓ≤A' ℓ≈A'} → isSet (PBRel' A A' ℓc)
isSetPBRel' = isSetRetract
  (Iso.fun PBRel'IsoΣ) (Iso.inv PBRel'IsoΣ)
  (Iso.leftInv PBRel'IsoΣ)
    (isSetΣSndProp
      (isSetΠ2 (λ _ _ -> isSetHProp))
      (λ R -> isProp× (isPropΠ5 (λ _ _ _ _ _ -> snd (R _ _)))
                      (isPropΠ5 (λ _ _ _ _ _ -> snd (R _ _)))))


-- PBRel is a Set
isSetPBRel : {A : PosetBisim ℓA ℓ≤A ℓ≈A} {A' : PosetBisim ℓA' ℓ≤A' ℓ≈A'} → isSet (PBRel X Y ℓR)
isSetPBRel = isSetRetract
  (Iso.fun PBRelIsoPBRel') (Iso.inv PBRelIsoPBRel')
  (Iso.leftInv PBRelIsoPBRel') isSetPBRel'

-- Equality of horizontal morphisms follows from equality of the underlying relations.

eqPBRel : {A : PosetBisim ℓA ℓ≤A ℓ≈A} {A' : PosetBisim ℓA' ℓ≤A' ℓ≈A'} -> (c c' : PBRel A A' ℓc) ->
  PBRel.R c ≡ PBRel.R c' -> c ≡ c'
eqPBRel {A = A} {A' = A'} c c' eq =
  isoFunInjective PBRelIsoPBRel' c c' (eqPBRel' _ _  eq1)
  where
    eq1 : (λ x y → c .R x y , c .is-prop-valued x y) ≡ (λ x y → c' .R x y , c' .is-prop-valued x y)
    eq1 = funExt (λ x → funExt (λ y → Σ≡Prop (λ _ → isPropIsProp) ((funExt⁻ (funExt⁻ eq x) y))))

    eqPBRel' : (c c' : PBRel' A A' ℓc) -> PBRel'.R c ≡ PBRel'.R c' -> c ≡ c'
    eqPBRel' c c' eq =
      isoFunInjective PBRel'IsoΣ c c'
        (Σ≡Prop (λ R → isProp× (isPropΠ5 (λ _ _ _ _ _ → snd (R _ _)))
                               (isPropΠ5 (λ _ _ _ _ _ → snd (R _ _))))
                 eq)


-- Identity relation
posetbisim-monrel : {ℓo : Level} -> (X : PosetBisim ℓ ℓ' ℓ'') -> PBRel X X (ℓ-max ℓ' ℓo)
posetbisim-monrel {ℓ' = ℓ'} {ℓo = ℓo} X = record {
  R = λ x x' -> Lift {i = ℓ'} {j = ℓo} (rel-≤ X x x') ;
  is-prop-valued = λ x x' -> isOfHLevelLift 1 (prop-valued-≤ X x x') ;
  is-antitone = λ {x'} {x} {y}  x'≤x x≤y -> lift (transitive-≤ X x' x y x'≤x (lower x≤y)) ;
  is-monotone = λ {x}  {y} {y'} x≤y y≤y' -> lift (transitive-≤ X x y y' (lower x≤y) y≤y') }


idPRel : (X : PosetBisim ℓ ℓ' ℓ'') -> PBRel X X ℓ'
idPRel {ℓ' = ℓ'}  X = record {
  R = λ x x' -> (rel-≤ X x x') ;
  is-prop-valued = λ x x' -> (prop-valued-≤ X x x') ;
  is-antitone = λ {x'} {x} {y}  x'≤x x≤y -> (transitive-≤ X x' x y x'≤x x≤y) ;
  is-monotone = λ {x}  {y} {y'} x≤y y≤y' -> (transitive-≤ X x y y' x≤y y≤y') }


-- idRel : (ℓo : Level) -> (X : PosetBisim ℓ ℓ' ℓ'') -> PBRel X X (ℓ-max ℓ' ℓo)
-- idRel ℓo = posetbisim-monrel {ℓo = ℓo}



-- Composition of relations

-- Composing pedomain relations
-- Note that becasue of the quantification over elements of Y,
-- the universe level of the resulting relation involves an
-- ℓ-max with ℓA₂ (i.e. the level of the elements in A₂)
_⊙_ : 
  {A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₃ : PosetBisim ℓA₃ ℓ≤A₃ ℓ≈A₃} ->
  PBRel A₁ A₂ ℓc₁ ->
  PBRel A₂ A₃ ℓc₂ ->
  PBRel A₁ A₃ (ℓ-max ℓA₂ (ℓ-max ℓc₁ ℓc₂))
_⊙_ {A₁ = A₁} {A₂ = A₂} {A₃ = A₃} c₁ c₂ = record {
  R = λ x z -> ∥ compRel (PBRel.R c₁) (PBRel.R c₂) x z ∥₁ ;
  is-prop-valued = λ x z -> isPropPropTrunc ;
  is-antitone = λ x'≤x H -> elim (λ _ -> isPropPropTrunc) (λ p -> ∣ comp-antitone x'≤x p ∣₁) H ;
  is-monotone = λ H y≤y' -> PTrec isPropPropTrunc (λ p → ∣ comp-monotone p y≤y' ∣₁) H }
    where

      module A₁ = PosetBisimStr (A₁ .snd)
      module A₃ = PosetBisimStr (A₃ .snd)
      
      module c₁ = PBRel c₁
      module c₂ = PBRel c₂

      comp-antitone : {x' x : ⟨ A₁ ⟩} {z : ⟨ A₃ ⟩} ->
         x' A₁.≤ x ->
        compRel (PBRel.R c₁) (PBRel.R c₂) x z ->
        compRel (PBRel.R c₁) (PBRel.R c₂) x' z 
      comp-antitone x'≤x (y , xc₁y , yc₂z) = y , (PBRel.is-antitone c₁ x'≤x xc₁y) , yc₂z

      comp-monotone : {x : ⟨ A₁ ⟩} {z z' : ⟨ A₃ ⟩} ->
        compRel (PBRel.R c₁) (PBRel.R c₂) x z ->
        z A₃.≤ z' ->
        compRel (PBRel.R c₁) (PBRel.R c₂) x z'
      comp-monotone (y , xc₁y , yc₂z) z≤z' = y , xc₁y , (PBRel.is-monotone c₂ yc₂z z≤z')





-- Exponential of relations

_==>pbmonrel_ :
  {Aᵢ : PosetBisim ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aᵢ' : PosetBisim ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
  {Aₒ : PosetBisim ℓAₒ ℓ≤Aₒ ℓ≈Aₒ} {Aₒ' : PosetBisim ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'} ->
  PBRel Aᵢ Aᵢ' ℓcᵢ ->
  PBRel Aₒ Aₒ' ℓcₒ ->
  PBRel (Aᵢ ==> Aₒ) (Aᵢ' ==> Aₒ') (ℓ-max (ℓ-max ℓAᵢ ℓAᵢ') (ℓ-max ℓcᵢ ℓcₒ))
cᵢ ==>pbmonrel cₒ = record {
  R = λ f g ->
    TwoCell (PBRel.R cᵢ) (PBRel.R cₒ) (PBMor.f f) (PBMor.f g)  ;
  is-prop-valued = λ f g -> isPropTwoCell (cₒ .PBRel.is-prop-valued) ;
  is-antitone = λ {f1} {f2} {g} f1≤f2 f1≤g  a b aRb →
    cₒ .PBRel.is-antitone (f1≤f2 a) (f1≤g a b aRb) ;
  is-monotone = λ {f} {g1} {g2} f≤g1 g1≤g2 a b aRb →
    cₒ .PBRel.is-monotone (f≤g1 a b aRb) (g1≤g2 b) }

_×pbmonrel_ :   {A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : PosetBisim ℓA₁' ℓ≤A₁' ℓ≈A₁'}
  {A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : PosetBisim ℓA₂' ℓ≤A₂' ℓ≈A₂'} ->
  PBRel A₁ A₁' ℓc₁ ->
  PBRel A₂ A₂' ℓc₂ ->
  PBRel (A₁ ×dp A₂) (A₁' ×dp A₂') _
c₁ ×pbmonrel c₂ = record
  { R = λ p q → c₁ .R (p .fst) (q .fst) × c₂ .R (p .snd) (q .snd)
  ; is-prop-valued = λ _ _ → isProp× (c₁ .is-prop-valued _ _) (c₂ .is-prop-valued _ _)
  ; is-antitone = λ x x₁ → (c₁ .is-antitone (x .fst) (x₁ .fst)) , c₂ .is-antitone (x .snd) (x₁ .snd)
  ; is-monotone = λ x x₁ → (c₁ .is-monotone (x .fst) (x₁ .fst)) , c₂ .is-monotone (x .snd) (x₁ .snd) }

-- Composing with vertical morphisms on either side

functionalRel :
  {Aᵢ : PosetBisim ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aₒ : PosetBisim ℓAₒ ℓ≤Aₒ ℓ≈Aₒ}
  {Aᵢ' : PosetBisim ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'} {Aₒ' : PosetBisim ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'} 
  (f : PBMor Aᵢ  Aₒ) →
  (g : PBMor Aᵢ' Aₒ') →
  (c : PBRel Aₒ Aₒ' ℓc) →
  PBRel Aᵢ Aᵢ' ℓc
functionalRel f g c = record {
  R = λ x' y' -> PBRel.R c (PBMor.f f x') (PBMor.f g y') ;
  is-prop-valued = λ x' y' -> PBRel.is-prop-valued c (PBMor.f f x') (PBMor.f g y') ;
  is-antitone = λ {x'1} {x'2} {y}   x'1≤x'2 H → PBRel.is-antitone c (PBMor.isMon f x'1≤x'2) H ;
  is-monotone = λ {x'}  {y'1} {y'2} H y'1≤y'2 → PBRel.is-monotone c H (PBMor.isMon g y'1≤y'2) }

-- Lifting a PB relation to a higher universe level
LiftPBRel : {ℓc ℓc' : Level} {A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂} (R : PBRel A₁ A₂ ℓc) ->
  PBRel A₁ A₂ (ℓ-max ℓc ℓc')
LiftPBRel {ℓc' = ℓc'} R = record {
  R = λ x y → Lift {j = ℓc'} (R .PBRel.R x y) ;
  is-prop-valued = λ x y -> isOfHLevelLift 1 (R .PBRel.is-prop-valued x y) ;
  is-antitone = λ x'≤x xRy -> lift (R .PBRel.is-antitone x'≤x (lower xRy)) ;
  is-monotone = λ xRy y≤y' -> lift (R .PBRel.is-monotone (lower xRy) y≤y') }




predomrel-transport : {A₁ A₁' : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ A₂' : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂} →
  {c : PBRel A₁ A₂ ℓc} →
  {c' : PBRel A₁' A₂' ℓc} →
  (eq₁ : A₁ ≡ A₁') →
  (eq₂ : A₂ ≡ A₂') →
  (PathP (λ i → PBRel (eq₁ i) (eq₂ i) ℓc) c c') →
  ∀ x y →
  c  .R x y →
  c' .R (transport (cong fst eq₁) x) (transport (cong fst eq₂) y)
predomrel-transport eq₁ eq₂ path x y xRy =
  transport
    (λ i → (path i) .R
      (transport-filler (λ j → ⟨ eq₁ j ⟩) x i)
      (transport-filler (λ j → ⟨ eq₂ j ⟩) y i))
    xRy


-- Action of Σ on predomain relations
ΣR : (X : hSet ℓX) → {ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓc : Level} →
  (A₁ : ⟨ X ⟩ → PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁) →
  (A₂ : ⟨ X ⟩ → PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂) →
  (rs : (x : ⟨ X ⟩) → PBRel (A₁ x) (A₂ x) ℓc) →
  PBRel (ΣP X A₁) (ΣP X A₂) (ℓ-max ℓX ℓc)
  
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

    _⊑Ax₂_ = A₁ x₂ .snd .PosetBisimStr._≤_

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
  (A₁ : X → PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁) →
  (A₂ : X → PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂) →
  (rs : (x : X) → PBRel (A₁ x) (A₂ x) ℓc) →
  PBRel (ΠP X A₁) (ΠP X A₂) (ℓ-max ℓX ℓc)
ΠR X A₁ A₂ rs .R as bs =
  ∀ x → rs x .R (as x) (bs x)
ΠR X A₁ A₂ rs .is-prop-valued as bs =
  isPropΠ (λ x → rs x .is-prop-valued _ _)
ΠR X A₁ A₂ rs .is-antitone {x' = as'} {x = as} {y = bs} as'≤as as-R-bs =
  λ x → rs x .is-antitone (as'≤as x) (as-R-bs x)
ΠR X A₁ A₂ rs .is-monotone {x = as} {y = bs} {y' = bs'} as-R-bs bs≤bs' =
  λ x → rs x .is-monotone (as-R-bs x) (bs≤bs' x)


module _ {k : Clock} (A : PosetBisim ℓA ℓ≤A ℓ≈A) where

  open Clocked k
  open ClockedCombinators k

  -- Relation between A and ▹ A defined by
  -- x  (relNext A)  y~  iff  (next x)  r(▹A)  y~
  -- i.e. ▸ₜ[ x  r(A)  (y~ t) ]
  relNext : PBRel A (PB▹ A) ℓ≤A
  relNext = functionalRel Next Id (idPRel (PB▹ A))
