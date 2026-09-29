{-# OPTIONS --cubical --rewriting --guarded #-}

{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.Proofs where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism


open import Cubical.Relation.Binary
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Empty hiding (elim)
open import Cubical.Data.Sum hiding (elim)
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_^_ ; elim)

open import Common.Common

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Convenience
-- open import Semantics.Concrete.Predomain.Constructions
open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓR ℓR1 ℓR2 : Level
    ℓA ℓ'A ℓ''A ℓA' ℓ'A' ℓ''A' : Level
    ℓB ℓ'B ℓ''B ℓB' ℓ'B' ℓ''B' : Level
    ℓC ℓ'C ℓ''C ℓC' ℓ'C' ℓ''C' ℓΓ ℓ'Γ ℓ''Γ : Level
    Γ :  Predomain ℓΓ ℓ'Γ ℓ''Γ
    A :  Predomain ℓA ℓ'A ℓ''A
    A' : Predomain ℓA' ℓ'A' ℓ''A'
    B :  Predomain ℓB ℓ'B ℓ''B
    B' : Predomain ℓB' ℓ'B' ℓ''B'
    C :  Predomain ℓC ℓ'C ℓ''C
    C' : Predomain ℓC' ℓ'C' ℓ''C'
    ℓRA ℓRB : Level


transport-rel :
  {A B : Type ℓ}
  (eq : A ≡ B) →
  (RA : Rel A A ℓR) →
  (RB : Rel B B ℓR) →
  (PathP (λ i → Rel (eq i) (eq i) ℓR) RA RB) →
  {x y : A} →
  (RA x y) →
  RB (transport eq x) (transport eq y)
transport-rel eq RA RB path {x = x} {y = y} xRy =
  transport (λ i → (path i) (transport-filler eq x i) (transport-filler eq y i)) xRy

transport-rel-lemma :
  {A B : Type ℓ}
  (eq : A ≡ B) →
  (RA : Rel A A ℓR) →
  (RB : Rel B B ℓR) →
  (PathP (λ i → Rel (eq i) (eq i) ℓR) RA RB) →
  {x : A} {y : B} →
  RA x (transport (λ i → eq (~ i)) y) →
  RB (transport (λ i → eq i) x) y
transport-rel-lemma eq RA RB path {x = x} {y = y} xRy =
  subst (λ x → RB ab x) (transportTransport⁻ eq y) lem
  where
    ab = transport eq x
    bab = transport eq (transport (sym eq) y)
    
    lem : RB ab bab
    lem = transport-rel eq RA RB path xRy

rel-transport-≤ :
  {A B : Predomain ℓ ℓ' ℓ''} ->
  (eq : A ≡ B) ->
  {a1 a2 : ⟨ A ⟩} ->
  rel-≤ A a1 a2 ->
  rel-≤ B (transport (λ i -> ⟨ eq i ⟩) a1) (transport (λ i -> ⟨ eq i ⟩) a2)
rel-transport-≤ {A} {B} eq {a1} {a2} a1≤a2 =
  transport (λ i → rel-≤ (eq i)
    (transport-filler (λ j → ⟨ eq j ⟩) a1 i)
    (transport-filler (λ j → ⟨ eq j ⟩) a2 i))
  a1≤a2

rel-transport-≈ :
  {A B : Predomain ℓ ℓ' ℓ''} ->
  (eq : A ≡ B) ->
  {a1 a2 : ⟨ A ⟩} ->
  rel-≈ A a1 a2 ->
  rel-≈ B (transport (λ i -> ⟨ eq i ⟩) a1) (transport (λ i -> ⟨ eq i ⟩) a2)
rel-transport-≈ {A} {B} eq {a1} {a2} a1≤a2 =
  transport (λ i → rel-≈ (eq i)
    (transport-filler (λ j → ⟨ eq j ⟩) a1 i)
    (transport-filler (λ j → ⟨ eq j ⟩) a2 i))
  a1≤a2


rel-transport-≤-lemma :
  {A B : Predomain ℓ ℓ' ℓ''} →
  (eq : A ≡ B) →
  {a : ⟨ A ⟩} {b : ⟨ B ⟩} →
  rel-≤ A a (transport (λ i → ⟨ eq (~ i) ⟩) b) →
  rel-≤ B (transport (λ i → ⟨ eq i ⟩) a) b
rel-transport-≤-lemma {A = A} {B = B} eq {a = a} {b = b} H =
  subst (λ x → rel-≤ B ab x) (transportTransport⁻ (cong fst eq) b) lem
  where
    ab = transport (λ i → ⟨ eq i ⟩) a
    bab = transport (λ i → ⟨ eq i ⟩) (transport (λ i → ⟨ eq (~ i) ⟩) b)
    
    lem : rel-≤ B ab bab
    lem = rel-transport-≤ eq H

rel-transport-≈-lemma :
  {A B : Predomain ℓ ℓ' ℓ''} →
  (eq : A ≡ B) →
  {a : ⟨ A ⟩} {b : ⟨ B ⟩} →
  rel-≈ A a (transport (λ i → ⟨ eq (~ i) ⟩) b) →
  rel-≈ B (transport (λ i → ⟨ eq i ⟩) a) b
rel-transport-≈-lemma {A = A} {B = B} eq {a = a} {b = b} H =
  subst (λ x → rel-≈ B ab x) (transportTransport⁻ (cong fst eq) b) lem
  where
    ab = transport (λ i → ⟨ eq i ⟩) a
    bab = transport (λ i → ⟨ eq i ⟩) (transport (λ i → ⟨ eq (~ i) ⟩) b)
    
    lem : rel-≈ B ab bab
    lem = rel-transport-≈ eq H



rel-transport-sym-≤ : {A B : Predomain ℓ ℓ' ℓ''} ->
  (eq : A ≡ B) ->
  {b1 b2 : ⟨ B ⟩} ->
  rel-≤ B b1 b2 ->
  rel-≤ A
    (transport (λ i → ⟨ sym eq i ⟩) b1)
    (transport (λ i → ⟨ sym eq i ⟩) b2)
rel-transport-sym-≤ eq {b1} {b2} b1≤b2 = rel-transport-≤ (sym eq) b1≤b2

rel-transport-sym-≈ : {A B : Predomain ℓ ℓ' ℓ''} ->
  (eq : A ≡ B) ->
  {b1 b2 : ⟨ B ⟩} ->
  rel-≈ B b1 b2 ->
  rel-≈ A
    (transport (λ i → ⟨ sym eq i ⟩) b1)
    (transport (λ i → ⟨ sym eq i ⟩) b2)
rel-transport-sym-≈ eq {b1} {b2} b1≤b2 = rel-transport-≈ (sym eq) b1≤b2

mon-transport-domain-≤ : {A B C : Predomain ℓ ℓ' ℓ''} ->
  (eq : A ≡ B) ->
  (f : PMor A C) ->
  {b1 b2 : ⟨ B ⟩} ->
  (rel-≤ B b1 b2) ->
  rel-≤ C
    (PMor.f f (transport (λ i → ⟨ sym eq i ⟩ ) b1))
    (PMor.f f (transport (λ i → ⟨ sym eq i ⟩ ) b2))
mon-transport-domain-≤ eq f {b1} {b2} b1≤b2 =
  PMor.isMon f (rel-transport-≤ (sym eq) b1≤b2)

mon-transport-domain-≈ : {A B C : Predomain ℓ ℓ' ℓ''} ->
  (eq : A ≡ B) ->
  (f : PMor A C) ->
  {b1 b2 : ⟨ B ⟩} ->
  (rel-≈ B b1 b2) ->
  rel-≈ C
    (PMor.f f (transport (λ i → ⟨ sym eq i ⟩ ) b1))
    (PMor.f f (transport (λ i → ⟨ sym eq i ⟩ ) b2))
mon-transport-domain-≈ eq f {b1} {b2} b1≤b2 =
  PMor.pres≈ f (rel-transport-≈ (sym eq) b1≤b2)


module ClockedProofs (k : Clock) where
  -- open import Semantics.Lift k
  -- open import Semantics.LockStepErrorOrdering k
  --open import Semantics.WeakBisimilarity k
  --open import Semantics.Concrete.Predomain.LockStepErrorBisim k
  --open LiftPredomain
  
{-
  private
    ▹_ : Type ℓ → Type ℓ
    ▹_ A = ▹_,_ k A

  ret-monotone-het-≤ : {A A' : Predomain ℓA ℓ'A ℓ''A} ->
    (rAA' : ⟨ A ⟩ -> ⟨ A' ⟩ -> Type ℓR1) ->
    TwoCell rAA' (LiftRelation._≾_ _ _ rAA') ret ret
  ret-monotone-het-≤ {A = A} {A' = A'} rAA' = λ a a' a≤a' →
    LiftRelation.Properties.ord-η-monotone ⟨ A ⟩ ⟨ A' ⟩ rAA' a≤a'

  ret-monotone-≤ : {A : Predomain ℓA ℓ'A ℓ''A} ->
    (a a' : ⟨ A ⟩) ->
    rel-≤ A a a' ->
    rel-≤ (𝕃 A) (ret a) (ret a')
  ret-monotone-≤ {A = A} = λ a a' a≤a' →
    LiftRelation.Properties.ord-η-monotone ⟨ A ⟩ ⟨ A ⟩ _ a≤a'

  ret-monotone-≈ : {A : Predomain ℓA ℓ'A ℓ''A} ->
    (a a' : ⟨ A ⟩) ->
    rel-≈ A a a' ->
    rel-≈ (𝕃 A) (ret a) (ret a')
  ret-monotone-≈ {A = A} = λ a a' a≤a' → {!!}
    where
      module LBisim = Bisim (⟨ A ⟩ ⊎ Unit) (rel-≈ (A ⊎p UnitPB))

  ext-monotone-het-≤ : {A A' : Predomain ℓA ℓ'A ℓ''A} {B B' : Predomain ℓB ℓ'B ℓ''B}
    (rAA' : ⟨ A ⟩ -> ⟨ A' ⟩ -> Type ℓR1) ->
    (rBB' : ⟨ B ⟩ -> ⟨ B' ⟩ -> Type ℓR2) ->
    (f :  ⟨ A ⟩  -> ⟨ (𝕃 B) ⟩) ->
    (f' : ⟨ A' ⟩ -> ⟨ (𝕃 B') ⟩) ->
    TwoCell rAA' (LiftRelation._≾_ _ _ rBB') f f' ->
    (la : ⟨ 𝕃 A ⟩) -> (la' : ⟨ 𝕃 A' ⟩) ->
    (LiftRelation._≾_ _ _ rAA' la la') ->
    LiftRelation._≾_ _ _ rBB' (ext f la) (ext f' la')
  ext-monotone-het-≤ {A = A} {A' = A'} {B = B} {B' = B'} rAA' rBB' f f' f≤f' la la' la≤la' = let fixed = fix (monotone-ext') in
    transport
      (sym (λ i -> LiftBB'.unfold-≾ i (unfold-ext f i la) (unfold-ext f' i la')))
      (fixed la la' (transport (λ i → LiftAA'.unfold-≾ i la la') la≤la'))
    where
      _≾'LA_  = LiftPredomain._≾'_ A
      _≾'LA'_ = LiftPredomain._≾'_ A'
      _≾'LB_  = LiftPredomain._≾'_ B
      _≾'LB'_ = LiftPredomain._≾'_ B'

      module LiftAA' = LiftRelation ⟨ A ⟩ ⟨ A' ⟩ rAA'
      module LiftBB' = LiftRelation ⟨ B ⟩ ⟨ B' ⟩ rBB'

      _≾'LALA'_ = LiftAA'.Inductive._≾'_ (next LiftAA'._≾_)
      _≾'LBLB'_ = LiftBB'.Inductive._≾'_ (next LiftBB'._≾_)
  
      monotone-ext' :
        ▹ (
            (la : ⟨ 𝕃 A ⟩) -> (la' : ⟨ 𝕃 A' ⟩)  ->
            (la ≾'LALA' la') ->
            (ext' f  (next (ext f))  la) ≾'LBLB'
            (ext' f' (next (ext f')) la')) ->
          (la : ⟨ 𝕃 A ⟩) -> (la' : ⟨ 𝕃 A' ⟩)  ->
          (la ≾'LALA' la') ->
          (ext' f  (next (ext f))  la) ≾'LBLB'
          (ext' f' (next (ext f')) la')
      monotone-ext' IH (η x) (η y) x≤y =
        transport
        (λ i → LiftBB'.unfold-≾ i (f x) (f' y))
        (f≤f' x y x≤y)
      monotone-ext' IH ℧ la' la≤la' = tt*
      monotone-ext' IH (θ lx~) (θ ly~) la≤la' = λ t ->
        transport
          (λ i → (sym (LiftBB'.unfold-≾)) i
            (sym (unfold-ext f) i (lx~ t))
            (sym (unfold-ext f') i (ly~ t)))
          (IH t (lx~ t) (ly~ t)
            (transport (λ i -> LiftAA'.unfold-≾ i (lx~ t) (ly~ t)) (la≤la' t)))

  --temporarily placed here
  rel-≈L : (A : Predomain ℓA ℓ'A ℓ''A) → L ⟨ A ⟩ → L ⟨ A ⟩ → Type (ℓ-max ℓA ℓ''A)
  rel-≈L A = LBsim._≈_
    where
      module LBsim = Bisim ⟨ A ⟩ (rel-≈ A)
  
  extL-monotone-≈ : {A : Predomain ℓA ℓ'A ℓ''A} {B : Predomain ℓB ℓ'B ℓ''B} ->
    (f g : ⟨ A ⟩ -> L ⟨ B ⟩) ->
    TwoCell (rel-≈ A) (rel-≈L B) f g ->
    (la la' : L ⟨ A ⟩) ->
    (la≈la' : rel-≈L A la la') ->
    rel-≈L B (extL f la) (extL g la')
  extL-monotone-≈ {A = A} {B = B} f g f≈g la la' la≈la' = 
    let fixed = fix extL-monotone-≈' in
    transport
      (sym (λ i → LiftB.unfold-≈ i (unfold-extL f i la) (unfold-extL g i la')))
      (fixed la la' (transport (λ i → LiftA.unfold-≈ i la la') la≈la'))
    where
      module LiftA = Bisim ⟨ A ⟩ (rel-≈ A)
      module LiftB = Bisim ⟨ B ⟩ (rel-≈ B)
      open LiftB.PropValued
      open LiftB.Reflexive
      symA = LiftA.Symmetric.symmetric (sym-≈ A)
      symB = LiftB.Symmetric.symmetric (sym-≈ B)

      _≈'LA_ = LiftA.Inductive._≈'_ (next LiftA._≈_)
      _≈'LB_ = LiftB.Inductive._≈'_ (next LiftB._≈_)

      aux : ∀ ly y' n -> (θ ly ≡ (δL ^ n) (η y')) -> Σ[ n' ∈ Nat ] n ≡ suc n' -- is (η x ≈'LA θ ly) required here?
      aux ly y' n = {!!}

      ηθ-lem : ∀ x ly n y -> (f g : ⟨ A ⟩ -> L ⟨ B ⟩) ->
        (f≈g : TwoCell (rel-≈ A) (rel-≈L B) f g) ->
        θ ly ≡ (δL ^ n) (η y) ->
        rel-≈ A x y -> (f x) ≈'LB (extL' g (next (extL g)) (θ ly))
      ηθ-lem x ly n y f g f≈g θly≡δⁿηy x≈y = let (n' , eq1) = aux ly y n θly≡δⁿηy in
            let eq2 = θ ly ≡⟨ θly≡δⁿηy ⟩ (δL ^ n) (η y) ≡⟨ funExt⁻ (cong₂ _^_ refl eq1) (η y) ⟩ θ (next ((δL ^ n') (η y))) ∎ in
            let eq3 = inj-θL ly (next ((δL ^ n') (η y))) eq2 in
            let eq4 = (θ (λ t -> (extL g (ly t))))
                         ≡⟨ (λ i -> (θ (λ t -> (extL g (eq3 t i))))) ⟩
                      (θ (λ t -> (extL g ((δL ^ n') (η y)))))
                        ≡⟨ cong (θ next) (extL-delay g (η y) n')  ⟩
                      (δL ^ (suc n')) (extL g (η y)) ≡⟨ cong (δL ^ (suc n')) (extL-eta y g) ⟩ (δL ^ (suc n')) (g y) ∎ in
            let fx≈gy = f≈g x y x≈y in
            let last = {!!} in -- last = LiftB.x≈δx' (f x) (g y) fx≈gy
            transport (λ i -> f x ≈'LB sym eq4 i) {!!} 
      
      extL-monotone-≈' :
        ▹ ((la la' : L ⟨ A ⟩) -> la ≈'LA la' ->
        extL' f  (next (extL f)) la ≈'LB extL' g (next (extL g))  la') ->
          (la la' : L ⟨ A ⟩) -> la ≈'LA la' ->
          extL' f  (next (extL f)) la ≈'LB extL' g (next (extL g))  la'
      extL-monotone-≈' IH (η x) (η y) x≈y =
        transport (λ i → LiftB.unfold-≈ i (f x) (g y)) (f≈g x y (lower x≈y))
      extL-monotone-≈' IH (η x) (θ ly) x≈ly = elim
        (λ _ → {!!}) --isProp ((next LiftB._≈_ LiftB.Inductive.≈' f x) (extL' g (next (extL g)) (θ ly)))
        (λ {(n , y , θly≡δⁿηy , x≈y) →
          ηθ-lem x ly n y f g f≈g θly≡δⁿηy x≈y }) x≈ly
      extL-monotone-≈' IH (θ lx) (η y) lx≈y = elim
        (λ _ → prop-≈→prop-≈' (prop-valued-≈ B) (prop (prop-valued-≈ B)) (θ (next (extL f) ⊛ lx)) (g y))
        (λ {(n , x , θlx≡δⁿηx , x≈y) →
          let g≈f = (λ a b a≈b → let fb≈ga = f≈g b a (sym-≈ A a b a≈b) in symB (f b) (g a) fb≈ga) in
          let sym-lem = ηθ-lem y lx n x g f g≈f θlx≡δⁿηx (sym-≈ A x y x≈y) in
          LiftB.≈→≈' (θ (next (extL f) ⊛ lx)) (g y) (symB (g y) (θ (next (extL f) ⊛ lx)) (LiftB.≈'→≈ (g y) (θ (next (extL f) ⊛ lx)) sym-lem)) }) lx≈y
      extL-monotone-≈' IH (θ x) (θ y) x≈y = λ t →
        transport
          (λ i → sym LiftB.unfold-≈ i
            (sym (unfold-extL f) i (x t))
            (sym (unfold-extL g) i (y t)))
          (IH t (x t) (y t)
            (transport (λ i → LiftA.unfold-≈ i (x t) (y t)) (x≈y t)))
      
  

  ext-monotone-≈ : {A : Predomain ℓA ℓ'A ℓ''A} {B : Predomain ℓB ℓ'B ℓ''B} ->
    (f g : ⟨ A ⟩ -> ⟨ (𝕃 B) ⟩) ->
    TwoCell (rel-≈ A) (rel-≈ (𝕃 B)) f g ->
    TwoCell (rel-≈ (𝕃 A)) (rel-≈ (𝕃 B)) (ext f) (ext g)
  ext-monotone-≈ {A = A} {B = B} f g f≈g la la' = fix monotone-ext' la la'
    where

      L℧→LA = L℧A→LA⊎Unit A
      L→L℧A = LA⊎Unit→L℧A A
      L℧→LB = L℧A→LA⊎Unit B
      L→L℧B = LA⊎Unit→L℧A B
      
      f* : ⟨ A ⟩ ⊎ Unit → L℧ ⟨ B ⟩
      f* (inl a) = f a
      f* (inr tt) = ℧

      g* : ⟨ A ⟩ ⊎ Unit → L℧ ⟨ B ⟩
      g* (inl a) = g a
      g* (inr tt) = ℧

      open Iso
      eq' : ▹ ((la : ⟨ 𝕃 A ⟩) -> ext f la ≡ L→L℧B (extL (L℧→LB ∘ f*) (L℧→LA la))) -> (la : ⟨ 𝕃 A ⟩) -> ext f la ≡ L→L℧B (extL (L℧→LB ∘ f*) (L℧→LA la))
      eq' IH (η a) = transport (λ i → unfold-ext f (~ i) (η a) ≡ unfold-L→L℧ B (~ i) (unfold-extL (L℧→LB ∘ f*) (~ i) (unfold-L℧→L A (~ i) (η a))))
         (sym (cong (LA⊎Unit→L℧A' B (next (LA⊎Unit→L℧A B))) (transport (λ i → (refl {x = L℧→LB (f a)} i) ≡ unfold-L℧→L B i (f a)) refl)
         ∙ (λ i → unfold-L→L℧ B (~ i) (unfold-L℧→L B (~ i) (f a))) ∙ L℧ALA⊎Unit-iso B .ret (f a)))
      eq' IH ℧ = transport (λ i → unfold-ext f (~ i) ℧ ≡ unfold-L→L℧ B (~ i) (unfold-extL (L℧→LB ∘ f*) (~ i) (unfold-L℧→L A (~ i) ℧)))
         (sym (cong (LA⊎Unit→L℧A' B (next (LA⊎Unit→L℧A B))) (transport (λ i → (refl {x = L℧→LB ℧} i) ≡ unfold-L℧→L B i ℧) refl)
         ∙ (λ i → unfold-L→L℧ B (~ i) (unfold-L℧→L B (~ i) ℧)) ∙ L℧ALA⊎Unit-iso B .ret ℧))
      eq' IH (θ la~) = transport (λ i → unfold-ext f (~ i) (θ la~) ≡ unfold-L→L℧ B (~ i) (unfold-extL (L℧→LB ∘ f*) (~ i) (unfold-L℧→L A (~ i) (θ la~))))
        λ i → θ (λ t → IH t (la~ t) i)
      
      eq : (la : ⟨ 𝕃 A ⟩) -> ext f la ≡ L→L℧B (extL (L℧→LB ∘ f*) (L℧→LA la))
      eq = fix eq'

      eq1' : ▹ ((la' : ⟨ 𝕃 A ⟩) -> ext g la' ≡ L→L℧B (extL (L℧→LB ∘ g*) (L℧→LA la'))) -> (la' : ⟨ 𝕃 A ⟩) -> ext g la' ≡ L→L℧B (extL (L℧→LB ∘ g*) (L℧→LA la'))
      eq1' IH (η a) = transport (λ i → unfold-ext g (~ i) (η a) ≡ unfold-L→L℧ B (~ i) (unfold-extL (L℧→LB ∘ g*) (~ i) (unfold-L℧→L A (~ i) (η a))))
         (sym (cong (LA⊎Unit→L℧A' B (next (LA⊎Unit→L℧A B))) (transport (λ i → (refl {x = L℧→LB (g a)} i) ≡ unfold-L℧→L B i (g a)) refl)
         ∙ (λ i → unfold-L→L℧ B (~ i) (unfold-L℧→L B (~ i) (g a))) ∙ L℧ALA⊎Unit-iso B .ret (g a)))
      eq1' IH ℧ = transport (λ i → unfold-ext g (~ i) ℧ ≡ unfold-L→L℧ B (~ i) (unfold-extL (L℧→LB ∘ g*) (~ i) (unfold-L℧→L A (~ i) ℧)))
         (sym (cong (LA⊎Unit→L℧A' B (next (LA⊎Unit→L℧A B))) (transport (λ i → (refl {x = L℧→LB ℧} i) ≡ unfold-L℧→L B i ℧) refl)
         ∙ (λ i → unfold-L→L℧ B (~ i) (unfold-L℧→L B (~ i) ℧)) ∙ L℧ALA⊎Unit-iso B .ret ℧))
      eq1' IH (θ la~) = transport (λ i → unfold-ext g (~ i) (θ la~) ≡ unfold-L→L℧ B (~ i) (unfold-extL (L℧→LB ∘ g*) (~ i) (unfold-L℧→L A (~ i) (θ la~))))
        λ i → θ (λ t → IH t (la~ t) i)
      
      eq1 : (la' : ⟨ 𝕃 A ⟩) -> ext g la' ≡ L→L℧B (extL (L℧→LB ∘ g*) (L℧→LA la'))
      eq1 = fix eq1'
      
      eq2 : (lb : L ( ⟨ B ⟩ ⊎ Unit)) -> lb ≡ L℧→LB (L→L℧B lb)
      eq2 lb = sym (L℧ALA⊎Unit-iso B .sec lb)
      

      f∘≈g∘ : TwoCell (rel-≈ A) (rel-≈ (𝕃 B)) f g -> TwoCell (rel-≈ (A ⊎p UnitPB)) (rel-≈L (B ⊎p UnitPB)) (L℧→LB ∘ f*) (L℧→LB ∘ g*)
      f∘≈g∘ f≈g (inl a) (inl a') a≈a' = f≈g a a' (lower a≈a')
      f∘≈g∘ f≈g (inr tt) (inr tt) a≈a' = transport
        (λ i -> rel-≈L (B ⊎p UnitPB) (unfold-L℧→L B (~ i) ℧) (unfold-L℧→L B (~ i) ℧))
        (LBisim.Reflexive.≈-refl (reflexive-≈ (B ⊎p UnitPB)) (η (inr tt)))
        where
          module LBisim = Bisim (⟨ B ⟩ ⊎ Unit) (rel-≈ (B ⊎p UnitPB))
      
      monotone-ext' :
        ▹ ((la la' : ⟨ 𝕃 A ⟩) -> rel-≈ (𝕃 A) la la' ->
          rel-≈ (𝕃 B) (ext f la) (ext g la')) ->
          (la la' : ⟨ 𝕃 A ⟩) -> rel-≈ (𝕃 A) la la' ->
          rel-≈ (𝕃 B) (ext f la) (ext g la')
      monotone-ext' IH la la' la≈la' = transport (λ i → rel-≈L (B ⊎p UnitPB) (L℧→LB (eq la (~ i))) (L℧→LB (eq1 la' (~ i))))
                                                           (transport (λ i → rel-≈L (B ⊎p UnitPB) (eq2 (extL (L℧→LB ∘ f*) (L℧→LA la)) i) (eq2 (extL (L℧→LB ∘ g*) (L℧→LA la')) i))
                                                             (extL-monotone-≈ (L℧→LB ∘ f*) (L℧→LB ∘ g*) (f∘≈g∘ f≈g) (L℧→LA la) (L℧→LA la') la≈la'))

  ext-monotone-≤ :
    (f f' : ⟨ A ⟩ -> ⟨ (𝕃 B) ⟩) ->
    TwoCell (rel-≤ A) (rel-≤ (𝕃 B)) f f' ->
    (la la' : ⟨ 𝕃 A ⟩) ->
    rel-≤ (𝕃 A) la la' ->
    rel-≤ (𝕃 B) (ext f la) (ext f' la')
  ext-monotone-≤ {A = A} {B = B} f f' f≤f' la la' la≤la' =
    ext-monotone-het-≤ {A = A} {A' = A} {B = B} {B' = B} (rel-≤ A) (rel-≤ B) f f' f≤f' la la' la≤la'

  
  bind-monotone-≤ :
    {la la' : ⟨ 𝕃 A ⟩} ->
    (f f' : ⟨ A ⟩ -> ⟨ (𝕃 B) ⟩) ->
    rel-≤ (𝕃 A) la la' ->
    TwoCell (rel-≤ A) (rel-≤ (𝕃 B)) f f' ->
    rel-≤ (𝕃 B) (bind la f) (bind la' f')
  bind-monotone-≤ {A = A} {B = B} {la = la} {la' = la'} f f' la≤la' f≤f' =
      ext-monotone-≤ {A = A} {B = B} f f' f≤f' la la' la≤la'


  bind-monotone-≈ :
    {la la' : ⟨ 𝕃 A ⟩} ->
    (f f' : ⟨ A ⟩ -> ⟨ (𝕃 B) ⟩) ->
    rel-≈ (𝕃 A) la la' ->
    TwoCell (rel-≈ A) (rel-≈ (𝕃 B)) f f' ->
    rel-≈ (𝕃 B) (bind la f) (bind la' f')
  bind-monotone-≈ {A = A} {B = B} {la = la} {la' = la'} f f' la≈la' f≈f' =
      ext-monotone-≈ {A = A} {B = B} f f' f≈f' la la' la≈la'


  mapL-monotone-het-≤ : {A A' : Predomain ℓA ℓ'A ℓ''A} {B B' : Predomain ℓB' ℓ'B' ℓ''B'} ->
    (rAA' : ⟨ A ⟩ -> ⟨ A' ⟩ -> Type ℓR1) ->
    (rBB' : ⟨ B ⟩ -> ⟨ B' ⟩ -> Type ℓR2) ->
    (f : ⟨ A ⟩ -> ⟨ B ⟩) ->
    (f' : ⟨ A' ⟩ -> ⟨ B' ⟩) ->
    TwoCell rAA' rBB' f f' ->
    (la : ⟨ 𝕃 A ⟩) -> (la' : ⟨ 𝕃 A' ⟩) ->
    (LiftRelation._≾_ _ _ rAA' la la') ->
     LiftRelation._≾_ _ _ rBB' (mapL f la) (mapL f' la')
  mapL-monotone-het-≤ {A = A} {A' = A'} {B = B} {B' = B'} rAA' rBB' f f' f≤f' la la' la≤la' =
    ext-monotone-het-≤ {A = A} {A' = A'} {B = B} {B' = B'} rAA' rBB' (ret ∘ f) (ret ∘ f')
      (λ a a' a≤a' → LiftRelation.Properties.ord-η-monotone _ _ rBB' (f≤f' a a' a≤a'))
      la la' la≤la'

  
  mapL-monotone-≤ : {A B : Predomain ℓ ℓ' ℓ''} ->
    (f f' : ⟨ A ⟩ -> ⟨ B ⟩) ->
    TwoCell (rel-≤ A) (rel-≤ B) f f' ->
    TwoCell (rel-≤ (𝕃 A)) (rel-≤ (𝕃 B)) (mapL f) (mapL f')
  mapL-monotone-≤ {A = A} {B = B} f f' f≤f' la la' la≤la'  =
    bind-monotone-≤ (ret ∘ f) (ret ∘ f') la≤la'
      (λ a1 a2 a1≤a2 → ord-η-monotone B (f≤f' a1 a2 a1≤a2))
  
  mapL-monotone-≈ : {A B : Predomain ℓ ℓ' ℓ''} ->
    (f f' : ⟨ A ⟩ -> ⟨ B ⟩) ->
    TwoCell (rel-≈ A) (rel-≈ B) f f' ->
    TwoCell (rel-≈ (𝕃 A)) (rel-≈ (𝕃 B)) (mapL f) (mapL f')
  mapL-monotone-≈ {A = A} {B = B} f f' f≈f' la la' la≈la' =
    bind-monotone-≈ (ret ∘ f) (ret ∘ f') la≈la'
      (λ a1 a2 a1≈a2 → ret-monotone-≈ (f a1) (f' a2) (f≈f' a1 a2 a1≈a2))

  monotone-bind-mon-≤ :
    {la la' : ⟨ 𝕃 A ⟩} ->
    (f : PMor A (𝕃 B)) ->
    (rel-≤ (𝕃 A) la la') ->
    rel-≤ (𝕃 B) (bind la (PMor.f f)) (bind la' (PMor.f f))
  monotone-bind-mon-≤ f la≤la' = bind-monotone-≤ (PMor.f f) (PMor.f f) la≤la'
    (≤mon-refl {!f!})

  monotone-bind-mon-≈ :
    {la la' : ⟨ 𝕃 A ⟩} ->
    (f : PMor A (𝕃 B)) ->
    (rel-≈ (𝕃 A) la la') ->
    rel-≈ (𝕃 B) (bind la (PMor.f f)) (bind la' (PMor.f f))
  monotone-bind-mon-≈ f la≈la' = bind-monotone-≈ (PMor.f f) (PMor.f f) la≈la'
    (≈mon-refl f)
-}
