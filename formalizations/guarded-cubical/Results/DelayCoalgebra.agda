{-# OPTIONS --cubical --rewriting --guarded #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -W noUnsupportedIndexedMatch #-}

module Results.DelayCoalgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sum
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Isomorphism

import Cubical.Data.Equality as Eq

open import Results.Delay

private
  variable
    ℓ : Level

module _ (X : Type ℓ) (isSetX : isSet X)  where

  record Coalg (ℓc : Level) : Type (ℓ-suc (ℓ-max ℓ ℓc)) where
    field
      V : Type ℓc
      un : V -> (X ⊎ V)

  liftSum : {ℓA ℓB : Level} -> {A : Type ℓA} -> {B : Type ℓB} -> 
    (A -> B) -> (X ⊎ A) -> (X ⊎ B)
  liftSum f (inl x) = inl x
  liftSum f (inr a) = inr (f a)

  open Coalg

  {-
  record CoalgMorphism {ℓ1 ℓ2 : Level} (c : Coalg ℓ1) (d : Coalg ℓ2) :
    Type (ℓ-max ℓ (ℓ-max ℓ1 ℓ2)) where
    field
      f : c .V -> d .V
      com : d .un ∘ f ≡ liftSum f ∘ c .un
  -}

  CoalgMorphism : {ℓ1 ℓ2 : Level} (c : Coalg ℓ1) (d : Coalg ℓ2) ->
    Type (ℓ-max (ℓ-max ℓ ℓ1) ℓ2)
  CoalgMorphism c d = Σ[ h ∈ (c .V -> d .V) ]
                      d .un ∘ h ≡ liftSum h ∘ c .un
  

  final-coalgebra : ∀ {ℓd : Level} -> Coalg ℓd ->
    Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓd))
  final-coalgebra {ℓd} d = ∀ (c : Coalg ℓd) -> isContr (CoalgMorphism c d)
  -- Doesn't work: {ℓc : Level} -> (c : Coalg ℓc) -> isContr (CoalgMorphism c d)

 


  inl≠inr : ∀ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} ->
    (a : A) (b : B) -> inl a ≡ inr b -> ⊥
  inl≠inr {_} {_} {A} {B} a b eq = transport (cong (diagonal ⊤ ⊥) eq) tt
    where
      diagonal : (Left Right : Type) -> (A ⊎ B) -> Type
      diagonal Left Right (inl a) = Left
      diagonal Left Right (inr b) = Right


  unfold-delay : Delay X -> X ⊎ Delay X
  unfold-delay d with (view d)
  ... | done x = inl x
  ... | running d' = inr d'

 
  unfold-delay-inv : X ⊎ Delay X -> Delay X
  unfold-delay-inv (inl x) .view = done x
  unfold-delay-inv (inr d) .view = running d

  -- Might be able to simplify this because d .view is isomorphic to X + Delay X
  delay-iso-sum : Iso (Delay X) (X ⊎ Delay X)
  delay-iso-sum = iso unfold-delay unfold-delay-inv sec retr
    where
      sec : section unfold-delay unfold-delay-inv
      sec (inl x) = refl
      sec (inr d) = refl

      retr : retract unfold-delay unfold-delay-inv
      retr d i .view with d .view
      ... | done x = done x
      ... | running d' = running d'


  unfold-delay-inj : (d1 d2 : Delay X) ->
    unfold-delay d1 ≡ unfold-delay d2 -> d1 ≡ d2
  unfold-delay-inj d1 d2 eq = isoFunInjective delay-iso-sum d1 d2 eq
 
  unfold-inv1 : (d : Delay X) -> (x : X) ->
    unfold-delay d ≡ inl x -> d .view ≡ done x
  unfold-inv1 d x H =
    cong view (isoFunInjective delay-iso-sum d (doneD x) H)

  unfold-inv2 : (d : Delay X) -> (d' : Delay X) ->
    unfold-delay d ≡ inr d' -> d .view ≡ running d'
  unfold-inv2 d d' H = cong view (isoFunInjective delay-iso-sum d (stepD d') H)



  DelayCoalg : Coalg ℓ
  DelayCoalg = record {
    V = Delay X ;
    un = unfold-delay }

  DelayCoalgFinal : {ℓc : Level} -> (c : Coalg ℓ) ->
    isContr (Σ[ h ∈ (c .V -> Delay X) ] unfold-delay ∘ h ≡ liftSum h ∘ c. un) -- isContr (CoalgMorphism c DelayCoalg)
  DelayCoalgFinal c =
    (fun , (funExt commute)) , {!!}
    where
      
      fun : c .V -> Delay X
      view (fun v) with c .un v
      ... | inl x = done x
      ... | inr v' = running (fun v')

      commute : (v : c. V) -> (DelayCoalg .un ∘ fun) v ≡ (liftSum fun ∘ c .un) v
      commute v with c. un v
      ... | inl x = refl
      ... | inr v' = refl


      unique' : (s s' : Σ[ h ∈ (c .V → Delay X) ]
                    (unfold-delay ∘ (h) ≡ liftSum h ∘ (c .un))) ->
        s ≡ s'
      unique' (h , com) (h' , com') = {!!}
        -- Σ≡Prop (λ g -> isPropΠ (λ v -> {!!})) (funExt eq-fun)
        where
          eq-fun : (v : c .V) -> h v ≡ h' v
          view (eq-fun v i) with c .un v in eq
          ... | inl x = view (unfold-delay-inj (h v) (h' v) (com-v ∙ sym com'-v) i)
            where
              com-v : (unfold-delay (h v)) ≡ inl x
              com-v = funExtS⁻ com v ∙ (λ j -> liftSum h (Eq.eqToPath eq j))

              com'-v : (unfold-delay (h' v)) ≡ inl x
              com'-v = funExtS⁻ com' v ∙ (λ j -> liftSum h' (Eq.eqToPath eq j))

          ... | inr v' = (goal (h v .view) (h' v .view)
                           (Eq.pathToEq eq-hv) (Eq.pathToEq eq-h'v) i)
          -- We state an auxiliary goal to which we pass the equalities eq-hv and eq-h'v
          -- as the built-in equality type so we can pattern match.
          -- If we tried to use transport instead, the termination checker would complain.
            where
              com-v : unfold-delay (h v) ≡ inr (h v')
              com-v = funExtS⁻ com v ∙ λ j -> liftSum h (Eq.eqToPath eq j)

              com'-v : unfold-delay (h' v) ≡ inr (h' v')
              com'-v = funExtS⁻ com' v ∙ λ j -> liftSum h' (Eq.eqToPath eq j)

              eq-hv : h v .view ≡ running (h v')
              eq-hv = unfold-inv2 (h v) (h v') com-v

              eq-h'v : h' v .view ≡ running (h' v')
              eq-h'v = unfold-inv2 (h' v) (h' v') com'-v

              goal : ∀ s1 s2 ->
                s1 Eq.≡ running (h v') ->
                s2 Eq.≡ running (h' v') ->
                s1 ≡ s2
              goal .(running (h v')) .(running (h' v')) Eq.refl Eq.refl =
                cong running (eq-fun v')

             

              


{-
      unique : (s : Σ[ h' ∈ (c .V → Delay X) ] (unfold-delay ∘ h' ≡ liftSum h' ∘ c .un)) →
        (fun , funExt commute) ≡ s
      unique (h' , com') = Σ≡Prop (λ g -> isSetΠ (λ v -> isSet⊎ isSetX (isSetDelay isSetX)) _ _) (funExt aux)
        where
          -- aux : (v : c .V) → fun v ≡ h' v
          -- aux v with c .un v
          -- ... | inl x = λ i -> {!!}
          -- ... | inr x = {!!}

          aux : (v : c .V) → fun v ≡ h' v
          view (aux v i) with c. un v in eq
          ... | inl x =
            let com-v = funExtS⁻ com' v in
            let eq' = lem1 (view (h' v)) x
                        (com-v ∙ λ j -> liftSum h' (Eq.eqToPath eq j)) in
            sym eq' i
          ... | inr v' =
            let com-v = funExtS⁻ com' v in
            {-let eq' = lem2 (view (h' v)) (fun v')
                        (com-v ∙ (λ j -> liftSum h' (Eq.eqToPath eq j)) ∙ cong inr (sym (aux v'))) in
            sym eq' i -}
            view (goal _ eq {!!})
              where
                goal : ∀ w -> w Eq.≡ inr v' -> (fun v') ≡ (h' v')
                goal w Eq.refl = λ j -> (aux v' j) -- view (aux v')
-}

  --  NTS: liftSum h' (c .un v) ≡ inr (fun v')
  --  Have : c .un v Eq.≡ inr v'
  --
  --  Substituting, NTS:
  --    liftSum h' (inr v') ≡ inr (fun v')
  --  i.e.
  --    inr (h' v') ≡ inr (fun v')
  --  i.e.
  --    h' v' ≡ fun v'
        
