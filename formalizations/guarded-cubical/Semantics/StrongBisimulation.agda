{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
open import Semantics.Monotone.Base

module Semantics.StrongBisimulation(k : Clock) where

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Data.Nat hiding (_^_) renaming (ℕ to Nat)
open import Cubical.Data.Bool.Base
open import Cubical.Data.Bool.Properties hiding (_≤_)
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary

open import Cubical.Data.Unit.Properties

open import Agda.Primitive

open import Common.Common
open import Semantics.Predomains
open import Semantics.Lift k
-- open import Semantics.ErrorDomains
open import Semantics.PredomainInternalHom

private
  variable
    l : Level
    A B : Set l
    ℓ ℓ' : Level
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A



 
-- Lifting a heterogeneous relation between A and B to a
-- relation between L A and L B
-- (We may be able to reuse this logic to define the homogeneous ordering on 𝕃 below)

module LiftRelation
  (A B : Predomain)
  (RAB : ⟨ A ⟩ -> ⟨ B ⟩ -> Type)
  where

  module A = PosetStr (A .snd)
  module B = PosetStr (B .snd)

  open A renaming (_≤_ to _≤A_)
  open B renaming (_≤_ to _≤B_)

  module Inductive
    (rec : ▹ ( L℧ ⟨ A ⟩ → L℧ ⟨ B ⟩ → Type)) where

    _≾'_ : L℧ ⟨ A ⟩ → L℧ ⟨ B ⟩ → Type
    (η a) ≾' (η b) = RAB a b
    ℧ ≾' lb = Unit
    (θ la~) ≾' (θ lb~) = ▸ (λ t → rec t (la~ t) (lb~ t))
    _ ≾' _ = ⊥

  _≾_ : L℧ ⟨ A ⟩ -> L℧ ⟨ B ⟩ -> Type
  _≾_ = fix _≾'_
    where open Inductive

  unfold-≾ : _≾_ ≡ Inductive._≾'_ (next _≾_)
  unfold-≾ = fix-eq Inductive._≾'_

  module Properties where
     open Inductive (next _≾_)

     ≾->≾' : {la : L℧ ⟨ A ⟩} {lb : L℧ ⟨ B ⟩} ->
       la ≾ lb -> la ≾' lb
     ≾->≾' {la} {lb} la≾lb = transport (λ i → unfold-≾ i la lb) la≾lb

     ≾'->≾ : {la : L℧ ⟨ A ⟩} {lb : L℧ ⟨ B ⟩} ->
       la ≾' lb -> la ≾ lb
     ≾'->≾ {la} {lb} la≾'lb = transport (sym (λ i → unfold-≾ i la lb)) la≾'lb

     ord-η-monotone : {a : ⟨ A ⟩} -> {b : ⟨ B ⟩} -> RAB a b -> (η a) ≾ (η b)
     ord-η-monotone {a} {b} a≤b = transport (sym (λ i → unfold-≾ i (η a) (η b))) a≤b

     ord-bot : (lb : L℧ ⟨ B ⟩) -> ℧ ≾ lb
     ord-bot lb = transport (sym (λ i → unfold-≾ i ℧ lb)) tt

     ord-θ-monotone : {la~ : ▹ L℧ ⟨ A ⟩} -> {lb~ : ▹ L℧ ⟨ B ⟩} ->
       ▸ (λ t -> la~ t ≾ lb~ t) -> θ la~ ≾ θ lb~
     ord-θ-monotone H = ≾'->≾ H


-- Predomain to lift predomain
module LiftPredomain (p : Predomain) where

  module X = PosetStr (p .snd)
  open X using (_≤_)


  -- Open the more general definitions from the heterogeneous
  -- lifting module, specializing the types for the current
  -- (homogeneous) situation, and re-export the definitions for
  -- clients of this module to use at these specialized types.
  open LiftRelation p p _≤_ public

  -- could also say: open LiftRelation.Inductive p p _≤_ (next _≾_)
  open Inductive (next _≾_) public
  open Properties public


  -- TODO move to heterogeneous lifting module
  ord-δ-monotone : {lx ly : L℧ ⟨ p ⟩} -> lx ≾ ly -> (δ lx) ≾ (δ ly)
  ord-δ-monotone {lx} {ly} lx≤ly =
    transport (sym (λ i → unfold-≾ i (δ lx) (δ ly))) (ord-δ-monotone' lx≤ly)
    where
      ord-δ-monotone' : {lx ly : L℧ ⟨ p ⟩} ->
        lx ≾ ly ->
        Inductive._≾'_ (next _≾_) (δ lx) (δ ly)
      ord-δ-monotone' {lx} {ly} lx≤ly = λ t → lx≤ly


  ord-refl-ind : ▹ ((a : L℧ ⟨ p ⟩) -> a ≾ a) ->
                    (a : L℧ ⟨ p ⟩) -> a ≾ a

  ord-refl-ind IH (η x) =
    transport (sym (λ i -> unfold-≾ i (η x) (η x))) (IsPoset.is-refl X.isPoset x)
  ord-refl-ind IH ℧ =
    transport (sym (λ i -> unfold-≾ i ℧ ℧)) tt
  ord-refl-ind IH (θ x) =
    transport (sym (λ i -> unfold-≾ i (θ x) (θ x))) λ t → IH t (x t)

  ord-refl : (a : L℧ ⟨ p ⟩) -> a ≾ a
  ord-refl = fix ord-refl-ind


  𝕃 : Predomain
  𝕃 =
    (L℧ ⟨ p ⟩) ,
    (posetstr _≾_ (isposet {!!} {!!} ord-refl ord-trans {!!}))
    where
      
      ord-trans-ind :
        ▹ ((a b c : L℧ ⟨ p ⟩) ->
           a ≾' b ->
           b ≾' c ->
           a ≾' c) ->
        (a b c : L℧ ⟨ p ⟩) ->
         a ≾' b ->
         b ≾' c ->
         a ≾' c
      ord-trans-ind IH (η x) (η y) (η z) ord-ab ord-bc =
        IsPoset.is-trans X.isPoset x y z ord-ab ord-bc
        -- x ≡⟨ ord-ab ⟩ y ≡⟨ ord-bc ⟩ z ∎
      ord-trans-ind IH (η x) (η y) ℧ ord-ab ord-bc = ord-bc
      ord-trans-ind IH (η x) (θ y) ℧ contra ord-bc = contra
      ord-trans-ind IH (η x) (η y) (θ z) ord-ab contra = contra
      ord-trans-ind IH (η x) ℧ (θ y) ord-ab ord-bc = ord-ab
      ord-trans-ind IH (η x) (θ y) (θ z) ord-ab ord-bc = ord-ab
      ord-trans-ind IH ℧ b c ord-ab ord-bc = tt
      ord-trans-ind IH (θ lx~) (θ ly~) (θ lz~) ord-ab ord-bc =
        λ t -> transport (sym λ i → unfold-≾ i (lx~ t) (lz~ t))
          (IH t (lx~ t) (ly~ t) (lz~ t)
          (transport (λ i -> unfold-≾ i (lx~ t) (ly~ t)) (ord-ab t))
          (transport (λ i -> unfold-≾ i (ly~ t) (lz~ t)) (ord-bc t)))

      ord-trans : (a b c : L℧ ⟨ p ⟩) -> a ≾ b -> b ≾ c -> a ≾ c
      ord-trans = fix (transport (sym (λ i ->
         (▹ ((a b c : L℧ ⟨ p ⟩) →
            unfold-≾ i a b → unfold-≾ i b c → unfold-≾ i a c) →
             (a b c : L℧ ⟨ p ⟩) →
            unfold-≾ i a b → unfold-≾ i b c → unfold-≾ i a c))) ord-trans-ind)




module LiftRelMon
  (A B : Predomain)
  (RAB : MonRel A B) where

  -- Bring the heterogeneous relation between 𝕃 A and 𝕃 B into scope
  open LiftRelation A B (MonRel.R RAB)
    using (_≾_ ; module Inductive ; module Properties) -- brings _≾_ into scope
  open Inductive (next _≾_)  -- brings _≾'_ into scope
  open Properties -- brings conversion between _≾_ and _≾'_ into scope

  -- Bring the homogeneous lifted relations on A and B into scope 
  -- open LiftPredomain renaming (_≾_ to _≾h_ ; _≾'_ to _≾h'_)
  open LiftPredomain using (𝕃)

  _≾LA_ = LiftPredomain._≾_ A
  _≾LB_ = LiftPredomain._≾_ B
  -- Could also say:
  -- open LiftPredomain A using () renaming (_≾_ to _≾LA_)

  _≾'LA_ = LiftPredomain._≾'_ A
  _≾'LB_ = LiftPredomain._≾'_ B

  R : MonRel (𝕃 A) (𝕃 B)
  R = record {
    R = _≾_ ;
    isAntitone = λ {la} {la'} {lb} la≤lb la'≤la -> {!!} ;
    isMonotone = {!!} }
    where
      antitone' :
        ▹ ({la la' : L℧ ⟨ A ⟩} -> {lb : L℧ ⟨ B ⟩} ->
            la ≾' lb -> la' ≾'LA la -> la' ≾' lb) ->
           {la la' : L℧ ⟨ A ⟩} -> {lb : L℧ ⟨ B ⟩} ->
            la ≾' lb -> la' ≾'LA la -> la' ≾' lb
      antitone' IH {η a2} {η a1} {η a3} la≤lb la'≤la =
        MonRel.isAntitone RAB la≤lb la'≤la
      antitone' IH {la} {℧} {lb} la≤lb la'≤la = tt
      antitone' IH {θ la2~} {θ la1~} {θ lb~} la≤lb la'≤la =
        λ t → ≾'->≾ {!!}

      monotone : {!!}
      monotone = {!!}

 -- isAntitone : ∀ {x x' y} -> R x y -> x' ≤X x -> R x' y
 -- isMonotone : ∀ {x y y'} -> R x y -> y ≤Y y' -> R x y'






-- Induced equivalence relation on a Predomain
equivRel : (d : Predomain) -> EquivRel ⟨ d ⟩ ℓ-zero
equivRel d =
  (λ x y → (x ≤ y) × (y ≤ x)) ,
  BinaryRelation.equivRel
    (λ x → (reflexive d x) , (reflexive d x))
    (λ x y (x≤y , y≤x) → y≤x , x≤y)
    λ x y z (x≤y , y≤x) (y≤z , z≤y) →
      (transitive d x y z x≤y y≤z) , (transitive d z y x z≤y y≤x)
  where
    module D = PosetStr (d .snd)
    _≤_ = D._≤_


congruence : {X : Type} -> (_R_ : L℧ X -> L℧ X -> Type) -> Type
congruence {X} _R_ = {lx ly : ▹ (L℧ X)} -> ▸ (λ t → (lx t) R (ly t)) -> (θ lx) R (θ ly)

congruence' : {X : Type} -> (_R_ : L℧ X -> L℧ X -> Type) -> Type
congruence' {X} _R_ = {lx ly : L℧ X} -> ▹ (lx R ly) -> (θ (next lx)) R (θ (next ly))

cong→cong' : ∀ {X}{_R_ : L℧ X -> L℧ X -> Type} → congruence _R_ → congruence' _R_
cong→cong' cong ▹R = cong ▹R

trivialize : {X : Type} (_R_ : L℧ X -> L℧ X -> Type) ->
  BinaryRelation.isTrans _R_ ->
  congruence _R_ ->
  ((x : L℧ X) -> x R (θ (next x))) ->
  ((x : L℧ X) -> x R (fix θ))
trivialize {X} _R_ hTrans hCong hθR = fix trivialize'
  where
   trivialize' :
    ▹ ((x : L℧ X) -> x R (fix θ)) → (x : L℧ X) -> x R (fix θ)
   trivialize' IH lx =
     subst (λ y → lx R y) (sym (fix-eq θ))
       (hTrans _ _ _
         (hθR lx)
         (hCong (λ t → IH t lx)))



-- Weak bisimulation relaion

module Bisimilarity (d : Predomain) where

  module D = PosetStr (d .snd)
  private
    _==_ = fst (equivRel d) -- the equivalence relation induced by d
    isEqRel = snd (equivRel d)

  -- make this a module so we can avoid having to make the IH
  -- a parameter of the comparison function
  module Inductive (IH : ▹ (L℧ ⟨ d ⟩ -> L℧ ⟨ d ⟩ -> Type)) where

    _≈'_ : L℧ (⟨ d ⟩) -> L℧ (⟨ d ⟩) -> Type
    ℧ ≈' ℧ = Unit
      
    η x ≈' η y = x == y
    
    θ lx ≈' θ ly = ▸ (λ t -> IH t (lx t) (ly t))
    -- or equivalently: θ lx ≾' θ ly = ▸ ((IH ⊛ lx) ⊛ ly)

    θ x~ ≈' ℧ = Σ Nat λ n -> θ x~ ≡ (δ ^ n) ℧

    θ x~ ≈' η y = Σ Nat λ n -> Σ ⟨ d ⟩ λ x -> (θ x~ ≡ (δ ^ n) (η x)) × (x == y)

    ℧ ≈' θ y~ = Σ Nat λ n -> θ y~ ≡ (δ ^ n) ℧

    η x ≈' θ y~ = Σ Nat λ n -> Σ ⟨ d ⟩ λ y -> (θ y~ ≡ (δ ^ n) (η y)) × (x == y)

    _ ≈' _ = ⊥


  _≈_ : L℧ (⟨ d ⟩) -> L℧ (⟨ d ⟩) -> Type
  _≈_ = fix _≈'_
    where open Inductive

  unfold-≈ : _≈_ ≡ Inductive._≈'_ (next _≈_)
  unfold-≈ = fix-eq Inductive._≈'_


  module Properties where
    open Inductive (next _≈_)
    open BinaryRelation (_==_)

    ≈->≈' : {lx ly : L℧ ⟨ d ⟩} ->
     lx ≈ ly -> lx ≈' ly
    ≈->≈' {lx} {ly} lx≈ly = transport (λ i → unfold-≈ i lx ly) lx≈ly

    ≈'->≈ : {lx ly : L℧ ⟨ d ⟩} ->
     lx ≈' ly -> lx ≈ ly
    ≈'->≈ {lx} {ly} lx≈'ly = transport (sym (λ i → unfold-≈ i lx ly)) lx≈'ly
    
    ≈-℧ : (lx : L℧ ⟨ d ⟩) ->
     lx ≈' ℧ -> (Σ Nat λ n -> lx ≡ (δ ^ n) ℧)
    ≈-℧ ℧ H = zero , refl
    ≈-℧ (θ x) H = H


    symmetric' :
      ▹ ((lx ly : L℧ ⟨ d ⟩) -> lx ≈' ly -> ly ≈' lx) ->
         (lx ly : L℧ ⟨ d ⟩) -> lx ≈' ly -> ly ≈' lx
    symmetric' _ ℧ ℧ _ = tt
    symmetric' _ (η x) (η y) (x≤y , y≤x) = y≤x , x≤y -- symmetry of the underlying relation
    symmetric' IH (θ lx~) (θ ly~) lx≈'ly =
      λ t → ≈'->≈  (IH t (lx~ t) (ly~ t) (≈->≈' (lx≈'ly t)))
    symmetric' _ (θ lx~) ℧ (n , H-eq) = n , H-eq
    symmetric' _ (θ lx~) (η y) (n , x , H-eq , H-rel) =
      n , x , H-eq , (isEquivRel.symmetric isEqRel x y H-rel)
    symmetric' _ ℧ (θ ly~) (n , H-eq) = n , H-eq
    symmetric' _ (η x) (θ ly~) (n , y , H-eq , H-rel) =
      n , y , H-eq , (isEquivRel.symmetric isEqRel x y H-rel)

    symmetric : (lx ly : L℧ ⟨ d ⟩) -> lx ≈ ly -> ly ≈ lx
    symmetric = {!!} -- fix {k} (subst {!!} {!!}) 

   {-
        ord-trans = fix (transport (sym (λ i ->
         (▹ ((a b c : L℧ ⟨ p ⟩) →
            unfold-ord i a b → unfold-ord i b c → unfold-ord i a c) →
             (a b c : L℧ ⟨ p ⟩) →
            unfold-ord i a b → unfold-ord i b c → unfold-ord i a c))) ord-trans-ind)
  -}

    θ-cong : congruence _≈_
    θ-cong {lx~} {ly~} H-later = ≈'->≈ H-later
    -- Goal: θ lx ≈ θ ly
    -- i.e. (θ lx) (≈' (next ≈)) (θ ly)
    -- i.e. ▸ (λ t → (lx t) ((next ≈) t) (ly t))
    -- i.e. ▸ (λ t → (lx t) ≈ (ly t))

    x≈'δx : ▹ ((lx : L℧ ⟨ d ⟩) -> lx ≈' (δ lx)) ->
               (lx : L℧ ⟨ d ⟩) -> lx ≈' (δ lx)
    x≈'δx _ (η x) = 1 , x , refl , (isEquivRel.reflexive isEqRel x)
    x≈'δx _ ℧ = 1 , refl
    x≈'δx IH (θ lx~) =

      -- Alternate solution:
      -- λ t → ≈'->≈
      --  (transport (λ i → (lx~ t) ≈' θ (next-Mt≡M lx~ t i)) (IH t (lx~ t)))

       transport
         (λ i -> ▸ (λ t -> unfold-≈ (~ i) (lx~ t) (θ (next-Mt≡M lx~ t i))))
         λ t → IH t (lx~ t)

    -- Goal: θ lx~ ≈' δ (θ lx~)
    -- i.e.  θ lx~ ≈' θ (next (θ lx~))
    -- i.e. ▸ λ t -> (lx~ t) ((next ≈) t) ((next (θ lx~)) t)
    -- i.e. ▸ λ t -> (lx~ t) ≈ (θ lx~)
    -- The IH says: ▸ λ t -> (lx~ t) ≈' (θ (next (lx~ t)))
    -- So we just need to change ≈' to ≈ and change
    -- (θ (next (lx~ t))) to (θ lx~). The below term does this.
   
    -- (λ i -> ▸ (λ t -> unfold-≈ (~ i) (lx~ t) (θ (next-Mt≡M lx~ t i)))) :
    --
    --   ▸ λ t -> (lx~ t) ≈' (θ (next (lx~ t))) ≡
    --   ▸ λ t -> (lx~ t) ≈  (θ lx~)

    -- Informally:
  
    -- By IH, we know:
    --   (lx~ t) ≈' (δ (lx~ t))

    -- Also Know:
    --   lx~ ≡ next (lx~ t) (using later-extensionality + tick irrelevance)

    -- So STS:
    --         (lx~ t) ≈ θ (next (lx~ t))
    -- which holds by IH.

    x≈δx : (lx : L℧ ⟨ d ⟩) -> lx ≈ (δ lx)
    x≈δx = transport
      (sym (λ i → (lx : L℧ ⟨ d ⟩) -> unfold-≈ i lx (δ lx)))
      (fix x≈'δx)


    contradiction : {A : Type} -> A -> ¬ A -> ⊥
    contradiction HA ¬A = ¬A HA

    contrapositive : {A : Type} -> (A -> B) -> (¬ B -> ¬ A)
    contrapositive A→B ¬B HA = ¬B (A→B HA)

    non-trivial→not-transitive :
      (Σ ⟨ d ⟩ λ x -> Σ ⟨ d ⟩ λ y -> (¬ (x == y))) ->
      ¬ (BinaryRelation.isTrans _≈_)
    non-trivial→not-transitive (x , y , x≠y) H-trans =
      let fixθ-top = trivialize _≈_ H-trans θ-cong x≈δx in
      let ηx≈ηy = H-trans (η x) (fix θ) (η y)
                        (fixθ-top (η x))
                        (symmetric _ _ (fixθ-top (η y))) in
      let not-ηx≈ηy = contrapositive (λ H -> ≈->≈' H) x≠y in
      contradiction ηx≈ηy not-ηx≈ηy


    inj-δ : {X : Set} -> (lx ly : L℧ X) -> δ lx ≡ δ ly -> lx ≡ ly
    inj-δ lx ly δlx≡δly = let tmp = inj-θ (next lx) (next ly) δlx≡δly in
      {!!}


    fixθ-lem1 : (n : Nat) ->
      (▹ (¬ (θ {X = Nat} (next (fix θ)) ≡ (δ ^ n) ℧))) ->
          ¬ (θ {X = Nat} (next (fix θ)) ≡ (δ ^ n) ℧)
    fixθ-lem1 zero    _  H-eq =  ℧≠θ (sym H-eq)
    fixθ-lem1 (suc n) IH H-eq =
       let tmp = inj-θ (next (fix θ)) (next ((δ ^ n) ℧)) H-eq in {!!}
     

    ℧-fixθ : ¬ (℧ ≈' θ (next (fix θ)))
    ℧-fixθ (n , H-eq) = {!!}
    
