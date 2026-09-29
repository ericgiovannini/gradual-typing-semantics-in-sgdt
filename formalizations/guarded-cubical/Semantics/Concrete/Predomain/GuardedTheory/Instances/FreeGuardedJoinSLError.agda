
{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}


open import Common.Later

module Semantics.Concrete.Predomain.GuardedTheory.Instances.FreeGuardedJoinSLError (k : Clock) where

open import Cubical.Foundations.Prelude hiding (Σ)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation
  renaming (elim to PTElim ; rec to PTRec)

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv

open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Sigma hiding (Σ)
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)

open import Cubical.Relation.Nullary

open import Common.LaterProperties

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Constructions
  renaming (module Clocked to PredomainClocked)
  hiding (ℕ)
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Combinators

private
  variable
    ℓ  ℓ≤  ℓ≈  : Level
    ℓ' ℓ'≤ ℓ'≈ : Level
    ℓM ℓ≤M ℓ≈M : Level
    ℓN ℓ≤N ℓ≈N : Level
    ℓΓ ℓ≤Γ ℓ≈Γ ℓA ℓ≤A ℓ≈A ℓA' ℓ≤A' ℓ≈A' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ : Level
    ℓA₃ ℓ≤A₃ ℓ≈A₃ ℓA₄ ℓ≤A₄ ℓ≈A₄ : Level

    ℓM₁ ℓ≤M₁ ℓ≈M₁ ℓM₂ ℓ≤M₂ ℓ≈M₂ : Level
    ℓM₃ ℓ≤M₃ ℓ≈M₃ ℓM₄ ℓ≤M₄ ℓ≈M₄ : Level

    ℓR : Level

    -- A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁
    -- A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂
    -- A₃ : Predomain ℓA₃ ℓ≤A₃ ℓ≈A₃
    -- A₄ : Predomain ℓA₄ ℓ≤A₄ ℓ≈A₄

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A



Prop▸ : ▹ (hProp ℓ) → hProp ℓ
Prop▸ P~ .fst = ▸ (λ t → P~ t .fst)
Prop▸ P~ .snd = isProp▸ (λ t → P~ t .snd)


-- We solve the equation T X ≅ P(X + ℧ + ▹ T X) in Set.
--
-- We can define this nicely using an inductive datatype as
-- below. This is equivalent to first defining the finite powerset
-- datatype P, and then using using guarded recursion to define T X as
-- the unique solution to T X ≅ P(X + ℧ + ▹ T X).

data |P| (X : Type ℓ) : Type ℓ where

  -- inclusion of generators
  [_] : X → |P| X

  -- Empty set (nullary operation)
  ∅ : |P| X

  -- Union (binary operation)
  _∪_ : |P| X → |P| X → |P| X

  -- Laws
  idem  : ∀ (m : |P| X)     → m ∪ m ≡ m
  comm  : ∀ (m n : |P| X)   → m ∪ n ≡ n ∪ m
  assoc : ∀ (m n p : |P| X) → (m ∪ n) ∪ p ≡ m ∪ (n ∪ p)

  -- Error for gradual typing (nullary)
  ℧ : |P| X

  -- Stepping for gradual typing (a guarded algebraic operation)
  θ : ▹ (|P| X) → |P| X

  -- h-level
  isSetP : isSet (|P| X)

-------------------------------------------------------------


-- Now we solve the same equation, but in the categorty of predomains.
-- Since the ordering relation on predomains is antisymmetric, we need
-- to quotient the underlying set by order equivalence. Thus, we
-- define the underlying datatype simultaneously with its ordering
-- relation.


module Free (X : Predomain ℓ ℓ≤ ℓ≈) where

  private
    module X = PredomainStr (X .snd)

  data |P≤| : Type (ℓ-max ℓ ℓ≤)

  data _⊑_ : |P≤| → |P≤| → Type (ℓ-max ℓ ℓ≤)

  data |P≤| where

    -- inclusion of generators
    [_] : ⟨ X ⟩ → |P≤|

    -- Empty set (nullary operation)
    ∅ : |P≤|

    -- Union (binary operation)
    _∪_ : |P≤| → |P≤| → |P≤|

    -- Laws
    idem  : ∀ (m : |P≤|)     → m ∪ m ≡ m
    comm  : ∀ (m n : |P≤|)   → m ∪ n ≡ n ∪ m
    assoc : ∀ (m n p : |P≤|) → (m ∪ n) ∪ p ≡ m ∪ (n ∪ p)

    -- Error for gradual typing (nullary)
    ℧ : |P≤|

    -- Stepping for gradual typing (a guarded algebraic operation)
    θ : ▹ |P≤| → |P≤|

    -- h-level
    isSetP : isSet |P≤|

    -- antisymmetry
    antisym : ∀ (m n : |P≤|) → m ⊑ n → n ⊑ m → m ≡ n


  data _⊑_ where

    [_] : ∀ {x y : ⟨ X ⟩}
      → x X.≤ y → [ x ] ⊑ [ y ]

    -- Congruences for the operations
    ∅ : ∅ ⊑ ∅
    _∪_ : ∀ {m₁ m₂ n₁ n₂}
      → m₁ ⊑ n₁ → m₂ ⊑ n₂ → (m₁ ∪ m₂) ⊑ (n₁ ∪ n₂)

    θ : ∀ {m~ n~} → ▸ (λ t → (m~ t) ⊑ (n~ t)) → θ m~ ⊑ θ n~

    -- Error is the least element
    ℧⊥ : ∀ {m} → ℧ ⊑ m

    isProp⊑ : ∀ m n → isProp (m ⊑ n)

    -- Note: Reflexivity and transitivity follow from the above rules.

  reflexive : (A : |P≤|) → A ⊑ A
  reflexive A = {!!}

module _ (X : hSet ℓ) where

  private
    dX = flat X
    module dX = PredomainStr (dX .snd)

  open Free hiding (_⊑_)
  open Free dX using (_⊑_)

  A₀ : |P≤| dX
  A₀ = ℧

  A₁ : |P≤| dX
  A₁ = θ (next A₀)

  A₂ : |P≤| dX
  A₂ = θ (next A₁)

  -- Since ℧ is the least element, we have:
  --
  --   ℧ ⊑ θ (next ℧)
  --
  -- Then by θ-congruence:
  --   θ (next ℧) ⊑ θ (next (θ (next ℧)))
  --

  A₀⊑A₁ : A₀ ⊑ A₁
  A₀⊑A₁ = ℧⊥

  l : (A₀ ∪ A₂) ⊑ ((A₀ ∪ A₁) ∪ A₂)
  l = subst (λ z → (z ∪ A₂) ⊑ ((A₀ ∪ A₁) ∪ A₂))
    (idem A₀)
    (((reflexive _ A₀) ∪ A₀⊑A₁) ∪ (reflexive _ A₂))

  r : ((A₀ ∪ A₁) ∪ A₂) ⊑ (A₀ ∪ A₂)
  r = {!!}


module Foo (X : Predomain ℓ ℓ≤ ℓ≈) where

  private
    module X = PredomainStr (X .snd)

  open Free

  -- data Val : |P≤| X → Type (ℓ-max ℓ ℓ≤) where
  --   val-inj : ∀ x → Val [ x ]
  --   val-θ   : {!!}

  data Atom : Type (ℓ-max ℓ ℓ≤) where
    val : ⟨ X ⟩ → Atom
    err : Atom
    later : ▹ (|P≤| X) → Atom

  private module MemRec (rec : ▹ (Atom → |P≤| X → hProp (ℓ-max ℓ ℓ≤))) where
  
    _∈'_ : Atom → |P≤| X → hProp (ℓ-max ℓ ℓ≤)
    val x ∈' [ y ] = Lift ℓ≤ (x ≡ y) , isOfHLevelLift 1 (X.is-set x y)
    _     ∈' [ y ] = ⊥* , isProp⊥*

    err ∈' ℧ = ⊤* , isPropUnit*
    _ ∈' ℧ = ⊥* , isProp⊥*

    -- later m~ ∈' θ n~ = Prop▸ (λ t → later m~ ∈ (n~ t))
    later m~ ∈' θ n~ = (m~ ≡ n~) , isSet▹ (next isSetP) m~ n~
    -- (later m~ ∈' θ n~) =
    --   ▸ (λ t → (x : Atom) → ⟨ rec t x (m~ t) ⟩ → ⟨ rec t x (n~ t) ⟩)
    --   , isProp▸ (λ t → isPropΠ (λ x → isProp→ (rec t x (n~ t) .snd)))

    _ ∈' θ n~ = ⊥* , isProp⊥*

    -- "Generic" cases
    x ∈' ∅ = ⊥* , isProp⊥*
    x ∈' (m ∪ n) = ∥ ⟨ x ∈' m ⟩ ⊎ ⟨ x ∈' n ⟩ ∥₁ , isPropPropTrunc

    x ∈' idem m i = {!!}
    x ∈' comm m n i = {!!}
    x ∈' assoc m n p i = {!!}
    x ∈' isSetP m n p q i j = {!!}
    x ∈' antisym m n e e' i = {!!}

  _∈_ : Atom → |P≤| X → hProp {!!}
  _∈_ = fix MemRec._∈'_

  open MemRec (next _∈_) public

  _⊂_ : |P≤| X → |P≤| X → hProp (ℓ-max ℓ ℓ≤)
  (A ⊂ B) .fst = ∀ (x : Atom) → ⟨ x ∈ A ⟩ → ⟨ x ∈ B ⟩ 
  (A ⊂ B) .snd = isPropΠ2 (λ x _ → (x ∈ B) .snd)

  bothsubset→eq : {A B : |P≤| X}
    → ⟨ A ⊂ B ⟩
    → ⟨ B ⊂ A ⟩
    → A ≡ B
  bothsubset→eq {A = A} {B = B} A⊂B B⊂A = {!!}

  -- These definitions are parameterized by the EM ordering "later"
  module Rec
    (rec : ▹ (|P≤| X → |P≤| X → hProp (ℓ-max ℓ ℓ≤))) where

    _≼'_ : Atom → Atom → hProp (ℓ-max ℓ ℓ≤)
    _≤EM'_ : |P≤| X → |P≤| X → hProp (ℓ-max ℓ ℓ≤)

    val x  ≼' val y  = Lift ℓ (x X.≤ y) , isOfHLevelLift 1 (X.is-prop-valued x y)
    err ≼' _ = ⊤* , isPropUnit*
    later A~ ≼' later B~ = Prop▸ (λ t → rec t (A~ t) (B~ t)) 
    _      ≼' _      = ⊥* , isProp⊥*

    _≤EM'_ A B .fst =
      (A ≡ ℧) ⊎
      ((¬ (A ≡ ℧)) × (¬ (B ≡ ℧)) ×
          (∀ a → ⟨ a ∈ A ⟩ → ∃[ b ∈ _ ] ⟨ b ∈ B ⟩ × ⟨ a ≼' b ⟩)
        × (∀ b → ⟨ b ∈ B ⟩ → ∃[ a ∈ _ ] ⟨ a ∈ A ⟩ × ⟨ a ≼' b ⟩))
    _≤EM'_ A B .snd =
      isProp⊎
        (isSetP A ℧)
        (isProp×
          (isProp→ isProp⊥)
          (isProp×
            (isProp→ isProp⊥)
            (isProp×
              (isPropΠ (λ a → isProp→ isPropPropTrunc))
              (isPropΠ (λ b → isProp→ isPropPropTrunc)))))
        (λ A≡℧ (A≢℧ , B≢℧ , _) → A≢℧ A≡℧)
      -- isProp⊎
      --   (isSetP A ℧)
      --   (isProp×
      --     (isProp× ? (isProp→ isProp⊥))
      --     (isProp× (isPropΠ (λ a → isProp→ isPropPropTrunc))
      --              (isPropΠ (λ b → isProp→ isPropPropTrunc))))
      --     ?
        -- (λ A≡℧ (A≢℧ , _) → A≢℧ A≡℧)



  -- Now we define the EM ordering as a guarded fixpoint
  _≤EM_ : |P≤| X → |P≤| X → hProp (ℓ-max ℓ ℓ≤)
  _≤EM_ = fix Rec._≤EM'_

  _≼_ : Atom → Atom → hProp (ℓ-max ℓ ℓ≤)
  _≼_ = Rec._≼'_ (next _≤EM_)

  open Rec (next _≤EM_) public

  ≤EM→≤EM' : {A B : |P≤| X} → ⟨ A ≤EM B ⟩ → ⟨ A ≤EM' B ⟩
  ≤EM→≤EM' {A = A} {B = B} A≤B =
    subst (λ f → ⟨ f A B ⟩) (fix-eq Rec._≤EM'_) A≤B

  neq-℧→exists-elt : ∀ (A : |P≤| X) → ¬ (A ≡ ℧) →
    ∃[ a ∈ Atom ] ⟨ a ∈ A ⟩
  neq-℧→exists-elt [ x ] A≢℧ = {!!}
  neq-℧→exists-elt ∅ A≢℧ = {!!}
  neq-℧→exists-elt (A ∪ A₁) A≢℧ = {!!}
  neq-℧→exists-elt (idem A i) A≢℧ = {!!}
  neq-℧→exists-elt (comm A A₁ i) A≢℧ = {!!}
  neq-℧→exists-elt (assoc A A₁ A₂ i) A≢℧ = {!!}
  neq-℧→exists-elt ℧ A≢℧ = {!!}
  neq-℧→exists-elt (θ x) A≢℧ = {!!}
  neq-℧→exists-elt (isSetP A A₁ x y i i₁) A≢℧ = {!!}
  neq-℧→exists-elt (antisym A A₁ x x₁ i) A≢℧ = {!!}

  ℧-bottom : ∀ (A : |P≤| X)
    → ⟨ A ≤EM ℧ ⟩ → A ≡ ℧
  ℧-bottom A H = aux (≤EM→≤EM' H)
    where
      aux : ⟨ A ≤EM' ℧ ⟩ → A ≡ ℧
      aux (inl A≡℧) = A≡℧
      aux (inr (A≢℧ , ℧≢℧ , A→℧ , ℧→A)) = ⊥.rec (℧≢℧ refl)


module Lemma (X : hSet ℓ) where

  dX = flat X
  private
    module dX = PredomainStr (dX .snd)

  open Foo dX
  open Free

{-
  lem : ∀ (A B : |P≤| dX) → ⟨ A ≤EM B ⟩ → (A ≡ ℧) ⊎ (A ≡ B)
  lem A B A≤B with (≤EM→≤EM' A≤B)
  ... | inl A≡℧ = inl A≡℧
  ... | inr (A≢℧ , A→B , B→A) = inr (bothsubset→eq {!!} {!!})
    where
      A⊂B : ⟨ A ⊂ B ⟩
      A⊂B (inl x) eltOf = {!A→B (inl x) eltOf!}
      A⊂B (inr x) eltOf = {!!}
-}


  module _
    (IH : ▹ ((A B : |P≤| dX) → ⟨ A ≤EM B ⟩ → ⟨ B ≤EM A ⟩ → (A ≡ B)))
    where
    
    lem' : ∀ (A B : |P≤| dX) → ⟨ A ≤EM B ⟩ → ⟨ B ≤EM A ⟩ → (A ≡ B)
    lem' A B A≤B B≤A = {!!}
      where
        aux : ⟨ A ≤EM' B ⟩ → ⟨ B ≤EM' A ⟩ → (A ≡ B)
        
        -- Both ℧
        aux (inl A≡℧) (inl B≡℧) = A≡℧ ∙ (sym B≡℧)

        -- A = ℧ and A,B ≠ ℧ (contradiction)
        aux (inl A≡℧) (inr (B≢℧ , A≢℧ , A→B , B→A)) = ⊥.rec (A≢℧ A≡℧)

        -- A,B ≠ ℧ , and B = ℧ (contradiction)
        aux (inr (A≢℧ , B≢℧ , A→B , B→A)) (inl B≡℧) = ⊥.rec (B≢℧ B≡℧)

        -- A ≠ ℧, B ≠ ℧
        aux (inr (A≢℧ , B≢℧ , a→a≤b , b→a≤b)) (inr (B≢℧' , A≢℧' , b→b≤a , a→b≤a)) =
          (bothsubset→eq {!!} {!!})
          where
            A⊂B : ⟨ A ⊂ B ⟩
            -- Goal: ∀ (x : EltTy) → ⟨ x ∈ A ⟩ → ⟨ x ∈ B ⟩ 
            -- Case i: a = val x
            A⊂B (val x) eltOf =
              PTRec
                ((val x ∈ B) .snd)
                (λ { (val x' , x'∈B , x≤x') →
                  subst (λ z → ⟨ val z ∈ B ⟩) (sym (lower x≤x')) x'∈B
                })
                (a→a≤b (val x) eltOf)

            -- Case ii: a = err
            A⊂B err eltOf = PTRec
              ((err ∈ B) .snd)
              (λ { (Foo.err , err∈B , p≤err) → err∈B})
              (a→b≤a err eltOf)

            -- Case iii: a = later C~
            A⊂B (later C~) eltOf =
              PTRec
                ((later C~ ∈ B) .snd)
                  (λ { (later D~ , D~∈B , C~≤D~) → {!!} })
                    -- subst
                    --   (λ Z~ → ⟨ later Z~ ∈ B ⟩)
                    --   (sym (later-ext (λ t → {!IH t (C~ t) (D~ t) (C~≤D~ t)!})))
                    --   D~∈B })
                (a→a≤b (later C~) eltOf)
  


module Testing (X : Predomain ℓ ℓ≤ ℓ≈) where
  open Free
  
  _∈_ : (⟨ X ⟩ ⊎ (▹ (|P≤| X))) → |P≤| X → hProp ℓ
  _∈_ = {!!}

  private module X = PredomainStr (X .snd)

  -- _≼_ : ⟨ X ⟩ ⊎ (▹ |P≤| X) → ⟨ X ⟩ ⊎ (▹ |P≤| X) → Type (ℓ-max ℓ ℓ≤)
  data _≼_ : ⟨ X ⟩ ⊎ (▹ |P≤| X) → ⟨ X ⟩ ⊎ (▹ |P≤| X) → Type (ℓ-max ℓ ℓ≤)
  EM : |P≤| X → |P≤| X → Type (ℓ-max ℓ ℓ≤)

  data _≼_ where
    left  : ∀ x  y  → x X.≤ y → inl x ≼ inl y
    right : ∀ A~ B~ → ▸ (λ t → EM (A~ t) (B~ t)) → inr A~ ≼ inr B~

  -- inl x ≼ inl y = Lift ℓ (x X.≤ y)
  -- inr A~ ≼ inr B~ = ▸ (λ t → EM (A~ t) (B~ t))
  -- _ ≼ _ = ⊥*
  
  EM A B =
      (∀ a → ⟨ a ∈ A ⟩ → ∃[ b ∈ _ ] ⟨ b ∈ B ⟩ × (a ≼ b))
    × (∀ b → ⟨ b ∈ B ⟩ → ∃[ a ∈ _ ] ⟨ a ∈ A ⟩ × (a ≼ b))
  -- EM A B .snd =
  -- isProp×
  --   (isPropΠ (λ a → isProp→ isPropPropTrunc))
  --   (isPropΠ (λ b → isProp→ isPropPropTrunc))


{-
  _≼_ : ⟨ X ⟩ ⊎ (▹ |P≤| X) → ⟨ X ⟩ ⊎ (▹ |P≤| X) → hProp (ℓ-max ℓ ℓ≤)
  EM : |P≤| X → |P≤| X → hProp (ℓ-max ℓ ℓ≤)

  inl x ≼ inl y = {!!} -- x X.≤ y , X.is-prop-valued x y
  inr A~ ≼ inr B~ = ▸ (λ t → EM (A~ t) (B~ t) .fst) , {!!}
  _ ≼ _ = ⊥* , isProp⊥*
  
  EM A B .fst =
      (∀ a → ⟨ a ∈ A ⟩ → ∃[ b ∈ _ ] ⟨ b ∈ B ⟩ × ⟨ a ≼ b ⟩)
    × (∀ b → ⟨ b ∈ B ⟩ → ∃[ a ∈ _ ] ⟨ a ∈ A ⟩ × ⟨ a ≼ b ⟩)
  EM A B .snd = isProp×
    (isPropΠ (λ a → isProp→ isPropPropTrunc))
    (isPropΠ (λ b → isProp→ isPropPropTrunc))
-}


module Old {X : Predomain ℓ ℓ≤ ℓ≈} where

  private
    module X = PredomainStr (X .snd)

  open Free

  _∈_ : ⟨ X ⟩ → |P≤| X → hProp ℓ
  x ∈ [ y ] = (x ≡ y) , X.is-set x y
  x ∈ ∅ = ⊥* , isProp⊥*
  x ∈ (m ∪ n) = ∥ ⟨ x ∈ m ⟩ ⊎ ⟨ x ∈ n ⟩ ∥₁ , isPropPropTrunc
  
  x ∈ ℧ = ⊥* , isProp⊥*
  x ∈ θ m~ = Prop▸ (λ t → x ∈ (m~ t))

  x ∈ idem m i = {!!}
  x ∈ comm m n i = {!!}
  x ∈ assoc m n p i = {!!}
  x ∈ isSetP m n p q i j = {!!}
  x ∈ antisym m n e e' i = {!!}


  -- Egli-Milner-style ordering
  EM : |P≤| X → |P≤| X → hProp (ℓ-max ℓ ℓ≤)
  EM A B .fst =
      (∀ a → ⟨ a ∈ A ⟩ → ∃[ b ∈ ⟨ X ⟩ ] ⟨ b ∈ B ⟩ × (a X.≤ b))
    × (∀ b → ⟨ b ∈ B ⟩ → ∃[ a ∈ ⟨ X ⟩ ] ⟨ a ∈ A ⟩ × (a X.≤ b))
  EM A B .snd = isProp×
    (isPropΠ (λ a → isProp→ isPropPropTrunc))
    (isPropΠ (λ b → isProp→ isPropPropTrunc))


  -- Note that just from the types, these are not a priori mutually
  -- exclusive possibilities.
  -- But we need this to be a Prop in order to define a map from _⊑_ 
  data OrdResult (A B : |P≤| X) : Type (ℓ-max ℓ ℓ≤) where
    LHSErr      : A ≡ ℧         → OrdResult A B
    BothEmpty   : A ≡ ∅ → B ≡ ∅ → OrdResult A B
    NonEmptyOrd : ⟨ EM A B ⟩    → OrdResult A B
    

  lem : ∀ {A B} → _⊑_ X A B → OrdResult A B
    -- → ((A ≡ ℧) ⊎ ((A ≡ ∅) × (B ≡ ∅))) ⊎ ⟨ EM A B ⟩
    
  lem ([_] {x} {y} p) = NonEmptyOrd
    ((λ a e → ∣ (y , (refl , subst (λ z → z X.≤ y) (sym e) p)) ∣₁) ,
     (λ b e → ∣ (x , (refl , subst (λ z → x X.≤ z) (sym e) p)) ∣₁))
     
  lem ∅ = BothEmpty refl refl
  
  lem (_∪_ {m₁} {m₂} {n₁} {n₂} H₁ H₂) =
    NonEmptyOrd
      ((λ a a∈∪ → PTRec isPropPropTrunc (λ {
          (inl a∈m₁) → {!lem H₁!}
        ; (inr a∈m₂) → {!!}}) a∈∪) ,
       {!!})
    
  lem (θ {m~} {n~} H~) = NonEmptyOrd
    ((λ a a∈m~ → {!!}) ,
     {!!})
     
  lem ℧⊥ = LHSErr refl
  
  lem (isProp⊑ m n H H₁ i) = {!!}

  -- Using the symmetry


module _ {X : Predomain ℓ ℓ≤ ℓ≈} where

  open Free

  -- Note: we define this function using only induction, even with the
  -- θ case, because ▹ A is just (Tick → A).
  --
  -- The definition using only induction is equivalent to one where we
  -- take an explicit guarded fixpoint.

  quo : (|P| ⟨ X ⟩) → |P≤| X
  quo [ x ] = [ x ]
  quo ∅ = ∅
  quo (m ∪ n) = (quo m) ∪ (quo n)
  quo (idem m i) = idem (quo m) i
  quo (comm m n i) = comm (quo m) (quo n) i
  quo (assoc m n p i) = assoc (quo m) (quo n) (quo p) i
  quo ℧ = ℧
  quo (θ m~) = θ (λ t → quo (m~ t))
  quo (isSetP m n p q i j) = {!!}


-- fix f ≡ f (next (fix f))


module Test (X : hSet ℓ) where

  open Free

  dX : Predomain ℓ ℓ ℓ
  dX = flat X

  inv : |P≤| dX → (|P| ⟨ dX ⟩)
  inv [ x ] = [ x ]
  inv ∅ = ∅
  inv (m ∪ n) = (inv m) ∪ (inv n)
  inv (idem m i) = idem (inv m) i
  inv (comm m n i) = comm (inv m) (inv n) i
  inv (assoc m n p i) = assoc (inv m) (inv n) (inv p) i
  inv ℧ = ℧
  inv (θ m~) = θ (λ t → inv (m~ t))
  inv (isSetP m n p q i j) = {!!}
  inv (antisym m n e e' i) = {!!}
  -- congP (λ _ z → inv z) (antisym m n e e') i

  -- Given: m ⊑ n
  --        n ⊑ m
  --
  -- Show: inv m ≡ inv n
