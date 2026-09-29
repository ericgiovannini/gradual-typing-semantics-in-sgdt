
{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}


open import Common.Later

module Semantics.Concrete.Predomain.GuardedTheory.Instances.FreeGuardedJoinSLErrorV2 (k : Clock) where

open import Cubical.Foundations.Prelude hiding (Σ)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

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
open import Cubical.Data.Bool

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
  unitL : ∀ (m : |P| X) → ∅ ∪ m ≡ m
  unitR : ∀ (m : |P| X) → m ∪ ∅ ≡ m

  -- Error for gradual typing (nullary)
  ℧ : |P| X

  -- Stepping for gradual typing (a guarded algebraic operation)
  θ : ▹ (|P| X) → |P| X

  θ-∅ : θ (next ∅) ≡ ∅
  θ-∪ : ∀ (m~ n~ : ▹ |P| X) → θ (λ t → (m~ t) ∪ (n~ t)) ≡ (θ m~ ∪ θ n~)

  -- h-level
  isSetP : isSet (|P| X)


module _ (X : Type ℓ) where

  not℧ : |P| X → Bool
  not℧ [ x ] = true
  not℧ ∅ = true
  not℧ ℧ = false
  not℧ (A ∪ B) = not℧ A or not℧ B
  not℧ (θ x) = true
  not℧ (idem A i) = (or-idem (not℧ A)) i
  not℧ (comm A B i) = or-comm (not℧ A) (not℧ B) i
  not℧ (assoc A B C i) = sym (or-assoc (not℧ A) (not℧ B) (not℧ C)) i
  not℧ (unitL A i) = {!!}
  not℧ (unitR A i) = {!!}
  not℧ (θ-∅ i) = true
  not℧ (θ-∪ A~ B~ i) = true
  not℧ (isSetP A B p q i j) =
    isSetBool (not℧ A) (not℧ B) (cong not℧ p) (cong not℧ q) i j


  not℧-false→℧ : ∀ (A : |P| X) → not℧ A ≡ false → A ≡ ℧
  not℧-false→℧ [ x ] H = ⊥.rec (true≢false H)
  not℧-false→℧ ∅ H = ⊥.rec (true≢false H)
  not℧-false→℧ ℧ _ = refl
  not℧-false→℧ (A ∪ B) = {!!}
  not℧-false→℧ (θ A~) H = ⊥.rec (true≢false H)
  not℧-false→℧ (idem A i) = {!!}
  not℧-false→℧ (comm A B i) = {!!}
  not℧-false→℧ (assoc A B C i) = {!!}
  not℧-false→℧ (unitL A i) = {!!}
  not℧-false→℧ (unitR A i) = {!!}  
  not℧-false→℧ (θ-∅ i) = {!!}
  not℧-false→℧ (θ-∪ A~ B~ i) = {!!}
  not℧-false→℧ (isSetP A B p q i j) = {!!}

  eq℧? : ∀ (A : |P| X) → Dec (A ≡ ℧)
  eq℧? A = aux (not℧ A) refl
    where
      aux : (b : Bool) → (not℧ A ≡ b) → Dec (A ≡ ℧)
      aux false H = yes (not℧-false→℧ A H)
      aux true H = no (λ p → true≢false {!!})
  -- eq℧? A with not℧ A in eq
  -- ... | false = yes (not℧-false→℧ A {!eq!})
  -- ... | true = no (λ p → {!cong not℧ p!})

module _ (X : Predomain ℓ ℓ≤ ℓ≈) where

  ∅≢℧ : ¬ ((∅ {X = ⟨ X ⟩}) ≡ ℧)
  ∅≢℧ = {!!}

  sing≢℧ : ∀ (x : ⟨ X ⟩) → ¬ ([ x ] ≡ ℧)
  sing≢℧ = {!!}


module Ordering (X : Predomain ℓ ℓ≤ ℓ≈) where

  private module X = PredomainStr (X .snd)

  data _⊑_ : |P| ⟨ X ⟩ → |P| ⟨ X ⟩ → Type (ℓ-max ℓ ℓ≤) where

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


module WkBisim (X : Predomain ℓ ℓ≤ ℓ≈) where

  private module X = PredomainStr (X .snd)

  data _≈_ : |P| ⟨ X ⟩ → |P| ⟨ X ⟩ → Type (ℓ-max ℓ ℓ≈) where

    [_] : ∀ {x y : ⟨ X ⟩} → x X.≈ y → [ x ] ≈ [ y ]

    -- Congruences for the operations
    ∅ : ∅ ≈ ∅
    
    _∪_ : ∀ {m₁ m₂ n₁ n₂}
      → m₁ ≈ n₁ → m₂ ≈ n₂ → (m₁ ∪ m₂) ≈ (n₁ ∪ n₂)

    θ : ∀ {m~ n~} → ▸ (λ t → (m~ t) ≈ (n~ t)) → θ m~ ≈ θ n~
    
    ℧ : ℧ ≈ ℧

    δl : ∀ {m n} → m ≈ n → (θ (next m)) ≈ n
    δr : ∀ {m n} → m ≈ n → m ≈ (θ (next n))

    isProp≈ : ∀ m n → isProp (m ≈ n)

    -- Symmetry
    symmetry : ∀ {m n} → m ≈ n → n ≈ m


-------------------------------------------------------------






module Example (X : hSet ℓ) where

  private
    dX = flat X
    module dX = PredomainStr (dX .snd)

  -- open Free hiding (_⊑_)
  -- open Free dX using (_⊑_)



module Membership (X : Predomain ℓ ℓ≤ ℓ≈) where

  private
    module X = PredomainStr (X .snd)


  data Atom : Type (ℓ-max ℓ ℓ≤) where
    val : ⟨ X ⟩ → Atom
    err : Atom
    later : ▹ (|P| ⟨ X ⟩) → Atom


  _∈_ : Atom → |P| ⟨ X ⟩ → hProp (ℓ-max ℓ ℓ≤)
  val x ∈ [ y ] = Lift ℓ≤ (x ≡ y) , isOfHLevelLift 1 (X.is-set x y)
  _     ∈ [ y ] = ⊥* , isProp⊥*

  err ∈ ℧ = ⊤* , isPropUnit*
  _ ∈ ℧ = ⊥* , isProp⊥*

  later m~ ∈ θ n~ = Lift ℓ≤ (m~ ≡ n~) , isOfHLevelLift 1 (isSet▹ (next isSetP) m~ n~)

  _ ∈ θ n~ = ⊥* , isProp⊥*

  -- "Generic" cases
  x ∈ ∅ = ⊥* , isProp⊥*
  x ∈ (m ∪ n) = ∥ ⟨ x ∈ m ⟩ ⊎ ⟨ x ∈ n ⟩ ∥₁ , isPropPropTrunc

  x ∈ idem m i = {!!}
  x ∈ comm m n i = {!!}
  x ∈ assoc m n p i = {!!}
  x ∈ unitL m i = {!!}
  x ∈ unitR m i = {!!}
  x ∈ isSetP m n p q i j = {!!}
  x ∈ θ-∅ i = {!!}
  x ∈ θ-∪ m~ n~ i = {!!}


  -- The empty set contains nothing
  ∅-empty : ∀ (a : Atom) → ¬ ⟨ a ∈ ∅ ⟩
  ∅-empty a = {!!}

  in-∪ : ∀ {A B : |P| ⟨ X ⟩} (a : Atom)
    → ⟨ a ∈ (A ∪ B) ⟩
    → ∥ ⟨ a ∈ A ⟩ ⊎ ⟨ a ∈ B ⟩ ∥₁
  in-∪ a = {!!} 


module EM (X : Predomain ℓ ℓ≤ ℓ≈) where

  private
    module X = PredomainStr (X .snd)

  open Membership X

  module Rec
    (rec : ▹ (|P| ⟨ X ⟩ → |P| ⟨ X ⟩ → hProp (ℓ-max ℓ ℓ≤))) where

    _≤Atom_ : Atom   → Atom   → hProp (ℓ-max ℓ ℓ≤)
    _≤EM'_  : |P| ⟨ X ⟩ → |P| ⟨ X ⟩ → hProp (ℓ-max ℓ ℓ≤)

    val x    ≤Atom val y    = Lift ℓ (x X.≤ y) , isOfHLevelLift 1 (X.is-prop-valued x y)
    err      ≤Atom _        = ⊤* , isPropUnit*
    later A~ ≤Atom later B~ = Prop▸ (λ t → rec t (A~ t) (B~ t)) 
    _        ≤Atom _        = ⊥* , isProp⊥*


    _≤EM'_ A B .fst =
      (A ≡ ℧) ⊎
      ((¬ (A ≡ ℧)) ×
          (∀ a → ⟨ a ∈ A ⟩ → ∃[ b ∈ _ ] ⟨ b ∈ B ⟩ × ⟨ a ≤Atom b ⟩)
        × (∀ b → ⟨ b ∈ B ⟩ → ∃[ a ∈ _ ] ⟨ a ∈ A ⟩ × ⟨ a ≤Atom b ⟩))
    _≤EM'_ A B .snd =
      isProp⊎
        (isSetP A ℧)
        (isProp×
          (isProp→ isProp⊥)
          (isProp× (isPropΠ (λ a → isProp→ isPropPropTrunc))
                   (isPropΠ (λ b → isProp→ isPropPropTrunc))))
         (λ A≡℧ (A≢℧ , _) → A≢℧ A≡℧)
          
   

  -- Now we define the EM ordering as a guarded fixpoint
  _≤EM_ : |P| ⟨ X ⟩ → |P| ⟨ X ⟩ → hProp (ℓ-max ℓ ℓ≤)
  _≤EM_ = fix Rec._≤EM'_

  _≼_ : Atom → Atom → hProp (ℓ-max ℓ ℓ≤)
  _≼_ = Rec._≤Atom_ (next _≤EM_)

  open Rec (next _≤EM_) public

  ≤EM→≤EM' : {A B : |P| ⟨ X ⟩} → ⟨ A ≤EM B ⟩ → ⟨ A ≤EM' B ⟩
  ≤EM→≤EM' {A = A} {B = B} A≤B =
    subst (λ f → ⟨ f A B ⟩) (fix-eq Rec._≤EM'_) A≤B

  ≤EM'→≤EM : {A B : |P| ⟨ X ⟩} → ⟨ A ≤EM' B ⟩ → ⟨ A ≤EM B ⟩
  ≤EM'→≤EM {A = A} {B = B} A≤B =
    subst⁻ (λ f → ⟨ f A B ⟩) (fix-eq Rec._≤EM'_) A≤B


  open Ordering X

  -- Compatibility Lemmas for ≤EM
  
  ∅≤∅ : ⟨ ∅ ≤EM ∅ ⟩
  ∅≤∅ = ≤EM'→≤EM (inr
      (∅≢℧ X
    , (λ a a∈∅ → ⊥.rec (∅-empty a a∈∅))
    , (λ b b∈∅ → ⊥.rec (∅-empty b b∈∅))))

  gen-≤ : ∀ {x y : ⟨ X ⟩}
    → x X.≤ y
    → ⟨ [ x ] ≤EM [ y ] ⟩
  gen-≤ {x = x} {y = y} x≤y = ≤EM'→≤EM (inr
     (sing≢℧ X _
    , (λ { (val x') x'≡x → ∣ (val y , (lift refl) , {!!}) ∣₁})
    , {!!}))

  ∪-cong : ∀ {A₁ A₂ B₁ B₂}
    → ⟨ A₁ ≤EM B₁ ⟩
    → ⟨ A₂ ≤EM B₂ ⟩
    → ⟨ (A₁ ∪ A₂) ≤EM (B₁ ∪ B₂) ⟩
  ∪-cong {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} A₁≤B₁ A₂≤B₂
    with eq℧? _ (A₁ ∪ A₂)
  ... | yes e = ≤EM'→≤EM (inl e)
  ... | no ¬e = ≤EM'→≤EM (inr
     (¬e
    , (λ {a mem → PTRec
            isPropPropTrunc
            (λ { (inl a∈A₁) → ∣ ({!≤EM→≤EM' A₁≤B₁!} , {!!} , {!!}) ∣₁ ; (inr A∈A₂) → {!!} })
            (in-∪ a mem)
      })
    , {!!}))

  θ-cong : ∀ {A~ B~ : ▹ |P| ⟨ X ⟩}
    → ▸ (λ t → ⟨ A~ t ≤EM B~ t ⟩)
    → ⟨ θ A~ ≤EM θ B~ ⟩
  θ-cong {A~ = A~} {B~ = B~} H~ = ≤EM'→≤EM (inr
     ({!!}
    , (λ { (later C~) mem → ∣ ((later B~) , (lift refl) , (λ t → {!!})) ∣₁
         ; (val x) mem    → ⊥.rec* mem
         ; err mem        → ⊥.rec* mem})
    , λ { (later D~) mem → {!!}
         ; _ → {!!}}))

  ℧-bot : ∀ B → ⟨ ℧ ≤EM B ⟩
  ℧-bot B = ≤EM'→≤EM (inl refl)


  module _ (IH : ▹ (∀ A B → A ⊑ B → ⟨ A ≤EM B ⟩)) where
  
    ⊑→EM' : ∀ A B → A ⊑ B → ⟨ A ≤EM B ⟩
    ⊑→EM' A B Ordering.[ x≤y ] = gen-≤ x≤y
    ⊑→EM' A B Ordering.∅ = ∅≤∅
    ⊑→EM' A B (A₁⊑B₁ Ordering.∪ A₂⊑B₂) =
      ∪-cong (⊑→EM' _ _ A₁⊑B₁) (⊑→EM' _ _ A₂⊑B₂)
    ⊑→EM' A B (Ordering.θ {A~} {B~} H~) =
      θ-cong λ (@tick t) → IH t (A~ t) (B~ t) (H~ t)
    ⊑→EM' A B Ordering.℧⊥ = ℧-bot B
    ⊑→EM' A B (Ordering.isProp⊑ A B H₁ H₂ i) = {!!}

  ⊑→EM : ∀ A B → A ⊑ B → ⟨ A ≤EM B ⟩
  ⊑→EM = fix ⊑→EM'


module Lemma (X : hSet ℓ) where

  dX = flat X
  private
    module dX = PredomainStr (dX .snd)

  open Ordering dX
  open WkBisim dX

  lem : ∀ {A B} → A ⊑ B → B ⊑ A → A ≈ B
  lem = {!!}
  -- lem [ p ] [ q ] = {!!}
  
{-
  module _
    (IH : ▹ ((A B : |P≤| dX) → ⟨ A  B ⟩ → ⟨ B ≤EM A ⟩ → (A ≈ B)))
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
  

-}












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

    θ-∅ : θ (next ∅) ≡ ∅
    θ-∪ : ∀ (m~ n~ : ▹ |P≤|) → θ (λ t → (m~ t) ∪ (n~ t)) ≡ (θ m~ ∪ θ n~)

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
