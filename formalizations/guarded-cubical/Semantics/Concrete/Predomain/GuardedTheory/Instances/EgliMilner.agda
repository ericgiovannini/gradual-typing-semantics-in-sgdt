{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.Predomain.GuardedTheory.Instances.EgliMilner (k : Clock) where

open import Cubical.Foundations.Prelude hiding (Σ)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.HITs.PropositionalTruncation
  renaming (elim to PTElim ; rec to PTRec)

open import Cubical.Data.List as L hiding ([_])
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

open import Semantics.Concrete.Predomain.GuardedTheory.Instances.FreeGuardedJoinSLErrorV2 k


private
  variable
    ℓ  ℓ≤  ℓ≈  : Level
    ℓ' ℓ'≤ ℓ'≈ : Level
    ℓA ℓ≤A ℓ≈A ℓA' ℓ≤A' ℓ≈A' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ : Level
    ℓA₃ ℓ≤A₃ ℓ≈A₃ ℓA₄ ℓ≤A₄ ℓ≈A₄ : Level

    ℓR : Level

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A



-- Utilities:

data _∈_ {X : Type ℓ} : X → List X → Type ℓ where
  here  : ∀ x xs   → x ∈ (x ∷ xs)
  there : ∀ x y xs → x ∈ xs → x ∈ (y ∷ xs)


Rel▸ : {X : Type ℓ} {Y : Type ℓ'}
  → ▹ (X → Y → Type ℓR)
  → X → Y → Type ℓR
Rel▸ R~ x y = ▸ (λ t → R~ t x y)


-- Computation branches

data Br (X : Type ℓ) : Type ℓ where
  val  : X → Br X
  err  : Br X
  step : ▹ (|P| X) → Br X

⟦_⟧ᵇ : {X : Type ℓ} → Br X → |P| X
⟦ val x ⟧ᵇ = [ x ]
⟦ err ⟧ᵇ = ℧
⟦ step A~ ⟧ᵇ = θ A~

joinBr : {X : Type ℓ} → List (Br X) → |P| X
joinBr []       = ∅
joinBr (b ∷ bs) = ⟦ b ⟧ᵇ ∪ joinBr bs

joinBr-sing : ∀ {X : Type ℓ}
  → (b : Br X) → joinBr (b ∷ []) ≡ ⟦ b ⟧ᵇ
joinBr-sing b = unitR ⟦ b ⟧ᵇ



-- Decomposition into computation branches.
--
-- Note that there may be multiple decompositions for the same A : |P| X.

module _ {X : Type ℓ} where

  -- A decomposition of A is a list of branches that, when joined,
  -- give back A.
  Decomp : |P| X → Type ℓ
  Decomp A =
    Σ[ bs ∈ List (Br X) ] (joinBr bs ≡ A)

  -- Mere existence of a decomposition
  HasDecomp : |P| X → Type ℓ
  HasDecomp A = ∥ Decomp A ∥₁


  θ∪-decomp :
    ∀ {A~ B~ : ▹ |P| X}
    → Decomp (θ (λ t → A~ t ∪ B~ t))
  θ∪-decomp {A~} {B~} .fst = step A~ ∷ step B~ ∷ []
  θ∪-decomp {A~} {B~} .snd = cong₂ _∪_ refl {!!} ∙ sym (θ-∪ A~ B~)

  -- For every A, there exsits a decomposition of A.
  --
  -- We state this using mere existence so that we do not need to
  -- choose a canonical decomposition for each A.
  mkDecomp : (A : |P| X) → HasDecomp A
  mkDecomp A = {!!}

  -- If we are eliminating into a Prop then we can assume we have
  -- access to the data of decomposition.
  -- recDecompFor : {B : Type ℓ'} → (A : |P| X) → isProp B → (Decomp A → B) → B
  -- recDecompFor A isPropB f = PTRec isPropB f (mkDecomp A)

  recDecompFor : {B : Type ℓ'} → (A : |P| X)
    → isProp B
    → ((bs : List (Br X)) → joinBr bs ≡ A → B)
    → B
  recDecompFor A isPropB f = PTRec isPropB (λ { (bs , equal) → f bs equal}) (mkDecomp A)


-- Error branches are not mandatory; other branches are.
Mandatory : {X : Type ℓ} → Br X → Type
Mandatory err        = ⊥
Mandatory (val x)    = ⊤
Mandatory (step A~)  = ⊤


module EgliMilnerOrder (X : Predomain ℓ ℓ≤ ℓ≈) where

  private
    module X = PredomainStr (X .snd)


  module _ (_R_ : |P| ⟨ X ⟩ → |P| ⟨ X ⟩ → Type (ℓ-max ℓ ℓ≤)) where

    data _≤ᵇ_ : Br ⟨ X ⟩ → Br ⟨ X ⟩ → Type (ℓ-max ℓ ℓ≤) where
      val≤ :
        ∀ {x y : ⟨ X ⟩}
        → x X.≤ y
        → val x ≤ᵇ val y

      err≤ :
        ∀ {b : Br ⟨ X ⟩}
        → err ≤ᵇ b

      step≤ :
        ∀ {A~ B~ : ▹ |P| ⟨ X ⟩}
        → ▸ (λ t → (A~ t) R (B~ t))
        → step A~ ≤ᵇ step B~


    record CoverLE (as bs : List (Br ⟨ X ⟩)) : Type (ℓ-max ℓ ℓ≤) where

      field
        -- Non-error behavior of the source is preserved.
        forth :
          ∀ {a} → a ∈ as
          → Mandatory a
          → Σ[ b ∈ Br ⟨ X ⟩ ]
              (b ∈ bs × a ≤ᵇ b)

        -- Every behavior of the target is explained by some source behavior.
        -- In particular, a source err may explain any target branch.
        back :
          ∀ {b} → b ∈ bs
          → Σ[ a ∈ Br ⟨ X ⟩ ]
              (a ∈ as × a ≤ᵇ b)


  -- Defining the EM ordering by guarded recursion, i.e., by assuming
  -- it exists later and showing it exists now.
  module Rec
    (rec : ▹ (|P| ⟨ X ⟩ → |P| ⟨ X ⟩ → Type (ℓ-max ℓ ℓ≤))) where

    -- We say that A is less than B if there are decompositions of A
    -- and B into lists of branches `as` and bs, respectively, and the
    -- branches in `as` cover those in `bs` using the EM relation one
    -- step later.
    Raw≤EM' : |P| ⟨ X ⟩ → |P| ⟨ X ⟩ → Type _
    Raw≤EM' A B =
      Σ[ as ∈ List (Br ⟨ X ⟩) ]
      Σ[ bs ∈ List (Br ⟨ X ⟩) ]
        (joinBr as ≡ A) × (joinBr bs ≡ B) × CoverLE (Rel▸ rec) as bs


    _≤EM'_ : |P| ⟨ X ⟩ → |P| ⟨ X ⟩ → Type (ℓ-max ℓ ℓ≤)  
    A ≤EM' B = ∥ Raw≤EM' A B ∥₁


  -- Now we define the EM ordering as a guarded fixpoint of the above
  -- definition.
  _≤EM_ : |P| ⟨ X ⟩ → |P| ⟨ X ⟩ → Type (ℓ-max ℓ ℓ≤) -- should this be hProp?
  _≤EM_ = fix Rec._≤EM'_

  _≤EM▹_ : |P| ⟨ X ⟩ → |P| ⟨ X ⟩ → Type (ℓ-max ℓ ℓ≤)
  _≤EM▹_ = Rel▸ (next _≤EM_)
  --
  -- Rel▸ (next _≤EM_) x y = ▸ (λ t → (next _≤EM_) t x y)
  --                       = ▸ (λ t → x ≤EM y)
  --                       = ▹ (x ≤EM y)



  open Rec (next _≤EM_) public

  ≤EM→≤EM' : {A B : |P| ⟨ X ⟩} → A ≤EM B → A ≤EM' B
  ≤EM→≤EM' {A = A} {B = B} A≤B =
    subst (λ f → f A B) (fix-eq Rec._≤EM'_) A≤B

  ≤EM'→≤EM : {A B : |P| ⟨ X ⟩} → A ≤EM' B → A ≤EM B
  ≤EM'→≤EM {A = A} {B = B} A≤B =
    subst⁻ (λ f → f A B) (fix-eq Rec._≤EM'_) A≤B

  -- Recursion principle for ≤EM
  rec≤EM : {A B : |P| ⟨ X ⟩} {ℓS : Level} {S : Type ℓS}
    → isProp S
    → ((dA : Decomp A) → (dB : Decomp B) → CoverLE _≤EM▹_ (dA .fst) (dB .fst) → S)
    → A ≤EM B
    → S
  rec≤EM {A = A} {B = B}{S = S} isPropS f A≤B =
    PTRec isPropS aux (≤EM→≤EM' A≤B)
    where
      aux : Raw≤EM' A B → S
      aux (as , bs , ea , eb , as≤bs) = f (as , ea) (bs , eb) as≤bs


module _ {X : Predomain ℓ ℓ≤ ℓ≈} where

  private
    open module O = Ordering X
    module W = WkBisim X

  open EgliMilnerOrder X

  open CoverLE


  module _ (IH : ▹ (∀ {A B : |P| ⟨ X ⟩} → A O.⊑ B → A ≤EM B)) where
  
    ⊑→≤EM : ∀ {A B : |P| ⟨ X ⟩}
      → A O.⊑ B
      → A ≤EM B
    ⊑→≤EM p = ≤EM'→≤EM (aux p)
      where
        aux : ∀ {A B : |P| ⟨ X ⟩} → A O.⊑ B → A ≤EM' B

        -- Generators
        aux ([_] {x = x} {y = y} x≤y) =
          ∣ (L.[ val x ] , L.[ val y ] , (joinBr-sing _) , (joinBr-sing _) , cov) ∣₁
          where
            cov : CoverLE _≤EM▹_ L.[ val x ] L.[ val y ]
            cov .forth (here .(val x) []) _ = (val y) , (here _ []) , (val≤ x≤y)
            cov .back  (here .(val y) [])   = (val x) , (here _ []) , (val≤ x≤y)

        -- Empty
        aux ∅ = ∣ ([] , [] , refl , refl , cov) ∣₁
          where
            cov : CoverLE _≤EM▹_ [] []
            cov .forth ()
            cov .back  ()

        -- Union
        aux (_∪_ {m₁ = A₁} {m₂ = A₂} {n₁ = B₁} {n₂ = B₂} A₁⊑B₁ A₂⊑B₂) =
          PTRec isPropPropTrunc
            (λ { (as₁ , bs₁ , ea₁ , eb₁ , rel₁)
              → PTRec isPropPropTrunc
                  (λ { (as₂ , bs₂ , ea₂ , eb₂ , rel₂) →
                    ∣ (as₁ ++ as₂) , (bs₁ ++ bs₂) , {!!} , {!!} , {!!} ∣₁})
                  (aux A₂⊑B₂)})
            (aux A₁⊑B₁)
            where
              
        -- Theta
        aux (θ {A~} {B~} H~) =
          ∣ (L.[ step A~ ] , L.[ step B~ ] , (joinBr-sing _) , (joinBr-sing _) , {!!}) ∣₁
          where
            cov : CoverLE _≤EM▹_ L.[ step A~ ] L.[ step B~ ]
            cov .forth (here .(step A~) []) _ =
              (step B~) , (here _ []) , step≤ (λ t → next (IH t (H~ t)))
            cov .back = {!!}

        -- Error is least
        aux (℧⊥ {m = C}) = recDecompFor C isPropPropTrunc (λ bs equal
          → ∣ (L.[ err ] , bs , (joinBr-sing _) , equal , (cov bs)) ∣₁)
          -- ∣ (L.[ err ] , {!!} , joinBr-sing _ , {!!} , {!!}) ∣₁
          where
            cov : ∀ bs → CoverLE _≤EM▹_ L.[ err ] bs
            -- err is not mandatory, so forth holds vacuously.
            cov bs .forth (here err []) ()
            
            -- every target branch b ∈ bs is covered by the source
            -- error branch since err ≤ᵇ b.
            cov bs .back mem = err , (here err []) , err≤

        -- Propositional truncation
        aux (isProp⊑ A B p q i) = isPropPropTrunc (aux p) (aux q) i



