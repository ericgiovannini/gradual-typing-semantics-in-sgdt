{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --polarity #-}

module Cubical.Algebra.AlgebraicStructures.AlgebraicTheory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as Maybe


private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓᴰ ℓᴰ' : Level
    ℓM ℓN ℓP : Level
    ℓMᴰ ℓNᴰ ℓPᴰ : Level
    ℓX ℓY ℓar ℓX' ℓar' : Level
    ℓR : Level
    ℓq : Level


extMaybe : {A : Type ℓ} {B : Type ℓ'}
  → (A → Maybe B)
  → Maybe A → Maybe B
extMaybe f nothing = nothing
extMaybe f (just x) = f x
  


record Sig (ℓX ℓar : Level) : Type (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓar)) where
  constructor signature
  field
    X : Type ℓX
    isDiscreteX : Discrete X
    ar : X → Type ℓar


module _ {ℓX ℓX' ℓar ℓar' : Level}
  (Σ₁ : Sig ℓX ℓar)
  (Σ₂ : Sig ℓX' ℓar')
  where

  private
    module Σ₁ = Sig Σ₁
    module Σ₂ = Sig Σ₂
    
  _⊎Sig_ : Sig (ℓ-max ℓX ℓX') (ℓ-max ℓar ℓar')
  (_⊎Sig_) .Sig.X = (Σ₁.X ⊎ Σ₂.X)
  (_⊎Sig_) .Sig.isDiscreteX = discrete⊎ Σ₁.isDiscreteX Σ₂.isDiscreteX
  (_⊎Sig_) .Sig.ar = Sum.rec (Lift ℓar' ∘ Σ₁.ar) (Lift ℓar ∘ Σ₂.ar)



module _ {ℓX ℓar : Level} where

  NullaryOp : Sig ℓX ℓar
  NullaryOp .Sig.X = ⊤*
  NullaryOp .Sig.isDiscreteX x y = yes refl
  NullaryOp .Sig.ar tt* = ⊥*

  UnaryOp : Sig ℓX ℓar
  UnaryOp .Sig.X = ⊤*
  UnaryOp .Sig.isDiscreteX x y = yes refl
  UnaryOp .Sig.ar tt* = ⊤*

  BinaryOp : Sig ℓX ℓar
  BinaryOp .Sig.X = ⊤*
  BinaryOp .Sig.isDiscreteX x y = yes refl
  BinaryOp .Sig.ar tt* = Lift ℓar Bool



module _ (σ : Sig ℓX ℓar)  where

  open Sig σ

  module _ (Y : Type ℓY) where
    -- The type of ASTs of terms with variables in Y. Such a tree is either:
    --   1. A leaf labeled by a variable in y
    --   2. A node labeled by the operation x : X, with a child tree/term
    --      for each z ∈ ar x.
    data Term : Type (ℓ-max ℓY (ℓ-max ℓX ℓar)) where
      var : (y : Y) → Term
      oper : (x : X) (vars : ar x → Term) → Term



    -- Elim principle for Terms
    module _
      {B : Term → Type ℓ}
      (var* : (y : Y) → B (var y))
      (oper* : (x : X) (vars : ar x → Term)
        → (recursive : (z : ar x) → B (vars z))
        → B (oper x vars))
      where
      
      elimTerm : (t : Term) → B t
      elimTerm (var y) = var* y
      elimTerm (oper x vars) = oper* x vars (λ z → elimTerm (vars z))


  -- Functorial action
  mapTerm : {A : Type ℓ} {B : Type ℓ'}
    → (f : A → B)
    → Term A → Term B
  mapTerm {A = A} {B = B} f = elimTerm A {B = λ _ → Term B}
    (λ y → var (f y))
    (λ x vars recursive → oper x recursive)
  



  Equations : (Y : Type ℓY) (ℓR : Level)
    → Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓY) (ℓ-suc ℓR))
  Equations Y ℓR = Rel (Term Y) (Term Y) ℓR

  EquationsLiftCod : (Y : Type ℓY) (ℓR ℓR' : Level)
    → Equations Y ℓR
    → Equations Y (ℓ-max ℓR ℓR')
  EquationsLiftCod Y ℓR ℓR' eqs lhs rhs = Lift ℓR' (eqs lhs rhs)

  Equation : {Y : Type ℓY} {ℓR : Level} (eqns : Equations Y ℓR)
    → Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓY) ℓR)
  Equation {Y = Y} eqns = Σ[ lhs ∈ Term Y ] Σ[ rhs ∈ Term Y ] eqns lhs rhs


  -- We specify a collection of equations via an indexing type E, and
  -- for each e : E, and arity `q e` along with a pair of terms over
  -- variables `q e`. Note that this specification is purely
  -- syntactic, i.e., we do not require a PreStructure to specify
  -- equations.
  record Eqns (ℓE ℓq : Level)
    : Type (ℓ-max (ℓ-max (ℓ-suc ℓE) (ℓ-suc ℓq)) (ℓ-max ℓX ℓar)) where
    field
      E : Type ℓE
      q : (e : E) → Type ℓq
      eqn : (e : E) → Term (q e) × Term (q e)

    lhs rhs : (e : E) → Term (q e)
    lhs e = fst (eqn e)
    rhs e = snd (eqn e)

  open Eqns


  Equations→Eqns : ∀ (Y : Type ℓY) (ℓR : Level)
    → Equations Y ℓR
    → Eqns (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓY) ℓR) ℓY
  Equations→Eqns Y ℓR eqs .E = Equation eqs
  Equations→Eqns Y ℓR eqs .q = (λ _ → Y)
  Equations→Eqns Y ℓR eqs .eqn (lhs , rhs , p) = lhs , rhs

  Eqns→Equations : ∀ {ℓE ℓq : Level}
    → Eqns ℓE ℓq
    → (Σ[ Y ∈ Type (ℓ-max ℓE ℓq) ] Equations Y (ℓ-max (ℓ-max (ℓ-max ℓX ℓar) ℓE) ℓq))
  Eqns→Equations eqns .fst = (e : eqns .E) → eqns .q e
  Eqns→Equations eqns .snd l r =
    Σ[ e ∈ eqns .E ]
      (lhs eqns e ≡ mapTerm (λ f → f e) l) × (rhs eqns e ≡ mapTerm (λ f → f e) r)

  lem1 : (Y : Type ℓY) (ℓR : Level) (eqs : Equations Y ℓR)
    → Eqns→Equations (Equations→Eqns Y ℓR eqs) ≡ (Lift (ℓ-max (ℓ-max ℓX ℓar) ℓR) Y , {!!})
  lem1 Y ℓR eqs = ΣPathP ({!!} , {!!})


{-
  Eqns→Equations' : ∀ {ℓE ℓq : Level}
    → Eqns ℓE ℓq
    → (Σ[ Y ∈ Type (ℓ-max ℓE ℓq) ] Equations Y {!!})
  Eqns→Equations' eqns .fst = Σ[ e ∈ eqns .E ] (eqns .q e)
  Eqns→Equations' eqns .snd l r = Σ[ e ∈ eqns .E ] (lhs eqns e ≡ {!l!}) × (rhs eqns e ≡ {!!})


  Eqns→Equations'' : ∀ {ℓE ℓq : Level}
    → Eqns ℓE ℓq
    → ((ℓY : Level) (Y : Type ℓY) → Equations Y {!!})
  Eqns→Equations'' eqns ℓY Y l r =
    Σ[ e ∈ eqns .E ] Σ[ x ∈ eqns .q e ] (lhs eqns e ≡ {!l!}) × (rhs eqns e ≡ {!!})
-}


-- Lifting terms and equations over a signature Σ to be over a
-- coproduct of signatures Σ + Σ'.
module _ {ℓX ℓX' ℓar ℓar' : Level}
  (Σ₁ : Sig ℓX ℓar) (Σ₂ : Sig ℓX' ℓar')
  {ℓY : Level} {Y : Type ℓY}
  where

  private
    module Σ₁ = Sig Σ₁
    module Σ₂ = Sig Σ₂
    
  Term-inl : 
      Term Σ₁ Y
    → Term (Σ₁ ⊎Sig Σ₂) Y
  Term-inl (var y) = var y
  Term-inl (oper x vars) = oper (inl x) (λ z → Term-inl (vars (lower z)))

  -- Term-proj-inl :
  --     Term (Σ₁ ⊎Sig Σ₂) Y
  --   → Maybe (Term Σ₁ Y)
  -- Term-proj-inl (var y) = just (var y)
  -- Term-proj-inl (oper (inl x) vars) = {!!}
  -- Term-proj-inl (oper (inr x) vars) = {!!}

  -- Eqns-inl : 
  --     Equations Σ₁ Y ℓR
  --   → Equations (Σ₁ ⊎Sig Σ₂) Y ℓR
  -- Eqns-inl e lhs rhs = Maybe.rec ⊥*
  --   (λ lhs' →
  --     Maybe.rec ⊥* (λ rhs' → e lhs' rhs') (Term-proj-inl rhs))
  --   (Term-proj-inl lhs)

  usesOnlyΣ₁ :
    Term (Σ₁ ⊎Sig Σ₂) Y → Type ℓar
  usesOnlyΣ₁ (var y) = ⊤*
  usesOnlyΣ₁ (oper (inl x) vars) = (z : Σ₁.ar x) → usesOnlyΣ₁ (vars (lift z)) 
  usesOnlyΣ₁ (oper (inr x) vars) = ⊥*

  usesOnlyΣ₁-Term-inl : ∀ t → usesOnlyΣ₁ (Term-inl t)
  usesOnlyΣ₁-Term-inl (var y) = tt*
  usesOnlyΣ₁-Term-inl (oper x vars) = (λ z → usesOnlyΣ₁-Term-inl (vars z))

  Term-proj-inl :
      (t : Term (Σ₁ ⊎Sig Σ₂) Y)
    → usesOnlyΣ₁ t
    → Term Σ₁ Y
  Term-proj-inl (var y) H = var y
  Term-proj-inl (oper (inl x) vars) H =
    oper x (λ z → Term-proj-inl (vars (lift z)) (H z))

  -- Eqns-inl : 
  --     Equations Σ₁ Y ℓR
  --   → Equations (Σ₁ ⊎Sig Σ₂) Y (ℓ-max ℓar ℓR)
  -- Eqns-inl e lhs rhs =
  --     (H : usesOnlyΣ₁ lhs)
  --   → (H' : usesOnlyΣ₁ rhs)
  --   → e (Term-proj-inl lhs H) (Term-proj-inl rhs H')

  Eqns-inl : 
      Equations Σ₁ Y ℓR
    → Equations (Σ₁ ⊎Sig Σ₂) Y (ℓ-max ℓar ℓR)
  Eqns-inl e lhs rhs =
      Σ[ H ∈ usesOnlyΣ₁ lhs ] Σ[ H' ∈ usesOnlyΣ₁ rhs ]
        e (Term-proj-inl lhs H) (Term-proj-inl rhs H')


  Term-inr : 
      Term Σ₂ Y
    → Term (Σ₁ ⊎Sig Σ₂) Y
  Term-inr (var y) = var y
  Term-inr (oper x vars) = oper (inr x) λ z → Term-inr (vars (lower z))

  Eqn-inr : 
      Equations Σ₂ Y ℓR
    → Equations (Σ₁ ⊎Sig Σ₂) Y ℓR
  Eqn-inr e = {!!}


module _ {ℓX ℓX' ℓar ℓar' : Level}
  (Σ₁ : Sig ℓX ℓar) (Σ₂ : Sig ℓX' ℓar')
  {ℓY : Level} {Y : Type ℓY}
  where

  swap : Term (Σ₁ ⊎Sig Σ₂) Y → Term (Σ₂ ⊎Sig Σ₁) Y
  swap (var y) = var y
  swap (oper (inl x) vars) = oper (inr x) (λ z → swap (vars z))
  swap (oper (inr x) vars) = oper (inl x) (λ z → swap (vars z))




-- Lifting terms and equations over variables in Y to equations over
-- variables in Lift Y.
module _ {ℓX ℓar : Level}
  (Σ : Sig ℓX ℓar)
  where

  Term-Lift : {Y : Type ℓY} {j : Level}
    → Term Σ Y
    → Term Σ (Lift j Y)
  Term-Lift (var y) = var (lift y)
  Term-Lift (oper x vars) = oper x (λ z → Term-Lift (vars z))

  Term-Lower : {Y : Type ℓY} {j : Level}
    → Term Σ (Lift j Y)
    → Term Σ Y
  Term-Lower (var y) = var (lower y)
  Term-Lower (oper x vars) = oper x λ z → Term-Lower (vars z)

  Eqn-Lift : {Y : Type ℓY} {j : Level}
    → Equations Σ Y ℓR
    → Equations Σ (Lift j Y) ℓR
  Eqn-Lift eqns lhs rhs = eqns (Term-Lower lhs) (Term-Lower rhs)




-- The coproduct of two sets of equations over different signatures.
module _ {ℓX ℓX' ℓar ℓar' : Level}
  (Σ₁ : Sig ℓX ℓar) (Σ₂ : Sig ℓX' ℓar')
  {ℓq ℓq' : Level}
  (Y : Type ℓY)
  (eqns  : Equations Σ₁ Y ℓq)
  (eqns' : Equations Σ₂ Y ℓq')
  where


  Equations-⊎ : Equations (Σ₁ ⊎Sig Σ₂) Y {!!}
  Equations-⊎ lhs rhs =
    (Σ[ H ∈ usesOnlyΣ₁ Σ₁ Σ₂ lhs ] Σ[ H' ∈ usesOnlyΣ₁ Σ₁ Σ₂ rhs ]
      eqns (Term-proj-inl _ _ lhs H) (Term-proj-inl _ _ rhs H'))
    ⊎ {!!}



-- The empty set of equations
module _ {ℓX ℓar : Level} (σ : Sig ℓX ℓar) (Y : Type ℓY) {ℓq : Level} where

  NoEqns : Equations σ Y ℓq
  NoEqns lhs rhs = ⊥*

-----------------------------------------------------------------------------

{-
record AlgTheory (ℓX ℓar ℓq : Level) : Typeω where
  field
    σ : Sig ℓX ℓar
    eqns : ∀ {ℓE : Level} {Y : Type ℓE} → Equations σ Y ℓq
-}

record Σω (A : Type ℓ) (B : A → Typeω) : Typeω where
  constructor pair
  field
    fst : A
    snd : B fst

AlgTheory : (ℓX ℓar ℓq : Level) → Typeω
AlgTheory ℓX ℓar ℓq = Σω (Sig ℓX ℓar)
  (λ σ → {ℓE : Level} {@++ Y : Type ℓE} → Equations σ Y ℓq)

module _ (T : AlgTheory ℓX ℓar ℓq) where

  AlgTheory→Sig : Sig ℓX ℓar
  AlgTheory→Sig = T .Σω.fst

  AlgTheory→Eqns : {ℓE : Level} {@++ Y : Type ℓE} → Equations (T .Σω.fst) Y ℓq
  AlgTheory→Eqns {Y = Y} = T .Σω.snd {Y = Y}


-----------------------------------------------------------------------------


record AlgTheory' (ℓX ℓar ℓE ℓq : Level)
  : Type (ℓ-max (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓar)) (ℓ-max (ℓ-suc ℓE) (ℓ-suc ℓq))) where
  field
    σ : Sig ℓX ℓar   
    eqns : ∀ {Y : Type ℓE} → Equations σ Y ℓq

  module σ = Sig σ
 

open AlgTheory'



-- The algebraic theory of a single nullary operation.
module _ {ℓX ℓar ℓE ℓq : Level} where

  𝟙 : AlgTheory' ℓX ℓar ℓE ℓq
  𝟙 .σ = NullaryOp
  𝟙 .eqns = NoEqns _ _


-- The coproduct of two algebraic theories.
module _
  {ℓX  ℓar  ℓE  ℓq : Level}
  {ℓX' ℓar' ℓE' ℓq' : Level}
  (T₁ : AlgTheory' ℓX ℓar ℓE ℓq)
  (T₂ : AlgTheory' ℓX' ℓar' ℓE' ℓq')
  where

  private
    module T₁ = AlgTheory' T₁
    module T₂ = AlgTheory' T₂

  AlgTheory'-⊎ : AlgTheory' (ℓ-max ℓX ℓX') (ℓ-max ℓar ℓar') (ℓ-max ℓE ℓE') (ℓ-max ℓq ℓq')
  AlgTheory'-⊎ .σ = T₁.σ ⊎Sig T₂.σ
  AlgTheory'-⊎ .eqns {Y} = Equations-⊎ T₁.σ T₂.σ Y {!T₁.eqns!} {!!} -- Eqns-⊎ T₁.σ T₂.σ T₁.eqns T₂.eqns


{-
module _ {ℓX ℓar ℓE ℓq : Level} (T : AlgTheory' ℓX ℓar ℓE ℓq) where
  private module T = AlgTheory' T
  
  mkPointed : AlgTheory' ℓX ℓar ℓE ℓq
  mkPointed = AlgTheory'-⊎ T (𝟙 {ℓX} {ℓar} {ℓE} {ℓq})
-}
