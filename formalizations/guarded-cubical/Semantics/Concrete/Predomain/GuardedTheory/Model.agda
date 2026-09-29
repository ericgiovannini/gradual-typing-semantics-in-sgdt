
{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --lossy-unification #-}


open import Common.Later

module Semantics.Concrete.Predomain.GuardedTheory.Model (k : Clock) where

open import Cubical.Foundations.Prelude hiding (Σ)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv

open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Sigma hiding (Σ)

open import Semantics.Concrete.Predomain.GuardedTheory.Arity
open import Semantics.Concrete.Predomain.GuardedTheory.Signature
open import Semantics.Concrete.Predomain.GuardedTheory.Term
open import Semantics.Concrete.Predomain.GuardedTheory.Substitution
open import Semantics.Concrete.Predomain.GuardedTheory.Shift

open import Semantics.Concrete.Predomain.GuardedTheory.Theory

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

    A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁
    A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂
    A₃ : Predomain ℓA₃ ℓ≤A₃ ℓ≈A₃
    A₄ : Predomain ℓA₄ ℓ≤A₄ ℓ≈A₄

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


open PredomainClocked k
open Signature

-- Iterated later on types:
Later : ℕ → Type ℓ → Type ℓ
Later zero A = A
Later (suc n) A = ▹ (Later n A)

-- Iterated later on predomains:
LaterP : ℕ → Predomain ℓ ℓ≤ ℓ≈ → Predomain ℓ ℓ≤ ℓ≈ 
LaterP zero A = A
LaterP (suc n) A = P▹ (LaterP n A)

PMor▹ : {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  → PMor A A'
  → PMor (P▹ A) (P▹ A')
PMor▹ f = PMor▸ (Common.Later.next f)

-- Functoriality of ▹ on predomain morphisms
PMor▹-Id : {A : Predomain ℓA ℓ≤A ℓ≈}
  → PMor▹ (Id {X = A}) ≡ Id
PMor▹-Id = refl -- surprised this works

PMor▹-Comp : (f : PMor A₁ A₂) (g : PMor A₂ A₃)
  → PMor▹ (g ∘p f) ≡ (PMor▹ g) ∘p (PMor▹ f)
PMor▹-Comp f g = refl -- surprised this works

LaterPMor : {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  → (n : ℕ) → (PMor A A') → PMor (LaterP n A) (LaterP n A')
LaterPMor zero f = f
LaterPMor (suc n) f = PMor▹ (LaterPMor n f)


-- Functoriality of iterated later:
LaterPMor-Id : {A : Predomain ℓA ℓ≤A ℓ≈A}
  → (n : ℕ) → LaterPMor {A = A} n Id ≡ Id
LaterPMor-Id zero = refl
LaterPMor-Id {A = A} (suc n) =
  (cong PMor▹ (LaterPMor-Id n)) ∙ (PMor▹-Id {A = LaterP n A})

LaterPMor-Comp : (f : PMor A₁ A₂) (g : PMor A₂ A₃)
  → (n : ℕ) → LaterPMor n (g ∘p f) ≡ (LaterPMor n g) ∘p (LaterPMor n f)
LaterPMor-Comp f g zero = refl
LaterPMor-Comp f g (suc n) =
  (cong PMor▹ (LaterPMor-Comp f g n)) ∙ (PMor▹-Comp (LaterPMor n f) (LaterPMor n g))


AppArg : {ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ ℓAₒ ℓ≤Aₒ ℓ≈Aₒ : Level}
  {Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ}
  {Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ}
  → ⟨ Aᵢ ⟩
  → PMor (Aᵢ ==> Aₒ) Aₒ
AppArg {Aᵢ = Aᵢ} {Aₒ = Aₒ} x = S (Aᵢ ==> Aₒ) App (Const Aᵢ x)

AppArg≡ : {ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ ℓAₒ ℓ≤Aₒ ℓ≈Aₒ : Level}
  {Aᵢ : Predomain ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ}
  {Aₒ : Predomain ℓAₒ ℓ≤Aₒ ℓ≈Aₒ}
  (x : ⟨ Aᵢ ⟩)
  → PMor.f (AppArg {Aᵢ = Aᵢ} {Aₒ = Aₒ} x) ≡ (λ g → g .PMor.f x)
AppArg≡ x = refl


PostComp : {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  → ⟨ A ==> A' ⟩ → ⟨ (Γ ==> A) ==> (Γ ==> A') ⟩
PostComp {Γ = Γ} {A = A} {A' = A'} f =
  (Curry {Γ = Γ ==> A} {A = Γ}) (mCompU f (App {A = Γ} {B = A}))

-- This also works but is much slower to typecheck:
-- PostComp {Γ = Γ} {A = A} {A' = A'} f =
--   S (Γ ==> A) (Uncurry mComp ∘p SwapPair {A = Γ ==> A} {B = A ==> A'}) (K (Γ ==> A) {A = A ==> A'} f)


∘p-Assoc : (f : PMor A₁ A₂) (g : PMor A₂ A₃) (h : PMor A₃ A₄)
  → h ∘p (g ∘p f) ≡ (h ∘p g) ∘p f
∘p-Assoc f g h = eqPMor _ _ refl

-- Fin (lookup Γ d) as a predomain
VarP : Arity → ℕ → Predomain ℓ-zero ℓ-zero ℓ-zero
VarP Γ d = flat ((Fin (lookup Γ d)) , isSetFin)


-- Environments (predomain mappings from the variables at depth d, to
-- elements of the predomain delayed by d time steps):
opaque
  Env : Predomain ℓ ℓ≤ ℓ≈ → Arity → Predomain (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈) ℓ≤ ℓ≈
  Env A Γ = ΠP ℕ (λ d → (VarP Γ d) ==> (LaterP d A))

  env-lookup : {A : Predomain ℓ ℓ≤ ℓ≈} {Γ : Arity}
    → ⟨ Env A Γ ⟩ → (d : ℕ) → Var Γ d → ⟨ LaterP d A ⟩
  env-lookup ρ d x = ρ d .PMor.f x

  Env-Lookup : {A : Predomain ℓ ℓ≤ ℓ≈} {Γ : Arity}
    → (d : ℕ) → Var Γ d → PMor (Env A Γ) (LaterP d A)
  Env-Lookup {ℓ = ℓ} {ℓ≤ = ℓ≤} {ℓ≈ = ℓ≈} {A = A} {Γ = Γ} d x =
    bar ∘p foo
    where
      mid : Predomain (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈) ℓ≤ ℓ≈
      mid = VarP Γ d ==> LaterP d A
 
      foo : PMor (Env A Γ) mid
      foo = (Π-elim {B = λ d' → (VarP Γ d') ==> (LaterP d' A)} d)

      bar : PMor mid (LaterP d A)
      bar = (AppArg {Aᵢ = VarP Γ d} {Aₒ = LaterP d A} x)

  EnvMor : {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
    → {Γ : Arity}
    → (f : PMor A A')
    → PMor (Env A Γ) (Env A' Γ)
  EnvMor {A = A} {A' = A'} {Γ = Γ} f =
    Π-mor ℕ
      (λ d → (VarP Γ d) ==> (LaterP d A))
      (λ d → (VarP Γ d) ==> (LaterP d A'))
      (λ d → PostComp {Γ = VarP Γ d} (LaterPMor d f))

  EnvMor-Id : {A : Predomain ℓA ℓ≤A ℓ≈A} {Γ : Arity}
    → EnvMor {Γ = Γ} (Id {X = A}) ≡ Id
  EnvMor-Id = eqPMor _ _ (funExt (λ ρ →
    funExt (λ d → eqPMor _ _ (funExt (λ x → {!!})))))

  EnvMor-Comp : {Γ : Arity}
    → (f : PMor A₁ A₂) (g : PMor A₂ A₃)
    → EnvMor {Γ = Γ} (g ∘p f) ≡ EnvMor g ∘p EnvMor f
  EnvMor-Comp f g = {!!}


-- This could take in a Type instead of a Predomain
Env' : Predomain ℓ ℓ≤ ℓ≈ → Arity → Predomain {!!} {!!} {!!}
Env' A Γ = flat (((d : ℕ) → Var Γ d → Later d ⟨ A ⟩) , isSetΠ (λ d → isSet→ {!!}))


-- Env : Predomain ℓ ℓ≤ ℓ≈ → Arity → Type (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈)
-- Env A Γ = (d : ℕ) → Fin (lookup Γ d) → ⟨ LaterP d A ⟩
-- Env A Γ = (d : ℕ) → PMor (VarP Γ d) (LaterP d A)


-- Pre-models:
module _ (Σ : Signature) where

  record PreModel (ℓ ℓ≤ ℓ≈ : Level) : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈))
    where
    no-eta-equality
    
    field
      A : Predomain ℓ ℓ≤ ℓ≈

      -- Interpretation of operations:
      ⟦_⟧op : (f : Op Σ) → PMor (Env A (ar Σ f)) A
      -- Note that all operations have output depth 0 (no later's)

    open PredomainStr (A .snd) public

module _ {Σ : Signature} (M : PreModel Σ ℓ ℓ≤ ℓ≈) where

  private module M = PreModel M

  eval : {Γ : Arity} {d : ℕ} → ⟨ Env M.A Γ ⟩ → Term Σ Γ d → ⟨ LaterP d M.A ⟩
  eval {d = d} ρ (var x) = env-lookup ρ d x
  eval ρ (Term.next t) = {!!}
  eval ρ (app f p args) = {!args!}

  -- Evaluating a Term as a morphism of predomains from environments to values
  Eval : {Γ : Arity} {d : ℕ} → Term Σ Γ d → PMor (Env M.A Γ) (LaterP d M.A)
  Eval (var x) = Env-Lookup _ x
  Eval (Term.next t) = {!!} ∘p (Eval t)
  Eval (app f p x) = {!!}

  open Equation
  Eval-eqn : Equation Σ → Type (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈)
  Eval-eqn e = Eval (e .lhs) ≡ Eval (e .rhs)


-- Morphisms of pre-models
module _ {Σ : Signature} where
  private module Σ = Signature Σ
  
  record PreModelMor (M : PreModel Σ ℓM ℓ≤M ℓ≈M) (N : PreModel Σ ℓN ℓ≤N ℓ≈N)
    : Type (ℓ-max (ℓ-max (ℓ-max ℓM ℓ≤M) ℓ≈M) (ℓ-max (ℓ-max ℓN ℓ≤N) ℓ≈N))
    where
    
    private
      module M = PreModel M
      module N = PreModel N
      
    field
      f : PMor M.A N.A
      is-hom : ∀ (o : Σ.Op)
        → (f ∘p M.⟦ o ⟧op) ≡ (N.⟦ o ⟧op ∘p (EnvMor f))
      -- is-hom : ∀ {x} (vars : (ar x) → ⟨ M ⟩)
      --   → f (M.op x vars) ≡ N.op x (f ∘ vars)

    ⟨_⟩PMM : PMor M.A N.A
    ⟨_⟩PMM = f

  open PreModelMor

  -- Identity and composition of morphisms
  idPM : {M : PreModel Σ ℓM ℓ≤M ℓ≈M}
    → PreModelMor M M
  idPM .f = Id
  idPM {M = M} .is-hom o =
    (CompPD-IdL _) ∙ (sym (CompPD-IdR _)) ∙ (cong₂ _∘p_ refl (sym EnvMor-Id))
  --   Id ∘p PreModel.⟦ M ⟧op o
  -- ≡ PreModel.⟦ M ⟧op o
  -- ≡ PreModel.⟦ M ⟧op o ∘p Id
  -- ≡ PreModel.⟦ M ⟧op o ∘p EnvMor Id

  module _
    {M₁ : PreModel Σ ℓM₁ ℓ≤M₁ ℓ≈M₁}
    {M₂ : PreModel Σ ℓM₂ ℓ≤M₂ ℓ≈M₂}
    {M₃ : PreModel Σ ℓM₃ ℓ≤M₃ ℓ≈M₃}
    (h : PreModelMor M₂ M₃)
    (g : PreModelMor M₁ M₂)
    where

    private
      module M₁ = PreModel M₁
      module M₂ = PreModel M₂
      module M₃ = PreModel M₃
      module g = PreModelMor g
      module h = PreModelMor h

    _∘PM_ : PreModelMor M₁ M₃
    _∘PM_ .f = h.f ∘p g.f
    _∘PM_ .is-hom o =
        sym (∘p-Assoc (M₁.⟦ o ⟧op) g.f h.f)
      ∙ cong₂ _∘p_ (refl {x = h.f}) (g.is-hom o)
      ∙ ∘p-Assoc (EnvMor g.f) (M₂.⟦ o ⟧op) h.f
      ∙ cong₂ _∘p_ (h.is-hom o) (refl {x = EnvMor g.f})
      ∙ sym (∘p-Assoc (EnvMor g.f) (EnvMor h.f) (M₃.⟦ o ⟧op))
      ∙ cong₂ _∘p_ (refl {x = M₃.⟦ o ⟧op}) (sym (EnvMor-Comp g.f h.f))
      
    --   (h ∘ g) ∘ M₁.⟦ o ⟧op ≡
    -- ≡ h ∘ (g ∘ M₁.⟦ o ⟧op)
    -- ≡ h ∘ (M₂.⟦ o ⟧op ∘ EnvMor g)
    -- ≡ (h ∘ M₂.⟦ o ⟧op) ∘ EnvMor g
    -- ≡ (M₃.⟦ o ⟧op ∘ EnvMor h) ∘ EnvMor g
    -- ≡ M₃.⟦ o ⟧op ∘ (EnvMor h ∘ EnvMor g)
    -- ≡ M₃.⟦ o ⟧op ∘ EnvMor (h ∘ g)
    

  -- Equivalence between PreModelMor record and a sigma type   
  unquoteDecl PMMorIsoΣ = declareRecordIsoΣ PMMorIsoΣ (quote (PreModelMor))


  -- PreModel morphisms form a set
  EDMorIsSet :
    (M : PreModel Σ ℓM ℓ≤M ℓ≈M)
    (N : PreModel Σ ℓN ℓ≤N ℓ≈N) →
    isSet (PreModelMor M N)
  EDMorIsSet M N = isSetRetract
    (Iso.fun PMMorIsoΣ) (Iso.inv PMMorIsoΣ)
    (Iso.ret PMMorIsoΣ)
    (isSetΣSndProp PMorIsSet (λ g → isPropΠ (λ o → PMorIsSet _ _)))
      where
        module M = PreModel M
        module N = PreModel N
  

  -- Equality of PreModel morphisms
  module _
    {M : PreModel Σ ℓM ℓ≤M ℓ≈M}
    {N : PreModel Σ ℓN ℓ≤N ℓ≈N}
    (g g'  : PreModelMor M N) where

    private
      module g  = PreModelMor g
      module g' = PreModelMor g'

    eqPMMor : g.f ≡ g'.f → g ≡ g'
    eqPMMor e = isoFunInjective PMMorIsoΣ g g'
      (Σ≡Prop (λ f → isPropΠ (λ o → PMorIsSet _ _)) e)


  -- Identity and associativity laws for morphisms
  module _
    {M : PreModel Σ ℓM ℓ≤M ℓ≈M}
    {N : PreModel Σ ℓN ℓ≤N ℓ≈N} where
    
    CompPMM-IdL : (g : PreModelMor M N) → idPM ∘PM g ≡ g
    CompPMM-IdL g = eqPMMor _ _ (CompPD-IdL _)

    CompPMM-IdR : (g : PreModelMor M N) → g ∘PM idPM ≡ g
    CompPMM-IdR g = eqPMMor _ _ (CompPD-IdR _)


  module _
    {M₁ : PreModel Σ ℓM₁ ℓ≤M₁ ℓ≈M₁}
    {M₂ : PreModel Σ ℓM₂ ℓ≤M₂ ℓ≈M₂}
    {M₃ : PreModel Σ ℓM₃ ℓ≤M₃ ℓ≈M₃}
    {M₄ : PreModel Σ ℓM₄ ℓ≤M₄ ℓ≈M₄} where

    CompPMM-Assoc :
        (f : PreModelMor M₁ M₂)
      → (g : PreModelMor M₂ M₃)
      → (h : PreModelMor M₃ M₄)
      → h ∘PM (g ∘PM f) ≡ (h ∘PM g) ∘PM f
    CompPMM-Assoc f g h = eqPMMor _ _ (∘p-Assoc ⟨ f ⟩PMM ⟨ g ⟩PMM ⟨ h ⟩PMM)


module _ (Th : GuardedTheory) where

  private module Th = GuardedTheory Th
  
  record Model (ℓ ℓ≤ ℓ≈ : Level) : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈)) where
    no-eta-equality

    field
      PM : PreModel Th.sig ℓ ℓ≤ ℓ≈
      eqns-hold : (e : Th.E) → Eval-eqn PM (Th.eqn e) 

    open PreModel PM public



-- Morphisms of models --

module _ {Th : GuardedTheory} where
  private module Th = GuardedTheory Th
  open PreModelMor

  -- Morphisms of models are simply morphisms of the underlying premodels
  ModelMor : (M : Model Th ℓM ℓ≤M ℓ≈M) (N : Model Th ℓN ℓ≤N ℓ≈N)
    → Type (ℓ-max (ℓ-max (ℓ-max ℓM ℓ≤M) ℓ≈M) (ℓ-max (ℓ-max ℓN ℓ≤N) ℓ≈N))
  ModelMor M N = PreModelMor (M .Model.PM) (N .Model.PM)

  ⟨_⟩MM : ∀ {M : Model Th ℓM ℓ≤M ℓ≈M} {N : Model Th ℓN ℓ≤N ℓ≈N}
    → ModelMor M N → PMor (M .Model.A) (N .Model.A)
  ⟨ f ⟩MM = ⟨ f ⟩PMM










{-
-- Pre-models:
module _ (Σ : Signature) where

  record PreModelStr {ℓ : Level} (ℓ≤ ℓ≈ : Level) (B : Type ℓ) :
    Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈)) where

    field
      is-predomain : PredomainStr ℓ≤ ℓ≈ B

    open PredomainStr is-predomain public
    Pre : Predomain ℓ ℓ≤ ℓ≈
    Pre = B , is-predomain

    field
      -- ⟦_⟧op : (f : Op Σ) → Env Pre (ar Σ f) → {!BCarrier!}
      ⟦_⟧op : (f : Op Σ) → PMor (Env Pre (ar Σ f)) Pre


  PreModel : ∀ ℓ ℓ≤ ℓ≈ → Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈))
  PreModel ℓ ℓ≤ ℓ≈ = TypeWithStr ℓ (PreModelStr ℓ≤ ℓ≈)
-}

{-
module _ (Σ : Signature) (M : PreModel Σ ℓ ℓ≤ ℓ≈) where

  private module M = PreModelStr (M .snd)
  
  eval : {Γ : Arity} {d : ℕ} → Env M.Pre Γ → Term Σ Γ d → ⟨ LaterP d M.Pre ⟩
  eval ρ t = ?
-}



{-

PreModel : (Σ : Signature) (ℓ ℓ≤ ℓ≈ : Level) → Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈))
PreModel Σ ℓ ℓ≤ ℓ≈  = Σ[ A ∈ Predomain ℓ ℓ≤ ℓ≈ ] ((f : Op Σ) → PMor (Env A (ar Σ f)) A)

module _ {Σ : Signature} where

  ⟨_⟩PM : PreModel Σ ℓ ℓ≤ ℓ≈ → Predomain ℓ ℓ≤ ℓ≈
  ⟨_⟩PM = fst

  _⟦_⟧op : (M : PreModel Σ ℓ ℓ≤ ℓ≈) → _
  _⟦_⟧op M = M .snd


module _ {Σ : Signature} where

  eval : {Γ : Arity} {d : ℕ} → (M : PreModel Σ ℓ ℓ≤ ℓ≈) → ⟨ Env ⟨ M ⟩PM Γ ⟩ → Term Σ Γ d → {!!}
  eval = {!!}
-}
