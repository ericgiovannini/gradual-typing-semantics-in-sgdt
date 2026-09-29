{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Syntax.FineGrained.LogicalRelation (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.Structure
open import Cubical.Data.List
open import Cubical.Data.Sigma as Data
open import Cubical.Data.Nat as Nat

open import Syntax.Types as Syn
open import Syntax.Surface
open import Syntax.FineGrained.Operational

open import Semantics.Concrete.Types k as SemTypes using (U ; F)
open import Semantics.Concrete.Predomain.FreeErrorDomainOpaque k
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions
open import Semantics.Concrete.Dyn.DynInstantiated k hiding (S)
open import Semantics.Concrete.Relations.Base
open import Semantics.Concrete.Perturbation.QuasiRepresentation k

open import Syntax.FineGrained.Denotation.Types k as Den

open F-ob

private
  variable
    ℓ ℓ' ℓR : Level
    
    Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
    R S T R' S' T' : Ty
    b b' c c' d d' : S ⊑ S'

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

Empty : Ctx
Empty = []

Term : Ty → Type
Term T = Tm Empty T





-- Since dyn is defined by induction and guarded recursion, the
-- logical relation for dyn must be defined by induction and guarded
-- recursion.
--
-- On the other hand, the value logical relation is defined by
-- induction over the syntactic type.

-- Question: how do we deal with dyn values that involve a "composed" upcast, e.g.
--
--   up (inj-times (inj-nat × inj-nat)) (pair 1 2)
--
-- Ans: These are not actually values!




module _
  (S : Ty)
  (R : ⟨ ⟦ S ⟧ty ⟩ → Value Empty S → Type)
 
  where

  data LiftRel : ⟨ U (F ⟦ S ⟧ty) ⟩ → Term S → Type where
    lift-η : ∀ x (M : Term S) (V : Value Empty S)
      → M ⇒[ 0 ] (V .fst)
      → R x V
      → LiftRel (ηM $ x) M

    lift-℧ : ∀ (M : Term S)
      → M →[ 0S ] err
      → LiftRel (℧M {A' = UnitP} $ tt) M

    lift-θ : ∀ (x~ : ▹ ⟨ U (F ⟦ S ⟧ty) ⟩) (M : Term S) {M' M'' : Term S} {k : Nat.ℕ}
      → M →*[ k ] M'
      → M' →[ 1S ] M''
      → ▸ (λ t → (LiftRel (x~ t) M''))
      → LiftRel (θM $ x~) M


data LR-Dyn (R : ⟨ ⟦ dyn ⟧ty ⟩ → Value Empty dyn → Type)
  : ⟨ ⟦ dyn ⟧ty ⟩ → Value Empty dyn → Type

LRDyn : ⟨ ⟦ dyn ⟧ty ⟩ → Value Empty dyn → Type
LRDyn = fix {k} (λ R~ → LR-Dyn λ x V → ▸ (λ t → R~ t x V))

-- Value relation
LR : (T : Ty) → ⟨ ⟦ T ⟧ty ⟩ → Value Empty T → Type

LR nat n V = (Result n (V .fst))

LR dyn d V = LRDyn d V

LR (S ⇀ T) f Vf =
  (∀ (x : ⟨ ⟦ S ⟧ty ⟩) (V : Value Empty S)
    → LR S x V
    → LiftRel T (LR T) (f $ x) (app (Vf .fst) (V .fst)))

LR (T₁ Syn.× T₂) x V = Σ[ V₁ ∈ Value Empty T₁ ] Σ[ V₂ ∈ Value Empty T₂ ]
  (V ≡ pairVal V₁ V₂)
  Data.× (LR T₁ (x .fst) V₁)
  Data.× (LR T₂ (x .snd) V₂)


data LR-Dyn R where
  dyn-nat : ∀ (n : Nat.ℕ) (V : Value Empty nat)
    -- → LR-Dyn (embV _ _ _ (injNat .snd .fst) $ n) {!up ? ?!}
    → (Result n (V .fst)) -- same logic as for the nat case of LR below
    → LR-Dyn R (embNat $ n) (upInjNatVal V) 

  dyn-times : ∀ (d₁ d₂ : ⟨ ⟦ dyn ⟧ty ⟩) {S : Ty}
    → {V : Value Empty (dyn Syn.× dyn)}
    → {V₁ V₂ : Value Empty dyn}
    → (V ≡ pairVal V₁ V₂)
    → LR-Dyn R d₁ V₁
    → LR-Dyn R d₂ V₂
    → LR-Dyn R (embTimes $ (d₁ , d₂)) (upInjTimesVal V)

  dyn-arr : ∀ (f : ⟨ ⟦ dyn ⇀ dyn ⟧ty ⟩) → (Vf : Value Empty (dyn ⇀ dyn))
    → (∀ (x : ⟨ ⟦ dyn ⟧ty ⟩) (V : Value Empty dyn)
      → R x V → LiftRel dyn (LR-Dyn R) (f $ x) (app ⟨ Vf ⟩v ⟨ V ⟩v))
    → LR-Dyn R (embArr $ f) (upInjArrVal Vf)



{-

-- This doesn't pass the termination checker.  The issue is that
-- LiftRel is too general: the "value relation" parameter has to work
-- for any type, so when we refer to LiftRel in the definition of the
-- value logical relation, we have to pass the whole relation in as an
-- argument to LiftRel.

-- There's also an issue with lack of positivity in the dyn-arr
-- constructor of LR-Dyn.

module _
  (R : (S : Ty) → ⟨ ⟦ S ⟧ty ⟩ → Value Empty S → Type)
  (S : Ty)
  where

  data LiftRel : ⟨ U (F ⟦ S ⟧ty) ⟩ → Term S → Type where
    lift-η : ∀ x (M : Term S) (V : Value Empty S)
      → M ⇒[ 0 ] (V .fst)
      → R S x V
      → LiftRel (ηM $ x) M

    lift-℧ : ∀ (M : Term S)
      → M →[ 0S ] err
      → LiftRel (℧M {A' = UnitP} $ tt) M

    lift-θ : ∀ (x~ : ▹ ⟨ U (F ⟦ S ⟧ty) ⟩) (M : Term S) {M' M'' : Term S} {k : Nat.ℕ}
      → M →*[ k ] M'
      → M' →[ 1S ] M''
      → ▸ (λ t → (LiftRel (x~ t) M''))
      → LiftRel (θM $ x~) M



data LR-Dyn (R : ⟨ ⟦ dyn ⟧ty ⟩ → Value Empty dyn → Type)
  : ⟨ ⟦ dyn ⟧ty ⟩ → Value Empty dyn → Type

LRDyn : ⟨ ⟦ dyn ⟧ty ⟩ → Value Empty dyn → Type
LRDyn = fix {k} (λ R~ → LR-Dyn λ x V → ▸ (λ t → R~ t x V))

-- Value relation
LR : (T : Ty) → ⟨ ⟦ T ⟧ty ⟩ → Value Empty T → Type

LR nat n V = (Result n (V .fst))

LR dyn d V = LRDyn d V

LR (S ⇀ T) f Vf =
  (∀ (x : ⟨ ⟦ S ⟧ty ⟩) (V : Value Empty S)
    → LR S x V
    → LiftRel LR T (f $ x) (app (Vf .fst) (V .fst)))

LR (T₁ Syn.× T₂) x V = Σ[ V₁ ∈ Value Empty T₁ ] Σ[ V₂ ∈ Value Empty T₂ ]
  (V ≡ pairVal V₁ V₂)
  Data.× (LR T₁ (x .fst) V₁)
  Data.× (LR T₂ (x .snd) V₂)


data LR-Dyn R where
  dyn-nat : ∀ (n : Nat.ℕ) (V : Value Empty nat)
    -- → LR-Dyn (embV _ _ _ (injNat .snd .fst) $ n) {!up ? ?!}
    → (Result n (V .fst)) -- same logic as for the nat case of LR below
    → LR-Dyn R (embNat $ n) (upInjNatVal V) 

  dyn-times : ∀ (d₁ d₂ : ⟨ ⟦ dyn ⟧ty ⟩) {S : Ty}
    → {V : Value Empty (dyn Syn.× dyn)}
    → {V₁ V₂ : Value Empty dyn}
    → (V ≡ pairVal V₁ V₂)
    → LR-Dyn R d₁ V₁
    → LR-Dyn R d₂ V₂
    → LR-Dyn R (embTimes $ (d₁ , d₂)) (upInjTimesVal V)

  dyn-arr : ∀ (f : ⟨ ⟦ dyn ⇀ dyn ⟧ty ⟩) → (Vf : Value Empty (dyn ⇀ dyn))
    → (∀ (x : ⟨ ⟦ dyn ⟧ty ⟩) (V : Value Empty dyn)
      → R x V → LiftRel {!!} dyn (f $ x) (app ⟨ Vf ⟩v ⟨ V ⟩v))
      -- → R x V → LR-Exp dyn (f $ x) (app ⟨ Vf ⟩v ⟨ V ⟩v))
    → LR-Dyn R (embArr $ f) (upInjArrVal Vf)


-}




{-

-- This attempt has an issue with positivity.

opaque
  unfolding F-ob

  data LR-Dyn (R : ⟨ ⟦ dyn ⟧ty ⟩ → Value Empty dyn → Type) : ⟨ ⟦ dyn ⟧ty ⟩ → Value Empty dyn → Type

  LRDyn : ⟨ ⟦ dyn ⟧ty ⟩ → Value Empty dyn → Type

  LR :     (T : Ty) → ⟨ ⟦ T ⟧ty ⟩       → Value Empty T → Type
  LR-Exp : (T : Ty) → ⟨ U (F ⟦ T ⟧ty) ⟩ → Term T        → Type


  -- Expression relation
  LR-Exp T (η x) M = Σ[ V ∈ Value Empty T ] (M ⇒[ 0 ] (V .fst)) Data.× (LR T x V)
  LR-Exp T ℧ M = M ⇒[ 0 ] err
  LR-Exp T (θ x) M = Σ[ M' ∈ Term T ] Σ[ M'' ∈ Term T ]
    (M →*[ 0 ] M') Data.× (M' ⇒[ 1 ] M'') Data.× {!!}

  -- Value relation
  LR nat n V = (Result n (V .fst))

  LR dyn d V = LRDyn d V

  LR (S ⇀ T) f Vf =
    (∀ (x : ⟨ ⟦ S ⟧ty ⟩) (V : Value Empty S)
      → LR S x V
      → LR-Exp T (f $ x) (app (Vf .fst) (V .fst)))

  LR (T₁ Syn.× T₂) x V = Σ[ V₁ ∈ Value Empty T₁ ] Σ[ V₂ ∈ Value Empty T₂ ]
    (V ≡ pairVal V₁ V₂)
    Data.× (LR T₁ (x .fst) V₁)
    Data.× (LR T₂ (x .snd) V₂)


  data LR-Dyn R where
    dyn-nat : ∀ (n : ℕ) (V : Value Empty nat)
      -- → LR-Dyn (embV _ _ _ (injNat .snd .fst) $ n) {!up ? ?!}
      → (Result n (V .fst)) -- same logic as for the nat case of LR below
      → LR-Dyn R (embNat $ n) (upInjNatVal V) 

    dyn-times : ∀ (d₁ d₂ : ⟨ ⟦ dyn ⟧ty ⟩) {S : Ty}
      → {V : Value Empty (dyn Syn.× dyn)}
      → {V₁ V₂ : Value Empty dyn}
      → (V ≡ pairVal V₁ V₂)
      → LR-Dyn R d₁ V₁
      → LR-Dyn R d₂ V₂
      → LR-Dyn R (embTimes $ (d₁ , d₂)) (upInjTimesVal V)

    dyn-arr : ∀ (f : ⟨ ⟦ dyn ⇀ dyn ⟧ty ⟩) → (Vf : Value Empty (dyn ⇀ dyn))
      → (∀ (x : ⟨ ⟦ dyn ⟧ty ⟩) (V : Value Empty dyn)
        → R x V → LR-Exp dyn (f $ x) (app ⟨ Vf ⟩v ⟨ V ⟩v))
      → LR-Dyn R (embArr $ f) (upInjArrVal Vf)

  LRDyn = fix {k} (λ R~ → LR-Dyn λ x V → ▸ (λ t → R~ t x V))

-}




{-
module _ (X : Type ℓR) where

  data LR : (T : Ty) → ⟨ ⟦ T ⟧ty ⟩ → Term T → Type ℓR where

    -- If M steps with 0 unfoldings to some M' which is a *synactic
    -- nat normal form* for some natural number n, then n is related
    -- to M.
    LR-nat : ∀ (M M' : Term nat) (n : ℕ)
      → M ⇒[ 0 ] M'
      → Result n M'
      → LR nat n M

    LR-times : ∀ {T₁ T₂ : Ty} (M : Term (T₁ Syn.× T₂)) (x : ⟨ ⟦ T₁ Syn.× T₂ ⟧ty ⟩)
      → {M₁ : Term T₁} {M₂ : Term T₂}
      → M ⇒[ 0 ] (pair M₁ M₂) -- M₁ and M₂ should be values?
      → LR T₁ (x .fst) M₁
      → LR T₂ (x .snd) M₂
      → LR (T₁ Syn.× T₂) x M

    LR-fun : ∀ {S T : Ty} (M Vf : Term (S ⇀ T)) (f : ⟨ ⟦ S ⇀ T ⟧ty ⟩)
      → M ⇒[ 0 ] Vf
      → isValue Vf
      → (∀ (x : ⟨ ⟦ S ⟧ty ⟩) (N : Term S) → LR S x N → LR T {!f $ x!} {!!})
      → LR (S ⇀ T) f M

-}
