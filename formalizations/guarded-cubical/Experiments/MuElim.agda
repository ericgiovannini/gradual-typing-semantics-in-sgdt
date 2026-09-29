{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --termination-depth=5 #-}
{-# OPTIONS --polarity #-}
{-# OPTIONS --sized-types #-}

open import Common.Common

module Experiments.MuElim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

import Cubical.Data.List as List
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Nat
open import Cubical.Data.Empty

open import Agda.Builtin.Size


private
  variable
    ℓ ℓ' ℓF : Level
    ℓA ℓA' ℓB ℓB' : Level
    ℓR ℓR₁ ℓR₂ : Level
    ℓX ℓY : Level


------------------------------------------------



data Mu' (i : Size) (F : {ℓF : Level} → @++ Type ℓF → Type ℓF) : Type where
  fold : ∀ {j : Size< i} → F (Mu' j F) → Mu' i F

module _
  (F : {ℓF : Level} → @++ Type ℓF → Type ℓF)
  (F-mor : ∀ {ℓX ℓY}
    → (X : Type ℓX) (Y : Type ℓY)
    → @++ (X → Y) → (F X → F Y))
  where

  elimMu'Bad : ∀ {B : (i : Size) → Mu' i F → Type ℓB}
    → ({i : Size} {j : Size< i}
        → (h : F (Σ (Mu' j F) (B j)))
        → B i ((fold {i = i} {j = j} (F-mor (Σ (Mu' j F) (B j)) (Mu' j F) fst h))) 
      )
    → ({i : Size} → (x : Mu' i F) → B i x)
  elimMu'Bad fold* {i = i} (fold {j = j} x') =
    transport
      {!!}
      (fold* {i = ↑ j} {j = j} (F-mor _ _ (λ q → q , (elimMu'Bad fold* {i = j} q)) x'))

     -- ((h : F (Σ (Mu F) P)) → P (fold (F-mor _ _ fst h)))



  elimMu' : ∀ {B : Mu' ∞ F → Type ℓB}
    → ({i : Size} {j : Size< i}
        → (h : F (Σ (Mu' j F) B))
        → B ((fold {i = i} {j = j} (F-mor (Σ (Mu' j F) B) (Mu' j F) fst h))) 
      )
    → ({i : Size} → (x : Mu' i F) → B x)
  elimMu' {B = B} fold* {i = i} (fold {j = j} x') =
    transport
      (cong B (cong fold {!!}))
      (fold* {i = ↑ j} {j = j} (F-mor _ _ (λ q → q , (elimMu' fold* {i = j} q)) x'))


  recMu' : ∀ {B : Type} {i : Size}
    → (F B → B)
    → (Mu' i F → B)
  recMu' {B = B} fold* (fold {j = j} x') =
    fold* (F-mor (Mu' j F) B (recMu' {i = j} fold*) x')


module _ (F : {ℓF : Level} → @++ Type ℓF → Type ℓF) where

  Mu : Type
  Mu = Mu' ∞ F

  module _
    (F-mor : ∀ {ℓX ℓY}
      → (X : Type ℓX) (Y : Type ℓY)
      → @++ (X → Y) → (F X → F Y))
    where
    
    recMu : ∀ {B : Type} {i : Size}
      → (F B → B)
      → (Mu → B)
    recMu fold* x = recMu' F F-mor fold* x

    elimMuBad : ∀ {B : Mu → Type ℓB}
      → ((h : F (Σ Mu B))
        → B ((fold (F-mor (Σ Mu B) Mu fst h))))
      → ((x : Mu) → B x)
    elimMuBad {B = B} fold* x = elimMu'Bad F F-mor {B = λ _ → B} fold*' x
      where
        fold*' : {i : Size} {j : Size< i} (h : F (Σ (Mu' j F) B))
          → B (fold (F-mor (Σ (Mu' j F) B) (Mu' j F) fst h))
        fold*' h = {!fold* ?!}
    -- (fold x') = elimMu' F F-mor {!!} {!x'!}

    elimMu : ∀ {B : Mu → Type ℓB}
      → ((h : F (Σ Mu B))
        → B ((fold (F-mor (Σ Mu B) Mu fst h))))
      → ((x : Mu) → B x)
    elimMu {B = B} fold* x = elimMu' F F-mor {B = B} fold*' x
      where
        fold*' : {i : Size} {j : Size< i} (h : F (Σ (Mu' j F) B))
          → B (fold (F-mor (Σ (Mu' j F) B) (Mu' j F) (λ r → fst r) h))
        fold*' h = {!fold* ?!}




{-

data Mu (F : @++ Type ℓ → Type ℓ) : Type ℓ where
  fold : F (Mu F) → Mu F


module _
  (F : @++ Type ℓ → Type ℓ) where

  unfoldMu : Mu F → F (Mu F)
  unfoldMu (fold x) = x

  module _ (F-rel : @++ (Mu F → Type ℓ) → (F (Mu F)) → Type ℓ) where

    data MuInd : Mu F → Type ℓ where
      fold-ind : ∀ {x' : F (Mu F)} → F-rel MuInd x' → MuInd (fold x')

    indMu : (B : Mu F → Type ℓB) → Type (ℓ-max ℓ ℓB)
    indMu B = (x : Mu F) → MuInd x → B x

    indMu→ind : ∀ (B : Mu F → Type ℓB) → indMu B → {!!}
    indMu→ind B = {!!}



module _
  (F : @++ Type ℓ → Type ℓ)
  (F-mor : ∀ (X Y : Type ℓ) →
    @++ (X → Y) → (F X → F Y)) where

  recMu : ∀ {B : Type ℓ}
    → (F B → B)
    → (Mu F → B)
  recMu fold* (fold x) = fold* (F-mor (Mu F) _ (recMu fold*) x)


  module _ {B : Type ℓ}
    (fold* : F B → B)
    (ind : @++ (Mu F → B → Type ℓ) → (F (Mu F) → F B → Type ℓ))
    where
    
    data recMuGraph : Mu F → B → Type ℓ where
      test : ∀ fx fb → (ind recMuGraph fx fb) → recMuGraph (fold fx) (fold* fb)

    total : ∀ (x : Mu F) → ∃![ b ∈ B ] (recMuGraph x b)
    total (fold x) = (fold* {!!} , (test x {!!} {!!})) , {!!}


  module _ {B : Type ℓ}
    (fold* : F B → B)
    (F-rel : @++ (Mu F → Type ℓ) → (F (Mu F)) → Type ℓ)
    (F-mor : ∀ (X Y : Type ℓ) → @++ (X → Y) → (F X → F Y))
    where

    data Def : Mu F → Type ℓ
    f₀ : (x : Mu F) → Def x → B

    data Def where
      def-fold : {x' : F (Mu F)} → (p : F-rel Def x') → Def (fold x')

    data Def' : F (Mu F) → Type ℓ where
      foo : {x : Mu F} → (p : Def x) → Def' (unfoldMu F x)

    lemDef : ∀ x → F-rel Def (unfoldMu F x) → Def x
    lemDef x = {!!}

    f₀ (fold x') (def-fold p) = fold* (F-mor (Mu F) B (λ x → f₀ x {!!}) x')


  -- ind : (P : Mu F → Type ℓ)
  --   → ((h : F (Σ (Mu F) P)) → P (fold (F-mor _ _ fst h)))
  --   → (x : Mu F) → P x
  -- ind P p (fold x) = transport {!!} (p (F-mor _ _ (λ q → q , ind P p q) x))


-}
