{-# OPTIONS --cubical --rewriting #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.Adequacy.BigStepFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat hiding (_·_ ; _^_)
open import Cubical.Data.Nat.Order hiding (eq)
open import Cubical.Data.Empty.Base renaming (rec to exFalso)
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Embedding

open import Common.Common

open import Semantics.Adequacy.Partial



private
  variable
    ℓ ℓ' : Level


-- Notation and properties of functions from ℕ to (X + 1)
module PartialFunctions {X : Type ℓ} where

  -- Type alias for the codomain of the big-step term semantics.
  Fun : Type ℓ
  Fun = ℕ → X ⊎ ⊤

  isleft : (X ⊎ ⊤) → Type ℓ-zero
  isleft = Sum.rec (λ _ → ⊤) (λ _ → ⊥)

  terminates-in : Fun → ℕ → Type ℓ-zero
  terminates-in f n = isleft (f n)

  terminates : Fun → Type ℓ-zero
  terminates f = Σ[ n ∈ ℕ ] terminates-in f n

  -- If f terminates in n steps, then we can extract an element x for
  -- which f n = inl x.  Note that this does not require that n is the
  -- only value for which f n is inl. There may be different values of
  -- n for which f n is inl, leading to different extracted values.
  extract' : (f : Fun) → (n : ℕ) → terminates-in f n →
    (Σ[ x ∈ X ] (f n ≡ inl x))
  extract' f n =
    Sum.elim {C = λ fn → isleft fn → Σ[ x ∈ X ] (fn ≡ inl x)}
      (λ x _ → x , refl) (λ _ → ⊥.rec) (f n)

  -- Extract a value from a proof that f terminates.  Note that for
  -- different proofs of termination of f, i.e., different values of
  -- n, we may obtain different extracted values.
  extract : (f : Fun) → terminates f → X
  extract f (n , H) = extract' f n H .fst

  -- For each fixed n, terminating in n steps is a Prop.
  isProp-term-in-n : ∀ f n → isProp (terminates-in f n)
  isProp-term-in-n f n = Sum.elim {C = λ fn → isProp (isleft fn)}
    (λ _ → isPropUnit) (λ _ → isProp⊥) (f n)
  

  -- "Intensional" termination predicate for big-step terms.
  _↓fun[_]_ : Fun → ℕ → X → Type ℓ
  f ↓fun[ n ] x = f n ≡ inl x


  -- Termination in n steps to some (unspecified) value.
  _↓fun[_] : Fun → ℕ → Type ℓ
  f ↓fun[ n ] = Σ[ x ∈ X ] (f ↓fun[ n ] x)
  -- equivalently: fiber inl (f n) (except this reverses the equality
  -- above, i.e. inl x ≡ f n)

  -- Alternative termination predicate.
  _↓fun_ : Fun → X → Type ℓ
  f ↓fun x = Σ[ m ∈ ℕ ] f ↓fun[ m ] x

  term-lemma : ∀ f n x → f ↓fun[ n ] x → terminates-in f n
  term-lemma f n x f↓n = transport (λ i → isleft (sym f↓n i)) tt

  term-lemma-1 : ∀ f n x →
    f ↓fun[ n ] x →
    Σ[ p ∈ terminates-in f n ] (extract' f n p .fst ≡ x)
  term-lemma-1 f n x =
    Sum.elim {C = λ fn → fn ≡ inl x → Σ[ p ∈ isleft fn ] ((Sum.elim {C = λ fn' → isleft fn' → Σ[ x' ∈ X ] (fn' ≡ inl x')} (λ x _ → x , refl) (λ _ → ⊥.rec) fn) p .fst) ≡ x}
    (λ x' f↓n → tt , isEmbedding→Inj isEmbedding-inl x' x f↓n) (λ _ f↓n → exFalso (inl≠inr _ _ (sym f↓n))) (f n)
  -- f↓n = (term-lemma f n x f↓n) , {!!}

  term-lemma-2 : ∀ f n x →
    (p : terminates-in f n) →
    extract' f n p .fst ≡ x →
    f ↓fun[ n ] x
  term-lemma-2 f n x p eq = (extract' f n p .snd) ∙ (cong inl eq)


  {-
  -- Alternative definition of the above.
  _↓fun'[_] : Fun → ℕ → Type ℓ
  f ↓fun'[ n ] = aux (f n)
    where
      aux : _ → _
      aux (inl x) = ⊤*
      aux (inr tt) = ⊥*

  ↓fun→↓fun' : (f : Fun) (n : ℕ) →
    f ↓fun[ n ] → f ↓fun'[ n ]
  ↓fun→↓fun' f n (x , eq) with (f n)
  ... | inl x' = tt*
  ... | inr tt = ⊥.rec (inl≠inr _ _ (sym eq))


  ↓fun'→↓fun : (f : Fun) (n : ℕ) →
    f ↓fun'[ n ] → f ↓fun[ n ]
  ↓fun'→↓fun f n H with (f n)
  ... | inl x = x , refl
  -}


  -- If a function terminates at n with x and with y, then x ≡ y.
  ↓n-unique : (f : Fun) → (n : ℕ) → (x y : X) →
    f ↓fun[ n ] x → f ↓fun[ n ] y → x ≡ y
  ↓n-unique f n x y f↓nx f↓ny =
    isEmbedding→Inj isEmbedding-inl x y (sym f↓nx ∙ f↓ny)

  -- Divergence at n
  _↑fun[_] : Fun → ℕ → Type ℓ
  f ↑fun[ n ] = ∀ m → m ≤ n → (f m ≡ inr tt)


  -- A function cannot both terminate at n and diverge at n
  coherence : (f : Fun) (n : ℕ) (x : X) →
    f ↓fun[ n ] x → f ↑fun[ n ] → ⊥
  coherence f n x f↓n f↑ = inl≠inr x tt (sym f↓n ∙ (f↑ n ≤-refl))

  -- Stronger uniqueness property stating that a function can
  -- terminate with at most one value. This isn't true for the Fun
  -- type in general, but it *is* true of the functions in the image
  -- of the big-step semantics.
  --
  -- TODO: is this a good definition?
  ↓-unique : Fun → Type ℓ
  ↓-unique f = (n m : ℕ) (x y : X) →
    f ↓fun[ n ] x → f ↓fun[ m ] y → (n ≡ m) × (x ≡ y)


  terminates-prop : Fun → Type ℓ-zero
  terminates-prop f = isProp (terminates f)

  BigStepFun : Type ℓ
  BigStepFun = Σ[ f ∈ Fun ] terminates-prop f

  ↓-unique→term-prop : (f : Fun) → ↓-unique f → terminates-prop f
  ↓-unique→term-prop f H-unique (n1 , H1) (n2 , H2) =
    ΣPathP (fst aux , isProp→PathP (λ i → isProp-term-in-n f (fst aux i)) H1 H2)
    where
      aux : (n1 ≡ n2) × _
      aux = H-unique n1 n2 _ _ (extract' f n1 H1 .snd) (extract' f n2 H2 .snd)
  

  -- This definition seems stronger (equivalence seems to require that X is a set)
  ↓-unique' : Fun → Type ℓ
  ↓-unique' f = isProp (Σ[ n ∈ ℕ ] Σ[ x ∈ X ] (f ↓fun[ n ] x))

  ↓-unique'→↓-unique : (f : Fun) → ↓-unique' f → ↓-unique f
  ↓-unique'→↓-unique f H n m x y f↓x f↓y = (λ i → H (n , x , f↓x) (m , y , f↓y) i .fst) , λ i → H (n , x , f↓x) (m , y , f↓y) i .snd .fst
    -- λ i → H (n , x , f↓x) (m , y , f↓y) i .snd .fst , ?

  ↓-unique→↓-unique' : isSet X → (f : Fun) → ↓-unique f → ↓-unique' f
  ↓-unique→↓-unique' isSetX f H (n1 , x1 , p1) (n2 , x2 , p2) =
    ΣPathP (n1≡n2 , ΣPathP (x1≡x2 , baz) ) -- ΣPathP (x1≡x2 , {!sym (cong f n1≡n2 ∙ p2)!}))
    where
      n1≡n2 : n1 ≡ n2
      n1≡n2 = H n1 n2 x1 x2 p1 p2 .fst

      -- x1≡x2 : x1 ≡ x2
      -- x1≡x2 = H n1 n2 x1 x2 p1 p2 .snd

      -- Both sides have type Σ[ v ∈ X ] ((inl v) ≡ (f n1))
      foo : (x1 , sym p1) ≡
            (x2 , sym (cong f n1≡n2 ∙ p2))
      foo = isEmbedding→hasPropFibers isEmbedding-inl (f n1) (x1 , sym p1) (x2 , sym (cong f n1≡n2 ∙ p2))

      x1≡x2 : x1 ≡ x2
      x1≡x2 = cong fst foo

      bar : PathP (λ i → inl (x1≡x2 i) ≡ f n1)
        (sym p1) (sym (cong f n1≡n2 ∙ p2))
      bar = cong snd foo
       
      baz : PathP (λ i → f (n1≡n2 i) ≡ (inl (x1≡x2 i))) p1 p2
      baz = {!symP-fromGoal bar!}



-- Extensional collapse of a big-step function:

module _ {X : Type ℓ} where

  open PartialFunctions {X = X}

  collapse : BigStepFun → Part X ℓ-zero
  collapse f .fst .fst = terminates (f .fst)
  collapse f .fst .snd = f .snd
  collapse f .snd = extract (f .fst)

  -- What if we instead said that collapse took a function that may be
  -- defined more than once? Then the proposition would be that there
  -- exists n such that f n is defined, and the function took such a
  -- proof and returned the smallest n for which f n is defined.



