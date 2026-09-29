{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}

open import Common.Later
open import Common.Common

module Experiments.Test where

open import Agda.Primitive

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.List as List
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)

private
  variable
    ℓ ℓ' : Level


module _ (k : Clock) where

  private
    ▹_ : Type ℓ -> Type ℓ
    ▹ A = ▹_,_ k A

  data L (X : Type ℓ) : Type ℓ where
    η : X → L X
    θ : ▹ L X → L X

  iterate-next : {X : Type ℓ} (n : ℕ) → X → (▹_ ^ n) X
  iterate-next zero x = x
  iterate-next (suc n) x = next (iterate-next n x)

  -- (n : ℕ) → ((▹_ ^ n) X) ⊎ ⊤
  Extract : {X : Type ℓ} → L X → (n : ℕ) → (▹_ ^ n) (X ⊎ ⊤)
  Extract (η x) n = iterate-next n (inl x)
  Extract (θ x) zero = inr tt
  Extract (θ lx~) (suc n) = λ t → Extract (lx~ t) n

  Map : {X : Type ℓ} {Y : Type ℓ'} (f : X → Y) → (L X → L Y)
  Map f (η x) = η (f x)
  Map f (θ lx~) = θ (λ t → Map f (lx~ t))

  Bind : {X : Type ℓ} {Y : Type ℓ'} (f : X → L Y) → (L X → L Y)
  Bind f (η x) = f x
  Bind f (θ lx~) = θ (λ t → Bind f (lx~ t))


  -- next-surj : (X : Type ℓ) → Type ℓ
  -- next-surj X = ∀ (x~ : ▹ X) → fiber next x~

  -- test : {X : Type ℓ} → next-surj X → next-surj (L X)
  -- test H x~ .fst = {!!}
  -- test H x~ .snd = later-ext (λ t → {!refl!})



  data TermBad {X : Type ℓ} : L X → X → Type ℓ where
    term-η : ∀ x → TermBad (η x) x
    term-θ : ∀ lx~ x → ▸ (λ t → TermBad (lx~ t) x) → TermBad (θ lx~) x

  Ω-term' : {X : Type ℓ} → ∀ (x : X) → ▹ (TermBad (fix θ) x) → TermBad (fix θ) x
  Ω-term' x IH = subst (λ z → TermBad z x) (sym (fix-eq θ)) (term-θ (next (fix θ)) x IH)

  Ω-term : {X : Type ℓ} → ∀ (x : X) → TermBad (fix θ) x
  Ω-term x = fix (Ω-term' x)

  data Term {X : Type ℓ} : L X → X → Type ℓ where
    term-η : ∀ x → Term (η x) x
    term-δ : ∀ lx x → Term lx x → Term (θ (next lx)) x

  Ω-term-fail : {X : Type ℓ} → ∀ (x : X) → ▹ (Term (fix θ) x) → Term (fix θ) x
  Ω-term-fail x IH = subst (λ z → Term z x) (sym (fix-eq θ)) (term-δ (fix θ) x {!!})


  -------------------------------------------------


  data Bar : ℕ → Type ℓ-zero where
    nat : ∀ n → ℕ → Bar n
    list : ∀ n → List (Bar n) → Bar (suc n)

  process-bar : ∀ n → Bar n → ℕ
  process-bar n (nat .n x) = x
  process-bar .(suc n) (list n fs) = foldr (λ x acc → process-bar n x + acc) 0 fs



  data Foo : Type ℓ-zero where
    nat : ℕ → Foo
    list : List Foo → Foo


  process-naive : Foo → ℕ
  process-naive (nat n) = n
  process-naive (list fs) = foldr (λ x acc → process-naive x + acc) 0 fs


  recFoo : ∀ {B : Type ℓ}
    → (ℕ → B)
    → (List B → B)
    → Foo → B
  recFoo nat* list* (nat n) = nat* n
  recFoo nat* list* (list fs) = list* (List.map (recFoo nat* list*) fs)

  process : Foo → ℕ
  process x = recFoo (λ x → x) (foldr _+_ 0) x



  data List' (X : Type ℓ) : Type ℓ where
    nil : List' X
    cons : X → (▹ (List' X)) → List' X

  foldr' : ∀ {ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → ▹ B → B) → B → List' A → B
  foldr' f b nil = b
  foldr' f b (cons x xs~) = f x (λ t → foldr' f b (xs~ t))
  -- f (λ t → (xs~ t .fst) , (foldr' f b (xs~ t .snd))) -- f x (foldr f b xs)

  data Foo' : Type ℓ-zero where
    nat : ℕ → Foo'
    list : List' Foo' → Foo'

  data Foo'' : Type ℓ-zero where
    nat : ℕ → Foo''
    list : List (▹ Foo'') → Foo''

  data Foo''' : Type ℓ-zero where
    nat : ℕ → Foo'''
    list : ▹ (List Foo''') → Foo'''
  

  Foo→Foo' : Foo → Foo'
  Foo→Foo' (nat n) = nat n
  Foo→Foo' (list xs) = list (aux xs)
    where
      aux : List Foo → List' Foo'
      aux [] = nil
      aux (x ∷ xs) = cons (Foo→Foo' x) (λ t → aux xs)

  Foo→Foo'' : Foo → Foo''
  Foo→Foo'' (nat n) = nat n
  Foo→Foo'' (list xs) = list (aux xs)
    where
      aux : List Foo → List (▹ Foo'')
      aux [] = []
      aux (x ∷ xs) = (next (Foo→Foo'' x)) ∷ aux xs


  depth : Foo → ℕ
  depth (nat x) = 0
  depth (list xs) = aux xs
    where
      aux : List Foo → ℕ
      aux [] = 0
      aux (x ∷ xs) = 1 + max (depth x) (aux xs)

{-
  process'' : (f : Foo) → (▹_ ^ (depth f)) ℕ
  process'' (nat n) = n
  process'' (list []) = 0
  process'' (list (x ∷ xs)) = λ t → foldr' {!!} {!!} {!!}


  process' : ▹ (Foo' → ℕ) → Foo' → ℕ
  process' rec (nat n) = n
  process' rec (list fs) = {!!}   -- foldr' (λ x x₁ → rec {!!} {!!}) 0 fs
-}

  process'-Foo' : ▹ (Foo' → L ℕ) → Foo' → L ℕ
  process'-Foo' rec (nat n) = η n
  process'-Foo' rec (list xs) =
    foldr'
      (λ x l-acc~ → θ (λ t → Bind (λ process-x → Bind (λ acc → η (process-x + acc)) (l-acc~ t)) (rec t x)))
      (η 0) xs
  -- θ (λ t → foldr' (λ x ln~ → Map {!!} {!ln~ t!}) (η 0) fs)
  -- foldr' (λ x xs~ → θ (λ t → {!rec t!})) (η 0) fs


  process-Foo' : Foo' → L ℕ
  process-Foo' = fix process'-Foo'

  process-Foo'-iterable : (n : ℕ) → Foo' → L ℕ
  process-Foo'-iterable zero = process'-Foo' (next process-Foo')
  process-Foo'-iterable (suc n) = process'-Foo' (next (process-Foo'-iterable n))


  -------------------------------------------------

  process'-Foo : ▹ (Foo → L ℕ) → Foo → L ℕ
  process'-Foo rec (nat n) = η n
  process'-Foo rec (list xs) =
    foldr (λ x l-acc → θ (λ t → Bind (λ process-x → Bind (λ acc → η (process-x + acc)) l-acc) (rec t x)))
    (η 0) xs

  process-Foo : Foo → L ℕ
  process-Foo = fix process'-Foo

  process-Foo-iterable : (n : ℕ) → Foo → L ℕ
  process-Foo-iterable zero = process'-Foo (next process-Foo)
  process-Foo-iterable (suc n) = process'-Foo (next (process-Foo-iterable n))


  lemma : (f : Foo) →
    Σ[ i ∈ ℕ ] Σ[ n ∈ ℕ ] Extract (process-Foo-iterable i f) i ≡ iterate-next i (inl n)
  lemma f = {!!}
  

  -------------------------------------------------

  process'-Foo'' : ▹ (Foo'' → L ℕ) → Foo'' → L ℕ
  process'-Foo'' rec (nat n) = η n
  process'-Foo'' rec (list xs) =
    foldr (λ x~ l-acc → θ (λ t → Bind (λ process-x → Bind (λ acc → η (process-x + acc)) l-acc) (rec t (x~ t))))
    (η 0) xs

  process-Foo'' : Foo'' → L ℕ
  process-Foo'' = fix process'-Foo''


  process'-Foo''-alt : Foo'' → L ℕ
  process'-Foo''-alt (nat n) = η n
  process'-Foo''-alt (list xs) =
    foldr (λ x~ l-acc → θ (λ t → Bind (λ process-x → {!!}) (process'-Foo''-alt (x~ t)))) (η 0) xs


-------------------------------------------------

  process'-Foo''' : Foo''' → L ℕ
  process'-Foo''' (nat n) = η n
  process'-Foo''' (list xs~) = θ (λ t →
    foldr (λ x l-acc → Bind (λ process-x → {!!}) (process'-Foo''' x)) (η 0) (xs~ t))


  -------------------------------------------------------------------------------------
  -- Tests

  foo1 : Foo
  foo1 = nat 1

  foo2 : Foo
  foo2 = list (nat 1 ∷ nat 2 ∷ [])

  foo3 : Foo
  foo3 = list (nat 1 ∷ list (nat 2 ∷ nat 3 ∷ []) ∷ nat 4 ∷ [])

  foos : List Foo
  foos = nat 1 ∷ nat 2 ∷ (list (nat 3 ∷ nat 4 ∷ (list (nat 5 ∷ [])) ∷ [])) ∷ nat 6 ∷ []

  foo : Foo
  foo = list foos


  eq1 : Extract (process-Foo-iterable 0 foo1) 0 ≡ inl 1
  eq1 = refl

  eq2 : Extract (process-Foo-iterable 2 foo2) 2 ≡ iterate-next 2 (inl 3)
  eq2 = refl

  eq3 : Extract (process-Foo-iterable 5 foo3) 5 ≡ iterate-next 5 (inl 10)
  eq3 = refl

  eq4 : Extract (process-Foo-iterable 8 foo) 8 ≡ iterate-next 8 (inl 21)
  eq4 = refl


  eq1' : process'-Foo' (next process-Foo') (Foo→Foo' foo1) ≡ η 1
  eq1' = refl

  eq2' : Extract (process-Foo'-iterable 2 (Foo→Foo' foo2)) 2 ≡ iterate-next 2 (inl 3)
  eq2' = refl

  eq3' : Extract (process-Foo'-iterable 5 (Foo→Foo' foo3)) 5 ≡ iterate-next 5 (inl 10)
  eq3' = refl

  eq4' : Extract (process-Foo'-iterable 8 (Foo→Foo' foo)) 8 ≡ iterate-next 8 (inl 21)
  eq4' = refl

  


  


