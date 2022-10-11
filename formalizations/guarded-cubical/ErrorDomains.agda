{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Later

module ErrorDomains(k : Clock) where

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Data.Nat

private
  variable
    l : Level
    A B : Set l
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A 

Predomain : Set₁
Predomain = Poset ℓ-zero ℓ-zero
record MonFun (X Y : Predomain) : Set where
  module X = PosetStr (X .snd)
  module Y = PosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    f : (X .fst) → (Y .fst)
    isMon : ∀ {x y} → x ≤X y → f x ≤Y f y

▸' : ▹ Predomain → Predomain
▸' X = ((@tick x : Tick k) → (X x) .fst) ,
       posetstr (fix {k = k} (λ _,_≤_ x₁ x₂ → ▸ λ x → x , x₁ ≤ x₂))
                (fix {k = k} λ proofs → isposet {!!} {!!} {!!} {!!} {!!})

▸''_ : Predomain → Predomain
▸'' X = ▸' (next X)

record ErrorDomain : Set₁ where
  field
    X : Predomain
  module X = PosetStr (X .snd)
  _≤_ = X._≤_
  field
    ℧ : X .fst
    ℧⊥ : ∀ x → ℧ ≤ x

    θ : MonFun (▸'' X) X

data L℧ (X : Set) : Set where
  η : X → L℧ X
  ℧ : L℧ X
  θ : ▹ (L℧ X) → L℧ X


-- Showing that L is a monad

mapL' : (A -> B) -> ▹ (L℧ A -> L℧ B) -> L℧ A -> L℧ B
mapL' f map_rec (η x) = η (f x)
mapL' f map_rec ℧ = ℧
mapL' f map_rec (θ l_la) = θ (map_rec ⊛ l_la)
-- mapL' f map_rec (θ-next x i) = θ-next {!!} {!!}

mapL : (A -> B) -> L℧ A -> L℧ B
mapL f = fix (mapL' f)

mapL-comp : {A B C : Set} (g : B -> C) (f : A -> B) (x : L℧ A) ->
 mapL g (mapL f x) ≡ mapL (g ∘ f) x
mapL-comp g f x = {!!}



ret : {X : Set} -> X -> L℧ X
ret = η

-- rename to ext?
bind' : ∀ {A B} -> (A -> L℧ B) -> ▹ (L℧ A -> L℧ B) -> L℧ A -> L℧ B
bind' f bind_rec (η x) = f x
bind' f bind_rec ℧ = ℧
bind' f bind_rec (θ l_la) = θ (bind_rec ⊛ l_la)


-- fix : ∀ {l} {A : Set l} → (f : ▹ k , A → A) → A
bind : L℧ A -> (A -> L℧ B) -> L℧ B
bind {A} {B} la f = (fix (bind' f)) la

ext : (A -> L℧ B) -> L℧ A -> L℧ B
ext f la = bind la f



bind-eta : ∀ (a : A) (f : A -> L℧ B) -> bind (η a) f ≡ f a
bind-eta a f =
  fix (bind' f) (ret a) ≡⟨ (λ i → fix-eq (bind' f) i (ret a)) ⟩
  (bind' f) (next (fix (bind' f))) (ret a) ≡⟨ refl ⟩
  f a ∎

bind-err : (f : A -> L℧ B) -> bind ℧ f ≡ ℧
bind-err f =
  fix (bind' f) ℧ ≡⟨ (λ i → fix-eq (bind' f) i ℧) ⟩
  (bind' f) (next (fix (bind' f))) ℧ ≡⟨ refl ⟩
  ℧ ∎

{-
bind-theta : (f : A -> L℧ B)
             (l : ▹ (L℧ A)) ->
             (fix (bind' f)) (θ l) ≡ θ (fix (bind' f) <$> l)
bind-theta f l =
  (fix (bind' f)) (θ l)                    ≡⟨ (λ i → fix-eq (bind' f) i (θ l)) ⟩
  (bind' f) (next (fix (bind' f))) (θ l)   ≡⟨ refl ⟩
  θ (fix (bind' f) <$> l) ∎
-}

bind-theta : (f : A -> L℧ B)
             (l : ▹ (L℧ A)) ->
             bind (θ l) f ≡ θ (ext f <$> l)
bind-theta f l =
  (fix (bind' f)) (θ l)                    ≡⟨ (λ i → fix-eq (bind' f) i (θ l)) ⟩
  (bind' f) (next (fix (bind' f))) (θ l)   ≡⟨ refl ⟩
  θ (fix (bind' f) <$> l) ∎


id : {A : Set} -> A -> A
id x = x



monad-unit-l : ∀ (a : A) (f : A -> L℧ B) -> bind (ret a) f ≡ f a
monad-unit-l = bind-eta

monad-unit-r : (la : L℧ A) -> bind la ret ≡ la
monad-unit-r = fix lem
  where
    lem : ▹ ((la : L℧ A) -> bind la ret ≡ la) ->
          (la : L℧ A) -> bind la ret ≡ la
    lem IH (η x) = monad-unit-l x ret
    lem IH ℧ = bind-err ret
    lem IH (θ x) = fix (bind' ret) (θ x)
                     ≡⟨ bind-theta ret x ⟩
                   θ (fix (bind' ret) <$> x)
                     ≡⟨ refl ⟩
                   θ ((λ la -> bind la ret) <$> x)
                     -- we get access to a tick since we're under a theta
                     ≡⟨ (λ i → θ λ t → IH t (x t) i) ⟩
                   θ (id <$> x)
                     ≡⟨ refl ⟩
                   θ x ∎


-- Should we import this?
-- _∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
-- (g ∘ f) x = g (f x)

map-comp : {A B C : Set} (g : B -> C) (f : A -> B) (x : ▹_,_ k _) ->
  g <$> (f <$> x) ≡ (g ∘ f) <$> x
map-comp g f x = -- could just say refl for the whole thing
  map▹ g (map▹ f x)          ≡⟨ refl ⟩
  (λ α -> g ((map▹ f x) α)) ≡⟨ refl ⟩
  -- (λ α -> g ((λ β -> f (x β)) α)) ≡⟨ refl ⟩
  (λ α -> g (f (x α))) ≡⟨ refl ⟩
  map▹ (g ∘ f) x ∎


monad-assoc-def =
  {A B C : Set} ->
  (f : A -> L℧ B) (g : B -> L℧ C) (la : L℧ A) ->
  bind (bind la f) g ≡ bind la (λ x -> bind (f x) g)

monad-assoc : monad-assoc-def
monad-assoc = fix lem
  where
    lem : ▹ monad-assoc-def -> monad-assoc-def

    -- Goal: bind (bind (η x) f) g ≡ bind (η x) (λ y → bind (f y) g)
    lem IH f g (η x) =
      bind ((bind (η x) f)) g                    ≡⟨ (λ i → bind (bind-eta x f i) g) ⟩
      bind (f x) g                               ≡⟨ sym (bind-eta x (λ y -> bind (f y) g)) ⟩
      bind (η x) (λ y → bind (f y) g) ∎


    -- Goal: bind (bind ℧ f) g ≡ bind ℧ (λ x → bind (f x) g)
    lem IH f g ℧ =
      bind (bind ℧ f) g           ≡⟨ (λ i → bind (bind-err f i) g) ⟩
      bind ℧ g                    ≡⟨ bind-err g ⟩
      ℧                           ≡⟨ sym (bind-err (λ x -> bind (f x) g)) ⟩
      bind ℧ (λ x → bind (f x) g) ∎


    -- Goal: bind (bind (θ x) f) g ≡ bind (θ x) (λ y → bind (f y) g)
    -- IH: ▹ (bind (bind la f) g ≡ bind la (λ x -> bind (f x) g))
    lem IH f g (θ x) =
       bind (bind (θ x) f) g
                              ≡⟨ (λ i → bind (bind-theta f x i) g) ⟩

       bind (θ (ext f <$> x)) g
                              ≡⟨ bind-theta g (ext f <$> x) ⟩

                                               -- we can put map-comp in the hole here and refine (but it's wrong)
       θ ( ext g <$> (ext f <$> x) )
                             ≡⟨ refl ⟩ 

       θ ( (ext g ∘ ext f) <$> x )
                             ≡⟨ refl ⟩

       θ ( ((λ lb -> bind lb g) ∘ (λ la -> bind la f)) <$> x )
                             ≡⟨ refl ⟩ -- surprised that this works

       θ ( (λ la -> bind (bind la f) g)  <$> x )
                             ≡⟨ (λ i → θ (λ t → IH t f g (x t) i)) ⟩

       θ ( (λ la -> bind la (λ y -> bind (f y) g)) <$> x )
                             ≡⟨ refl ⟩

       θ ( (ext (λ y -> bind (f y) g)) <$> x )
                             ≡⟨ sym (bind-theta ((λ y -> bind (f y) g)) x) ⟩
                             
       bind (θ x) (λ y → bind (f y) g) ∎



  -- bind (θ ( (λ la -> bind la f) <$> x)) g ≡⟨ {!!} ⟩


--------------------------------------------------------------------------


  -- 1. Define denotational semantics for gradual STLC and show soundness of term precision
  -- 1a. Define interpretation of terms of gradual CBV cast calculus (STLC + casts)
  --   i) Semantic domains
  --   ii) Term syntax (intrinsically typed, de Bruijn)
  --   iii) Denotation function
  -- 1b. Soundness of term precision with equational theory only (no ordering)

  -- The language supports Dyn, CBV functions, nat




data Dyn' (D : ▹ Type) : Type where
  nat : ℕ -> Dyn' D
  arr : ▸ (λ t → D t -> L℧ (D t)) -> Dyn' D

Dyn : Type
Dyn = fix Dyn'


-- Embedding-projection pairs
record EP (A B : Set) : Set where
  field
    emb  : A -> B
    proj : B -> L℧ A


-- E-P Pair for a type with itself
EP-id : (A : Type) -> EP A A
EP-id A = record {
  emb = id;
  proj = ret }

-- Composing EP pairs

EP-comp : {A B C : Type} -> EP A B -> EP B C -> EP A C
EP-comp epAB epBC = record {
  emb =  λ a -> emb epBC (emb epAB a) ;
  proj = λ c -> bind (proj epBC c) (proj epAB) }
  where open EP


-- E-P Pair for nat

e-nat : ℕ -> Dyn
e-nat n = transport (sym (fix-eq Dyn')) (nat n) 

p-nat' : Dyn' (next Dyn) -> L℧ ℕ
p-nat' (nat n) = ret n
p-nat' (arr f) = ℧

p-nat : Dyn -> L℧ ℕ
p-nat d = p-nat' (transport (fix-eq Dyn') d)

retraction-nat : (n : ℕ) -> p-nat (e-nat n) ≡ ret n
retraction-nat n =
  λ i → p-nat'
    (transport⁻Transport (sym (fix-eq Dyn')) (nat n) i)

EP-nat : EP ℕ Dyn
EP-nat = record {
  emb = e-nat;
  proj = p-nat }


-- E-P Pair for functions Dyn to L℧ Dyn

e-fun : (Dyn -> L℧ Dyn) -> Dyn
e-fun f = transport (sym (fix-eq Dyn'))
  (arr (next f))

p-fun' : Dyn' (next Dyn) -> L℧ (Dyn -> L℧ Dyn)
p-fun' (nat x) = ℧
p-fun' (arr x) = θ (ret <$> x) -- could also define using tick

p-fun : Dyn -> L℧ (Dyn -> L℧ Dyn)
p-fun d = p-fun' (transport (fix-eq Dyn') d)


fun-retract : (f : (Dyn -> L℧ Dyn)) ->
  p-fun (e-fun f) ≡ θ (next (ret f))
fun-retract f =
  p-fun' (transport (fix-eq Dyn') (e-fun f))
                         ≡⟨  refl ⟩
  p-fun' (transport (fix-eq Dyn') (transport (sym (fix-eq Dyn')) (arr (next f))))
                         ≡⟨ (λ i → p-fun' (transportTransport⁻ (fix-eq Dyn') (arr (next f)) i)) ⟩
  p-fun' (arr (next f))  ≡⟨ refl ⟩
  θ (ret <$> next f)     ≡⟨ refl ⟩
  θ (next (ret f)) ∎

EP-fun : EP (Dyn -> L℧ Dyn) Dyn
EP-fun = record {
  emb = e-fun;
  proj = p-fun }



-- Lifting retractions to functions

module LiftRetraction
  {A A' B B' : Set}
  (epAA' : EP A A')
  (epBB' : EP B B') where

    e-lift :
      (A → L℧ B) → (A' → L℧ B')
    e-lift f a' =
      bind (EP.proj epAA' a') λ a -> mapL (EP.emb epBB') (f a)
      -- or equivalently:
      -- mapL (EP.emb epBB') (bind (EP.proj epAA' a') h)

    p-lift :
      (A' -> L℧ B') -> L℧ (A -> L℧ B)
    p-lift f =
      ret (λ a → bind (f (EP.emb epAA' a)) (EP.proj epBB'))



EP-lift : {A A' B B' : Set} ->
  EP A A' ->
  EP B B' ->
  EP (A -> L℧ B) (A' -> L℧ B')
EP-lift epAA' epBB' = record {
  emb = e-lift;
  proj = p-lift  }
  where open LiftRetraction epAA' epBB'







{-
L℧ : Predomain → ErrorDomain
L℧ X = record { X = L℧X ; ℧ = ℧ ; ℧⊥ = {!!} ; θ = record { f = θ₀ ; isMon = {!!} } }
  where
    L℧X : Predomain
    L℧X = L℧₀ (X .fst) , {!!}
-}

-- | TODO:
-- | 1. monotone monad structure
-- | 2. strict functions
-- | 3. UMP?
-- | 4. show that later preserves domain structures
-- | 5. Solve some example recursive domain equations
-- | 6. Program in shallow embedded lambda calculus
-- | 7. Embedding-Projection pairs!
-- | 8. GLTC Syntax, Inequational theory
-- | 9. Model of terms & inequational theory
