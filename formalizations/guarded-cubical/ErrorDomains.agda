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

open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Bool.Base
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Data.Sum hiding (rec)

open import Agda.Primitive

private
  variable
    l : Level
    A B : Set l
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A


id : {ℓ : Level} -> {A : Type ℓ} -> A -> A
id x = x

_^_ : {ℓ : Level} -> {A : Type ℓ} -> (A -> A) -> ℕ -> A -> A
f ^ zero = id
f ^ suc n = f ∘ (f ^ n)



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


EofP : Predomain → ErrorDomain
EofP X = record {
  X = L℧X ; ℧ = ℧ ; ℧⊥ = {!!} ;
  θ = record { f = θ ; isMon = λ t -> {!!} } }
  where
    module X = PosetStr (X .snd)
    L℧X : Predomain
    L℧X = L℧ (X .fst) , posetstr {!X._≤_!} {!!}



-- Although tempting from an equational perspective,
-- we should not add the restriction that θ (next x) ≡ x
-- for all x. If we did do this, we would end up collapsing
-- everything down to the infinite looping computation, fix θ.
-- The following lemma proves this.

trivialize' : {X : Set} ->
  ((lx : L℧ X) -> lx ≡ θ (next lx)) ->
  ▹ ((lx : L℧ X) -> lx ≡ fix θ) → (lx : L℧ X) -> lx ≡ fix θ
trivialize' hθ IH lx =
  lx                 ≡⟨ hθ lx ⟩
  θ (next lx)        ≡⟨ ( λ i -> θ λ t -> IH t lx i) ⟩
  θ (next (fix θ))   ≡⟨ sym (fix-eq θ) ⟩
  (fix θ ∎)

trivialize : {X : Set} ->
          ((lx : L℧ X) -> lx ≡ θ (next lx)) ->
          ((lx : L℧ X) -> (lx ≡ fix θ))
trivialize hθ = fix (trivialize' hθ)

-- A slightly stronger version (i.e. a weaker assumption)
-- This applies to the weak bisimulation relation in Mogelberg-Paviotti
trivialize_quotient_stronger : ∀ {X} ->
  (∀ x -> η x ≡ θ (next (η x))) ->
  (x : X) -> η x ≡ fix θ
trivialize_quotient_stronger {X} hθ = fix rec
  where rec : ▹ ((x : X) -> η x ≡ fix θ) → (x : X) -> η x ≡ fix θ
        rec IH x = 
         η x                ≡⟨ hθ x ⟩
         θ (next (η x))     ≡⟨ (λ i → θ (λ t → IH t x i)) ⟩
         θ (next (fix θ))   ≡⟨ sym (fix-eq θ) ⟩
         (fix θ ∎)


-- We can prove a similar fact for an arbitrary relation R,
-- so long as it is symmetric, transitive, and a congruence
-- with respect to θ.

transitive : {X : Type} -> (_R_ : X -> X -> Type) -> Type
transitive {X} _R_ =
  {x y z : X} -> x R y -> y R z -> x R z

symmetric : {X : Type} -> (_R_ : X -> X -> Type) -> Type
symmetric {X} _R_ =
  {x y : X} -> x R y -> y R x

congruence : {X : Type} -> (_R_ : L℧ X -> L℧ X -> Type) -> Type
congruence {X} _R_ = {lx ly : ▹ (L℧ X)} -> ▸ (λ t → (lx t) R (ly t)) -> (θ lx) R (θ ly)

congruence' : {X : Type} -> (_R_ : L℧ X -> L℧ X -> Type) -> Type
congruence' {X} _R_ = {lx ly : L℧ X} -> ▹ (lx R ly) -> (θ (next lx)) R (θ (next ly))

cong→cong' : ∀ {X}{_R_ : L℧ X -> L℧ X -> Type} → congruence _R_ → congruence' _R_
cong→cong' cong ▹R = cong ▹R

trivialize2 : {X : Type} (_R_ : L℧ X -> L℧ X -> Type) ->
  symmetric _R_ ->
  transitive _R_ ->
  congruence _R_ ->
  ((x : L℧ X) -> (θ (next x)) R x) ->
  ((x : L℧ X) -> x R (fix θ))
trivialize2 {X} _R_ hSym hTrans hCong hθ = fix trivialize2'
  where
   trivialize2' :
    ▹ ((x : L℧ X) -> x R (fix θ)) → (x : L℧ X) -> x R (fix θ)
   trivialize2' IH lx =
     hTrans
       (hSym (hθ lx))
       (hTrans
         (hCong (λ t → IH t lx))
         (hθ (fix θ)))




-- lx                  R
-- (θ (next lx))       R
-- (θ (λ t -> fix θ)   ≡
-- (θ (next (fix θ)))  R
-- (fix θ)

-- don't need symmetry
trivialize3 : {X : Type} (_R_ : L℧ X -> L℧ X -> Type) ->
  transitive _R_ ->
  congruence _R_ ->
  ((x : L℧ X) -> x R (θ (next x))) ->
  ((x : L℧ X) -> x R (fix θ))
trivialize3 {X} _R_ hTrans hCong hθR = fix trivialize3'
  where
   trivialize3' :
    ▹ ((x : L℧ X) -> x R (fix θ)) → (x : L℧ X) -> x R (fix θ)
   trivialize3' IH lx =
     subst (λ y → lx R y) (sym (fix-eq θ))
       (hTrans
         (hθR lx)
         (hCong (λ t → IH t lx)))

--------------------------------------------------------------------------


-- Showing that L is a monad

{-
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
-}


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

mapL : (A -> B) -> L℧ A -> L℧ B
mapL f la = bind la (λ a -> ret (f a))


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

-- Would this Dyn be better?
data Dyn'' (D : ▹ Type) : Type where
  nat : ℕ -> Dyn'' D
  arr : (▸ D -> L℧ (Dyn'' D)) -> Dyn'' D

Dyn : Type
Dyn = fix Dyn'

-- Embedding-projection pairs

record EP (A B : Set) : Set where
  field
    emb  : A -> B
    proj : B -> L℧ A

=======
data Maybe {ℓ : Level} (A : Set ℓ) : Set ℓ where
  η : A -> Maybe A
  ℧ : Maybe A

ret-Maybe : {A : Set} -> A -> Maybe A
ret-Maybe = η

bind-Maybe : {A B : Set} ->
  Maybe A -> (A -> Maybe B) -> Maybe B
bind-Maybe (η x) f = f x
bind-Maybe ℧ f = ℧

data L (X : Set) : Set where
  η : X -> L X
  θ : ▹ (L X) -> L X

Lret : {A : Set} -> A -> L A
Lret = η

Lbind' : ∀ {A B} -> (A -> L B) -> ▹ (L A -> L B) -> L A -> L B
Lbind' f bind_rec (η x) = f x
Lbind' f bind_rec (θ l_la) = θ (bind_rec ⊛ l_la)

Lbind : L A -> (A -> L B) -> L B
Lbind {A} {B} la f = (fix (Lbind' f)) la

-- Try to show that Maybe (L A) is a monad by defining bind...

mapMaybe : (A -> B) -> (Maybe A) -> Maybe B
mapMaybe = {!!}

joinMaybe : Maybe (Maybe A) -> Maybe A
joinMaybe = {!!}

joinL : L (L A) -> L A
joinL = {!!}

Lmap : (A -> B) -> L A -> L B
Lmap = {!!}


ret-Maybe-L : A -> Maybe (L A)
ret-Maybe-L a = η (η a)

bind-Maybe-L' :
  (A -> Maybe (L B)) ->
  ▹ (Maybe (L A) -> Maybe (L B)) ->
  Maybe (L A) -> Maybe (L B)
bind-Maybe-L' f bind-rec (η (η x)) = f x
bind-Maybe-L' f bind-rec (η (θ l_la)) = {!!}
 --  joinMaybe (η ( mapMaybe joinL (swap (θ λ t -> Lmap (bind-rec t) (η (η (l_la t)))))))
bind-Maybe-L' f bind-rec ℧ = ℧

bind-Maybe-L : Maybe (L A) -> (A -> Maybe (L B)) ->  Maybe (L B)
bind-Maybe-L mla f = (fix (bind-Maybe-L' f)) mla


MaybeL-monad-unit-l : ∀ (a : A) (f : A -> Maybe (L B)) ->
  bind-Maybe-L (ret-Maybe-L a) f ≡ f a
MaybeL-monad-unit-l a f = {!!}

MaybeL-monad-unit-r : (mla : Maybe (L A)) -> bind-Maybe-L mla ret-Maybe-L ≡ mla
MaybeL-monad-unit-r = fix lem
  where
    lem : ▹ ((mla : Maybe (L A)) -> bind-Maybe-L mla ret-Maybe-L ≡ mla) ->
             (mla : Maybe (L A)) -> bind-Maybe-L mla ret-Maybe-L ≡ mla
    lem IH (η (η x)) = {!!}
    lem IH (η (θ x)) = {!!}
    lem IH ℧ = {!!}


record EP' (A B : Set) : Set where
  field
    emb : A -> B
    proj : B -> Maybe (▹ A)

record EP'' (A B : Set) : Set where
  field
    emb : A -> B
    proj : B -> Maybe (L A)

record EP''' (A B : Set) : Set where
  field
    emb : A -> B
    proj : ▸ (λ _ -> B -> ▹ (Maybe A))

record EP4 (A B : Set) : Set where
  field
    emb : ▹ (A -> B)
    proj : ▹ (B -> Maybe A)

record EP5 (A B : Set) : Set where
  field
    emb : A -> B
    proj : B -> ▹ (Maybe A)




fin-later : {ℓ : Level} -> Type ℓ -> Type ℓ
fin-later A = Σ ℕ λ n -> (_^_ ▹_ n) (Maybe A)

fin-later-bind' : (A -> fin-later B) ->
  ▹ (fin-later A -> fin-later B) ->
     fin-later A -> fin-later B
fin-later-bind' f rec (n , ▹^n-f) = {!!} , {!!}

many▹intro : (n : ℕ) -> (A -> B) -> (▹_ ^ n) A -> (▹_ ^ n) B
many▹intro zero = id
many▹intro (suc n) f l_ln_a = λ t → (many▹intro n f) (l_ln_a t)

lemma : (n m : ℕ) -> (▹_ ^ m) ((▹_ ^ n) B) ≡ (▹_ ^ (m + n)) B
lemma = {!!}

many▹bind : {n m p : ℕ} -> n + m ≡ p -> (▹_ ^ n) A -> (A -> (▹_ ^ m) B) -> (▹_ ^ (n + m)) B
many▹bind {n = n} {m = m} {p = p} eq a f =
  transport (lemma m n) (many▹intro n f a) --  (many▹intro {!!} f a)
  -- many▹intro {!!} f a
-- many▹bind {n = zero} {m = m} eq a f = {!!}
-- many▹bind {n = suc n} {m = m} eq = {!!}

record EP6 (A B : Type) (n : ℕ) : Type where
  field
    emb : A -> B
    proj : B -> (▹_ ^ n) (Maybe A)


-- E-P Pair for a type with itself
EP-id : (A : Type) -> EP A A
EP-id A = record {
  emb = id;
  proj = ret }

EP'''-id : (A : Type) -> EP''' A A
EP'''-id A = record {
  emb = {!!};
  proj = {!!} }

EP4-id : (A : Type) -> EP4 A A
EP4-id A = record {
  emb = {!!};
  proj = next (ret-Maybe) }

EP6-id : (A : Type) (n : ℕ) -> EP6 A A n
EP6-id A n = record {
  emb = {!!};
  proj = {!!} }

-- Composing EP pairs
EP-comp : {A B C : Type} -> EP A B -> EP B C -> EP A C
EP-comp epAB epBC = record {
  emb =  λ a -> emb epBC (emb epAB a) ;
  proj = λ c -> bind (proj epBC c) (proj epAB) }
  where open EP


EP-later : {A : Type} -> EP' A B -> EP' (▹ A) (▹ B)
EP-later epAB = record {
  emb = λ a -> next (emb epAB {!!});
  proj = λ lb -> {!!} }
  where open EP'
   
EP-comp-precise : {A B C : Type} -> EP' A (▹ B) -> EP' (B) (C) -> EP' A (▹ C)
EP-comp-precise epAB epBC = record {
  emb =  λ a -> {!!};
  proj = λ c -> bind-Maybe (proj epBC {!!}) (proj {!!}) }
  where open EP'

   
EP-comp4 : {A B C : Type} -> EP4 A B -> EP4 B C -> EP4 A C
EP-comp4 epAB epBC = record {
  emb =  λ t a -> emb epBC t (emb epAB t a) ;
  proj = λ t c -> bind-Maybe (proj epBC t c) λ b -> proj epAB t b}
  where open EP4

EP-comp5 : {A B C : Type} -> EP5 A B -> EP5 B C -> EP5 A C
EP-comp5 epAB epBC = record {
  emb =  λ a -> emb epBC (emb epAB a) ;
  proj = λ c t -> bind-Maybe (proj epBC c t) (λ b -> {!!}) } -- proj epAB b t is invalid
  where open EP5

EP-comp6 : {A B C : Type} -> {n m : ℕ} -> EP6 A B n -> EP6 B C m -> EP6 A C (n + m)
EP-comp6 {n = n} {m = m} epAB epBC = record {
  emb =  λ a -> emb epBC (emb epAB a) ;
  proj = λ c -> {!!} }
  -- many▹bind {n = m} {m = n} {p = n + m} {!!} (proj epBC c) (λ b -> proj epAB b) }
  -- many▹bind (proj epBC c) (λ b -> proj epAB b) }
  where open EP6



{-
EP-comp-precise2 : {A B C : Type} -> EP'' A B -> EP'' B C -> EP'' A C
EP-comp-precise2 epAB epBC = record {
  emb =  λ a -> emb epBC (emb epAB a) ;
  proj = λ c -> bind-Maybe
    (proj epBC c)
    (λ lb -> bind-Maybe {!!} {!!}) }
  where open EP'' 
-}

{-
EP'''-comp : {A B C : Type} -> EP''' A B -> EP''' B C -> EP''' A C
EP'''-comp epAB epBC = record {
  emb = λ t -> λ a -> emb epBC t (emb epAB t a) ;
  proj = λ t -> λ c -> λ t' ->
    bind-Maybe (proj epBC t c t) (λ b -> proj epAB t b t) }
  where open EP'''
-}


-- E-P pair between a type and its lift
EP-L : {A : Type} -> EP A B -> EP (L℧ A) (L℧ B)
EP-L epAB = record {
  emb = λ la -> mapL (emb epAB) la;
  proj = λ lb -> mapL (proj epAB) lb }
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




p-fun-precise' : Dyn' (next Dyn) -> (Maybe (▹ (Dyn -> L℧ Dyn)))
p-fun-precise' (nat x) = ℧
p-fun-precise' (arr x) = η x -- (ret <$> x) -- could also define using tick

p-fun-precise : Dyn -> (Maybe (▹ (Dyn -> L℧ Dyn)))
p-fun-precise d = p-fun-precise' (transport (fix-eq Dyn') d)


fun-retract-precise : (f : (Dyn -> L℧ Dyn)) ->
  p-fun-precise (e-fun f) ≡ η (next f)
fun-retract-precise f =
  p-fun-precise' (transport (fix-eq Dyn') (transport (sym (fix-eq Dyn')) (arr (next f))))
                         ≡⟨ {!!} ⟩
  p-fun-precise' (arr (next f)) ∎


e-fun4 : ▹ ((Dyn -> L℧ Dyn) -> Dyn)
e-fun4 = next (λ f -> transport (sym (fix-eq Dyn')) (arr (next f)))

p-fun4' : (Dyn' (next Dyn) -> Maybe (Dyn -> L℧ Dyn))
p-fun4' (nat x) = ℧
p-fun4' (arr f) = η λ d -> θ (λ t -> f t d)
 
p-fun4 : ▹ (Dyn -> Maybe (Dyn -> L℧ Dyn))
p-fun4 = next λ d -> p-fun4' (transport (fix-eq Dyn') d)

EP4-fun : EP4 (Dyn -> L℧ Dyn) Dyn
EP4-fun = record {
  emb = e-fun4;
  proj = p-fun4 }


EP4-fun-retract : (f : (Dyn -> L℧ Dyn)) (t : Tick k) ->
  p-fun4 t (e-fun4 t f) ≡ η f
EP4-fun-retract f t =
  p-fun4' (transport (fix-eq Dyn') (e-fun4 t f)) ≡⟨ refl ⟩
  p-fun4' (transport (fix-eq Dyn') (transport (sym (fix-eq Dyn')) (arr (next f)))) ≡⟨ {!!} ⟩
  p-fun4' (arr (next f)) ≡⟨ refl ⟩
  (η λ d -> θ (λ t' -> (next f) t' d)) ≡⟨ refl ⟩
  (η λ d -> θ (λ t' -> f d)) ≡⟨ refl ⟩
  (η λ d -> θ (next (f d))) ≡⟨ {!!} ⟩
  (η ((next f) t)) ≡⟨  refl ⟩
  η f ∎


-- transport (sym (fix-eq Dyn')) (arr (next f))


-- Lifting retractions to functions
module ArrowRetraction
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
  where open ArrowRetraction epAA' epBB'




--------------------------------------------------------------------------


-- Ordering on terms

  {-
  record Predomain (ℓ ℓ' : Level) (X : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
      _≾X_ : X -> X -> Type
      pst : IsPoset _≾X_
  -}


U : ErrorDomain -> Type
U d = (ErrorDomain.X d) .fst

δ : {X : Type} -> L℧ X -> L℧ X
δ = θ ∘ next
  where open L℧


      

-- Should this be on Predomains?
module Relation (d : ErrorDomain) where

  -- make this a module so we can avoid having to make the IH
  -- a parameter of the comparison function
  module Inductive (IH : ▹ (L℧ (U d) -> L℧ (U d) -> Type)) where

    open ErrorDomain d renaming (θ to θ')

    _≾'_ : L℧ (U d) -> L℧ (U d) -> Type
    ℧ ≾' _ = Unit
      
    η x ≾' η y = x ≤ y
    
    θ lx ≾' θ ly = ▸ (λ t -> IH t (lx t) (ly t))
    -- or equivalently: θ lx ≾' θ ly = ▸ ((IH ⊛ lx) ⊛ ly)
      
    η x ≾' θ t = Σ ℕ λ n -> Σ (U d) (λ y -> (θ t ≡ (δ ^ n) (η y)) × (x ≤ y))

    -- need to account for error (θ s ≡ delay of η x or delay of ℧, in which case we're done)
    θ s ≾' η y = Σ ℕ λ n ->
       (θ s ≡ (δ ^ n) L℧.℧) ⊎
       (Σ (U d) (λ x -> (θ s ≡ (δ ^ n) (η x)) × (x ≤ y)))
      
    _ ≾' ℧ = ⊥
   
  _≾_ : L℧ (U d) -> L℧ (U d) -> Type
  _≾_ = fix _≾'_
    where open Inductive


  module Properties where

  -- To show that this is not transitive:
  -- Prove that it's not trivial (i.e., η true is not related to η false.
  -- Should follow by definition.)
  -- Appeal to lemma: it is a congruence with respect to θ,
  -- so if it were transitive, then by the lemma, it would be trivial.


    non-trivial : Σ (U d) (λ x -> Σ (U d) (λ y -> x ≡ y -> ⊥)) ->
                  Σ (U d) (λ x -> Σ (U d) (λ y -> (η x) ≾ (η y) -> ⊥))
    non-trivial (x , y , H-contra) = x , (y , (λ H-contra2 → H-contra {!!}))

    lem-rewrite : (lx ly : ▹ (L℧ (U d))) ->
           (θ lx ≾ θ ly) ≡ (Inductive._≾'_ (next (_≾_)) (θ lx) (θ ly))
    lem-rewrite lx ly =
      (fix Inductive._≾'_) (θ lx) (θ ly)

             -- can't come up with this through refining:
             ≡⟨ (λ i -> fix-eq (Inductive._≾'_) i (θ lx) (θ ly)) ⟩
                      
      (Inductive._≾'_ (next (_≾_)) (θ lx) (θ ly)) ∎

   -- fix _≾'_ ≡ _≾'_ (next (_≾_))
   -- fix _≾'_ (θ lx) (θ ly) ≡  _≾'_ (next (_≾_)) (θ lx) (θ ly)


    θ-cong : congruence _≾_
    θ-cong {lx} {ly} h = transport (sym (lem-rewrite lx ly)) h

                






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
