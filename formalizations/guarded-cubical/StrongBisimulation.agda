{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Later

module StrongBisimulation(k : Clock) where

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Data.Nat hiding (_^_) renaming (ℕ to Nat)
open import Cubical.Data.Bool.Base
open import Cubical.Data.Bool.Properties hiding (_≤_)
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit.Properties

open import Agda.Primitive

private
  variable
    l : Level
    A B : Set l
    ℓ ℓ' : Level
private
  ▹_ : Set l → Set l
  ▹_ A = ▹_,_ k A


id : {ℓ : Level} -> {A : Type ℓ} -> A -> A
id x = x

_^_ : {ℓ : Level} -> {A : Type ℓ} -> (A -> A) -> Nat -> A -> A
f ^ zero = id
f ^ suc n = f ∘ (f ^ n)


-- Define predomains as posets

Predomain : Set₁
Predomain = Poset ℓ-zero ℓ-zero

-- The relation associated to a predomain d
rel : (d : Predomain) -> (⟨ d ⟩ -> ⟨ d ⟩ -> Type)
rel d = PosetStr._≤_ (d .snd)

reflexive : (d : Predomain) -> (x : ⟨ d ⟩) -> (rel d x x)
reflexive d x = IsPoset.is-refl (PosetStr.isPoset (str d)) x


-- Monotone functions from X to Y

record MonFun (X Y : Predomain) : Set where
  module X = PosetStr (X .snd)
  module Y = PosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_
  field
    f : (X .fst) → (Y .fst)
    isMon : ∀ {x y} → x ≤X y → f x ≤Y f y

record IsMonFun {X Y : Predomain} (f : ⟨ X ⟩ → ⟨ Y ⟩) : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor ismonfun

  module X = PosetStr (X .snd)
  module Y = PosetStr (Y .snd)
  _≤X_ = X._≤_
  _≤Y_ = Y._≤_

  field
    isMon : ∀ {x y} → x ≤X y → f x ≤Y f y

record MonFunStr (ℓ' : Level) (X Y : Predomain) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor monfunstr

  field
    f : ⟨ X ⟩ -> ⟨ Y ⟩
    isMonFun : IsMonFun {ℓ'} f

  open IsMonFun isMonFun public

MonF : ∀ ℓ ℓ' -> Predomain -> Predomain -> Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
MonF ℓ ℓ' X Y = TypeWithStr ℓ {!!}

{-
lem-later : {X~ : ▹ Type} ->
  (x~ y~ : ▸ X~) -> (x~ ≡ y~) ≡ ( ▸ λ t -> ( x~ t ≡ y~ t ))
lem-later = ?
-}

isSet-poset : {ℓ ℓ' : Level} -> (P : Poset ℓ ℓ') -> isSet ⟨ P ⟩
isSet-poset P = IsPoset.is-set (PosetStr.isPoset (str P))

▸' : ▹ Predomain → Predomain
▸' X = (▸ (λ t → ⟨ X t ⟩)) ,
       posetstr ord
                (isposet isset-later {!!} ord-refl ord-trans ord-antisym)
   where

     ord : ▸ (λ t → ⟨ X t ⟩) → ▸ (λ t → ⟨ X t ⟩) → Type ℓ-zero
     -- ord x1~ x2~ =  ▸ (λ t → (str (X t) PosetStr.≤ (x1~ t)) (x2~ t))
     ord x1~ x2~ =  ▸ (λ t → (PosetStr._≤_ (str (X t)) (x1~ t)) (x2~ t))
     

     isset-later : isSet (▸ (λ t → ⟨ X t ⟩))
     isset-later = λ x y p1 p2 i j t →
       isSet-poset (X t) (x t) (y t) (λ i' → p1 i' t) (λ i' → p2 i' t) i j

     ord-refl : (a : ▸ (λ t → ⟨ X t ⟩)) -> ord a a
     ord-refl a = λ t ->
       IsPoset.is-refl (PosetStr.isPoset (str (X t))) (a t)

     ord-trans : BinaryRelation.isTrans ord
     ord-trans = λ a b c ord-ab ord-bc t →
       IsPoset.is-trans
         (PosetStr.isPoset (str (X t))) (a t) (b t) (c t) (ord-ab t) (ord-bc t)

     ord-antisym : BinaryRelation.isAntisym ord
     ord-antisym = λ a b ord-ab ord-ba i t ->
       IsPoset.is-antisym
         (PosetStr.isPoset (str (X t))) (a t) (b t) (ord-ab t) (ord-ba t) i


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


-- Lift monad

data L℧ (X : Set) : Set where
  η : X → L℧ X
  ℧ : L℧ X
  θ : ▹ (L℧ X) → L℧ X


ret : {X : Set} -> X -> L℧ X
ret = η

{-
bind' : ∀ {A B} -> (A -> L℧ B) -> ▹ (L℧ A -> L℧ B) -> L℧ A -> L℧ B
bind' f bind_rec (η x) = f x
bind' f bind_rec ℧ = ℧
bind' f bind_rec (θ l_la) = θ (bind_rec ⊛ l_la)

-- fix : ∀ {l} {A : Set l} → (f : ▹ k , A → A) → A
bind : L℧ A -> (A -> L℧ B) -> L℧ B
bind {A} {B} la f = (fix (bind' f)) la

ext : (A -> L℧ B) -> L℧ A -> L℧ B
ext f la = bind la f
-}

ext' : (A -> L℧ B) -> ▹ (L℧ A -> L℧ B) -> L℧ A -> L℧ B
ext' f rec (η x) = f x
ext' f rec ℧ = ℧
ext' f rec (θ l-la) = θ (rec ⊛ l-la)

ext : (A -> L℧ B) -> L℧ A -> L℧ B
ext f = fix (ext' f)


bind : L℧ A -> (A -> L℧ B) -> L℧ B
bind {A} {B} la f = ext f la

unfold-ext : (f : A -> L℧ B) -> ext f ≡ ext' f (next (ext f))
unfold-ext f = fix-eq (ext' f)

mapL : (A -> B) -> L℧ A -> L℧ B
mapL f la = bind la (λ a -> ret (f a))


-- Strong bisimulation relation/ordering for the lift monad

U : Predomain -> Type
U p = ⟨ p ⟩

{-
module LiftOrder (p : Predomain) where

  module X = PosetStr (p .snd)
  open X using (_≤_)
  -- _≤_ = X._≤_

  module Inductive (rec : ▹ (L℧ (U p) -> L℧ (U p) -> Type)) where

    _≾'_ : L℧ (U p) -> L℧ (U p) -> Type
    ℧ ≾' _ = Unit
    η x ≾' η y = x ≤ y
    θ lx ≾' θ ly = ▸ (λ t -> rec t (lx t) (ly t))
    η _ ≾' _ = ⊥
    θ _ ≾' _ = ⊥

  open Inductive
  _≾_ : L℧ (U p) -> L℧ (U p) -> Type
  _≾_ = fix _≾'_

  ≾-refl : BinaryRelation.isRefl _≾_

  ≾-refl' : ▹ (BinaryRelation.isRefl _≾_) ->
            BinaryRelation.isRefl _≾_
  ≾-refl' IH (η x) =
    transport (sym (λ i -> fix-eq _≾'_ i (η x) (η x)))
              (IsPoset.is-refl (X.isPoset) x)
  ≾-refl' IH ℧ =
    transport (sym (λ i -> fix-eq _≾'_ i ℧ ℧))
              tt
  ≾-refl' IH (θ lx~) =
    transport (sym (λ i -> fix-eq _≾'_ i (θ lx~) (θ lx~)))
              λ t → IH t (lx~ t)

  ≾-refl = fix ≾-refl'

  
  ℧-bot : (l : L℧ (U p)) -> ℧ ≾ l
  ℧-bot l = transport (sym λ i → fix-eq _≾'_ i ℧ l) tt



-- Predomain to lift predomain

𝕃℧' : Predomain -> Predomain
𝕃℧' X = L℧ (X .fst) ,
      posetstr (LiftOrder._≾_ X)
        (isposet {!!} {!!} ≾-refl {!!} {!!})
  where open LiftOrder X


-- Predomain to lift Error Domain

𝕃℧ : Predomain → ErrorDomain
𝕃℧ X = record {
  X = 𝕃℧' X ; ℧ = ℧ ; ℧⊥ = ℧-bot ;
  θ = record { f = θ ; isMon = λ t -> {!!} } }
  where
    -- module X = PosetStr (X .snd)
    -- open Relation X
    open LiftOrder X

𝕌 : ErrorDomain -> Predomain
𝕌 d = ErrorDomain.X d
-}


-- Flat predomain from a set

flat : hSet ℓ-zero -> Predomain
flat h = ⟨ h ⟩ ,
         (posetstr _≡_ (isposet (str h) (str h)
           (λ _ → refl)
           (λ a b c a≡b b≡c → a ≡⟨ a≡b ⟩ b ≡⟨ b≡c ⟩ c ∎)
           λ a b a≡b _ → a≡b))

𝔹 : Predomain
𝔹 = flat (Bool , isSetBool)

ℕ : Predomain
ℕ = flat (Nat , isSetℕ)

UnitP : Predomain
UnitP = flat (Unit , isSetUnit)


-- Underlying predomain of an error domain

𝕌 : ErrorDomain -> Predomain
𝕌 d = ErrorDomain.X d



-- Predomains from arrows (need to ensure monotonicity)

-- Ordering on functions between predomains. This does not require that the
-- functions are monotone.
fun-order-het : (P1 P1' P2 P2' : Predomain) ->
  (⟨ P1 ⟩ -> ⟨ P1' ⟩ -> Type) ->
  (⟨ P2 ⟩ -> ⟨ P2' ⟩ -> Type) ->
  (⟨ P1 ⟩ -> ⟨ P2 ⟩) -> (⟨ P1' ⟩ -> ⟨ P2' ⟩) -> Type ℓ-zero
fun-order-het P1 P1' P2 P2' rel-P1P1' rel-P2P2' fP1P2 fP1'P2' =
  (p : ⟨ P1 ⟩) -> (p' : ⟨ P1' ⟩) ->
  rel-P1P1' p p' ->
  rel-P2P2' (fP1P2 p) (fP1'P2' p')


-- TODO can define this in terms of fun-order-general
fun-order : (P1 P2 : Predomain) -> (⟨ P1 ⟩ -> ⟨ P2 ⟩) -> (⟨ P1 ⟩ -> ⟨ P2 ⟩) -> Type ℓ-zero
fun-order P1 P2 f1 f2 =
  (x y : ⟨ P1 ⟩) -> x ≤P1 y -> (f1 x) ≤P2 (f2 y)
  where
    module P1 = PosetStr (P1 .snd)
    module P2 = PosetStr (P2 .snd)
    _≤P1_ = P1._≤_
    _≤P2_ = P2._≤_

{-
mon-fun-order-refl : {P1 P2 : Predomain} ->
  (f : ⟨ P1 ⟩ -> ⟨ P2 ⟩) ->
  ({x y : ⟨ P1 ⟩} -> rel P1 x y -> rel P2 (f x) (f y)) ->
  fun-order P1 P2 f f
mon-fun-order-refl {P1} {P2} f f-mon = λ x y x≤y → f-mon x≤y
-}

fun-order-trans : {P1 P2 : Predomain} ->
  (f g h : ⟨ P1 ⟩ -> ⟨ P2 ⟩) ->
  fun-order P1 P2 f g ->
  fun-order P1 P2 g h ->
  fun-order P1 P2 f h
fun-order-trans {P1} {P2} f g h f≤g g≤h =
  λ x y x≤y ->
    P2.is-trans (f x) (g x) (h y)
    (f≤g x x (reflexive P1 x))
    (g≤h x y x≤y)
   where
     module P1 = PosetStr (P1 .snd)
     module P2 = PosetStr (P2 .snd)



mon-fun-order : (P1 P2 : Predomain) -> MonFun P1 P2 → MonFun P1 P2 → Type ℓ-zero
mon-fun-order P1 P2 mon-f1 mon-f2 =
  fun-order P1 P2 (MonFun.f mon-f1) (MonFun.f mon-f2)
   where
     module P1 = PosetStr (P1 .snd)
     module P2 = PosetStr (P2 .snd)
     _≤P1_ = P1._≤_
     _≤P2_ = P2._≤_


mon-fun-order-refl : {P1 P2 : Predomain} ->
  (f : MonFun P1 P2) ->
  fun-order P1 P2 (MonFun.f f) (MonFun.f f)
mon-fun-order-refl f = λ x y x≤y -> MonFun.isMon f x≤y

mon-fun-order-trans : {P1 P2 : Predomain} ->
  (f g h : MonFun P1 P2) ->
  mon-fun-order P1 P2 f g ->
  mon-fun-order P1 P2 g h ->
  mon-fun-order P1 P2 f h
mon-fun-order-trans f g h f≤g g≤h =
  fun-order-trans (MonFun.f f) (MonFun.f g) (MonFun.f h) f≤g g≤h


-- Predomain of monotone functions between two predomains
arr' : Predomain -> Predomain -> Predomain
arr' P1 P2 =
  MonFun P1 P2 ,
  -- (⟨ P1 ⟩ -> ⟨ P2 ⟩) ,
  (posetstr
    (mon-fun-order P1 P2)
    (isposet {!!} {!!}
      mon-fun-order-refl
      
      -- TODO can use fun-order-trans
      (λ f1 f2 f3 Hf1-f2 Hf2-f3 x y H≤xy ->
      -- Goal: f1 .f x ≤P2 f3 .f y
       P2.is-trans (f1 .f x) (f2 .f x) (f3 .f y)
         (Hf1-f2 x x (IsPoset.is-refl (P1.isPoset) x))
         (Hf2-f3 x y H≤xy))
      {!!}))
  where
    -- Two functions from P1 to P2 are related if, when given inputs
    -- that are related (in P1), the outputs are related (in P2)
    open MonFun
    module P1 = PosetStr (P1 .snd)
    module P2 = PosetStr (P2 .snd)
    _≤P1_ = P1._≤_
    _≤P2_ = P2._≤_

    {-
    mon-fun-order : MonFun P1 P2 → MonFun P1 P2 → Type ℓ-zero
    mon-fun-order mon-f1 mon-f2 =
      fun-order P1 P2 (MonFun.f mon-f1) (MonFun.f mon-f2)
    -}

    {-
    fun-order : MonFun P1 P2 → MonFun P1 P2 → Type ℓ-zero
    fun-order mon-f1 mon-f2 =
      (x y : ⟨ P1 ⟩) -> x ≤P1 y -> (mon-f1 .f) x ≤P2 (mon-f2 .f) y
    -}

_==>_ : Predomain -> Predomain -> Predomain
A ==> B = arr' A B

infixr 20 _==>_


arr : Predomain -> ErrorDomain -> ErrorDomain
arr dom cod =
  record {
    X = arr' dom (𝕌 cod) ;
    ℧ = const-err ;
    ℧⊥ = const-err-bot ;
    θ = {!!} }
    where
       -- open LiftOrder
       const-err : ⟨ arr' dom (𝕌 cod) ⟩
       const-err = record { f = λ _ -> ErrorDomain.℧ cod ; isMon = λ _ -> reflexive (𝕌 cod) (ErrorDomain.℧ cod) }

       const-err-bot : (f : ⟨ arr' dom (𝕌 cod) ⟩) -> rel (arr' dom (𝕌 cod)) const-err f
       const-err-bot f = λ x y x≤y → ErrorDomain.℧⊥ cod (MonFun.f f y)
       




-- Lifting a heterogeneous relation between A and B to a
-- relation between L A and L B
-- (We may be able to reuse this logic to define the homogeneous ordering on 𝕃 below)

module LiftRelation
  (A B : Predomain)
  (ordAB : ⟨ A ⟩ -> ⟨ B ⟩ -> Type)
  where

  module A = PosetStr (A .snd)
  module B = PosetStr (B .snd)

  open A renaming (_≤_ to _≤A_)
  open B renaming (_≤_ to _≤B_)

  ord' : ▹ ( L℧ ⟨ A ⟩ → L℧ ⟨ B ⟩ → Type) ->
             L℧ ⟨ A ⟩ → L℧ ⟨ B ⟩ → Type
  ord' rec (η a) (η b) = ordAB a b
  ord' rec ℧ lb = Unit
  ord' rec (θ la~) (θ lb~) = ▸ (λ t → rec t (la~ t) (lb~ t))
  ord' _ _ _ = ⊥

  ord : L℧ ⟨ A ⟩ -> L℧ ⟨ B ⟩ -> Type
  ord = fix ord'

  unfold-ord : ord ≡ ord' (next ord)
  unfold-ord = fix-eq ord'

  ord-η-monotone : {a : ⟨ A ⟩} -> {b : ⟨ B ⟩} -> ordAB a b -> ord (η a) (η b)
  ord-η-monotone {a} {b} a≤b = transport (sym (λ i → unfold-ord i (η a) (η b))) a≤b

  ord-bot : (lb : L℧ ⟨ B ⟩) -> ord ℧ lb
  ord-bot lb = transport (sym (λ i → unfold-ord i ℧ lb)) tt


  -- ord-trans-IH


module LiftRelTransitive
  (A B C : Predomain)
  (ordAB : ⟨ A ⟩ -> ⟨ B ⟩ -> Type)
  (ordBC : ⟨ B ⟩ -> ⟨ C ⟩ -> Type)
  where

  module A = PosetStr (A .snd)
  module B = PosetStr (B .snd)
  module C = PosetStr (C .snd)

  open A renaming (_≤_ to _≤A_)
  open B renaming (_≤_ to _≤B_)
  open C renaming (_≤_ to _≤C_)

  open LiftRelation A B ordAB renaming (ord to ordLALB; unfold-ord to unfold-ordLALB)
  open LiftRelation B C ordBC renaming (ord to ordLBLC; unfold-ord to unfold-ordLBLC)

  ordAC : ⟨ A ⟩ -> ⟨ C ⟩ -> Type
  ordAC a c = Σ ⟨ B ⟩ λ b → ordAB a b × ordBC b c

  open LiftRelation A C ordAC renaming (ord to ordLALC; unfold-ord to unfold-ordLALC)


  {-
  ord-trans-ind :
        ▹ ((a b c : L℧ ⟨ p ⟩) ->
           ord' (next ord) a b ->
           ord' (next ord) b c ->
           ord' (next ord) a c) ->
        (a b c : L℧ ⟨ p ⟩) ->
         ord' (next ord) a b ->
         ord' (next ord) b c ->
         ord' (next ord) a c
  -}


  ord-trans :
    (la : L℧ ⟨ A ⟩) (lb : L℧ ⟨ B ⟩) (lc : L℧ ⟨ C ⟩) ->
    ordLALB la lb -> ordLBLC lb lc -> ordLALC la lc
  ord-trans la lb lc la≤lb lb≤lc = {!!}
 

  {- ord-trans = fix (transport (sym (λ i ->
         (▹ ((a b c : L℧ ⟨ p ⟩) →
            unfold-ord i a b → unfold-ord i b c → unfold-ord i a c) →
             (a b c : L℧ ⟨ p ⟩) →
            unfold-ord i a b → unfold-ord i b c → unfold-ord i a c))) ord-trans-ind)
  -}
  


-- Predomain to lift predomain
module 𝕃 (p : Predomain) where

  module X = PosetStr (p .snd)
  open X using (_≤_)
      -- _≤_ = X._≤_


  ord' : ▹ ( L℧ ⟨ p ⟩ → L℧ ⟨ p ⟩ → Type) ->
                 L℧ ⟨ p ⟩ → L℧ ⟨ p ⟩ → Type
  ord' _ ℧ _ = Unit
  ord' _ (η x) (η y) = x ≤ y
  ord' _ (η _) _ = ⊥
  ord' rec (θ lx~) (θ ly~) = ▸ (λ t -> (rec t) (lx~ t) (ly~ t))
        -- or: ▸ ((rec ⊛ lx~) ⊛ ly~)
  ord' _ (θ _) _ = ⊥

  ord :  L℧ ⟨ p ⟩ → L℧ ⟨ p ⟩ → Type
  ord = fix ord'

  unfold-ord : ord ≡ ord' (next ord)
  unfold-ord = fix-eq ord'

  ord-η-monotone : {x y : ⟨ p ⟩} -> x ≤ y -> ord (η x) (η y)
  ord-η-monotone {x} {y} x≤y = transport (sym λ i → unfold-ord i (η x) (η y)) x≤y

  ord-bot : (lx : L℧ ⟨ p ⟩) -> ord ℧ lx
  ord-bot lx = transport (sym λ i → unfold-ord i ℧ lx) tt

  -- lift-ord : (A -> A -> Type) -> (L℧ A -> L℧ A -> Type)

  ord-refl-ind : ▹ ((a : L℧ ⟨ p ⟩) -> ord a a) ->
                    (a : L℧ ⟨ p ⟩) -> ord a a

  ord-refl-ind IH (η x) =
    transport (sym (λ i -> fix-eq ord' i (η x) (η x))) (IsPoset.is-refl X.isPoset x)
  ord-refl-ind IH ℧ =
    transport (sym (λ i -> fix-eq ord' i ℧ ℧)) tt
  ord-refl-ind IH (θ x) =
    transport (sym (λ i -> fix-eq ord' i (θ x) (θ x))) λ t → IH t (x t)

  ord-refl : (a : L℧ ⟨ p ⟩) -> ord a a
  ord-refl = fix ord-refl-ind

 

  𝕃 : Predomain
  𝕃 =
    (L℧ ⟨ p ⟩) ,
    (posetstr ord (isposet {!!} {!!} ord-refl ord-trans {!!}))
    where

      ord-trans-ind :
        ▹ ((a b c : L℧ ⟨ p ⟩) ->
           ord' (next ord) a b ->
           ord' (next ord) b c ->
           ord' (next ord) a c) ->
        (a b c : L℧ ⟨ p ⟩) ->
         ord' (next ord) a b ->
         ord' (next ord) b c ->
         ord' (next ord) a c
      ord-trans-ind IH (η x) (η y) (η z) ord-ab ord-bc =
        IsPoset.is-trans X.isPoset x y z ord-ab ord-bc
        -- x ≡⟨ ord-ab ⟩ y ≡⟨ ord-bc ⟩ z ∎
      ord-trans-ind IH (η x) (η y) ℧ ord-ab ord-bc = ord-bc
      ord-trans-ind IH (η x) (θ y) ℧ contra ord-bc = contra
      ord-trans-ind IH (η x) (η y) (θ z) ord-ab contra = contra
      ord-trans-ind IH (η x) ℧ (θ y) ord-ab ord-bc = ord-ab
      ord-trans-ind IH (η x) (θ y) (θ z) ord-ab ord-bc = ord-ab
      ord-trans-ind IH ℧ b c ord-ab ord-bc = tt
      ord-trans-ind IH (θ lx~) (θ ly~) (θ lz~) ord-ab ord-bc =
        λ t -> transport (sym λ i → unfold-ord i (lx~ t) (lz~ t))
          (IH t (lx~ t) (ly~ t) (lz~ t)
          (transport (λ i -> unfold-ord i (lx~ t) (ly~ t)) (ord-ab t))
          (transport (λ i -> unfold-ord i (ly~ t) (lz~ t)) (ord-bc t)))

      ord-trans : (a b c : L℧ ⟨ p ⟩) -> ord a b -> ord b c -> ord a c
      ord-trans = fix (transport (sym (λ i ->
         (▹ ((a b c : L℧ ⟨ p ⟩) →
            unfold-ord i a b → unfold-ord i b c → unfold-ord i a c) →
             (a b c : L℧ ⟨ p ⟩) →
            unfold-ord i a b → unfold-ord i b c → unfold-ord i a c))) ord-trans-ind)


-- Predomain to lift Error Domain

𝕃℧ : Predomain → ErrorDomain
𝕃℧ X = record {
  X = 𝕃 X ; ℧ = ℧ ; ℧⊥ = ord-bot X ;
  θ = record { f = θ ; isMon = λ t -> {!!} } }
  where
    -- module X = PosetStr (X .snd)
    -- open Relation X
    open 𝕃



-- Product of predomains


-- We can't use Cubical.Data.Prod.Base for products, because this version of _×_
-- is not a subtype of the degenerate sigma type Σ A (λ _ → B), and this is needed
-- when we define the lookup function.
-- So we instead use Cubical.Data.Sigma.

-- These aren't included in Cubical.Data.Sigma, so we copy the
-- definitions from Cubical.Data.Prod.Base.
proj₁ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → A × B → A
proj₁ (x , _) = x

proj₂ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → A × B → B
proj₂ (_ , x) = x


infixl 21 _×d_
_×d_  : Predomain -> Predomain -> Predomain
A ×d B =
  (⟨ A ⟩ × ⟨ B ⟩) ,
  (posetstr order {!!})
  where
    module A = PosetStr (A .snd)
    module B = PosetStr (B .snd)
   

    prod-eq : {a1 a2 : ⟨ A ⟩} -> {b1 b2 : ⟨ B ⟩} ->
      (a1 , b1) ≡ (a2 , b2) -> (a1 ≡ a2) × (b1 ≡ b2)
    prod-eq p = (λ i → proj₁ (p i)) , λ i -> proj₂ (p i)

    isSet-prod : isSet (⟨ A ⟩ × ⟨ B ⟩)
    isSet-prod (a1 , b1) (a2 , b2) p1 p2 =
      let (p-a1≡a2 , p-b1≡b2) = prod-eq p1 in
      let (p'-a1≡a2 , p'-b1≡b2) = prod-eq p2 in
      {!!}

    order : ⟨ A ⟩ × ⟨ B ⟩ -> ⟨ A ⟩ × ⟨ B ⟩ -> Type ℓ-zero
    order (a1 , b1) (a2 , b2) = (a1 A.≤ a2) × (b1 B.≤ b2)

    order-refl : BinaryRelation.isRefl order
    order-refl = λ (a , b) → reflexive A a , reflexive B b

    order-trans : BinaryRelation.isTrans order
    order-trans (a1 , b1) (a2 , b2) (a3 , b3) (a1≤a2 , b1≤b2) (a2≤a3 , b2≤b3) =
      (IsPoset.is-trans A.isPoset a1 a2 a3 a1≤a2 a2≤a3) ,
       IsPoset.is-trans B.isPoset b1 b2 b3 b1≤b2 b2≤b3
    

    {-
    order : ⟨ A ⟩ × ⟨ B ⟩ → ⟨ A ⟩ × ⟨ B ⟩ → Type ℓ-zero
    order (a1 , b1) (a2 , b2) = (a1 A.≤ a2) ⊎ ((a1 ≡ a2) × b1 B.≤ b2)

    order-trans : BinaryRelation.isTrans order
    order-trans (a1 , b1) (a2 , b2) (a3 , b3) (inl a1≤a2) (inl a2≤a3) =
      inl (IsPoset.is-trans A.isPoset a1 a2 a3 a1≤a2 a2≤a3)
    order-trans (a1 , b1) (a2 , b2) (a3 , b3) (inl a1≤a2) (inr (a2≡a3 , b2≤b3)) =
      inl (transport (λ i → a1 A.≤ a2≡a3 i) a1≤a2)
    order-trans (a1 , b1) (a2 , b2) (a3 , b3) (inr (a1≡a2 , b1≤b2)) (inl a2≤a3) =
      inl (transport (sym (λ i → a1≡a2 i A.≤ a3)) a2≤a3)
    order-trans (a1 , b1) (a2 , b2) (a3 , b3) (inr (a1≡a2 , b1≤b2)) (inr (a2≡a3 , b2≤b3)) =
      inr (
        (a1 ≡⟨ a1≡a2 ⟩ a2 ≡⟨ a2≡a3 ⟩ a3 ∎) ,
        IsPoset.is-trans B.isPoset b1 b2 b3 b1≤b2 b2≤b3)
    -}

    is-poset : IsPoset order
    is-poset = isposet
      isSet-prod
      {!!}
      order-refl
      order-trans
      {!!}



π1 : {A B : Predomain} -> ⟨ (A ×d B) ==> A ⟩
π1 {A} {B} = record {
  f = g;
  isMon = g-mon }
  where
    g : ⟨ A ×d B ⟩ -> ⟨ A ⟩
    g (a , b) = a

    g-mon  : {p1 p2 : ⟨ A ×d B ⟩} → rel (A ×d B) p1 p2 → rel A (g p1) (g p2)
    g-mon {γ1 , a1} {γ2 , a2} (a1≤a2 , b1≤b2) = a1≤a2


π2 : {A B : Predomain} -> ⟨ (A ×d B) ==> B ⟩
π2 {A} {B} = record {
  f = g;
  isMon = g-mon }
  where
    g : ⟨ A ×d B ⟩ -> ⟨ B ⟩
    g (a , b) = b

    g-mon  : {p1 p2 : ⟨ A ×d B ⟩} → rel (A ×d B) p1 p2 → rel B (g p1) (g p2)
    g-mon {γ1 , a1} {γ2 , a2} (a1≤a2 , b1≤b2) = b1≤b2



Pair : {A B : Predomain} -> ⟨ A ==> B ==> (A ×d B) ⟩
Pair {A} = record {
  f = λ a →
    record {
      f = λ b -> a , b ;
      isMon = λ b1≤b2 → (reflexive A a) , b1≤b2 } ;
  isMon = λ {a1} {a2} a1≤a2 b1 b2 b1≤b2 → a1≤a2 , b1≤b2 }


-- Weak bisimulation relaion
-- Define compositionally

δ : {X : Type} -> L℧ X -> L℧ X
δ = θ ∘ next
  where open L℧

module WeakRel (d : Predomain) where

  module D = PosetStr (d .snd)
  _≤_ = D._≤_

  -- make this a module so we can avoid having to make the IH
  -- a parameter of the comparison function
  module Inductive (IH : ▹ (L℧ ⟨ d ⟩ -> L℧ ⟨ d ⟩ -> Type)) where


    _≾'_ : L℧ (U d) -> L℧ (U d) -> Type
    ℧ ≾' _ = Unit
      
    η x ≾' η y = x ≤ y
    
    θ lx ≾' θ ly = ▸ (λ t -> IH t (lx t) (ly t))
    -- or equivalently: θ lx ≾' θ ly = ▸ ((IH ⊛ lx) ⊛ ly)
      
    η x ≾' θ t = Σ Nat λ n -> Σ (U d) (λ y -> (θ t ≡ (δ ^ n) (η y)) × (x ≤ y))

    -- need to account for error (θ s ≡ delay of η x or delay of ℧, in which case we're done)
    θ s ≾' η y = Σ Nat λ n ->
       (θ s ≡ (δ ^ n) L℧.℧) ⊎
       (Σ (U d) (λ x -> (θ s ≡ (δ ^ n) (η x)) × (x ≤ y)))
      
    _ ≾' ℧ = ⊥
   
  _≾_ : L℧ (U d) -> L℧ (U d) -> Type
  _≾_ = fix _≾'_
    where open Inductive






{-
-- Weak bisimulation relaion
-- Define compositionally

module WeakRel (d : ErrorDomain) where

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

-}
