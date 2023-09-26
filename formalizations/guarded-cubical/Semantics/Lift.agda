{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Common
open import Common.Later

module Semantics.Lift (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Sigma

open import Common.Common
open import Common.LaterProperties

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ
private
  ▹_ : Set ℓ → Set ℓ
  ▹_ A = ▹_,_ k A


-- Lift + Error monad
data L℧ (X : Type ℓ) : Type ℓ where
  η : X → L℧ X
  ℧ : L℧ X
  θ : ▹ (L℧ X) → L℧ X

-- Lift monad (no error)
data L (X : Type ℓ) : Type ℓ where
  η : X -> L X
  θ : ▹ (L X) -> L X

-- Delay function
δ : {X : Type ℓ} -> L℧ X -> L℧ X
δ = L℧.θ ∘ (next {k = k})


L℧→sum : {X : Type ℓ} -> L℧ X → (X ⊎ ⊤) ⊎ (▹ L℧ X)
L℧→sum (η x) = inl (inl x)
L℧→sum ℧ = inl (inr tt)
L℧→sum (θ lx~) = inr lx~

sum→L℧ : {X : Type ℓ} -> (X ⊎ ⊤) ⊎ (▹ L℧ X) -> L℧ X
sum→L℧ (inl (inl x)) = η x
sum→L℧ (inl (inr tt)) = ℧
sum→L℧ (inr lx~) = θ lx~

L℧-iso : {X : Type ℓ} -> Iso (L℧ X) ((X ⊎ ⊤) ⊎ (▹ (L℧ X)))
L℧-iso {X = X} = iso L℧→sum sum→L℧ sec retr
  where
   
    sec : section L℧→sum sum→L℧
    sec (inl (inl x)) = refl
    sec (inl (inr tt)) = refl
    sec (inr lx~) = refl

    retr : retract L℧→sum sum→L℧
    retr (η x) = refl
    retr ℧ = refl
    retr (θ x) = refl

-- isSet for Lift
isSetL℧ : {X : Type ℓ} -> isSet X -> isSet (L℧ X)
isSetL℧ {X = X} isSetX = fix isSetL℧'
  where
    isSetL℧' : ▹ (isSet (L℧ X)) -> isSet (L℧ X)
    isSetL℧' IH = isSetRetract L℧→sum sum→L℧ (Iso.leftInv L℧-iso)
      (isSet⊎ (isSet⊎ isSetX isSetUnit) (isSet▹ IH))



Iso-L : {X : Type ℓ} -> Iso (L X) (X ⊎ (▹ (L X)))
Iso-L {X = X} = iso to inv sec retr
  where
    to : L X → X ⊎ (▹ L X)
    to (η x) = inl x
    to (θ l~) = inr l~

    inv : X ⊎ (▹ L X) → L X
    inv (inl x) = η x
    inv (inr l~) = θ l~

    sec : section to inv
    sec (inl x) = refl
    sec (inr l~) = refl

    retr : retract to inv
    retr (η x) = refl
    retr (θ l~) = refl

L-unfold : {X : Type ℓ} -> L X ≡ X ⊎ (▹ (L X))
L-unfold = isoToPath Iso-L


-- Defining L using a guarded fixpoint
L-fix : Type ℓ -> Type ℓ
L-fix X = fix {k} λ L' -> X ⊎ (▸ λ t -> L' t)

-- L-fixpoint-iso : {X : Type ℓ} -> Iso (L-fixpoint X) 
L-fix-unfold : {X : Type ℓ} -> L-fix X ≡ (X ⊎ (▹ (L-fix X)))
L-fix-unfold = fix-eq _


L-fix-eq' : {X : Type ℓ} -> ▸ (λ t -> (L-fix X ≡ L X)) -> L-fix X ≡ L X
L-fix-eq' {X = X} IH = L-fix X ≡⟨ L-fix-unfold ⟩
  ((X ⊎ (▹ (L-fix X)))) ≡⟨ (λ i -> X ⊎ (▸ λ t -> IH t i)) ⟩
  ((X ⊎ (▹ (L X)))) ≡⟨ sym L-unfold ⟩
  L X ∎

-- Note: ▸ (λ t -> L-fix X ≡ L X) is equivalent to ▸ (next (L-fix X ≡ L X))
-- which is equivalent to ▹ (L-fix X ≡ L X)

-- IH : ▸ (λ t' → L-fix X ≡ L X)  a.k.a. ▹ (L-fix X ≡ L X)
-- So λ i -> X ⊎ (▸ λ t -> IH t i) has type
-- (X ⊎ (▸ λ t -> L-fix X)) ≡ (X ⊎ (▸ λ t -> L X)) i.e.
-- (X ⊎ (▹ L-fix X)) ≡ (X ⊎ (▹ L X))

L-fix-eq : {X : Type ℓ} -> L-fix X ≡ L X
L-fix-eq = fix L-fix-eq'

L-fix-iso : {X : Type ℓ} -> Iso (L-fix X) (L X)
L-fix-iso = pathToIso L-fix-eq




    

{-
Iso-L-fix : {X : Type ℓ} -> Iso (L-fix X) (L X)
Iso-L-fix {X = X} = iso to inv sec {!!}
  where
    to' : ▹ ((X ⊎ (▹ (L-fix X))) -> L X) -> (X ⊎ (▹ (L-fix X))) -> L X
    to' _   (inl x) = η x
    to' rec (inr l~) = θ λ t -> rec t (inr l~)

    to : L-fix X -> L X
    to lx = fix to' (transport L-fix-unfold lx)

    inv : L X -> L-fix X
    inv' : L X -> (X ⊎ (▹ (L-fix X)))

    inv lx = transport (sym L-fix-unfold) (inv' lx)
    inv' (η x) = inl x
    inv' (θ l~) = inr (λ t -> inv (l~ t))

    sec' : ▹ ((y : L X) -> to' (next (fix to')) (inv' y) ≡ y) ->
              (y : L X) -> to' (next (fix to')) (inv' y) ≡ y
    sec' _ (η x) = refl
    sec' IH (θ l~) = {!!}

    sec : section to inv
    sec (η x) = {!!}
    sec (θ l~) = {!!}
-}
  





-- Similar to caseNat,
-- defined at https://agda.github.io/cubical/Cubical.Data.Nat.Base.html#487
caseL℧ : {X : Type ℓ} -> {A : Type ℓ'} -> (aη a℧ aθ : A) → L℧ X → A
caseL℧ aη a℧ aθ (η x) = aη
caseL℧ aη a℧ aθ ℧ = a℧
caseL℧ a0 a℧ aθ (θ lx~) = aθ


-- Similar to znots and snotz, defined at
-- https://agda.github.io/cubical/Cubical.Data.Nat.Properties.html
℧≠θ : {X : Type ℓ} -> {lx~ : ▹ (L℧ X)} -> ¬ (℧ ≡ θ lx~)
℧≠θ {X = X} {lx~ = lx~} eq =
  rec* (subst (caseL℧ X (L℧ X) ⊥*) eq ℧) -- subst (caseL℧ X (L℧ X) ⊥) eq ℧

η≠℧ : {X : Type ℓ} -> {x : X} -> ¬ (η x ≡ ℧)
η≠℧ {X = X} {x = x} eq =
  rec* (subst (caseL℧ X ⊥* ⊥*) eq x) -- subst (caseL℧ X ⊥ ⊥) eq x

η≠θ : {X : Type ℓ} -> {x : X} -> {lx~ : ▹ (L℧ X)} -> ¬ (L℧.η x ≡ θ lx~)
η≠θ {X = X} {x = x} {lx~ = lx~} eq =
  rec* (subst (caseL℧ X ⊥* ⊥*) eq x) -- subst (caseL℧ X ⊥ ⊥) eq x




-- TODO: Does this make sense?
pred : {X : Type ℓ} -> (lx : L℧ X) -> ▹ (L℧ X)
pred (η x) = next ℧
pred ℧ = next ℧
pred (θ lx~) = lx~

pred-def : {X : Type ℓ} -> (def : ▹ (L℧ X)) -> (lx : L℧ X) -> ▹ (L℧ X)
pred-def def (η x) = def
pred-def def ℧ = def
pred-def def (θ lx~) = lx~


-- TODO: This uses the pred function above, and I'm not sure whether that
-- function makes sense.
inj-θ : {X : Type ℓ} -> (lx~ ly~ : ▹ (L℧ X)) ->
  θ lx~ ≡ θ ly~ ->
  ▸ (λ t -> lx~ t ≡ ly~ t)
inj-θ lx~ ly~ H = let lx~≡ly~ = cong pred H in
  λ t i → lx~≡ly~ i t


-- Monadic structure

ret : {X : Type ℓ} -> X -> L℧ X
ret = η


ext' : (A -> L℧ B) -> ▹ (L℧ A -> L℧ B) -> L℧ A -> L℧ B
ext' f rec (η x) = f x
ext' f rec ℧ = ℧
ext' f rec (θ l-la) = θ (rec ⊛ l-la)

ext : (A -> L℧ B) -> L℧ A -> L℧ B
ext f = fix (ext' f)

lift×' : (▹ (L℧ (A × B) -> L℧ A × L℧ B)) -> L℧ (A × B) -> L℧ A × L℧ B
lift×' rec (η (a , b)) = η a , η b
lift×' rec ℧ = ℧ , ℧
lift×' rec (θ l~) = (θ (λ t → rec t (l~ t) .fst)) , θ (λ t -> rec t (l~ t) .snd)

lift× : {A : Type ℓ} {B : Type ℓ'} -> L℧ (A × B) -> L℧ A × L℧ B
lift× {A = A} {B = B} = fix lift×'

lift×-inv' : ▹ (L℧ A × L℧ B -> L℧ (A × B)) -> L℧ A × L℧ B -> L℧ (A × B)
lift×-inv' rec (η a , η b) = η (a , b)
lift×-inv' rec (η a , θ l'~) = θ (λ t -> (rec t (η a , l'~ t)))
lift×-inv' rec (℧ , _) = ℧
lift×-inv' rec (_ , ℧) = ℧ -- not sure whether it's gray
lift×-inv' rec (θ l~ , η b) = θ (λ t -> rec t (l~ t , η b))
lift×-inv' rec (θ l~ , θ l'~) = θ (λ t -> rec t (l~ t , l'~ t))

lift×-inv : {A : Type ℓ} {B : Type ℓ'} -> L℧ A × L℧ B -> L℧ (A × B)
lift×-inv {A = A} {B = B} = fix lift×-inv'

unfold-lift×-inv : {A : Type ℓ} {B : Type ℓ'} ->
  lift×-inv {A = A} {B = B} ≡ lift×-inv' (next lift×-inv)
unfold-lift×-inv = fix-eq lift×-inv'

bind : L℧ A -> (A -> L℧ B) -> L℧ B
bind {A} {B} la f = ext f la


unfold-ext : (f : A -> L℧ B) -> ext f ≡ ext' f (next (ext f))
unfold-ext f = fix-eq (ext' f)


ext-eta : ∀ (a : A) (f : A -> L℧ B) ->
  ext f (η a) ≡ f a
ext-eta a f =
  fix (ext' f) (ret a)            ≡⟨ (λ i → unfold-ext f i (ret a)) ⟩
  (ext' f) (next (ext f)) (ret a) ≡⟨ refl ⟩
  f a ∎

ext-err : (f : A -> L℧ B) ->
  bind ℧ f ≡ ℧
ext-err f =
  fix (ext' f) ℧            ≡⟨ (λ i → unfold-ext f i ℧) ⟩
  (ext' f) (next (ext f)) ℧ ≡⟨ refl ⟩
  ℧ ∎


ext-theta : (f : A -> L℧ B)
            (l : ▹ (L℧ A)) ->
            bind (θ l) f ≡ θ (ext f <$> l)
ext-theta f l =
  (fix (ext' f)) (θ l)            ≡⟨ (λ i → unfold-ext f i (θ l)) ⟩
  (ext' f) (next (ext f)) (θ l)   ≡⟨ refl ⟩
  θ (fix (ext' f) <$> l) ∎


monad-unit-l : ∀ (a : A) (f : A -> L℧ B) -> ext f (ret a) ≡ f a
monad-unit-l = ext-eta

monad-unit-r : (la : L℧ A) -> ext ret la ≡ la
monad-unit-r = fix lem
  where
    lem : ▹ ((la : L℧ A) -> ext ret la ≡ la) ->
          (la : L℧ A) -> ext ret la ≡ la
    lem IH (η x) = monad-unit-l x ret
    lem IH ℧ = ext-err ret
    lem IH (θ x) = fix (ext' ret) (θ x)
                     ≡⟨ ext-theta ret x ⟩
                   θ (fix (ext' ret) <$> x)
                     ≡⟨ refl ⟩
                   θ ((λ la -> ext ret la) <$> x)
                     ≡⟨ (λ i → θ λ t → IH t (x t) i) ⟩
                   θ (id <$> x)
                     ≡⟨ refl ⟩
                   θ x ∎

monad-assoc : {A B C : Type} -> (f : A -> L℧ B) (g : B -> L℧ C) (la : L℧ A) ->
  ext g (ext f la) ≡ ext (λ x -> ext g (f x)) la
monad-assoc = {!!}



ext-comp-ret : (f : L℧ A -> L℧ B) (a : A) (n : ℕ) ->
     ext (f ∘ ret) ((δ ^ n) (η a)) ≡ (δ ^ n) (f (η a))
ext-comp-ret f a zero = ext-eta a (f ∘ ret)
ext-comp-ret f a (suc n) =
  ext (f ∘ ret) (δ ((δ ^ n) (η a)))
    ≡⟨ ext-theta (f ∘ ret) _ ⟩
  θ (ext (f ∘ ret) <$> (next ((δ ^ n) (η a))))
    ≡⟨ refl ⟩
  θ (λ t -> ext (f ∘ ret) (next ((δ ^ n) (η a)) t))
    ≡⟨ refl ⟩
  δ (ext (f ∘ ret) ((δ ^ n) (η a)))
    ≡⟨ cong δ (ext-comp-ret f a n) ⟩
  δ ((δ ^ n) (f (η a))) ∎


-- Need f to preserve ℧ and preserve θ...
ext-comp-ret' : (f : L℧ A -> L℧ B) ->
  ▹ ((la : L℧ A) ->  ext (f ∘ ret) la ≡ f la) ->
     (la : L℧ A) ->  ext (f ∘ ret) la ≡ f la
ext-comp-ret' f IH (η a) = ext-eta a (f ∘ ret)
ext-comp-ret' f IH ℧ = {!!}
ext-comp-ret' f IH (θ la~) = {!!}


-- Ext commutes with delay
ext-delay : (f : A -> L℧ B) (la : L℧ A) (n : ℕ) ->
  ext f ((δ ^ n) la) ≡ (δ ^ n) (ext f la)
ext-delay f la zero = refl
ext-delay f la (suc n) =
  ext f (δ ((δ ^ n) la))
    ≡⟨ refl ⟩
  ext f (θ (next ((δ ^ n) la)))
    ≡⟨ ext-theta f _ ⟩
  θ (ext f <$> next ((δ ^ n) la))
    ≡⟨ refl ⟩
  θ (λ t -> ext f (next ((δ ^ n) la) t))
    ≡⟨ refl ⟩
  θ (λ t -> ext f ((δ ^ n) la))
    ≡⟨ (λ i -> θ λ t -> ext-delay f la n i) ⟩
  θ (λ t -> (δ ^ n) (ext f la))
    ≡⟨ refl ⟩
  δ ((δ ^ n) (ext f la)) ∎



{-
monad-assoc-def =
  {A B C : Type} ->
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
-}



mapL : (A -> B) -> L℧ A -> L℧ B
mapL f la = bind la (λ a -> ret (f a))

mapL-eta : (f : A -> B) (a : A) ->
  mapL f (η a) ≡ η (f a)
mapL-eta f a = ext-eta a λ a → ret (f a)

mapL-℧ : (f : A -> B) ->
  mapL f ℧ ≡ ℧
mapL-℧ f = ext-err (ret ∘ f)

mapL-theta : (f : A -> B) (la~ : ▹ (L℧ A)) ->
  mapL f (θ la~) ≡ θ (mapL f <$> la~)
mapL-theta f la~ = ext-theta (ret ∘ f) la~


mapL-id : (la : L℧ A) -> mapL id la ≡ la -- mapL id_A ≡ id_LA
mapL-id la = monad-unit-r la

mapL-comp' : (g : B -> C) (f : A -> B) -> -- mapL (g ∘ f) ≡ mapL g ∘ mapL f
  ▹ ((la : L℧ A) -> mapL (g ∘ f) la ≡ (mapL g ∘ mapL f) la) ->
     (la : L℧ A) -> mapL (g ∘ f) la ≡ (mapL g ∘ mapL f) la
mapL-comp' g f _ (η x) = lem1 ∙ sym lem2
  where
    lem1 : mapL (g ∘ f) (η x) ≡ η (g (f x))
    lem1 = mapL-eta _ _

    lem2 : (mapL g ∘ mapL f) (η x) ≡ η (g (f x))
    lem2 = (cong (mapL g) (mapL-eta f x)) ∙ mapL-eta g (f x)
    
mapL-comp' g f _ ℧ = lem1 ∙ sym lem2
  where
    lem1 : mapL (g ∘ f) ℧ ≡ ℧
    lem1 = mapL-℧ _

    lem2 : (mapL g ∘ mapL f) ℧ ≡ ℧
    lem2 = (cong (mapL g) (mapL-℧ _)) ∙ mapL-℧ _

mapL-comp' g f IH (θ la~) = lem1 ∙ sym lem2
  where
    lem1 : mapL (g ∘ f) (θ la~) ≡ θ (mapL (g ∘ f) <$> la~)
    lem1 = mapL-theta _ _

    lem2 : (mapL g ∘ mapL f) (θ la~) ≡ θ (mapL (g ∘ f) <$> la~)
    lem2 = cong (mapL g) (mapL-theta _ _) ∙
           mapL-theta g (mapL f <$> la~) ∙
           λ i -> θ λ t -> sym (IH t (la~ t)) i -- θ (mapL g <$> (mapL f <$> la~)) ≡ θ (mapL (g ∘ f) <$> la~)

-- for lem2:
--
-- (mapL g ∘ mapL f) (θ la~) = mapL g (θ (mapL f <$> la~))    [by applying mapL-theta on the inside]
--                           = θ ((mapL g <$> mapL f <$> la~) [by applying mapL-theta on the inside]
--                           = θ ((mapL g ∘ mapL f) <$> la~)  [by definition of <$>]
--                           = θ (λ t -> (mapL g ∘ mapL f) (la~ t))  [by definition of <$>]
--                           = θ (λ t -> mapL (g ∘ f) (la~ t))  [by IH]
--                           = θ (mapL (g ∘ f) <$> la~)         [by definition of <$>]

mapL-comp : (g : B -> C) (f : A -> B) -> (la : L℧ A) ->
  mapL (g ∘ f) la ≡ (mapL g ∘ mapL f) la
mapL-comp g f = fix (mapL-comp' g f)

-- MapL commutes with delta
mapL-delay : (f : A -> B) (la : L℧ A) (n : ℕ) ->
  mapL f ((δ ^ n) la) ≡ (δ ^ n) (mapL f la)
mapL-delay f la n = ext-delay (ret ∘ f) la n


-- Strong monadic structure

retStrong : {Γ X : Type ℓ} -> Γ -> X -> L℧ X
retStrong γ x = ret x

extStrong' : {Γ X Y : Type ℓ} ->
  (Γ -> X -> L℧ Y) ->
  ▹ (Γ -> L℧ X -> L℧ Y) -> (Γ -> L℧ X -> L℧ Y)
extStrong' f rec γ (η x) = f γ x
extStrong' f rec _ ℧ = ℧
extStrong' f rec γ (θ l-la) = θ (λ t -> rec t γ (l-la t))

extStrong : {Γ X Y : Type ℓ} -> (Γ -> X -> L℧ Y) -> (Γ -> L℧ X -> L℧ Y)
extStrong f = fix (extStrong' f)


-- Commuting condition between theta and delta

theta-delta-comm : {X : Type ℓ} (lx~ : ▹ L℧ X) ->
  θ (λ t -> δ (lx~ t)) ≡ δ (θ (λ t -> lx~ t))
theta-delta-comm lx~ = θ (λ t -> δ (lx~ t)) ≡⟨ refl ⟩
  θ (λ t -> θ (next (lx~ t))) ≡⟨ (λ i -> θ (λ t -> θ (next-Mt≡M lx~ t i))) ⟩
  θ (λ t -> θ lx~) ≡⟨ refl ⟩
  θ (next (θ lx~)) ≡⟨ refl ⟩
  δ (θ lx~) ∎

theta-delta-n-comm : {X : Type ℓ} (lx~ : ▹ L℧ X) (n : ℕ) ->
  θ (λ t -> (δ ^ n) (lx~ t)) ≡ (δ ^ n) (θ (λ t -> lx~ t))
theta-delta-n-comm lx~ zero = refl
theta-delta-n-comm lx~ (suc n) =
-- Goal: θ (λ t → δ ((δ ^ n) (lx~ t))) ≡ δ ((δ ^ n) (θ lx~))
  θ (λ t → δ ((δ ^ n) (lx~ t)))
    ≡⟨ theta-delta-comm (λ t → (δ ^ n) (lx~ t)) ⟩ -- i.e δ^n ∘ lx~
  δ (θ (λ t → ((δ ^ n) (lx~ t))))
    ≡⟨ cong δ (theta-delta-n-comm lx~ n) ⟩
  δ ((δ ^ n) (θ lx~)) ∎

