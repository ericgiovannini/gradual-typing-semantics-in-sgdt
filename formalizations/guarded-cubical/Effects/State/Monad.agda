{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Later

module Effects.State.Monad (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Semantics.Concrete.GuardedLiftError k renaming (module Monad to L℧)
open import Semantics.Concrete.Predomain.Error
open import Semantics.Concrete.Predomain.SimpleErrorDomain k
import Semantics.Concrete.Predomain.Ext k as L℧Ext


private
  variable
    ℓ ℓ' : Level
    ℓS ℓA ℓA' ℓB : Level
    ℓR ℓRS : Level

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A



module _ (S : Type ℓS) where

  record StateDelayStr (B : Type ℓB) : Type (ℓ-max ℓB ℓS) where
    field
    
      -- Algebraic structure
      errS : B
      stepS : ▹ B → B
      getS : (S → B) → B
      putS : B → (S → B)

      -- isSet
      isSetSD : isSet B

      -- Usual laws for get and put
      get-getS : ∀ (f : (S → (S → B)))
        → getS (λ s → getS (f s)) ≡ getS (λ s → f s s)

      get-put : ∀ (x : B)
        → getS (putS x) ≡ x

      put-get : ∀ (g : S → B) (s : S)
        → putS (getS g) s ≡ putS (g s) s

      put-put : ∀ (x : B) (s t : S)
        → putS (putS x s) t ≡ putS x s

      -- Get and put commute with stepping
      step-get : ∀ (f~ : ▹ (S → B))
        → getS (λ s → stepS (λ t → f~ t s)) ≡ stepS (λ t → getS (f~ t))

      step-put : ∀ (d~ : ▹ B) (s : S)
        → putS (stepS d~) s ≡ stepS (λ t → putS (d~ t) s)

      -- Get and put commute with error
      -- TODO: are these necessary?
      err-get :
          getS (λ s → errS) ≡ errS

      err-put : ∀ (s : S)
        → putS errS s ≡ errS



  StateDelay : (ℓB : Level) → Type (ℓ-max ℓS (ℓ-suc ℓB))
  StateDelay ℓB = TypeWithStr ℓB StateDelayStr


-- The free state-delay-error algebra as a HIT.

module _ (S : Type ℓS) (A : Type ℓA) where

  data Free : Type (ℓ-max ℓS ℓA) where
    ret : A → Free
    err : Free
    step : ▹ Free → Free
    get : (S → Free) → Free
    put : Free → (S → Free)
    -- alternatively: put : (S × Free) → Free

    trunc : isSet Free

    -- equations
    get-get : ∀ (f : (S → (S → Free)))
      → get (λ s → get (f s)) ≡ get (λ s → f s s)

    get-put : ∀ (x : Free)
      → get (put x) ≡ x

    put-get : ∀ (g : S → Free) (s : S)
      → put (get g) s ≡ put (g s) s

    put-put : ∀ (x : Free) (s t : S)
      → put (put x s) t ≡ put x s

    step-get : ∀ (f~ : ▹ (S → Free))
      → get (λ s → step (λ t → f~ t s)) ≡ step (λ t → get (f~ t))

    step-put : ∀ (d~ : ▹ Free) (s : S)
      → put (step d~) s ≡ step (λ t → put (d~ t) s)

   


  -- Elim principle
  module _ {B : Free → Type ℓ}
    (ret* : (a : A) → B (ret a))
    (err* : B err)
    (step* : {d~ : ▹ Free} → ▸ (λ t → B (d~ t)) → B (step d~))
    (get* : {f : S → Free}
      → ((s : S) → B (f s))
      → B (get f))
    (put* : {d : Free} {s : S} → B d → B (put d s))
    (trunc* : (d : Free) → isSet (B d))
    (get-get* : ∀ {f : (S → (S → Free))}
      → (fᴰ : ((s₁ : S) → (s₂ : S) → B (f s₁ s₂)))
      → PathP (λ i → B (get-get f i))
          (get* (λ s → get* (fᴰ s)))
          (get* (λ s → fᴰ s s)))
    -- (step-get* : ∀ {f~ : ▹ (S → Free)}
    --   → (fᴰ~ : ▸ (λ t → ((s : S) → B (f~ t s))))
    --   → PathP (λ i → B (step-get f~ i))
    --       (get* (λ s → step* (λ t → fᴰ~ t s)))
    --       (step* (λ t → get* (fᴰ~ t))))
    (step-get* : ∀ {f~ : ▹ (S → Free)}
      -- → (fᴰ~ : ▸ (λ t → ((s : S) → B (f~ t s))))
      → (IH : ▹ ((d : Free) → B d))
      → PathP (λ i → B (step-get f~ i))
          (get* (λ s → step* (λ t → IH t (f~ t s))))
          (step* (λ t → IH t (get (f~ t)))))
          -- we don't know a priori that IH t will take (get (f~ t)) to get* (...)
    where

    elim : ▹ ((d : Free) → B d)
            → (d : Free) → B d
    elim _ (ret x) = ret* x
    elim _ err = err*
    elim IH (step d~) = step* (λ t → IH t (d~ t))
    elim IH (get g) = get* (λ s → elim IH (g s))
    elim IH (put d s) = put* {s = s} (elim IH d)
    elim _ (trunc x y p q i j) = {!!}
    elim IH (get-get f i) = get-get* (λ s₁ s₂ → elim IH (f s₁ s₂)) i
    elim _ (get-put d i) = {!!}
    elim _ (put-get g s i) = {!!}
    elim _ (put-put d s t i) = {!!}
    elim IH (step-get f~ i) = step-get* IH i
    elim _ (step-put d~ s i) = {!!}


-- Another presentation of the free state-delay-error algebra.

module _ (S : Type ℓS) (A : Type ℓA) where

  Free' : Type (ℓ-max ℓS ℓA)
  Free' = S → L℧ (S × A)


module _ {S : Type ℓS} {A : Type ℓA} where


  -- Proving that Free' is a monad and implements the operations
  -- in the algebraic signature of state + error + delay
  ret' : A → Free' S A
  ret' x s = η (s , x)

  err' : Free' S A
  err' s = ℧

  step' : ▹ Free' S A → Free' S A
  step' d~ s = θ (λ t → d~ t s)

  get' : (S → Free' S A) → Free' S A
  get' g s = g s s

  put' : Free' S A → (S → Free' S A)
  put' d s s' = d s


  open StateDelayStr


  module _ (isSetA : isSet A) where
  
    Free'→SDStr : StateDelayStr S (Free' S A)
    Free'→SDStr .errS = err'
    Free'→SDStr .stepS = step'
    Free'→SDStr .getS = get'
    Free'→SDStr .putS = put'
    Free'→SDStr .isSetSD = {!!}
    Free'→SDStr .get-getS f = refl
    Free'→SDStr .StateDelayStr.get-put x = refl
    Free'→SDStr .StateDelayStr.put-get g s = refl
    Free'→SDStr .StateDelayStr.put-put x s t = refl
    Free'→SDStr .StateDelayStr.step-get f~ = {!!}
    Free'→SDStr .StateDelayStr.step-put d~ s = refl
    Free'→SDStr .err-get = refl
    Free'→SDStr .err-put s = {!!}

    Free'→SD : StateDelay S (ℓ-max ℓS ℓA)
    Free'→SD = Free' S A , Free'→SDStr


{-
module _ (S : Type ℓS) where

  U : (B : StateDelay S ℓB) → Type (ℓ-max ℓS ℓB)
  U B = S → ⟨ B ⟩

  module _ (A : Type ℓA) where

    |F| : Type {!!}
    |F| = L℧ (S × A)

    err'' : |F|
    err'' = ℧

    step'' : ▹ |F| → |F|
    step'' x~ = θ x~

    get'' : (S → |F|) → |F|
    get'' g = {!!}

    put'' : |F| → (S → |F|)
    put'' x s = {!!}
-}


-- Monadic extension for *functions* and *relations*

module _ (S : Type ℓS) where

  T : Type ℓA → Type (ℓ-max ℓS ℓA)
  T A = Free' S A

module _ {S : Type ℓS} {A : Type ℓA} where
  
  retT : A → T S A
  retT = ret'

  errT : T S A
  errT = err'

  stepT : ▹ T S A → T S A
  stepT = step'

  getT : (S → T S A) → T S A
  getT = get'

  putT : T S A → (S → T S A)
  putT = put'


module _ {S : Type ℓS} (A : Type ℓA) (A' : Type ℓA') where
  
  module _ (f : A → T S A') where

    ext : T S A → T S A'
    ext x s = L℧.ext (λ {(s' , a) → f a s'}) (x s)

  module _ (RS : S → S → Type ℓRS) (R : A → T S A' → Type ℓR) where

    extRel : T S A → T S A' → Type {!!}
    extRel x y = ∀ (s s' : S) → RS s s' → R {!!} y


  module _ (A : Type ℓA) (B : StateDelay S ℓB) where

    private
      module B = StateDelayStr (B .snd)
      B→SimpleErrorDomain : SimpleErrorDomain ℓB
      B→SimpleErrorDomain =
        mkSimpleErrorDomain ⟨ B ⟩ (simpleerrordomainstr B.errS B.stepS)

    module _ (f : A → ⟨ B ⟩) where

      opaque
        unfolding ⟨_⟩s

        extCBPV : T S A → ⟨ B ⟩
        extCBPV x = B.getS (λ s → f' (x s))
          where
            f' : L℧ (S × A) → ⟨ B ⟩
            f' y = L℧Ext.ext {B = B→SimpleErrorDomain}
              (λ {(s , a) → B.putS (f a) s}) y
    

    module _ (R : A → ⟨ B ⟩ → Type ℓR) where

      extRelCBPV : T S A → ⟨ B ⟩ → Type {!!}
      extRelCBPV x y = ∀ (s : S) → {!!}


module _ {S : Type ℓS} {A : Type ℓA} where

  iterate' : (T S A → T S A) → T S A → T S A
  iterate' f x₀ = ext A A (λ x → f (retT x)) x₀

  fixT : (T S A → T S A) → T S A
  fixT f = fix fixT'
    where
      fixT' : ▹ T S A → T S A
      fixT' x~ = stepT (λ t → f (x~ t))

module _ {S : Type ℓS} {A : Type ℓA} {A' : Type ℓA'} where

  -- iterateT : (T S A → T S A') → T S A → T S A'
  -- iterateT f x₀ = ext A A' (λ x → f (retT x)) x₀

module _ {S : Type ℓS} {A : Type ℓA} {A' : Type ℓA'} where

  iterateT : ((A → T S A') → (A → T S A')) → (A → T S A')
  iterateT f = fix iterateT'
    where
      iterateT' : ▹ (A → T S A') → A → T S A'
      iterateT' f~ x = stepT (λ t → f~ t x)



module Test (S : Type)
  (T : Type → Type)
  (η : {X : Type} → X → T X)
  (℧ : {X : Type} → T X)
  (θ : {X : Type} → ▹ (T X) → T X)
  -- (θ : {X : Type} → (Tick → T X) → T X
  (get : {X : Type} → (S → T X) → T X)
  (X : Type)
  (_R_ : X → X → Type) where

  import Cubical.Data.Equality as Eq

  -- data _⊑_ : T X → T X → Type {!!} where
  --   ⊑ηη : ∀ x y → x R y → (η x) ⊑ (η y)

  --   ⊑℧ : ∀ l → ℧ ⊑ l

  --   ⊑θθ : ∀ l~ l'~ → ▸ (λ t → l~ t ⊑ l'~ t) → θ l~ ⊑ θ l'~

  -- lem : ∀ l l' → l ⊑ l' → l' ⊑ l → l ≡ l'
  -- lem l l' (⊑ηη x y x₁) H2 = {!!}
  -- lem l l' (⊑℧ x) H2 = {!H2!}
  -- lem l l' (⊑θθ l~ l'~ x) H2 = {!!}


  data _⊑_ : T X → T X → Type {!!} where
    ⊑ηη : ∀ {l l'} x y → l Eq.≡ η x → l' Eq.≡ η y → x R y → l ⊑ l'

    ⊑℧ : ∀ {l l'} → l Eq.≡ ℧ → l ⊑ l'

    ⊑θθ : ∀ {l l'} l~ l'~ → l Eq.≡ θ l~ → l' Eq.≡ θ l'~
      → ▸ (λ t → l~ t ⊑ l'~ t)
      → l ⊑ l'

  module _
    (R-antisym : ∀ x y → x R y → y R x → x ≡ y)
    (η-inj : ∀ (x y : X) → η x ≡ η y → x ≡ y)
    (θ-inj : ∀ (l~ l'~ : ▹ (T X)) → θ l~ ≡ θ l'~ → ▸ (λ t → l~ t ≡ l'~ t))

    where
  
    lem : ▹ (∀ l l' → l ⊑ l' → l' ⊑ l → l ≡ l') →
             ∀ l l' → l ⊑ l' → l' ⊑ l → l ≡ l'

    -- Case: l ≡ η x
    lem _ l l' (⊑ηη x y Eq.refl Eq.refl H) (⊑ηη y' x' eq eq' H') = {!!} -- show x ≡ x', y ≡ y'
    lem _ l l' (⊑ηη x y e e' _) (⊑℧ eq) = {!!} -- contra
    lem _ l l' (⊑ηη x y Eq.refl Eq.refl H) (⊑θθ l~ l'~ eq eq' H') = {!!} -- contra

    -- Case: l ≡ ℧
    lem _ l l' (⊑℧ e) (⊑ηη x y eq eq' H) = {!!} -- contra: ℧ ≡ η
    lem _ l l' (⊑℧ Eq.refl) (⊑℧ Eq.refl) = refl
    lem _ l l' (⊑℧ Eq.refl) (⊑θθ l~ l'~ eq eq' H) = {!!} -- contra: ℧ ≡ θ

    -- Case: l ≡ θ l~
    lem _ l l' (⊑θθ l~ l'~ Eq.refl Eq.refl H) (⊑ηη x y eq eq' H') = {!!}
    lem _ l l' (⊑θθ l~ l'~ Eq.refl Eq.refl H) (⊑℧ eq) = {!!}
    lem IH l l' (⊑θθ l~ l'~ Eq.refl Eq.refl H) (⊑θθ m~' m~ eq eq' H') =
      {!!}

  

module Test2 (S : Type)
  (T : Type → Type)
  (η : {X : Type} → X → T X)
  (℧ : {X : Type} → T X)
  (get : {X : Type} → (S → T X) → T X)
  (X : Type)
  (_R_ : X → X → Type) where

  import Cubical.Data.Equality as Eq


  data _⊑_ : T X → T X → Type ℓ-zero where
    ⊑ηη : ∀ {l l'} x y → l Eq.≡ η x → l' Eq.≡ η y → x R y → l ⊑ l'

    ⊑getget : ∀ {l l'} f f' → l Eq.≡ get f → l' Eq.≡ get f'
      → ((s : S) → f s ⊑ f' s)
      → l ⊑ l'


  module _
    (R-antisym : ∀ x y → x R y → y R x → x ≡ y)
    (η-inj : ∀ (x y : X) → η x ≡ η y → x ≡ y)
    (get-inj : ∀ (f f' : (S → (T X))) → get f ≡ get f' → (∀ s → f s ≡ f' s))

    where
  
      lem : ∀ l l' → l ⊑ l' → l' ⊑ l → l ≡ l'
      lem l l' (⊑ηη x y Eq.refl Eq.refl H) (⊑ηη y' x' eq eq' H') = {!!}
      lem l l' (⊑ηη x y Eq.refl Eq.refl H) (⊑getget f f' x₁ x₂ x₃) = {!!}
      
      lem l l' (⊑getget f f' Eq.refl Eq.refl H) (⊑ηη x y x₁ x₂ x₃) = {!!}
      lem l l' (⊑getget f f' Eq.refl Eq.refl H) (⊑getget g' g eq' eq H') =
        cong get
          (funExt (λ s → lem (f s) (f' s)
            (H s)
            (subst2 (λ w z → w ⊑ z) (sym (f'≡g' s)) (sym (f≡g s)) (H' s))))
        where
          f≡g : ∀ s → f s ≡ g s
          f≡g = get-inj f g (Eq.eqToPath eq)

          f'≡g' : ∀ s → f' s ≡ g' s
          f'≡g' = get-inj f' g' (Eq.eqToPath eq')
          

 
