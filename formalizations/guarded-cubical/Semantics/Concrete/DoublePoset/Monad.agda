{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.DoublePoset.Monad (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Common.Common
open import Semantics.Concrete.GuardedLiftError k


private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓΓ ℓΓ' : Level
    ℓA ℓA' : Level
    ℓB ℓB'  : Level
    ℓC : Level
    ℓAᵢ ℓAₒ : Level
    ℓ≤Γ ℓ≤A ℓ≤B : Level
    ℓA₁ ℓA₂ ℓA₃ : Level
    ℓR ℓS ℓT : Level
    ℓ≈Γ ℓ≈A ℓ≈B : Level
private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A




-- Defining the "call-by-push-value ext" of type (A → U B) → (F A -* B).
-- This is not the same as the "Kleisli extension" (A → U F A') → (F A -* F A'),
-- because there B has the form F A'.

--module CBPVMonad (A : PosetBisim ℓA ℓ≤A ℓ≈A) (B : ErrorDomain ℓB ℓ≤B ℓ≈B) where

module StrongCBPVExt
  (Γ : Type ℓΓ)
  (A : Type ℓA)
  (B : Type ℓB)
  (℧B : B) (θB : (▹ B) → B)
  (f : Γ → A → B) where

  -- private
    -- module Γ = PosetBisimStr (Γ .snd)
    -- module A = PosetBisimStr (A .snd)
    -- module B = ErrorDomainStr (B .snd)

    --module LockStep = LiftOrdHomogenous ⟨ A ⟩ (A._≤_)

  -- _≤LA_ : _
  -- _≤LA_ = LockStep._⊑_
  

  module Rec (rec : ▹ (Γ → L℧ A → B)) where 
    ext' : Γ → L℧ A → B
    ext' γ (η x) = f γ x
    ext' _ ℧ = ℧B
    ext' γ (θ lx~) = θB (λ t → rec t γ (lx~ t))

  ext : _
  ext = fix Rec.ext'

  unfold-ext : ext ≡ Rec.ext' (next ext)
  unfold-ext = fix-eq Rec.ext'

  open Rec (next ext) public -- brings ext' into scope instantiated with (next ext)

  -- All of the below equations involve an element γ of ⟨ Γ ⟩,
  -- so we group them into a module parameterized by an element γ for
  -- easy re-use by the "non-strong" monad definition in module CBPVExt.
  module Equations (γ : Γ) where

    ext-η : (x : A) → ext γ (η x) ≡ f γ x
    ext-η x = funExt⁻ (funExt⁻ unfold-ext γ) (η x) -- funExt⁻ unfold-ext (η x)

    ext-℧ : ext γ ℧ ≡ ℧B
    ext-℧ = funExt⁻ (funExt⁻ unfold-ext γ) ℧ -- funExt⁻ unfold-ext ℧

    ext-θ : (lx~ : ▹ L℧ A) → ext γ (θ lx~) ≡ θB (map▹ (ext γ) lx~)
    ext-θ lx~ = funExt⁻ (funExt⁻ unfold-ext γ) (θ lx~) -- funExt⁻ unfold-ext (θ lx~)

    ext-δ : (lx : L℧ A) → ext γ (δ lx) ≡ (θB (next (ext γ lx)))
    ext-δ lx = ext-θ (next lx)



--------------
-- Monad laws
--------------

module MonadLawsStrong
  (Γ : Type ℓΓ)
  (γ : Γ)
  where

  module Strong-Unit-Left (A : Type ℓA) (B : Type ℓB) (℧B : B) (θB : (▹ B) → B) where
    open StrongCBPVExt Γ A B ℧B θB
  
    strong-monad-unit-left : ∀ (f : Γ → A → B) (x : A) → ext f γ (η x) ≡ f γ x
    strong-monad-unit-left f x = Equations.ext-η f γ x


  module Strong-Unit-Right (A : Type ℓA) where

    ret : Γ → A → L℧ A
    ret γ x = η x

    open StrongCBPVExt Γ A (L℧ A) ℧ θ

    open Equations
  
    strong-monad-unit-right : (lx : L℧ A) -> ext (λ γ x → η x) γ lx ≡ lx
    strong-monad-unit-right = fix lem
      where
        lem : ▹ ((lx : L℧ A) -> ext (λ γ x → η x) γ lx ≡ lx) →
                 (lx : L℧ A) -> ext (λ γ x → η x) γ lx ≡ lx
        lem IH (η x) = ext-η ret γ x
        lem IH ℧ = ext-℧ ret γ
        lem IH (θ lx~) = (ext-θ ret γ lx~) ∙ (congS θ (later-ext (λ t → IH t (lx~ t))))

{- Not sure if this is needed...

  module Unit-Right' (A : Type ℓA) (B : Type ℓB) (℧B : B) (θB : (▹ B) → B) where
    open StrongCBPVExt Γ A B ℧B θB

    ret : Γ → A → L℧ A
    ret γ x = η x

    -- Need g to be a homomorphism for this to work...
    monad-unit-right' : (g : Γ → L℧ A → B) → g ≡ ext (λ γ x → g γ (ret γ x))
    monad-unit-right' g = funExt (λ γ → funExt (λ lx → {!!}))
      where
        lem : ▹ ((lx : L℧ A) → g γ lx ≡ ext (λ γ' x → g γ' (ret γ' x)) γ lx) →
                 (lx : L℧ A) → g γ lx ≡ ext (λ γ' x → g γ' (ret γ' x)) γ lx
        lem IH (η x) = {!!}
        lem IH ℧ = {!!}
        lem IH (θ lx~) = {!!}
-}

  module Strong-Ext-Assoc
    (A₁ : Type ℓA₁) (A₂ : Type ℓA₂) (A₃ : Type ℓA₃)
    (f : Γ → A₁ -> L℧ A₂) (g : Γ → A₂ -> L℧ A₃) where

    open StrongCBPVExt
    open Equations

    -- Because the ext module is parameterized by the error and theta elements, we
    -- need three versions:
    private
      module A₁₃ = StrongCBPVExt Γ A₁ (L℧ A₃) ℧ θ
      module A₁₂ = StrongCBPVExt Γ A₁ (L℧ A₂) ℧ θ
      module A₂₃ = StrongCBPVExt Γ A₂ (L℧ A₃) ℧ θ
 
    strong-ext-assoc :
      ∀ (lx : L℧ A₁) → A₂₃.ext g γ (A₁₂.ext f γ lx) ≡ A₁₃.ext (λ γ' x' → A₂₃.ext g γ' (f γ' x')) γ lx
    strong-ext-assoc = fix aux
      where
        aux : ▹ (∀ (lx : L℧ A₁) → A₂₃.ext g γ (A₁₂.ext f γ lx) ≡ A₁₃.ext (λ γ' x' → A₂₃.ext g γ' (f γ' x')) γ lx) →
                 ∀ (lx : L℧ A₁) → A₂₃.ext g γ (A₁₂.ext f γ lx) ≡ A₁₃.ext (λ γ' x' → A₂₃.ext g γ' (f γ' x')) γ lx
        aux IH (η x) = eq1 ∙ (sym eq2)
          where
            eq1 = (λ i → A₂₃.ext g γ (A₁₂.Equations.ext-η f γ x i))
            eq2 = A₁₃.Equations.ext-η {!λ v v₁ → A₂₃.ext g v (f v v₁)!} γ x
          
        aux IH ℧ = eq1 ∙ (sym eq2)
          where
            eq1 = (λ i → A₂₃.ext g γ (A₁₂.Equations.ext-℧ f γ i)) ∙ (λ i → A₂₃.Equations.ext-℧ g γ i)
            eq2 = A₁₃.Equations.ext-℧ _ γ
            
        aux IH (θ lx~) = eq1 ∙ (sym eq2)
          where
            eq1 = (λ i → A₂₃.ext g γ (A₁₂.Equations.ext-θ f γ lx~ i)) ∙
                  (λ i → A₂₃.Equations.ext-θ g γ (map▹ (A₁₂.ext f γ) lx~) i) ∙
                  congS θ (later-ext (λ t → IH t (lx~ t))) -- (λ i → A₂₃.Equations.ext-θ g γ (map▹ (A₁₂.ext f γ) lx~) i) ∙ {!!}
            eq2 = A₁₃.Equations.ext-θ _ γ lx~

    -- monad-assoc : {Γ X Y Z : Type ℓ} -> (f : Γ -> Y -> S Z) -> (g : (Γ -> X -> S Y)) ->
    -- (γ : Γ) -> (x : X) -> (s : S X) ->
    -- ext f γ (strong-bind-s g γ s) ≡ ext (λ γ' x' -> strong-bind-s f γ' (g γ' x')) γ s

    -- monad-assoc : ext g (ext f la) ≡ ext (λ x -> ext g (f x)) la



-----------------------------------------
-- The "non-strong" version of the monad
-----------------------------------------

module CBPVExt
  (A : Type ℓA)
  (B : Type ℓB)
  (℧B : B)
  (θB : (▹ B) → B)
  (f : A → B) where

  f' : Unit → A → B
  f' _ = f

  open StrongCBPVExt Unit A B ℧B θB f'
    renaming (ext' to strong-ext' ; ext to strong-ext ; module Equations to StrongEquations)

  ext : L℧ A → B
  ext = strong-ext tt

  -- Re-export all equations, without the need for the client to provide an element of type Unit.
  -- This allows us to directly use the equations defined in
  -- StrongCBPVExt by just supplying tt to the Equations module.
  -- open Equations tt public
  module Equations = StrongEquations tt

-- Monad laws for the non-strong version
module MonadLaws where

  open MonadLawsStrong Unit tt

  module Unit-Left (A : Type ℓA) (B : Type ℓB) (℧B : B) (θB : (▹ B) → B) where
    --open StrongCBPVExt Unit A B ℧B θB hiding (ext)
    open CBPVExt A B ℧B θB
    open Strong-Unit-Left A B ℧B θB
  
    monad-unit-left : ∀ (f : A → B) (x : A) → ext f (η x) ≡ f x
    monad-unit-left f x = strong-monad-unit-left (λ _ x → f x) x

  module Unit-Right (A : Type ℓA) where
    open CBPVExt A (L℧ A) ℧ θ
    open Strong-Unit-Right A

    monad-unit-right : (lx : L℧ A) -> ext η lx ≡ lx
    monad-unit-right lx = strong-monad-unit-right lx

  module Ext-Assoc (A₁ : Type ℓA₁) (A₂ : Type ℓA₂) (A₃ : Type ℓA₃)
   (f : A₁ -> L℧ A₂) (g : A₂ -> L℧ A₃) where

    open Strong-Ext-Assoc A₁ A₂ A₃ (λ _ → f) (λ _ → g)

    module A₁₂ = CBPVExt A₁ (L℧ A₂) ℧ θ
    module A₂₃ = CBPVExt A₂ (L℧ A₃) ℧ θ
    module A₁₃ = CBPVExt A₁ (L℧ A₃) ℧ θ

    ext-assoc : ∀ (lx : L℧ A₁) →
      A₂₃.ext g (A₁₂.ext f lx) ≡ A₁₃.ext (λ x' → A₂₃.ext g (f x')) lx
    ext-assoc = strong-ext-assoc


------------------------------------------------------
-- The map function from (Aᵢ → Aₒ) to (L℧ Aᵢ → L℧ Aₒ)
------------------------------------------------------

module Map {Aᵢ : Type ℓAᵢ} {Aₒ : Type ℓAₒ} where

  map : (Aᵢ → Aₒ) → (L℧ Aᵢ → L℧ Aₒ)
  map f = ext (η ∘ f)
    where open CBPVExt Aᵢ (L℧ Aₒ) ℧ θ


module MapProperties where

  open Map
  pres-id : ∀ {A : Type ℓ} → Map.map {Aᵢ = A} {Aₒ = A} id ≡ id
  pres-id {A = A} = funExt (λ lx → MonadLaws.Unit-Right.monad-unit-right A lx)


  pres-comp : ∀ {A₁ : Type ℓA₁} {A₂ : Type ℓA₂} {A₃ : Type ℓA₃} →
    (f : A₁ → A₂) (g : A₂ → A₃) → map (g ∘ f) ≡ map g ∘ map f
    
    -- NTS: ext (η ∘ (g ∘ f)) = (ext (η ∘ g)) ∘ (ext (η ∘ f))
    -- Know: ext (η ∘ g) (ext (η ∘ f) lx) ≡
    --       ext (λ x → ext (η ∘ g) ((η ∘ f) x)) lx ≡
    --       ext (λ x → (η ∘ g) (f x)) lx ≡
    --       ext (η ∘ (g ∘ f)) lx ≡
    --       map (g ∘ f) lx
             
  pres-comp {A₁ = A₁} {A₂ = A₂} {A₃ = A₃} f g = sym (funExt aux) -- sym {!ext-assoc!} ∙ {!!}
    where
      open MonadLaws.Ext-Assoc A₁ A₂ A₃ (η ∘ f) (η ∘ g)
      aux : (lx : L℧ A₁) → _
      aux lx = ext-assoc lx ∙
        (λ i → A₁₃.ext (λ x → A₂₃.Equations.ext-η (η ∘ g) (f x) i) lx)

  map-η : ∀ {Aᵢ : Type ℓAᵢ} {Aₒ : Type ℓAₒ} →
    (f : Aᵢ → Aₒ) (x : Aᵢ) → map f (η x) ≡ η (f x)
  map-η {Aᵢ = Aᵢ} {Aₒ = Aₒ} f x = Equations.ext-η (η ∘ f) x
    where open CBPVExt Aᵢ (L℧ Aₒ) ℧ θ

  map-℧ : ∀ {Aᵢ : Type ℓAᵢ} {Aₒ : Type ℓAₒ} →
    (f : Aᵢ → Aₒ) → map f ℧ ≡ ℧
  map-℧ {Aᵢ = Aᵢ} {Aₒ = Aₒ} f = Equations.ext-℧ (η ∘ f)
    where open CBPVExt Aᵢ (L℧ Aₒ) ℧ θ

  map-θ : ∀ {Aᵢ : Type ℓAᵢ} {Aₒ : Type ℓAₒ} →
    (f : Aᵢ → Aₒ) (lx~ : ▹ (L℧ Aᵢ)) →
      map f (θ lx~) ≡ θ (map▹ (map f) lx~)
  map-θ {Aᵢ = Aᵢ} {Aₒ = Aₒ} f lx~ = Equations.ext-θ (η ∘ f) lx~
     where open CBPVExt Aᵢ (L℧ Aₒ) ℧ θ


  
