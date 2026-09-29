{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.Ext (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Common.Common
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.Predomain.SimpleErrorDomain k


private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓΓ ℓΓ' : Level
    ℓA ℓA' : Level
    ℓB ℓB'  : Level
    ℓC : Level
    ℓAᵢ ℓAₒ : Level
    ℓA₁ ℓA₂ ℓA₃ : Level
   
private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


-----------------------------
-- Strong monadic structure
-----------------------------

module _
  {Γ : Type ℓΓ}
  {A : Type ℓA}
  {B : SimpleErrorDomain ℓB}
  (f : Γ → A → ⟨ B ⟩s) where

  private
    module B = SimpleErrorDomain→module B

  module StrongExtRec (rec : ▹ (Γ → L℧ A → ⟨ B ⟩s)) where 
    strongext' : Γ → L℧ A → ⟨ B ⟩s
    strongext' γ (η x) = f γ x
    strongext' _ ℧ = B.℧
    strongext' γ (θ lx~) = B.θ (λ t → rec t γ (lx~ t))

  module StrongExtRec' (γ : Γ) (rec : ▹ (L℧ A → ⟨ B ⟩s)) where

  opaque
    strongext : Γ → L℧ A → ⟨ B ⟩s
    strongext = fix StrongExtRec.strongext'

    unfold-strongext : strongext ≡ StrongExtRec.strongext' (next strongext)
    unfold-strongext = fix-eq StrongExtRec.strongext'

  strong-ext : Γ → ⟨ 𝔽 A ⟩s → ⟨ B ⟩s
  strong-ext γ x = strongext γ (𝔽-elim x)

  opaque -- marked opaque to hide the implementation
    st-ext : Γ → ⟨ 𝔽 A ⟩s → ⟨ B ⟩s
    st-ext γ = rec𝔽
      (λ x → f γ x) -- η case
      B.℧           -- ℧ case
      (λ rec lx~ → B.θ (λ t → rec t (lx~ t))) -- θ case

  module _ (γ : Γ) where
    opaque
      unfolding st-ext
      st-ext-η : ∀ (x : A)
        → st-ext γ (η𝔽 x) ≡ f γ x
      st-ext-η x = rec𝔽-η _ _ _ x

      st-ext-℧ : st-ext γ ℧𝔽 ≡ B.℧
      st-ext-℧ = rec𝔽-℧ _ _ _

      st-ext-θ : ∀ (lx~ : ▹ ⟨ 𝔽 A ⟩s)
        → st-ext γ (θ𝔽 lx~) ≡ B.θ (map▹ (st-ext γ) lx~)
      st-ext-θ = rec𝔽-θ _ _ _

      st-ext-δ : ∀ (lx : ⟨ 𝔽 A ⟩s)
        → st-ext γ (δ𝔽 lx) ≡ B.δ (st-ext γ lx)
      st-ext-δ lx = rec𝔽-δ _ _ _ _

  St-ext : Γ → SEDmor (𝔽 A) B
  St-ext γ .SEDmor.f = st-ext γ
  St-ext γ .SEDmor.f℧ = (cong₂ st-ext refl FA℧≡℧) ∙ (st-ext-℧ γ)
  St-ext γ .SEDmor.fθ x~ = (cong₂ st-ext refl (FAθ≡θ x~)) ∙ (st-ext-θ γ x~)

{-
  open StrongExtRec (next strongext) public -- brings strongext' into scope instantiated with (next strongext)

  -- All of the below equations involve an element γ of ⟨ Γ ⟩,
  -- so we group them into a module parameterized by an element γ.
  module _ (γ : Γ) where

    opaque
      unfolding sed-elim
      strongext-η : (x : A) → strong-ext γ (η𝔽 x) ≡ f γ x
      strongext-η x = funExt⁻ (funExt⁻ unfold-strongext γ) (η x) 

      strongext-℧ : strong-ext γ (𝔽-intro ℧) ≡ B.℧
      strongext-℧ = funExt⁻ (funExt⁻ unfold-strongext γ) ℧ 

      strongext-θ : (lx~ : ▹ L℧ A) → strong-ext γ (𝔽-intro (θ lx~)) ≡ B.θ (map▹ (strong-ext γ ∘ 𝔽-intro) lx~)
      strongext-θ lx~ = funExt⁻ (funExt⁻ unfold-strongext γ) (θ lx~)

      strongext-δ : (lx : L℧ A) → strong-ext γ (𝔽-intro (δ lx)) ≡ (B.θ (next (strong-ext γ (𝔽-intro lx))))
      strongext-δ lx = strongext-θ (next lx)

-}



---------------------
-- Strong monad laws
---------------------

module MonadLawsStrong
  (Γ : Type ℓΓ)
  (γ : Γ)
  where

  module _ (A : Type ℓA) (B : SimpleErrorDomain ℓB) where
  
    strong-monad-unit-left : ∀ (f : Γ → A → ⟨ B ⟩s) (x : A)
      → st-ext f γ (η𝔽 x) ≡ f γ x
    strong-monad-unit-left f x = st-ext-η f γ x

  module _ (A : Type ℓA) where

    ret : Γ → A → L℧ A
    ret γ x = η x

    -- opaque
      --unfolding SimpleErrorDomain→record sed-elim

    strong-monad-unit-right : (lx : ⟨ 𝔽 A ⟩s)
      → st-ext (λ γ x → (η𝔽 x)) γ lx ≡ lx
    strong-monad-unit-right = elim𝔽
      -- η case
      (λ x → st-ext-η _ γ x)

      -- ℧ case
      ((st-ext-℧ _ γ) ∙ FA℧≡℧)

      -- θ case
      (λ IH lx~ →
          st-ext-θ (λ γ x → (η𝔽 x)) γ lx~
        ∙ FAθ≡θ _
        ∙ congS θ𝔽 (later-ext (λ t → IH t (lx~ t))))

{-
      strong-monad-unit-right = fix lem
        where
          lem : ▹ ((lx : L℧ A) -> st-ext (𝔽 A) (λ γ x → η x) γ lx ≡ lx) →
                   (lx : L℧ A) -> st-ext (𝔽 A) (λ γ x → η x) γ lx ≡ lx
          lem IH (η x)   = st-ext-η _ ret γ x
          lem IH ℧       = st-ext-℧ _ ret γ
          lem IH (θ lx~) = (st-ext-θ _ ret γ lx~) ∙ (congS θ (later-ext (λ t → IH t (lx~ t))))
-}



  module _
    {A₁ : Type ℓA₁} {A₂ : Type ℓA₂} {A₃ : Type ℓA₃}
    (f : Γ → A₁ -> ⟨ 𝔽 A₂ ⟩s) (g : Γ → A₂ -> ⟨ 𝔽 A₃ ⟩s) where
 
    strong-ext-assoc :
      ∀ (lx : ⟨ 𝔽 A₁ ⟩s)
        → st-ext g γ (st-ext f γ lx) ≡
          st-ext (λ γ' x' → st-ext g γ' (f γ' x')) γ lx
    strong-ext-assoc = {!!}

{-
    strong-ext-assoc = fix aux
      where
        aux : ▹ (∀ (lx : L℧ A₁) → strongext g γ (strongext f γ lx) ≡ strongext (λ γ' x' → strongext g γ' (f γ' x')) γ lx) →
                 ∀ (lx : L℧ A₁) → strongext g γ (strongext f γ lx) ≡ strongext (λ γ' x' → strongext g γ' (f γ' x')) γ lx
        aux IH (η x) = eq1 ∙ (sym eq2)
          where
            eq1 = (λ i → strongext g γ (Equations.strongext-η f γ x i))
            eq2 = Equations.strongext-η {!λ v v₁ → A₂₃.ext g v (f v v₁)!} γ x
          
        aux IH ℧ = eq1 ∙ (sym eq2)
          where
            eq1 = (λ i → strongext g γ (Equations.strongext-℧ f γ i)) ∙ (λ i → Equations.strongext-℧ g γ i)
            eq2 = Equations.strongext-℧ _ γ
            
        aux IH (θ lx~) = eq1 ∙ (sym eq2)
          where
            eq1 = (λ i → strongext g γ (Equations.strongext-θ f γ lx~ i)) ∙
                  (λ i → Equations.strongext-θ g γ (map▹ (strongext f γ) lx~) i) ∙
                  congS θ (later-ext (λ t → IH t (lx~ t))) -- (λ i → A₂₃.Equations.ext-θ g γ (map▹ (A₁₂.ext f γ) lx~) i) ∙ {!!}
            eq2 = Equations.strongext-θ _ γ lx~
-}


-- module _
--   {Γ : Type ℓΓ}
--   {A : Type ℓA}
--   {B : SimpleErrorDomain ℓB}
--   (f : Γ → A → ⟨ B ⟩s) where

--   private
--     module B = SimpleErrorDomain→module B

--   st-ext∘δ : st-ext (λ γ x → B.δ (f γ x)) ≡ (λ γ lx → B.δ (st-ext f γ lx))
--   st-ext∘δ = {!!}



-----------------------------------------
-- The "standard" version of the monad
-----------------------------------------

module _
  {A : Type ℓA}
  {B : SimpleErrorDomain ℓB}
  (f : A → ⟨ B ⟩s) where

  private
    f' : Unit → A → ⟨ B ⟩s
    f' _ = f

    module B = SimpleErrorDomain→module B

  opaque
    ext : ⟨ 𝔽 A ⟩s → ⟨ B ⟩s
    ext = st-ext f' tt

  module Equations where

    opaque
      unfolding ext
      ext-η : (x : A) → ext (η𝔽 x) ≡ f x
      ext-η x = st-ext-η f' tt x

      ext-℧ : ext ℧𝔽 ≡ B.℧
      ext-℧ = st-ext-℧ f' tt

      ext-θ : (lx~ : ▹ ⟨ 𝔽 A ⟩s) → ext (θ𝔽 lx~) ≡ B.θ (map▹ ext lx~)
      ext-θ lx~ = st-ext-θ f' tt lx~

      ext-δ : (lx : ⟨ 𝔽 A ⟩s) → ext ((δ𝔽 lx)) ≡ (B.θ (next (ext lx)))
      ext-δ lx = st-ext-δ f' tt lx


-- Monad laws
--------------

module MonadLaws where

  open MonadLawsStrong Unit tt

  module _ {A : Type ℓA} {B : SimpleErrorDomain ℓB} where

    opaque
      unfolding ext
      monad-unit-left : ∀ (f : A → ⟨ B ⟩s) (x : A) → ext f (η𝔽 x) ≡ f x
      monad-unit-left f x = strong-monad-unit-left A B (λ _ x → f x) x

  module _ {A : Type ℓA} where

    opaque
      unfolding ext
      monad-unit-right : (lx : ⟨ 𝔽 A ⟩s) → ext η𝔽 lx ≡ lx
      monad-unit-right lx = strong-monad-unit-right A lx

  module _ {A₁ : Type ℓA₁} {A₂ : Type ℓA₂} {A₃ : Type ℓA₃}
   (f : A₁ → ⟨ 𝔽 A₂ ⟩s) (g : A₂ → ⟨ 𝔽 A₃ ⟩s) where

    -- open Strong-Ext-Assoc A₁ A₂ A₃ (λ _ → f) (λ _ → g)

    opaque
      unfolding ext
      ext-assoc : ∀ (lx : ⟨ 𝔽 A₁ ⟩s) →
        ext g (ext f lx) ≡ ext (λ x' → ext g (f x')) lx
      ext-assoc = strong-ext-assoc (λ _ → f) (λ _ → g)



  

------------------------------------------------------
-- The map function from (Aᵢ → Aₒ) to (L℧ Aᵢ → L℧ Aₒ)
------------------------------------------------------

module _ {Aᵢ : Type ℓAᵢ} {Aₒ : Type ℓAₒ} where

  map : (Aᵢ → Aₒ) → (⟨ 𝔽 Aᵢ ⟩s → ⟨ 𝔽 Aₒ ⟩s)
  map f = ext (η𝔽 ∘ f)
    -- where open CBPVExt Aᵢ (L℧ Aₒ) ℧ θ


module MapProperties where

  pres-id : ∀ {A : Type ℓ} → map {Aᵢ = A} {Aₒ = A} id ≡ id
  pres-id {A = A} = funExt (λ lx → MonadLaws.monad-unit-right lx)


  pres-comp : ∀ {A₁ : Type ℓA₁} {A₂ : Type ℓA₂} {A₃ : Type ℓA₃} →
    (f : A₁ → A₂) (g : A₂ → A₃) → map (g ∘ f) ≡ map g ∘ map f
    
    -- NTS: ext (η ∘ (g ∘ f)) = (ext (η ∘ g)) ∘ (ext (η ∘ f))
    -- Know: ext (η ∘ g) (ext (η ∘ f) lx) ≡
    --       ext (λ x → ext (η ∘ g) ((η ∘ f) x)) lx ≡
    --       ext (λ x → (η ∘ g) (f x)) lx ≡
    --       ext (η ∘ (g ∘ f)) lx ≡
    --       map (g ∘ f) lx
             
  pres-comp {A₁ = A₁} {A₂ = A₂} {A₃ = A₃} f g = sym (funExt aux)
    where
      -- open MonadLaws.Ext-Assoc A₁ A₂ A₃ (η ∘ f) (η ∘ g)
      aux : (lx : ⟨ 𝔽 A₁ ⟩s) → _
      aux lx = (MonadLaws.ext-assoc (η𝔽 ∘ f) (η𝔽 ∘ g) lx)
             ∙ (λ i → ext (λ x → Equations.ext-η (η𝔽 ∘ g) (f x) i) lx)


  map-η : ∀ {Aᵢ : Type ℓAᵢ} {Aₒ : Type ℓAₒ} →
    (f : Aᵢ → Aₒ) (x : Aᵢ) → map f (η𝔽 x) ≡ η𝔽 (f x)
  map-η {Aᵢ = Aᵢ} {Aₒ = Aₒ} f x = Equations.ext-η (η𝔽 ∘ f) x
    -- where open CBPVExt Aᵢ (L℧ Aₒ) ℧ θ

  map-℧ : ∀ {Aᵢ : Type ℓAᵢ} {Aₒ : Type ℓAₒ} →
    (f : Aᵢ → Aₒ) → map f ℧𝔽 ≡ ℧𝔽
  map-℧ {Aᵢ = Aᵢ} {Aₒ = Aₒ} f = {!!} -- Equations.ext-℧ (η𝔽 ∘ f)
    -- where open CBPVExt Aᵢ (L℧ Aₒ) ℧ θ

  map-θ : ∀ {Aᵢ : Type ℓAᵢ} {Aₒ : Type ℓAₒ} →
    (f : Aᵢ → Aₒ) (lx~ : ▹ ⟨ 𝔽 Aᵢ ⟩s) →
      map f (θ𝔽 lx~) ≡ θ𝔽 (map▹ (map f) lx~)
  map-θ {Aᵢ = Aᵢ} {Aₒ = Aₒ} f lx~ = {!!} -- Equations.ext-θ (η𝔽 ∘ f) lx~
     -- where open CBPVExt Aᵢ (L℧ Aₒ) ℧ θ


