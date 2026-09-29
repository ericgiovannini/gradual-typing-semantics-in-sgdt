{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.MonadRelationalResultsOpaque (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Relation.Binary
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to PTrec ; map to PTmap)
open import Cubical.Data.Unit renaming (Unit to ⊤)


open import Common.Common
open import Semantics.Concrete.GuardedLiftError k


open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Error
open import Semantics.Concrete.Predomain.Ext k
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.SquareOpaque

open import Semantics.Concrete.Predomain.SimpleErrorDomain k
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.ErrorDomain.Free.F-Object k
open import Semantics.Concrete.Predomain.ErrorDomain.Free.F-Rel k


private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓΓ ℓΓ' ℓA ℓA' ℓB ℓB' ℓC ℓC' : Level
    ℓAᵢ ℓAₒ : Level
    ℓ≤Γ ℓ≤Γ' ℓ≤A ℓ≤A' ℓ≤B ℓ≤B' : Level
    ℓA₁ ℓA₂ ℓA₃ : Level
    ℓR ℓS ℓT : Level
    ℓ≈Γ ℓ≈Γ' ℓ≈A ℓ≈A' ℓ≈B ℓ≈B' : Level
    ℓc ℓd : Level
private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


-- The lock-step error ordering between 𝔽 A and 𝔽 A'

module _ {A : Type ℓ} {A' : Type ℓ'} {ℓRAA' : Level}
  (_RAA'_ : A → A' → Type ℓRAA') where

  open LiftOrd A A' _RAA'_ renaming (_⊑_ to _⊑LALA'_)

  opaque
    unfolding sed-intro
    _⊑ls_ : ⟨ 𝔽 A ⟩s → ⟨ 𝔽 A' ⟩s → Type (ℓ-max (ℓ-max ℓ ℓ') ℓRAA')
    lx ⊑ls ly = lx ⊑LALA' ly

    ⊑ls-intro : ∀ {lx : L℧ A} {ly : L℧ A'}
      → lx ⊑LALA' ly → 𝔽-intro lx ⊑ls 𝔽-intro ly
    ⊑ls-intro H = H

    ⊑ls-elim : {C : ∀ {lx ly} → lx ⊑ls ly → Type ℓC}
      → (∀ (lx : L℧ A) (ly : L℧ A') → (p : lx ⊑LALA' ly) → C {lx = 𝔽-intro lx} {ly = 𝔽-intro ly} (⊑ls-intro p))
      → ∀ lx ly → (p : lx ⊑ls ly) → (C p)
    ⊑ls-elim H lx ly = H lx ly



-- Weak bisimilarity on 𝔽 A


-----------------------------------------------------------------
-- Monotonicity and preservation of bisimilarity for monadic ext
-----------------------------------------------------------------

_×rel_ :
  {ℓX ℓX' ℓY ℓY' ℓR ℓS : Level}
  {X : Type ℓX} {X' : Type ℓX'} {Y : Type ℓY} {Y' : Type ℓY'} →
  (_R_ : X → X' → Type ℓR) → (_S_ : Y → Y' → Type ℓS) →
  (X × Y → X' × Y' → Type (ℓ-max ℓR ℓS))
(_R_ ×rel _S_) (x , y) (x' , y') = (x R x') × (y S y')


{-
module _
  {ℓRΓΓ' ℓRAA' : Level}
  -- {Γ : Predomain ℓΓ} {Γ' : Type ℓΓ'} (_RΓΓ'_ : Γ → Γ' → Type ℓRΓΓ')
  {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'} (c : PRel A A' ℓc)
  (B : ErrorDomain ℓB ℓ≤B ℓ≈B) (B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B')
  (d : ErrorDomRel B B' ℓd)
  where

  open F-ob
  open F-rel
  open LiftOrd

  private
    module A  = PredomainStr (A .snd)
    module A' = PredomainStr (A' .snd)
    module B  = ErrorDomainStr (B .snd)
    module B' = ErrorDomainStr (B' .snd)
    module d  = ErrorDomRel d

  module _ (f : ErrorDomMor (F-ob A) B) (g : ErrorDomMor (F-ob A') B') where

    private
      module f = ErrorDomMor f
      module g = ErrorDomMor g
    opaque
      unfolding F-rel PSq ηM
      ⊑F-lem' : ▹ (PSq c (U-rel d) ((U-mor f) ∘p ηM) ((U-mor g) ∘p ηM) → ErrorDomSq (F-rel c) d f g)
                 → PSq c (U-rel d) ((U-mor f) ∘p ηM) ((U-mor g) ∘p ηM) → ErrorDomSq (F-rel c) d f g
      ⊑F-lem' IH α .(η x) .(η y) (⊑ηη x y xRy) =
        α x y xRy
        
      ⊑F-lem' IH α .℧ y (⊑℧⊥ .y) =
        subst (λ z → d.R z (g.fun y)) (sym f.f℧) (d.R℧ _)
        
      ⊑F-lem' IH α .(θ lx~) .(θ ly~) (⊑θθ lx~ ly~ H) =
        subst2
          (λ z w → d.R z w)
          (sym (f.fθ lx~))
          (sym (g.fθ ly~))
          (d.Rθ (map▹ f.fun lx~) (map▹ g.fun ly~) (λ t → IH t α (lx~ t) (ly~ t) (H t)))

      ⊑F-lem : PSq c (U-rel d) ((U-mor f) ∘p ηM) ((U-mor g) ∘p ηM) → ErrorDomSq (F-rel c) d f g
      ⊑F-lem = fix ⊑F-lem'
-}



module _
  {A : Type ℓA} {A' : Type ℓA'}
  (c : A → A' → Type ℓc)
  (B  : SimpleErrorDomain ℓB)
  (B' : SimpleErrorDomain ℓB')
  (d  : SEDrel B B' ℓd)
  where

  open F-ob
  open F-rel
  open LiftOrd

  private
    module B  = SimpleErrorDomain→module B
    module B' = SimpleErrorDomain→module B'
    module d  = SEDrel d
    private
      Lc = _⊑ls_ c

  module _ (f : SEDmor (𝔽 A) B) (g : SEDmor (𝔽 A') B') where

    module f = SEDmor f
    module g = SEDmor g
    opaque
      unfolding η𝔽 SimpleErrorDomain→record _⊑ls_
      ⊑F-lem' : ▹ (TwoCell c d.R (f.f ∘ η𝔽) (g.f ∘ η𝔽) → TwoCell Lc d.R f.f g.f)
                → (TwoCell c d.R (f.f ∘ η𝔽) (g.f ∘ η𝔽) → TwoCell Lc d.R f.f g.f)
      ⊑F-lem' IH α .(η x) .(η y) (⊑ηη x y xRy) =
        α x y xRy
        
      ⊑F-lem' IH α .℧ y (⊑℧⊥ .y) =
        subst (λ z → d.R z (g.f y)) (sym f.f℧) (d.R℧ _)
        
      ⊑F-lem' IH α .(θ lx~) .(θ ly~) (⊑θθ lx~ ly~ H) =
        subst2
          (λ z w → d.R z w)
          (sym (f.fθ lx~))
          (sym (g.fθ ly~))
          (d.Rθ (map▹ f.f lx~) (map▹ g.f ly~) (λ t → IH t α (lx~ t) (ly~ t) (H t)))

      ⊑F-lem : (TwoCell c d.R (f.f ∘ η𝔽) (g.f ∘ η𝔽) → TwoCell Lc d.R f.f g.f)
      ⊑F-lem = fix ⊑F-lem'




module _
  {ℓcΓ : Level}
  {Γ : Type ℓΓ} {Γ' : Type ℓΓ'} (cΓ : Γ → Γ' → Type ℓcΓ)
  {A : Type ℓA} {A' : Type ℓA'} (c : A → A' → Type ℓc)
  (B : SimpleErrorDomain ℓB) (B' : SimpleErrorDomain ℓB')
  (d : SEDrel B B' ℓd)
  where

  private
    module d = SEDrel d
    Lc = _⊑ls_ c

  -- module _ (f g : Γ → A → ⟨ B ⟩)
  --   where

  --   private
  --     f-ext : Γ → ⟨ 𝔽 A ⟩s → ⟨ B ⟩
  --     f-ext γ lx = ⟨SimpleErrorDomain⟩→⟨ErrorDomain⟩ {B = B}
  --       (st-ext (λ γ1 x → ⟨ErrorDomain⟩→⟨SimpleErrorDomain⟩ {B = B} (f γ1 x)) γ lx)

  --     g-ext : Γ → ⟨ 𝔽 A ⟩s → ⟨ B ⟩
  --     g-ext γ lx = ⟨SimpleErrorDomain⟩→⟨ErrorDomain⟩ {B = B}
  --       (st-ext (λ γ1 x → ⟨ErrorDomain⟩→⟨SimpleErrorDomain⟩ {B = B} (g γ1 x)) γ lx)

  --     B₀ = ErrorDomain→SimpleErrorDomain B
      
  opaque
    unfolding η𝔽
    strong-ext-mon-sq : ∀ (f : Γ → A → ⟨ B ⟩s) (g : Γ' → A' → ⟨ B' ⟩s)     
      → TwoCell cΓ (TwoCell c d.R) f g
      → TwoCell cΓ (TwoCell Lc d.R) (st-ext f) (st-ext g)
    strong-ext-mon-sq f g α γ γ' γ≤γ' =
      ⊑F-lem c B B' d (St-ext f γ) (St-ext g γ')
             (transport (λ i → TwoCell c d.R (eq1 i) (eq2 i)) β)
      where
        β : TwoCell c d.R (f γ) (g γ')
        β = α γ γ' γ≤γ'

        eq1 : f γ ≡ st-ext {B = B} f γ ∘ η𝔽
        eq1 = sym (funExt (λ x → st-ext-η f γ x))

        eq2 : g γ' ≡ st-ext {B = B'} g γ' ∘ η𝔽
        eq2 = sym (funExt (λ x → st-ext-η g γ' x))


  
{-
module _
  {ℓRΓΓ' ℓRAA' : Level}
  {Γ : Type ℓΓ} {Γ' : Type ℓΓ'} (_RΓΓ'_ : Γ → Γ' → Type ℓRΓΓ')
  {A : Type ℓA} {A' : Type ℓA'} (_RAA'_ : A → A' → Type ℓRAA')
  (B  : SimpleErrorDomain ℓB)
  (B' : SimpleErrorDomain ℓB')
  where

  private
    module B  = SimpleErrorDomain→module B
    module B' = SimpleErrorDomain→module B'

  module _
    {ℓRBB' : Level}
    (_RBB'_ : ⟨ B ⟩s → ⟨ B' ⟩s → Type ℓRBB')
    (R℧B⊥ : ∀ x → B.℧ RBB' x)
    (Rθ  : ∀ (x~ : ▹ ⟨ B ⟩s) (y~ : ▹ ⟨ B' ⟩s) →
      ▸ (λ t → (x~ t) RBB' (y~ t)) → (B.θ x~) RBB' (B'.θ y~))
    where

    open LiftOrd A A' _RAA'_ renaming (_⊑_ to _⊑LALA'_) public

    private
      _⊑LS_ = _⊑ls_ _RAA'_

    -- monotone : If f ≤ g and x ≤ y, then ext f x ≤ ext g y

    -- An ordering between the function types Γ → A → B and Γ' → A' → B' extends
    -- to an ordering between the function types Γ → L℧ A → B and Γ' → L℧ A' → B'.
    opaque
      unfolding _⊑ls_ η𝔽 ℧𝔽 θ𝔽
      strong-ext-mon : ∀ (f : Γ → A → ⟨ B ⟩s) (g : Γ' → A' → ⟨ B' ⟩s) →
        TwoCell _RΓΓ'_ (TwoCell _RAA'_ _RBB'_) f g →
        TwoCell _RΓΓ'_ (TwoCell _⊑LS_ _RBB'_) (st-ext f) (st-ext g)
      strong-ext-mon f g α γ γ' γRγ' =
        fix aux
        where
          aux : ▹ (∀ la la' → la ⊑LALA' la' → (st-ext {B = B} f γ la) RBB' (st-ext {B = B'} g γ' la')) →
                   ∀ la la' → la ⊑LALA' la' → (st-ext {B = B} f γ la) RBB' (st-ext {B = B'} g γ' la')
          aux _ .(η a) .(η a') (⊑ηη a a' aRa') =
            -- Goal:  Ext1.ext f γ (L.η (ok a)) RBB' Ext2.ext g γ' (L.η (ok a'))
            transport
              (sym (λ i → (st-ext-η {B = B} f γ a i) RBB' (st-ext-η {B = B'} g γ' a' i)))
              (α γ γ' γRγ' a a' aRa') 
          aux _ .℧ la' (⊑℧⊥ .la') =
            -- Goal: (Ext1.ext f γ ℧) RBB' (Ext2.ext g γ' la')
            transport
              (sym (λ i → (st-ext-℧ {B = B} f γ i) RBB' (st-ext {B = B'} g γ' la')))
              (R℧B⊥ _)
          aux IH .(θ la~) .(θ la'~) (⊑θθ la~ la'~ H~) =
            -- Goal: Ext1.ext f γ (L.θ lx~) RBB' Ext2.ext g γ' (L.θ ly~)
            transport
              (sym (λ i → (st-ext-θ {B = B}f γ la~ i) RBB' (st-ext-θ {B = B'} g γ' la'~ i)))
              (Rθ _ _ (λ t → IH t (la~ t) (la'~ t) (H~ t)))



module _
  {ℓRAA' ℓRBB' : Level}
  {A : Type ℓA} {A' : Type ℓA'} (_RAA'_ : A → A' → Type ℓRAA')
  (B  : SimpleErrorDomain ℓB)
  (B' : SimpleErrorDomain ℓB')
  where

  private
    module B  = SimpleErrorDomain→module B
    module B' = SimpleErrorDomain→module B'

  module _
    (_RBB'_ : ⟨ B ⟩s → ⟨ B' ⟩s → Type ℓRBB')
    (R℧B⊥ : ∀ x → B.℧ RBB' x)
    (Rθ  : ∀ (x~ : ▹ ⟨ B ⟩s) (y~ : ▹ ⟨ B' ⟩s) →
      ▸ (λ t → (x~ t) RBB' (y~ t)) → (B.θ x~) RBB' (B'.θ y~))
    where

    private
      _⊑LS_ = _⊑ls_ _RAA'_

    opaque
      unfolding ext
      ext-mon : ∀ (f : A → ⟨ B ⟩s) (g : A' → ⟨ B' ⟩s) →
        (TwoCell _RAA'_ _RBB'_) f g →
        (TwoCell _⊑LS_ _RBB'_) (ext f) (ext g)
      ext-mon f g α = strong-ext-mon (λ _ _ → ⊤) _RAA'_ B B' _RBB'_ R℧B⊥ Rθ
        (λ _ → f) (λ _ → g)
        (λ _ _ _ → α) -- (*)
        tt tt tt

      -- Goal for line (*) :
      -- TwoCell (λ _ _ → ⊤) (TwoCell _RAA'_  _RBB'_) (λ _ → f) (λ _ → g)
-}

open BinaryRelation

-- Some general lemmas needed in the following proofs:

  -- lemma : g ((δ ^ n) x) ≡ (δB ^ n) (g x) and likewise for f
module presθ→presδ {X : Type ℓ} {Y : Type ℓ'}
  (θY : (▹ Y) → Y)
  (h : L℧ X → Y)
  (h-pres-θ : ∀ x~ → h (θ x~) ≡ θY (map▹ h x~)) where

  δY = θY ∘ next

  -- Recall that δ : L℧ X → L℧ X
  
  h-pres-δ : ∀ x → h (δ x) ≡ δY (h x)
  h-pres-δ x = h-pres-θ (next x)

  h-pres-δ^n : ∀ n x → h ((δ ^ n) x) ≡ (δY ^ n) (h x)
  h-pres-δ^n zero x = refl
  h-pres-δ^n (suc n) x =
    (h-pres-δ ((δ ^ n) x)) ∙ (cong δY (h-pres-δ^n n x))





-- The goal of the next module is to show that the monadic ext function
-- preserves bisimilarity.

module Preserve-Bisim-Lemma
  (A : Type ℓA) (_≈A_ : A → A → Type ℓ≈A)
  (B : ErrorDomain ℓB ℓ≤B ℓ≈B)
  where

  private
    module B = ErrorDomainStr (B .snd)
    _≈B_ = B._≈_
    isRefl≈B = B.is-refl-Bisim
    isSym≈B = B.is-sym
    isProp≈B = B.is-prop-valued-Bisim
    δB≈id = B.δ≈id
    ℧B = B.℧
    θB = B.θ.f
    ≈Bθ = B.θ.pres≈

  open presθ→presδ {X = A} {Y = ⟨ B ⟩} B.θ.f

  δB = B.θ.f ∘ next

  id≈δB : TwoCell _≈B_ _≈B_ id δB
  id≈δB x y x≈y =
    isSym≈B (δB y) x (δB≈id y x (isSym≈B x y x≈y))


 -- open LiftBisim A A' _RAA'_ renaming (_⊑_ to _⊑LALA'_)
  open LiftBisim (Error A) (≈ErrorX _≈A_) renaming (_≈_ to _≈L℧A_)

  module _ (f g : (L℧ A → ⟨ B ⟩))
    (f-pres-℧ : f ℧ ≡ ℧B)
    (f-pres-θ : ∀ x~ → f (θ x~) ≡ θB (map▹ f x~))
    (g-pres-℧ : g ℧ ≡ ℧B)
    (g-pres-θ : ∀ x~ → g (θ x~) ≡ θB (map▹ g x~)) where

    ≈lem' :
      ▹ (TwoCell _≈A_ _≈B_ (f ∘ η) (g ∘ η) → TwoCell _≈L℧A_ _≈B_ f g) →
         TwoCell _≈A_ _≈B_ (f ∘ η) (g ∘ η) → TwoCell _≈L℧A_ _≈B_ f g

    -- case η η : use the provided two-cell between (f ∘ η) and (g ∘ η)
    ≈lem' _ α .(η x) .(η y) (≈ηη (ok x) (ok y) x≈y) = α x y x≈y

    -- case ℧ η : impossible
    ≈lem' _ α .℧ .(η y) (≈ηη error (ok y) contra) = ⊥.rec* contra

    -- case η ℧ : impossible
    ≈lem' _ α .(η x) .℧ (≈ηη (ok x) error contra) = ⊥.rec* contra

    -- case ℧ ℧ : follows by preservation of ℧ and reflexivity of _≈B_
    ≈lem' _ α .℧ .℧ (≈ηη error error contra) =
      transport (sym (λ i → (f-pres-℧ i) ≈B (g-pres-℧ i)))
                (isRefl≈B ℧B)

    -- case η θ : know that ly is an iterated delay of a value y
    -- that is bisimilar to x. Then g ly ≡ g ((δ ^ n) (η y)) ≡ (δB ^ n) (g (η y))
    -- since g commutes with θ. Then since δB ≈ id and f (η x) ≈ g (η y),
    -- we have f (η x) ≈ (δB ^ n) (g (η y)).
    ≈lem' _ α .(η x) ly (≈ηθ (ok x) .ly H) = PTrec (isProp≈B _ _) aux H
      where
        aux : _ → f (η x) ≈B (g ly)
        aux (n , (ok y) , eq , p) =
          transport (λ i → (f (η x)) ≈B lem2 i) lem1
          where
            lem1 : (f (η x)) ≈B ((δB ^ (suc n)) (g (η y)))
            lem1 = TwoCell-iterated-idL _≈B_ δB id≈δB (suc n) (f (η x)) (g (η y)) (α x y p)

            lem2 : (δB ^ (suc n)) (g (η y)) ≡ g ly
            lem2 = sym ((cong g eq) ∙ (h-pres-δ^n g g-pres-θ (suc n) (η y)))

    -- case ℧ θ
    ≈lem' _ α .℧ ly (≈ηθ error .ly H) = PTrec (isProp≈B _ _) aux H
       where
        aux : _ → f ℧ ≈B (g ly)
        aux (n , error , eq , p) =
          transport (λ i → (f ℧) ≈B lem2 i) lem1
          where
            lem1 : (f ℧) ≈B ((δB ^ (suc n)) (g ℧))
            lem1 = TwoCell-iterated-idL _≈B_ δB id≈δB (suc n) (f ℧) (g ℧)
                (transport (sym (λ i → (f-pres-℧ i) ≈B (g-pres-℧ i)))
                           (isRefl≈B ℧B))

            lem2 : (δB ^ (suc n)) (g ℧) ≡ g ly
            lem2 = sym ((cong g eq) ∙ (h-pres-δ^n g g-pres-θ (suc n) ℧))

    -- case θ η
    ≈lem' _ α lx .(η y) (≈θη .lx (ok y) H) = PTrec (isProp≈B _ _) aux H
      where
        aux : _ → (f lx) ≈B (g (η y))
        aux (n , (ok x) , eq , p) =
          transport (λ i → lem2 i ≈B (g (η y))) lem1
          where
            lem1 : ((δB ^ (suc n)) (f (η x))) ≈B (g (η y))
            lem1 = TwoCell-iterated-idR _≈B_ δB δB≈id (suc n) (f (η x)) (g (η y)) (α x y p)

            lem2 : (δB ^ (suc n)) (f (η x)) ≡ f lx
            lem2 = sym ((cong f eq) ∙ (h-pres-δ^n f f-pres-θ (suc n) (η x)))

    -- case θ ℧
    ≈lem' _ α lx .℧ (≈θη .lx error H) = PTrec (isProp≈B _ _) aux H
      where
        aux : _ → (f lx) ≈B g ℧
        aux (n , error , eq , p) =
          transport (λ i → lem2 i ≈B (g ℧)) lem1
           where
            lem1 : ((δB ^ (suc n)) (f ℧)) ≈B (g ℧)
            lem1 = TwoCell-iterated-idR _≈B_ δB δB≈id (suc n) (f ℧) (g ℧)
              (transport (sym (λ i → (f-pres-℧ i) ≈B (g-pres-℧ i)))
                          (isRefl≈B ℧B))

            lem2 : (δB ^ (suc n)) (f ℧) ≡ f lx
            lem2 = sym ((cong f eq) ∙ (h-pres-δ^n f f-pres-θ (suc n) ℧))
          

    -- case θ θ : use the fact that f and g preserve θ, then use the
    -- fact that ≈B is a θ-congruence, and then use Lob-induction
    -- hypothesis.
    ≈lem' IH α .(θ lx~) .(θ ly~) (≈θθ lx~ ly~ H~) =
      transport (sym (λ i → (f-pres-θ lx~ i) ≈B (g-pres-θ ly~ i))) aux
      where
        aux : θB (map▹ f lx~) ≈B θB (map▹ g ly~)
        aux = ≈Bθ (λ t → IH t α (lx~ t) (ly~ t) (H~ t))         

    ≈lem : TwoCell _≈A_ _≈B_ (f ∘ η) (g ∘ η) → TwoCell _≈L℧A_ _≈B_ f g
    ≈lem = fix ≈lem'





module _
  {ℓ≈Γ : Level}
  (Γ : Type ℓΓ) (_≈Γ_ : Γ → Γ → Type ℓ≈Γ)
  (A : Type ℓA) (_≈A_ : A → A → Type ℓ≈A)
  (B : ErrorDomain ℓB ℓ≤B ℓ≈B)

  where

  private
    module B = ErrorDomainStr (B .snd)
    _≈B_ = B._≈_

  -- module Ext = StrongCBPVExt Γ  A  B  ℧B  θB
  open LiftBisim (Error A) (≈ErrorX _≈A_) renaming (_≈_ to _≈L℧A_)
  open Preserve-Bisim-Lemma A _≈A_ B

  opaque
    unfolding ⟨_⟩s mkSimpleErrorDomain
    _≈FA_ : ⟨ 𝔽 A ⟩s → ⟨ 𝔽 A ⟩s → Type (ℓ-max ℓA ℓ≈A)
    _≈FA_ = _≈L℧A_

  module _ (f g : Γ → A → ⟨ B ⟩)
    where

    private
      f-ext : Γ → ⟨ 𝔽 A ⟩s → ⟨ B ⟩
      f-ext γ lx = ⟨SimpleErrorDomain⟩→⟨ErrorDomain⟩ {B = B}
        (st-ext (λ γ1 x → ⟨ErrorDomain⟩→⟨SimpleErrorDomain⟩ {B = B} (f γ1 x)) γ lx)

      g-ext : Γ → ⟨ 𝔽 A ⟩s → ⟨ B ⟩
      g-ext γ lx = ⟨SimpleErrorDomain⟩→⟨ErrorDomain⟩ {B = B}
        (st-ext (λ γ1 x → ⟨ErrorDomain⟩→⟨SimpleErrorDomain⟩ {B = B} (g γ1 x)) γ lx)

      B₀ = ErrorDomain→SimpleErrorDomain B

    opaque
      unfolding _≈FA_ ⟨_⟩s ⟨SimpleErrorDomain⟩→⟨ErrorDomain⟩ ⟨ErrorDomain⟩→⟨SimpleErrorDomain⟩ SimpleErrorDomain→record ℧𝔽 θ𝔽
      strong-ext-pres≈ :
        TwoCell _≈Γ_ (TwoCell _≈A_ _≈B_) f g →
        TwoCell _≈Γ_ (TwoCell _≈FA_ _≈B_) f-ext g-ext -- (st-ext f) (st-ext g)
      strong-ext-pres≈ α γ γ' γ≤γ' =
        aux λ a a' a≈a' →
          transport
            (sym λ i → (st-ext-η {B = B₀} f γ a i) ≈B (st-ext-η {B = B₀} g γ' a' i))
            (α γ γ' γ≤γ' a a' a≈a')
        where
          aux : TwoCell _≈A_ _≈B_ ((f-ext γ) ∘ η) ((g-ext γ') ∘ η)  →
                TwoCell _≈L℧A_ _≈B_ (st-ext {B = B₀} f γ) (st-ext {B = B₀} g γ')
          aux = ≈lem
            (λ z → st-ext {B = B₀} f γ z) (λ z → st-ext {B = B₀} g γ' z)
            (st-ext-℧ {B = B₀} f γ)  (st-ext-θ {B = B₀} f γ)
            (st-ext-℧ {B = B₀} g γ') (st-ext-θ {B = B₀} g γ')
        



{-
-- Monotonicity and preservation of bisimilarity for the map
-- function (Aᵢ → Aₒ) → (L℧ Aᵢ → L℧ Aₒ).

module MapMonotone
  {ℓAᵢ ℓAᵢ' ℓAₒ ℓAₒ' ℓRᵢ ℓRₒ : Level}
  (Aᵢ : Type ℓAᵢ) (Aᵢ' : Type ℓAᵢ')
  (Aₒ : Type ℓAₒ) (Aₒ' : Type ℓAₒ')
  (_Rᵢ_ : Aᵢ → Aᵢ' → Type ℓRᵢ)
  (_Rₒ_ : Aₒ → Aₒ' → Type ℓRₒ)
  where

  private
    _⊑LSᵢ_ = _⊑ls_ _Rᵢ_
    _⊑LSₒ_ = _⊑ls_ _Rₒ_ 

  --open Map
  --open ExtMonotone

  open module LRᵢ = LiftOrd Aᵢ Aᵢ' _Rᵢ_ renaming (_⊑_ to _LRᵢ_)
  open module LRₒ = LiftOrd Aₒ Aₒ' _Rₒ_ renaming (_⊑_ to _LRₒ_)

  -- module ExtMon =
  --   ExtMonotone
  --     Aᵢ Aᵢ' _Rᵢ_ (L℧ Aₒ) ℧ θ (L℧ Aₒ') ℧ θ
  --     _LRₒ_ LRₒ.Properties.℧-bot (λ lx~ ly~ → LRₒ.Properties.θ-monotone)
  
  -- map f = ext (η ∘ f)
  -- map g = ext (η ∘ g)
  -- ext (η ∘ f) ≤ ext (η ∘ g)

  map-monotone : ∀ f g →
    TwoCell _Rᵢ_ _Rₒ_ f g →
    TwoCell _⊑LSᵢ_ _⊑LSₒ_ (map f) (map g)
  map-monotone f g α = ext-mon _Rᵢ_ {!!} {!!} {!!} {!!} {!!} (η𝔽 ∘ f) (η𝔽 ∘ g) {!!} -- ext-mon (η ∘ f) (η ∘ g) β
    where
      β : TwoCell _Rᵢ_ _LRₒ_ (η ∘ f) (η ∘ g)
      β x y xRᵢy = LRₒ.Properties.η-monotone (α x y xRᵢy)




module MapPresBisim
  {ℓAᵢ ℓAₒ ℓ≈Aᵢ ℓ≈Aₒ : Level}
  (Aᵢ : Type ℓAᵢ) 
  (Aₒ : Type ℓAₒ)
  (_≈Aᵢ_ : Aᵢ → Aᵢ → Type ℓ≈Aᵢ)
  (_≈Aₒ_ : Aₒ → Aₒ → Type ℓ≈Aₒ)
  (isProp≈Aₒ : ∀ x y → isProp (x ≈Aₒ y))
  (isRefl≈Aₒ : isRefl _≈Aₒ_)
  (isSym≈Aₒ : isSym _≈Aₒ_) where

  open module BisimLAᵢ = LiftBisim (Error Aᵢ) (≈ErrorX _≈Aᵢ_) renaming (_≈_ to _≈L℧Aᵢ_)
  open module BisimLAₒ = LiftBisim (Error Aₒ) (≈ErrorX _≈Aₒ_) renaming (_≈_ to _≈L℧Aₒ_)

  bisimErrorAₒ : IsBisim (≈ErrorX _≈Aₒ_)
  bisimErrorAₒ = IsBisimErrorX _≈Aₒ_ (isbisim isRefl≈Aₒ isSym≈Aₒ isProp≈Aₒ)
  module BisimErrorAₒ = IsBisim (bisimErrorAₒ)

  symmetric : _
  symmetric = BisimLAₒ.Properties.symmetric BisimErrorAₒ.is-sym

  δ≈id : TwoCell _≈L℧Aₒ_ _≈L℧Aₒ_ (θ ∘ next) id
  δ≈id lx ly lx≈ly =
    symmetric _ _
      (BisimLAₒ.Properties.δ-closed-r BisimErrorAₒ.is-prop-valued _ _ (symmetric _ _ lx≈ly))

  open Map
  open StrongExtPresBisim Unit (λ _ _ → Unit) Aᵢ _≈Aᵢ_ (L℧ Aₒ) ℧ θ _≈L℧Aₒ_
    (BisimLAₒ.Properties.is-prop BisimErrorAₒ.is-prop-valued)
    (BisimLAₒ.Properties.reflexive BisimErrorAₒ.is-refl)
    symmetric
    (λ x~ y~ → BisimLAₒ.Properties.θ-pres≈)
    δ≈id

  map-pres-≈ : ∀ f g →
    TwoCell _≈Aᵢ_ _≈Aₒ_ f g →
    TwoCell _≈L℧Aᵢ_ _≈L℧Aₒ_  (map f) (map g)
  map-pres-≈ f g f≈g =
    strong-ext-pres≈
      (λ _ → η ∘ f)(λ _ → η ∘ g)
      (λ _ _ _ a₁ a₂ a₁≈a₂ → BisimLAₒ.Properties.η-pres≈ (f≈g a₁ a₂ a₁≈a₂))
      tt tt tt



-}
