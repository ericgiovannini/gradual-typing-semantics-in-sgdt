{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.DoublePoset.MonadRelationalResults (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
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
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Error k
open import Semantics.Concrete.DoublePoset.Monad k



private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓΓ ℓΓ' ℓA ℓA' ℓB ℓB' ℓC ℓC' : Level
    ℓAᵢ ℓAₒ : Level
    ℓ≤Γ ℓ≤A ℓ≤B : Level
    ℓA₁ ℓA₂ ℓA₃ : Level
    ℓR ℓS ℓT : Level
    ℓ≈Γ ℓ≈A ℓ≈B : Level
private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


-----------------------------------------------------------------
-- Monotonicity and preservation of bisimilarity for monadic ext
-----------------------------------------------------------------

_×rel_ :
  {ℓX ℓX' ℓY ℓY' ℓR ℓS : Level}
  {X : Type ℓX} {X' : Type ℓX'} {Y : Type ℓY} {Y' : Type ℓY'} →
  (_R_ : X → X' → Type ℓR) → (_S_ : Y → Y' → Type ℓS) →
  (X × Y → X' × Y' → Type (ℓ-max ℓR ℓS))
(_R_ ×rel _S_) (x , y) (x' , y') = (x R x') × (y S y')

module StrongExtMonotone
  {ℓRΓΓ' ℓRAA' ℓRBB' : Level}
  (Γ : Type ℓΓ) (Γ' : Type ℓΓ)  (_RΓΓ'_ : Γ → Γ' → Type ℓRΓΓ')
  (A : Type ℓA) (A' : Type ℓA') (_RAA'_ : A → A' → Type ℓRAA')
  (B  : Type ℓB)  (℧B  : B)  (θB  : (▹ B) → B)
  (B' : Type ℓB') (℧B' : B') (θB' : (▹ B') → B')
  (_RBB'_ : B → B' → Type ℓRBB')
  (R℧B⊥ : ∀ x → ℧B RBB' x)
  (Rθ  : ∀ (x~ : ▹ B) (y~ : ▹ B') →
    ▸ (λ t → (x~ t) RBB' (y~ t)) → (θB x~) RBB' (θB' y~))
  where

  module Ext1 = StrongCBPVExt Γ  A  B  ℧B  θB
  module Ext2 = StrongCBPVExt Γ' A' B' ℧B' θB'

  open LiftOrd A A' _RAA'_ renaming (_⊑_ to _⊑LALA'_) public

  -- monotone : If f ≤ g and x ≤ y, then ext f x ≤ ext g y

  -- An ordering between the function types Γ → A → B and Γ' → A' → B' extends
  -- to an ordering between the function types Γ → L℧ A → B and Γ' → L℧ A' → B'.
  strong-ext-mon : ∀ f g →
    TwoCell _RΓΓ'_ (TwoCell _RAA'_ _RBB'_) f g →
    TwoCell _RΓΓ'_ (TwoCell _⊑LALA'_ _RBB'_) (Ext1.ext f) (Ext2.ext g)
  strong-ext-mon f g α γ γ' γRγ' = fix aux
    where
      aux : ▹ (∀ la la' → la ⊑LALA' la' → (Ext1.ext f γ la) RBB' (Ext2.ext g γ' la')) →
               ∀ la la' → la ⊑LALA' la' → (Ext1.ext f γ la) RBB' (Ext2.ext g γ' la')
      aux _ .(η a) .(η a') (⊑ηη a a' aRa') =
        -- Goal:  Ext1.ext f γ (L.η (ok a)) RBB' Ext2.ext g γ' (L.η (ok a'))
        transport
          (sym (λ i → (Ext1.Equations.ext-η f γ a i) RBB' (Ext2.Equations.ext-η g γ' a' i)))
          (α γ γ' γRγ' a a' aRa') 
      aux _ .℧ la' (⊑℧⊥ .la') =
        -- Goal: (Ext1.ext f γ ℧) RBB' (Ext2.ext g γ' la')
        transport
          (sym (λ i → (Ext1.Equations.ext-℧ f γ i) RBB' (Ext2.ext g γ' la')))
          (R℧B⊥ _)
      aux IH .(θ la~) .(θ la'~) (⊑θθ la~ la'~ H~) =
        -- Goal: Ext1.ext f γ (L.θ lx~) RBB' Ext2.ext g γ' (L.θ ly~)
        transport
          (sym (λ i → (Ext1.Equations.ext-θ f γ la~ i) RBB' (Ext2.Equations.ext-θ g γ' la'~ i)))
          (Rθ _ _ (λ t → IH t (la~ t) (la'~ t) (H~ t)))


module ExtMonotone
  {ℓRAA' ℓRBB' : Level}
  (A : Type ℓA) (A' : Type ℓA') (_RAA'_ : A → A' → Type ℓRAA')
  (B  : Type ℓB)  (℧B  : B)  (θB  : (▹ B) → B)
  (B' : Type ℓB') (℧B' : B') (θB' : (▹ B') → B')
  (_RBB'_ : B → B' → Type ℓRBB')
  (R℧B⊥ : ∀ x → ℧B RBB' x)
  (Rθ  : ∀ (x~ : ▹ B) (y~ : ▹ B') →
    ▸ (λ t → (x~ t) RBB' (y~ t)) → (θB x~) RBB' (θB' y~)) where

  open StrongExtMonotone
    ⊤ ⊤ (λ x y → ⊤) A A' _RAA'_ B ℧B θB B' ℧B' θB' _RBB'_ R℧B⊥ Rθ
  module ExtAB   = CBPVExt A  B  ℧B  θB
  module ExtA'B' = CBPVExt A' B' ℧B' θB'

  ext-mon : ∀ (f : A → B) (g : A' → B') →
    (TwoCell _RAA'_ _RBB'_) f g →
    (TwoCell _⊑LALA'_ _RBB'_) (ExtAB.ext f) (ExtA'B'.ext g)
  ext-mon f g α = strong-ext-mon
    (λ _ → f) (λ _ → g)
    (λ _ _ _ → α) -- (*)
    tt tt tt

    -- Goal for line (*) :
    -- TwoCell (λ _ _ → ⊤) (TwoCell _RAA'_  _RBB'_) (λ _ → f) (λ _ → g)
   


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


TwoCell-iterated : {X : Type ℓ'} {Y : Type ℓ''} →
  (R : X → Y → Type ℓR) →
  (f : X → X) (g : Y → Y) →
  (TwoCell R R f g) →
  (n : ℕ) → TwoCell R R (f ^ n) (g ^ n)
TwoCell-iterated R f g α zero = λ _ _ → id
TwoCell-iterated R f g α (suc n) = λ x y Rxy →
  α ((f ^ n) x)
    ((g ^ n) y)
    (TwoCell-iterated R f g α n x y Rxy)

id^n≡id : {X : Type ℓ'} →
  ∀ n → (id {A = X}) ^ n ≡ id
id^n≡id zero = refl
id^n≡id (suc n) = id^n≡id n

TwoCell-iterated-idL : {X : Type ℓ'} →
  (R : X → X → Type ℓR) →
  (g : X → X) →
  (TwoCell R R id g) →
  (n : ℕ) → TwoCell R R id (g ^ n)
TwoCell-iterated-idL R g α n =
  transport (λ i → TwoCell R R (id^n≡id n i) (g ^ n)) (TwoCell-iterated R id g α n)

TwoCell-iterated-idR : {X : Type ℓ'} →
  (R : X → X → Type ℓ'') →
  (f : X → X) →
  (TwoCell R R f id) →
  (n : ℕ) → TwoCell R R (f ^ n) id
TwoCell-iterated-idR R f α n =
  transport (λ i → TwoCell R R (f ^ n) (id^n≡id n i)) (TwoCell-iterated R f id α n)


-- The goal of the next module is to show that the monadic ext function
-- preserves bisimilarity.

module Preserve-Bisim-Lemma
  (A : Type ℓA) (_≈A_ : A → A → Type ℓ≈A)
  (B : Type ℓB) (℧B : B) (θB : (▹ B) → B)
  (_≈B_ : B → B → Type ℓ≈B)
  (isProp≈B : ∀ x y → isProp (x ≈B y))
  (isRefl≈B : isRefl _≈B_)
  (isSym≈B : isSym _≈B_)
  (≈Bθ  : ∀ (x~ y~ : ▹ B) →
    ▸ (λ t → (x~ t) ≈B (y~ t)) → (θB x~) ≈B (θB y~))
  (δB≈id : TwoCell _≈B_ _≈B_  (θB ∘ next) id) 
  where

  open presθ→presδ {X = A} {Y = B} θB

  δB = θB ∘ next

  id≈δB : TwoCell _≈B_ _≈B_ id δB
  id≈δB x y x≈y =
    isSym≈B (δB y) x (δB≈id y x (isSym≈B x y x≈y))


 -- open LiftBisim A A' _RAA'_ renaming (_⊑_ to _⊑LALA'_)
  open LiftBisim (Error A) (≈ErrorX _≈A_) renaming (_≈_ to _≈L℧A_)

  module _ (f g : (L℧ A → B))
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
    ≈lem' _ α lx .(η y) (≈θη .lx (ok y) H) = {!sym!}

    -- case θ ℧
    ≈lem' _ α lx .℧ (≈θη .lx error H) = {!!}

    -- case θ θ : use the fact that f and g preserve θ, then use the
    -- fact that ≈B is a θ-congruence, and then use Lob-induction
    -- hypothesis.
    ≈lem' IH α .(θ lx~) .(θ ly~) (≈θθ lx~ ly~ H~) =
      transport (sym (λ i → (f-pres-θ lx~ i) ≈B (g-pres-θ ly~ i))) aux
      where
        aux : θB (map▹ f lx~) ≈B θB (map▹ g ly~)
        aux = ≈Bθ (map▹ f lx~) (map▹ g ly~)
          (λ t → IH t α (lx~ t) (ly~ t) (H~ t))

    ≈lem : TwoCell _≈A_ _≈B_ (f ∘ η) (g ∘ η) → TwoCell _≈L℧A_ _≈B_ f g
    ≈lem = fix ≈lem'


module StrongExtPresBisim
  {ℓ≈Γ : Level}
  (Γ : Type ℓΓ) (_≈Γ_ : Γ → Γ → Type ℓ≈Γ)
  (A : Type ℓA) (_≈A_ : A → A → Type ℓ≈A)
  (B : Type ℓB) (℧B : B) (θB : (▹ B) → B)
  (_≈B_ : B → B → Type ℓ≈B)
  (isProp≈B : ∀ x y → isProp (x ≈B y))
  (isRefl≈B : isRefl _≈B_)
  (isSym≈B : isSym _≈B_)
  (≈Bθ  : ∀ (x~ y~ : ▹ B) →
    ▸ (λ t → (x~ t) ≈B (y~ t)) → (θB x~) ≈B (θB y~))
  (δB≈id : TwoCell _≈B_ _≈B_  (θB ∘ next) id)

  where

  module Ext = StrongCBPVExt Γ  A  B  ℧B  θB
  open LiftBisim (Error A) (≈ErrorX _≈A_) renaming (_≈_ to _≈L℧A_)
  open Preserve-Bisim-Lemma
    A _≈A_ B ℧B θB _≈B_ isProp≈B isRefl≈B isSym≈B ≈Bθ δB≈id

  module _
    -- (f g : (Γ → L℧ A → B))
    -- (f-pres-℧ : ∀ γ → f γ ℧ ≡ ℧B)
    -- (f-pres-θ : ∀ γ x~ → f γ (θ x~) ≡ θB (map▹ (f γ) x~))
    -- (g-pres-℧ : ∀ γ → g γ ℧ ≡ ℧B)
    -- (g-pres-θ : ∀ γ x~ → g γ (θ x~) ≡ θB (map▹ (g γ) x~))
    where
  
    strong-ext-pres≈ : ∀ f g →
       TwoCell _≈Γ_ (TwoCell _≈A_ _≈B_) f g →
       TwoCell _≈Γ_ (TwoCell _≈L℧A_ _≈B_) (Ext.ext f) (Ext.ext g)
    strong-ext-pres≈ f g α γ γ' γ≤γ' =
      aux λ a a' a≈a' →
        transport
          (sym λ i → (Ext.Equations.ext-η f γ a i) ≈B (Ext.Equations.ext-η g γ' a' i))
          (α γ γ' γ≤γ' a a' a≈a')
      where
        aux : TwoCell _≈A_ _≈B_ ((Ext.ext f γ) ∘ η) ((Ext.ext g γ') ∘ η)  →
              TwoCell _≈L℧A_ _≈B_ (Ext.ext f γ) (Ext.ext g γ')
        aux = ≈lem
          (λ z → Ext.ext f γ z) (λ z → Ext.ext g γ' z)
          (Ext.Equations.ext-℧ f γ) (Ext.Equations.ext-θ f γ)
          (Ext.Equations.ext-℧ g γ') (Ext.Equations.ext-θ g γ')
        

-- Monotonicity and preservation of bisimilarity for the map
-- function (Aᵢ → Aₒ) → (L℧ Aᵢ → L℧ Aₒ).

module MapMonotone
  {ℓAᵢ ℓAᵢ' ℓAₒ ℓAₒ' ℓRᵢ ℓRₒ : Level}
  (Aᵢ : Type ℓAᵢ) (Aᵢ' : Type ℓAᵢ')
  (Aₒ : Type ℓAₒ) (Aₒ' : Type ℓAₒ')
  (_Rᵢ_ : Aᵢ → Aᵢ' → Type ℓRᵢ)
  (_Rₒ_ : Aₒ → Aₒ' → Type ℓRₒ)
  where

  open Map
  open ExtMonotone

  open module LRᵢ = LiftOrd Aᵢ Aᵢ' _Rᵢ_ renaming (_⊑_ to _LRᵢ_)
  open module LRₒ = LiftOrd Aₒ Aₒ' _Rₒ_ renaming (_⊑_ to _LRₒ_)

  module ExtMon =
    ExtMonotone
      Aᵢ Aᵢ' _Rᵢ_ (L℧ Aₒ) ℧ θ (L℧ Aₒ') ℧ θ
      _LRₒ_ LRₒ.Properties.℧-bot (λ lx~ ly~ → LRₒ.Properties.θ-monotone)
  
  -- map f = ext (η ∘ f)
  -- map g = ext (η ∘ g)
  -- ext (η ∘ f) ≤ ext (η ∘ g)

  map-monotone : ∀ f g →
    TwoCell _Rᵢ_ _Rₒ_ f g →
    TwoCell _LRᵢ_ _LRₒ_ (map f) (map g)
  map-monotone f g α = ExtMon.ext-mon (η ∘ f) (η ∘ g) β
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

