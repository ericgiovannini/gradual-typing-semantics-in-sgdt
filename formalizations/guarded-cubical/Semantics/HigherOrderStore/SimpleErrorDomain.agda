{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.HigherOrderStore.SimpleErrorDomain (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category

open import Common.Common
open import Semantics.Concrete.GuardedLiftError k renaming (℧ to ℧L ; θ to θL ; δ to δL)

private
  variable
    ℓ ℓ' : Level
    ℓC ℓR : Level
    ℓB₁ ℓB₂ ℓB₃ ℓB₄ : Level
    ℓBᵢ ℓBₒ : Level

private
  ▹_ : Type ℓ -> Type ℓ
  ▹ A = ▹_,_ k A

record SimpleErrorDomainStr (B : Type ℓ) : Type ℓ where
  constructor simpleerrordomainstr
  
  field
    is-set : isSet B
    ℧ : B
    θ : ▹ B → B

  δ : B → B
  δ = θ ∘ next

open SimpleErrorDomainStr

opaque
  SimpleErrorDomain : ∀ ℓ → Type (ℓ-suc ℓ)
  SimpleErrorDomain ℓ = TypeWithStr ℓ SimpleErrorDomainStr


opaque
  unfolding SimpleErrorDomain

  -- The underlying type
  ⟨_⟩s : SimpleErrorDomain ℓ → Type ℓ
  ⟨ B ⟩s = B .fst

  mkSimpleErrorDomain : (B : Type ℓ) → SimpleErrorDomainStr B → SimpleErrorDomain ℓ
  mkSimpleErrorDomain B x = B , x

opaque
  unfolding ⟨_⟩s mkSimpleErrorDomain
  sed-intro : {B : Type ℓ} {x : SimpleErrorDomainStr B} → B → ⟨ mkSimpleErrorDomain B x ⟩s
  sed-intro b = b

  sed-elim : {B : Type ℓ} {x : SimpleErrorDomainStr B} → ⟨ mkSimpleErrorDomain B x ⟩s → B
  sed-elim b = b
  

module _ (B : SimpleErrorDomain ℓ) where

  opaque
    unfolding SimpleErrorDomain ⟨_⟩s

    -- Access the underlying record
    SimpleErrorDomain→record : SimpleErrorDomainStr ⟨ B ⟩s
    SimpleErrorDomain→record = B .snd

    -- Access the underlying record as a module
    module SimpleErrorDomain→module = SimpleErrorDomainStr SimpleErrorDomain→record

    

opaque
  unfolding SimpleErrorDomain ⟨_⟩s mkSimpleErrorDomain SimpleErrorDomain→record sed-intro
  foo : {B : Type ℓ} {x : SimpleErrorDomainStr B}
    →   SimpleErrorDomain→record (mkSimpleErrorDomain B x) .SimpleErrorDomainStr.℧
      ≡ sed-intro (x .SimpleErrorDomainStr.℧)
  foo = refl



-------------------------------------
-- Morphisms of simple error domains
-------------------------------------

record SEDMor (B₁ : SimpleErrorDomain ℓ) (B₂ : SimpleErrorDomain ℓ') : Type (ℓ-max ℓ ℓ') where

  private
    module B₁ = SimpleErrorDomain→module B₁
    module B₂ = SimpleErrorDomain→module B₂
    
  field
    f : ⟨ B₁ ⟩s → ⟨ B₂ ⟩s
    f℧ : f B₁.℧ ≡ B₂.℧
    fθ : ∀ (x~ : ▹ ⟨ B₁ ⟩s) → f (B₁.θ x~) ≡ B₂.θ (map▹ f x~)


open SEDMor

-- Identity and composition

idSEDmor : {B : SimpleErrorDomain ℓ} → SEDMor B B
idSEDmor .f x = x
idSEDmor .f℧ = refl
idSEDmor .fθ _ = refl

_∘sed_ : {B₁ : SimpleErrorDomain ℓB₁} {B₂ : SimpleErrorDomain ℓB₂} {B₃ : SimpleErrorDomain ℓB₃}
  → SEDMor B₂ B₃
  → SEDMor B₁ B₂
  → SEDMor B₁ B₃
(ϕ' ∘sed ϕ) .f = ϕ' .f ∘ ϕ .f
(ϕ' ∘sed ϕ) .f℧ = (cong (ϕ' .f) (ϕ .f℧)) ∙ (ϕ' .f℧)
(ϕ' ∘sed ϕ) .fθ x~ = cong (ϕ' .f) (ϕ .fθ x~) ∙ (ϕ' .fθ (map▹ (ϕ .f) x~))


-- Equivalence between SEDMor record and a sigma type   
unquoteDecl SEDMorIsoΣ = declareRecordIsoΣ SEDMorIsoΣ (quote (SEDMor))

-- Simple error domain morphisms form a set
SEDMorIsSet :
  {Bᵢ : SimpleErrorDomain ℓBᵢ}
  {Bₒ : SimpleErrorDomain ℓBₒ} →
  isSet (SEDMor Bᵢ Bₒ)
SEDMorIsSet {Bₒ = Bₒ} = isSetRetract
  (Iso.fun SEDMorIsoΣ) (Iso.inv SEDMorIsoΣ)
  (Iso.leftInv SEDMorIsoΣ)
  (isSetΣSndProp
    (isSet→ Bₒ.is-set)
    (λ h → isProp× (Bₒ.is-set _ _) (isPropΠ (λ x~ → Bₒ.is-set _ _))))
    where
      module Bₒ = SimpleErrorDomain→module Bₒ



-- Equality of simple error domain morphisms
module _
  {Bᵢ : SimpleErrorDomain ℓBᵢ}
  {Bₒ : SimpleErrorDomain ℓBₒ}
  (ϕ ϕ'  : SEDMor Bᵢ Bₒ) where

  private
    module ϕ  = SEDMor ϕ
    module ϕ' = SEDMor ϕ'

  eqSEDMor :
    ϕ.f ≡ ϕ'.f → ϕ ≡ ϕ'
  eqSEDMor eq = isoFunInjective SEDMorIsoΣ ϕ ϕ'
    (Σ≡Prop (λ f → isProp×
                       (Bₒ.is-set _ _)
                       (isPropΠ (λ x~ → Bₒ.is-set _ _)))
            eq)
    where
      module Bₒ = SimpleErrorDomain→module Bₒ

  SEDMorExt :
    (∀ x → SEDMor.f ϕ x ≡ SEDMor.f ϕ' x) → ϕ ≡ ϕ'
  SEDMorExt eq = eqSEDMor (funExt eq)



-- Identity and associativity laws for composition

CompSED-IdL : {Bᵢ : SimpleErrorDomain ℓBᵢ} {Bₒ : SimpleErrorDomain ℓBₒ} →
  (ϕ : SEDMor Bᵢ Bₒ) → idSEDmor ∘sed ϕ ≡ ϕ
CompSED-IdL g = eqSEDMor _ _ refl

CompSED-IdR : {Bᵢ : SimpleErrorDomain ℓBᵢ} {Bₒ : SimpleErrorDomain ℓBₒ} →
  (ϕ : SEDMor Bᵢ Bₒ) → ϕ ∘sed idSEDmor ≡ ϕ
CompSED-IdR g = eqSEDMor _ _ refl

CompSED-Assoc :
  {B₁ : SimpleErrorDomain ℓB₁}
  {B₂ : SimpleErrorDomain ℓB₂}
  {B₃ : SimpleErrorDomain ℓB₃}
  {B₄ : SimpleErrorDomain ℓB₄} →
  (ϕ : SEDMor B₁ B₂) (ϕ' : SEDMor B₂ B₃) (ϕ'' : SEDMor B₃ B₄) →
  ϕ'' ∘sed (ϕ' ∘sed ϕ) ≡ (ϕ'' ∘sed ϕ') ∘sed ϕ
CompSED-Assoc f g h = eqSEDMor _ _ refl




------------------------------------------
-- Relations between simple error domains
------------------------------------------

record SEDRel (B : SimpleErrorDomain ℓ) (B' : SimpleErrorDomain ℓ') (ℓR : Level) :
  Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓR)) where

  private
    module B  = SimpleErrorDomain→module B
    module B' = SimpleErrorDomain→module B'

  field
    R    : ⟨ B ⟩s → ⟨ B' ⟩s → Type ℓR
    is-prop-valued : ∀ x y → isProp (R x y)
    R℧ : ∀ x → R B.℧ x
    Rθ   : ∀ (x~ : ▹ ⟨ B ⟩s) (y~ : ▹ ⟨ B' ⟩s)
           → ▸ (λ t → R (x~ t) (y~ t))
           → R (B.θ x~) (B'.θ y~)


------------------------------------
-- Category of simple error domains
------------------------------------

open Category

module _ (ℓ : Level) where
  SIMPED : Category (ℓ-suc ℓ) ℓ
  SIMPED .ob = SimpleErrorDomain ℓ
  SIMPED .Hom[_,_] = SEDMor
  SIMPED .Category.id = idSEDmor
  SIMPED ._⋆_ ϕ ϕ' = ϕ' ∘sed ϕ
  SIMPED .⋆IdL = CompSED-IdR
  SIMPED .⋆IdR = CompSED-IdL
  SIMPED .⋆Assoc = CompSED-Assoc
  SIMPED .isSetHom = SEDMorIsSet



---------------------------------
-- The free simple error domain
---------------------------------

-- open import Semantics.Concrete.LockStepErrorOrdering k

𝔽 : (A : hSet ℓ) → SimpleErrorDomain ℓ
𝔽 A = mkSimpleErrorDomain (L℧ ⟨ A ⟩) structure-F
  where
    structure-F : SimpleErrorDomainStr _
    structure-F .SimpleErrorDomainStr.is-set = isSetL℧ ⟨ A ⟩ (A .snd)
    structure-F .SimpleErrorDomainStr.℧ = ℧L
    structure-F .SimpleErrorDomainStr.θ = θL

𝔽-intro : {A : hSet ℓ} → L℧ ⟨ A ⟩ → ⟨ 𝔽 A ⟩s
𝔽-intro {A = A} lx = sed-intro lx

𝔽-elim : {A : hSet ℓ} → ⟨ 𝔽 A ⟩s → L℧ ⟨ A ⟩
𝔽-elim {A = A} x = sed-elim x


-----------------
-- The U functor
-----------------

U-simp-ob : (B : SimpleErrorDomain ℓ) → Type ℓ
U-simp-ob B = ⟨ B ⟩s

U-simp-mor : {B₁ : SimpleErrorDomain ℓ} {B₂ : SimpleErrorDomain ℓ'}
  → SEDMor B₁ B₂
  → U-simp-ob B₁ → U-simp-ob B₂
U-simp-mor ϕ = ϕ .SEDMor.f


-- Introduction forms
module _ {A : hSet ℓ} where

  opaque
    unfolding ⟨_⟩s
    η𝔽 : ⟨ A ⟩ → ⟨ 𝔽 A ⟩s
    η𝔽 x = η x

    ℧𝔽 : ⟨ 𝔽 A ⟩s
    ℧𝔽 = ℧L

    θ𝔽 : ▹ ⟨ 𝔽 A ⟩s → ⟨ 𝔽 A ⟩s
    θ𝔽 = θL

    δ𝔽 : ⟨ 𝔽 A ⟩s → ⟨ 𝔽 A ⟩s
    δ𝔽 = δL


-- Equations
module _ {A : hSet ℓ} where

  private
    module FA = SimpleErrorDomain→module (𝔽 A)

  opaque
    unfolding SimpleErrorDomain→record ℧𝔽 θ𝔽 δ𝔽

    FA℧≡℧ : FA.℧ ≡ ℧𝔽
    FA℧≡℧ = refl

    FAθ≡θ : ∀ lx~ → FA.θ lx~ ≡ θ𝔽 lx~
    FAθ≡θ lx~ = refl


-- Dependent eliminator
------------------------
module _ {A : hSet ℓ} {B : ⟨ 𝔽 A ⟩s → Type ℓ'}
  (η* : ∀ x → B (η𝔽 x))
  (℧* : B ℧𝔽)
  (θ* : ∀ (IH : ▹ (∀ lx → B lx))
      →   (lx~ : ▹ ⟨ 𝔽 A ⟩s)
      → B (θ𝔽 lx~))
  where
  
    private
      opaque
        unfolding mkSimpleErrorDomain η𝔽 ℧𝔽 θ𝔽
        elim𝔽-helper : ▹ (∀ lx → B lx) → (∀ lx → B lx)
        elim𝔽-helper _ (η x) = η* x
        elim𝔽-helper _ ℧L = ℧*
        elim𝔽-helper IH (θL lx~) = θ* IH lx~

    opaque
      elim𝔽 : ∀ lx → B lx
      elim𝔽 = fix elim𝔽-helper

    opaque
      unfolding elim𝔽 elim𝔽-helper
      elim𝔽-η : ∀ x → elim𝔽 (η𝔽 x) ≡ η* x
      elim𝔽-η x = funExt⁻ (fix-eq elim𝔽-helper) (η𝔽 x)

      elim𝔽-℧ : elim𝔽 ℧𝔽 ≡ ℧*
      elim𝔽-℧ = funExt⁻ (fix-eq elim𝔽-helper) ℧𝔽

      elim𝔽-θ : ∀ lx~ → elim𝔽 (θ𝔽 lx~) ≡ θ* (next elim𝔽) lx~
      elim𝔽-θ lx~ = funExt⁻ (fix-eq elim𝔽-helper) (θ𝔽 lx~)

-- Recursor
------------
module _ {A : hSet ℓ} {B : Type ℓ'}
  (η* : ⟨ A ⟩ → B)
  (℧* : B)
  (θ* : ▹ (⟨ 𝔽 A ⟩s → B) → ▹ ⟨ 𝔽 A ⟩s → B)
  where

  opaque
    unfolding elim𝔽 δ𝔽
    rec𝔽 : ⟨ 𝔽 A ⟩s → B
    rec𝔽 = elim𝔽 η* ℧* θ*

    rec𝔽-η : ∀ x → rec𝔽 (η𝔽 x) ≡ η* x
    rec𝔽-η x = elim𝔽-η _ _ _ x

    rec𝔽-℧ : rec𝔽 ℧𝔽 ≡ ℧*
    rec𝔽-℧ = elim𝔽-℧ _ _ _

    rec𝔽-θ : ∀ lx~ → rec𝔽 (θ𝔽 lx~) ≡ θ* (next rec𝔽) lx~
    rec𝔽-θ lx~ = elim𝔽-θ _ _ _ lx~

    rec𝔽-δ : ∀ lx → rec𝔽 (δ𝔽 lx) ≡ θ* (next rec𝔽) (next lx)
    rec𝔽-δ lx = rec𝔽-θ (next lx)



---------------------------------------------------



-- Dependent eliminator
-----------------------
module _ {A : hSet ℓ} {B : ⟨ 𝔽 A ⟩s → Type ℓ'}
  (η* : ∀ x → B (η𝔽 x))
  (℧* : B ℧𝔽)
  (θ* : ∀ (lx~ : ▹ ⟨ 𝔽 A ⟩s)
      → ▸ (λ t → B (lx~ t))
      → B (θ𝔽 lx~))
  where

  opaque
    unfolding mkSimpleErrorDomain η𝔽 ℧𝔽 θ𝔽
    elim𝔽' : ∀ lx → B lx
    elim𝔽' = fix aux
      where
        aux : ▹ (∀ lx → B lx) → (∀ lx → B lx)
        aux _ (η x) = η* x
        aux _ ℧L = ℧*
        aux IH (θL lx~) = θ* lx~ (λ t → IH t (lx~ t))


-- Recursor
------------
module _ {A : hSet ℓ} {B : Type ℓ'}
  (η* : ⟨ A ⟩ → B)
  (℧* : B)
  (θ* : ▹ B → B)
  where

  opaque
    unfolding elim𝔽
    rec𝔽' : ⟨ 𝔽 A ⟩s → B
    rec𝔽' = elim𝔽' {B = λ _ → B} η* ℧* (λ _ → θ*)


