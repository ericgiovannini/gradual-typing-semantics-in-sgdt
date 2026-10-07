{-
  Square and bisimilarity lemmas for the combinators used by the term
  semantics. These are the ingredients of the interpretation of term
  precision as extensional squares: for each term former we need that
  its denotation preserves squares (the strict part) and bisimilarity
  of morphisms (the part that absorbs perturbations and delays).

  The cast rules need in addition the squares UpL-sq, UpR-sq, DnL-sq
  and DnR-sq, which turn the quasi-representability squares of a
  relation and the push-pull squares of the other relation into a
  square for the composite relation (Section 6.4.3 of the paper).
-}
{-# OPTIONS --rewriting --lossy-unification #-}
open import Common.Later
module Syntax.FineGrained.Denotation.Squares (k : Clock) where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat using (zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation as PT

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions
  using (_×dp_ ; π1 ; π2 ; ℕ ; UnitP ; UnitP!)
open import Semantics.Concrete.Predomain.Combinators
  using (Curry ; App ; PairFun ; K ; SwapPair ; _×mor_ ; mSuc)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Predomain.MonadCombinators k

open import Syntax.FineGrained.Denotation.Combinators k

private
  variable
    ℓ ℓ' ℓ'' : Level
    ℓΓ ℓ≤Γ ℓ≈Γ ℓΓ' ℓ≤Γ' ℓ≈Γ' : Level
    ℓΔ ℓ≤Δ ℓ≈Δ ℓΔ' ℓ≤Δ' ℓ≈Δ' : Level
    ℓA ℓ≤A ℓ≈A ℓA' ℓ≤A' ℓ≈A' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓA₃ ℓ≤A₃ ℓ≈A₃ : Level
    ℓB ℓ≤B ℓ≈B ℓB' ℓ≤B' ℓ≈B' : Level
    ℓB₁ ℓ≤B₁ ℓ≈B₁ ℓB₁' ℓ≤B₁' ℓ≈B₁' : Level
    ℓB₂ ℓ≤B₂ ℓ≈B₂ ℓB₂' ℓ≤B₂' ℓ≈B₂' : Level
    ℓB₃ ℓ≤B₃ ℓ≈B₃ ℓB₃' ℓ≤B₃' ℓ≈B₃' : Level
    ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ' : Level
    ℓBₒ ℓ≤Bₒ ℓ≈Bₒ ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ' : Level
    ℓc ℓc' ℓc₁ ℓc₂ ℓcΓ ℓcΔ ℓcᵢ ℓcₒ ℓd ℓd₁ ℓd₂ ℓd₃ ℓdᵢ ℓdₒ : Level

open PMor
open ErrorDomMor
open PRel
open ExtAsEDMorphism
open F-ob
open F-mor
open F-rel
open F-sq


-----------------------------------------------------------------------
-- Plugging and composition of evaluation contexts
-----------------------------------------------------------------------

module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {Γ' : Predomain ℓΓ' ℓ≤Γ' ℓ≈Γ'}
         {Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ} {Bᵢ' : ErrorDomain ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ'}
         {Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ} {Bₒ' : ErrorDomain ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ'}
         (cΓ : PRel Γ Γ' ℓcΓ) (dᵢ : ErrorDomRel Bᵢ Bᵢ' ℓdᵢ) (dₒ : ErrorDomRel Bₒ Bₒ' ℓdₒ)
         {E : ErrorDomMor Bᵢ (Γ ⟶ob Bₒ)} {E' : ErrorDomMor Bᵢ' (Γ' ⟶ob Bₒ')}
         {M : PMor Γ (U-ob Bᵢ)} {M' : PMor Γ' (U-ob Bᵢ')} where

  plug-sq : ErrorDomSq dᵢ (cΓ ⟶rel dₒ) E E' → PSq cΓ (U-rel dᵢ) M M' →
    PSq cΓ (U-rel dₒ) (plugE E M) (plugE E' M')
  plug-sq α β γ γ' γRγ' = α (M .f γ) (M' .f γ') (β γ γ' γRγ') γ γ' γRγ'

module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ}
         {Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ} {Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ}
         {E E₂ : ErrorDomMor Bᵢ (Γ ⟶ob Bₒ)} {M M₂ : PMor Γ (U-ob Bᵢ)} where

  plug-≈ : (U-mor E) ≈mon (U-mor E₂) → M ≈mon M₂ → plugE E M ≈mon plugE E₂ M₂
  plug-≈ α β γ γ' γ≈γ' = α (M .f γ) (M₂ .f γ') (β γ γ' γ≈γ') γ γ' γ≈γ'

module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {Γ' : Predomain ℓΓ' ℓ≤Γ' ℓ≈Γ'}
         {B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁} {B₁' : ErrorDomain ℓB₁' ℓ≤B₁' ℓ≈B₁'}
         {B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂} {B₂' : ErrorDomain ℓB₂' ℓ≤B₂' ℓ≈B₂'}
         {B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃} {B₃' : ErrorDomain ℓB₃' ℓ≤B₃' ℓ≈B₃'}
         (cΓ : PRel Γ Γ' ℓcΓ)
         (d₁ : ErrorDomRel B₁ B₁' ℓd₁) (d₂ : ErrorDomRel B₂ B₂' ℓd₂) (d₃ : ErrorDomRel B₃ B₃' ℓd₃)
         {E' : ErrorDomMor B₂ (Γ ⟶ob B₃)} {F' : ErrorDomMor B₂' (Γ' ⟶ob B₃')}
         {E : ErrorDomMor B₁ (Γ ⟶ob B₂)} {F : ErrorDomMor B₁' (Γ' ⟶ob B₂')} where

  compE-sq : ErrorDomSq d₂ (cΓ ⟶rel d₃) E' F' → ErrorDomSq d₁ (cΓ ⟶rel d₂) E F →
    ErrorDomSq d₁ (cΓ ⟶rel d₃) (compE E' E) (compE F' F)
  compE-sq α β b b' bRb' γ γ' γRγ' =
    α (E .fun b .f γ) (F .fun b' .f γ') (β b b' bRb' γ γ' γRγ') γ γ' γRγ'

module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ}
         {B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁} {B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂} {B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃}
         {E' E'₂ : ErrorDomMor B₂ (Γ ⟶ob B₃)} {E E₂ : ErrorDomMor B₁ (Γ ⟶ob B₂)} where

  compE-≈ : (U-mor E') ≈mon (U-mor E'₂) → (U-mor E) ≈mon (U-mor E₂) →
    (U-mor (compE E' E)) ≈mon (U-mor (compE E'₂ E₂))
  compE-≈ α β b b' b≈b' γ γ' γ≈γ' =
    α (E .fun b .f γ) (E₂ .fun b' .f γ') (β b b' b≈b' γ γ' γ≈γ') γ γ' γ≈γ'

module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {Γ' : Predomain ℓΓ' ℓ≤Γ' ℓ≈Γ'}
         {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
         (cΓ : PRel Γ Γ' ℓcΓ) (d : ErrorDomRel B B' ℓd) where

  K-arrow-sq : ErrorDomSq d (cΓ ⟶rel d) (K-arrow {Γ = Γ}) (K-arrow {Γ = Γ'})
  K-arrow-sq b b' bRb' γ γ' _ = bRb'

-- Substitution into an evaluation context.
module _ {Δ : Predomain ℓΔ ℓ≤Δ ℓ≈Δ} {Δ' : Predomain ℓΔ' ℓ≤Δ' ℓ≈Δ'}
         {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {Γ' : Predomain ℓΓ' ℓ≤Γ' ℓ≈Γ'}
         {Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ} {Bᵢ' : ErrorDomain ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ'}
         {Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ} {Bₒ' : ErrorDomain ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ'}
         (cΔ : PRel Δ Δ' ℓcΔ) (cΓ : PRel Γ Γ' ℓcΓ)
         (dᵢ : ErrorDomRel Bᵢ Bᵢ' ℓdᵢ) (dₒ : ErrorDomRel Bₒ Bₒ' ℓdₒ)
         {s : PMor Δ Γ} {s' : PMor Δ' Γ'}
         {E : ErrorDomMor Bᵢ (Γ ⟶ob Bₒ)} {E' : ErrorDomMor Bᵢ' (Γ' ⟶ob Bₒ')} where

  substE-sq : PSq cΔ cΓ s s' → ErrorDomSq dᵢ (cΓ ⟶rel dₒ) E E' →
    ErrorDomSq dᵢ (cΔ ⟶rel dₒ) ((s ⟶mor IdE) ∘ed E) ((s' ⟶mor IdE) ∘ed E')
  substE-sq σ α b b' bRb' δ δ' δRδ' = α b b' bRb' (s .f δ) (s' .f δ') (σ δ δ' δRδ')

module _ {Δ : Predomain ℓΔ ℓ≤Δ ℓ≈Δ} {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ}
         {Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ} {Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ}
         {s s₂ : PMor Δ Γ} {E E₂ : ErrorDomMor Bᵢ (Γ ⟶ob Bₒ)} where

  substE-≈ : s ≈mon s₂ → (U-mor E) ≈mon (U-mor E₂) →
    (U-mor ((s ⟶mor IdE) ∘ed E)) ≈mon (U-mor ((s₂ ⟶mor IdE) ∘ed E₂))
  substE-≈ σ α b b' b≈b' δ δ' δ≈δ' = α b b' b≈b' (s .f δ) (s₂ .f δ') (σ δ δ' δ≈δ')

-- Bind.
module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {Γ' : Predomain ℓΓ' ℓ≤Γ' ℓ≈Γ'}
         {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
         {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
         (cΓ : PRel Γ Γ' ℓcΓ) (c : PRel A A' ℓc) (d : ErrorDomRel B B' ℓd)
         {M : PMor (Γ ×dp A) (U-ob B)} {M' : PMor (Γ' ×dp A') (U-ob B')} where

  bind-sq : PSq (cΓ ×pbmonrel c) (U-rel d) M M' →
    ErrorDomSq (F-rel c) (cΓ ⟶rel d) (Ext (Curry (M ∘p SwapPair))) (Ext (Curry (M' ∘p SwapPair)))
  bind-sq α = Ext-sq c (cΓ ⟶rel d) (Curry (M ∘p SwapPair)) (Curry (M' ∘p SwapPair))
    (λ a a' aRa' γ γ' γRγ' → α (γ , a) (γ' , a') (γRγ' , aRa'))

module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {A : Predomain ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B}
         {M M₂ : PMor (Γ ×dp A) (U-ob B)} where

  bind-≈ : M ≈mon M₂ →
    (U-mor (Ext (Curry (M ∘p SwapPair)))) ≈mon (U-mor (Ext (Curry (M₂ ∘p SwapPair))))
  bind-≈ α = ExtCombinator.Ext {A = A} {B = Γ ⟶ob B} .pres≈
    {x = Curry (M ∘p SwapPair)} {y = Curry (M₂ ∘p SwapPair)}
    (λ a a' a≈a' γ γ' γ≈γ' → α (γ , a) (γ' , a') (γ≈γ' , a≈a'))


-----------------------------------------------------------------------
-- Value-level combinators
-----------------------------------------------------------------------

module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {Γ' : Predomain ℓΓ' ℓ≤Γ' ℓ≈Γ'}
         {Aᵢ : Predomain ℓA ℓ≤A ℓ≈A} {Aᵢ' : Predomain ℓA' ℓ≤A' ℓ≈A'}
         {Aₒ : Predomain ℓB ℓ≤B ℓ≈B} {Aₒ' : Predomain ℓB' ℓ≤B' ℓ≈B'}
         (cΓ : PRel Γ Γ' ℓcΓ) (cᵢ : PRel Aᵢ Aᵢ' ℓcᵢ) (cₒ : PRel Aₒ Aₒ' ℓcₒ)
         {g : PMor (Γ ×dp Aᵢ) Aₒ} {g' : PMor (Γ' ×dp Aᵢ') Aₒ'} where

  Curry-sq : PSq (cΓ ×pbmonrel cᵢ) cₒ g g' → PSq cΓ (cᵢ ==>pbmonrel cₒ) (Curry g) (Curry g')
  Curry-sq α γ γ' γRγ' x y xRy = α (γ , x) (γ' , y) (γRγ' , xRy)

module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {Aᵢ : Predomain ℓA ℓ≤A ℓ≈A} {Aₒ : Predomain ℓB ℓ≤B ℓ≈B}
         {g g₂ : PMor (Γ ×dp Aᵢ) Aₒ} where

  Curry-≈ : g ≈mon g₂ → Curry g ≈mon Curry g₂
  Curry-≈ α γ γ' γ≈γ' x y x≈y = α (γ , x) (γ' , y) (γ≈γ' , x≈y)

module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {Γ' : Predomain ℓΓ' ℓ≤Γ' ℓ≈Γ'}
         {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : Predomain ℓA ℓ≤A ℓ≈A}
         {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : Predomain ℓA' ℓ≤A' ℓ≈A'}
         (cΓ : PRel Γ Γ' ℓcΓ) (c₁ : PRel A₁ A₁' ℓc₁) (c₂ : PRel A₂ A₂' ℓc₂)
         {f₁ : PMor Γ A₁} {g₁ : PMor Γ' A₁'} {f₂ : PMor Γ A₂} {g₂ : PMor Γ' A₂'} where

  PairFun-sq : PSq cΓ c₁ f₁ g₁ → PSq cΓ c₂ f₂ g₂ →
    PSq cΓ (c₁ ×pbmonrel c₂) (PairFun f₁ f₂) (PairFun g₁ g₂)
  PairFun-sq α β γ γ' γRγ' = α γ γ' γRγ' , β γ γ' γRγ'

module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂}
         {f₁ f₁' : PMor Γ A₁} {f₂ f₂' : PMor Γ A₂} where

  PairFun-≈ : f₁ ≈mon f₁' → f₂ ≈mon f₂' → PairFun f₁ f₂ ≈mon PairFun f₁' f₂'
  PairFun-≈ α β γ γ' γ≈γ' = α γ γ' γ≈γ' , β γ γ' γ≈γ'

module _ {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₁' : Predomain ℓA ℓ≤A ℓ≈A}
         {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₂' : Predomain ℓA' ℓ≤A' ℓ≈A'}
         (c₁ : PRel A₁ A₁' ℓc₁) (c₂ : PRel A₂ A₂' ℓc₂) where

  π1-sq : PSq (c₁ ×pbmonrel c₂) c₁ π1 π1
  π1-sq _ _ p = p .fst

  π2-sq : PSq (c₁ ×pbmonrel c₂) c₂ π2 π2
  π2-sq _ _ p = p .snd

-- Successor on the flat predomain of naturals, in a context.
module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {Γ' : Predomain ℓΓ' ℓ≤Γ' ℓ≈Γ'} (cΓ : PRel Γ Γ' ℓcΓ) where

  suc-sq : PSq (cΓ ×pbmonrel idPRel ℕ) (idPRel ℕ) (mSuc ∘p π2) (mSuc ∘p π2)
  suc-sq _ _ p = cong suc (p .snd)

-- Application: the context is (Γ × U(A ⟶ B)) × A.
module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {Γ' : Predomain ℓΓ' ℓ≤Γ' ℓ≈Γ'}
         {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
         {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
         (cΓ : PRel Γ Γ' ℓcΓ) (c : PRel A A' ℓc) (d : ErrorDomRel B B' ℓd) where

  app-sq : PSq ((cΓ ×pbmonrel U-rel (c ⟶rel d)) ×pbmonrel c) (U-rel d)
    (App ∘p (π2 ×mor Id)) (App ∘p (π2 ×mor Id))
  app-sq _ _ ((_ , α) , xRy) = α _ _ xRy

-- Case analysis on naturals.
module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {Γ' : Predomain ℓΓ' ℓ≤Γ' ℓ≈Γ'}
         {B : Predomain ℓB ℓ≤B ℓ≈B} {B' : Predomain ℓB' ℓ≤B' ℓ≈B'}
         (cΓ : PRel Γ Γ' ℓcΓ) (b : PRel B B' ℓd)
         {z : PMor Γ B} {z' : PMor Γ' B'} {s : PMor (Γ ×dp ℕ) B} {s' : PMor (Γ' ×dp ℕ) B'} where

  natCase-sq : PSq cΓ b z z' → PSq (cΓ ×pbmonrel idPRel ℕ) b s s' →
    PSq (cΓ ×pbmonrel idPRel ℕ) b (natCase z s) (natCase z' s')
  natCase-sq α β (γ , n) (γ' , n') (γRγ' , n≡n') =
    subst (λ m → b .R (natCase z s .f (γ , n)) (natCase z' s' .f (γ' , m))) n≡n' (aux n)
    where
      aux : ∀ n → b .R (natCase z s .f (γ , n)) (natCase z' s' .f (γ' , n))
      aux zero = α γ γ' γRγ'
      aux (suc m) = β (γ , m) (γ' , m) (γRγ' , refl)

module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {B : Predomain ℓB ℓ≤B ℓ≈B}
         {z z' : PMor Γ B} {s s' : PMor (Γ ×dp ℕ) B} where

  private module B = PredomainStr (B .snd)

  natCase-≈ : z ≈mon z' → s ≈mon s' → natCase z s ≈mon natCase z' s'
  natCase-≈ α β (γ , n) (γ' , n') (γ≈γ' , n≡n') =
    subst (λ m → natCase z s .f (γ , n) B.≈ natCase z' s' .f (γ' , m)) n≡n' (aux n)
    where
      aux : ∀ n → natCase z s .f (γ , n) B.≈ natCase z' s' .f (γ' , n)
      aux zero = α γ γ' γ≈γ'
      aux (suc m) = β (γ , m) (γ' , m) (γ≈γ' , refl)


-----------------------------------------------------------------------
-- Lifting a square through U ∘ F
-----------------------------------------------------------------------

module _ {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
         {B : Predomain ℓB ℓ≤B ℓ≈B} {B' : Predomain ℓB' ℓ≤B' ℓ≈B'}
         (c : PRel A A' ℓc) (c' : PRel B B' ℓc') (f : PMor A B) (g : PMor A' B') where

  UF-sq : PSq c c' f g →
    PSq (U-rel (F-rel c)) (U-rel (F-rel c')) (U-mor (F-mor f)) (U-mor (F-mor g))
  UF-sq α = U-sq (F-rel c) (F-rel c') (F-mor f) (F-mor g) (F-sq c c' f g α)


-----------------------------------------------------------------------
-- Squares for the cast rules
-----------------------------------------------------------------------

module _ {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₃ : Predomain ℓA₃ ℓ≤A₃ ℓ≈A₃}
         (c : PRel A₁ A₂ ℓc) (d : PRel A₂ A₃ ℓd) where

  private
    module A₂ = PredomainStr (A₂ .snd)

  -- UpL: the embedding of c against a perturbation, pushed along d.
  UpL-sq : {e : PMor A₁ A₂} {δ : PMor A₂ A₂} {δ' : PMor A₃ A₃} →
    PSq c (idPRel A₂) e δ → PSq d d δ δ' → PSq (c ⊙ d) d e δ'
  UpL-sq upl push x z H = PT.rec (d .is-prop-valued _ _)
    (λ { (y , xcy , ydz) → d .is-antitone (upl x y xcy) (push y z ydz) }) H

  -- UpR: a perturbation pulled along c, against the embedding of d.
  UpR-sq : {δ₁ : PMor A₁ A₁} {δ₂ : PMor A₂ A₂} {e : PMor A₂ A₃} →
    PSq c c δ₁ δ₂ → PSq (idPRel A₂) d δ₂ e → PSq c (c ⊙ d) δ₁ e
  UpR-sq {δ₂ = δ₂} pull upr x y xcy = ∣ δ₂ .f y , pull x y xcy , upr y y (A₂.is-refl y) ∣₁

  -- DnL: the projection of F c against a perturbation, pushed along F d,
  -- then lax functoriality of F.
  DnL-sq : {p : ErrorDomMor (F-ob A₂) (F-ob A₁)}
    {δ : ErrorDomMor (F-ob A₂) (F-ob A₂)} {δ' : ErrorDomMor (F-ob A₃) (F-ob A₃)} →
    ErrorDomSq (idEDRel (F-ob A₂)) (F-rel c) p δ → ErrorDomSq (F-rel d) (F-rel d) δ δ' →
    ErrorDomSq (F-rel d) (F-rel (c ⊙ d)) p δ'
  DnL-sq {p = p} {δ = δ} {δ' = δ'} dnl push x z xdz =
    F-rel-lax-functoriality.lax-functoriality c d _ _
      (ED-CompSqH {ϕ₁ = p} {ϕ₂ = δ} {ϕ₃ = δ'} dnl push x z (sq-d-idB⊙d (F-rel d) x z xdz))

  -- DnR: from a square F(c ⊙ d) to F c ⊙ F d (the quasi-equivalence of
  -- Lemma D.11), a perturbation pulled along F c, and the projection of
  -- F d.
  DnR-sq : {ε₁ : ErrorDomMor (F-ob A₁) (F-ob A₁)} {ε₁' : ErrorDomMor (F-ob A₃) (F-ob A₃)}
    {δ₁ : ErrorDomMor (F-ob A₁) (F-ob A₁)} {δ₂ : ErrorDomMor (F-ob A₂) (F-ob A₂)}
    {p : ErrorDomMor (F-ob A₃) (F-ob A₂)} →
    ErrorDomSq (F-rel (c ⊙ d)) (F-rel c ⊙ed F-rel d) ε₁ ε₁' →
    ErrorDomSq (F-rel c) (F-rel c) δ₁ δ₂ →
    ErrorDomSq (F-rel d) (idEDRel (F-ob A₂)) δ₂ p →
    ErrorDomSq (F-rel (c ⊙ d)) (F-rel c) (δ₁ ∘ed ε₁) (p ∘ed ε₁')
  DnR-sq {δ₁ = δ₁} {δ₂ = δ₂} {p = p} eq pull dnr x z H =
    sq-d⊙idB'-d (F-rel c) _ _ (ED-CompSqH {ϕ₁ = δ₁} {ϕ₂ = δ₂} {ϕ₃ = p} pull dnr _ _ (eq x z H))


-----------------------------------------------------------------------
-- Upcasts as evaluation contexts
-----------------------------------------------------------------------

-- Evaluation at a point of the environment, as a homomorphism.
module _ {Γ : Predomain ℓΓ ℓ≤Γ ℓ≈Γ} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} (γ : ⟨ Γ ⟩) where

  evAt : ErrorDomMor (Γ ⟶ob B) B
  evAt .f = App ∘p PairFun Id (K _ γ)
  evAt .f℧ = refl
  evAt .fθ g~ = refl

-- The evaluation context  bind (ret (e x))  of a value morphism e, in
-- the empty environment, is (the Kleisli extension of) F e.
module _ {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'} (e : PMor A A') where

  private
    g : PMor A (U-ob (UnitP ⟶ob F-ob A'))
    g = Curry (((η-mor ∘p π2) ∘p PairFun UnitP! (e ∘p π2)) ∘p SwapPair)

  upE-eq : evAt tt ∘ed Ext g ≡ F-mor e
  upE-eq = F-extensionality (evAt tt ∘ed Ext g) (F-mor e)
    (eqPMor _ _ (funExt (λ x →
      cong (λ h → h .f tt) (funExt⁻ (cong PMor.f (ExtAsEDMorphism.Equations.Ext-η g)) x)
      ∙ sym (funExt⁻ (cong PMor.f (F-mor.Equations.F-mor-η e)) x))))
