{-# OPTIONS --safe #-}
{-# OPTIONS --polarity #-}

module Experiments.FreeMonoidWithHom where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Reindex
open import Cubical.Algebra.Monoid.Displayed.Instances.Path
open import Cubical.Data.Empty as Empty hiding (elim; rec)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma as Sigma


private variable
  ℓ ℓ' ℓ'' ℓ''' ℓᴰ ℓᴰ' : Level
  ℓM : Level
  

snd' : {A : Type ℓ} {B : A → Type ℓ'}
  → (x : Sigma.Σ A B) → B (x .fst)
snd' (x , y) = y

module _  (A : Type ℓ) -- (B : Type ℓ') (C : Type ℓ'')
  (F : ∀ {ℓM} → @++ Monoid ℓM → Monoid ℓM) where
  FM : Monoid ℓ

  F-FM : Monoid ℓ
  F-FM = F FM

  private module F-FM = MonoidStr (F-FM .snd)

  F-FM-· : F FM .fst → F FM .fst → F FM .fst
  F-FM-· x y = (F FM) .snd .MonoidStr._·_ x y
  

  data FreeMonoidWithHom : Type ℓ where
    ⟦_⟧       : A → FreeMonoidWithHom
    ⟦_⟧inj    : F FM .fst → FreeMonoidWithHom
    ε         : FreeMonoidWithHom
    _·_       : FreeMonoidWithHom → FreeMonoidWithHom → FreeMonoidWithHom
    identityᵣ : ∀ x     → x · ε ≡ x
    identityₗ : ∀ x     → ε · x ≡ x
    assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
    inj-ε :   ⟦ F FM .snd .MonoidStr.ε ⟧inj ≡ ε
    --test-inj-·   : ∀ x y → ⟦ F-FM-· x y ⟧inj ≡ (⟦ x ⟧inj · ⟦ y ⟧inj)
    inj-·    : ∀ x y → ⟦ F FM .snd .MonoidStr._·_ x y ⟧inj ≡ (⟦ x ⟧inj · ⟦ y ⟧inj)
    trunc     : isSet FreeMonoidWithHom

  FM = FreeMonoidWithHom , (monoidstr ε _·_ (ismonoid (issemigroup trunc assoc) identityᵣ identityₗ))

  gen : A → ⟨ FM ⟩
  gen x = ⟦ x ⟧

  injHom : MonoidHom (F FM) FM
  injHom .fst = ⟦_⟧inj
  injHom .snd .IsMonoidHom.presε = inj-ε
  injHom .snd .IsMonoidHom.pres· = inj-·

{-
  coHom : B → MonoidHom FM FM
  coHom b .fst = ⟦ b ⟧co
  coHom b .snd .IsMonoidHom.presε = co-ε b
  coHom b .snd .IsMonoidHom.pres· = co-· b

  opHom : C → MonoidHom (FM ^op) FM
  opHom c .fst = ⟦ c ⟧op
  opHom c .snd .IsMonoidHom.presε = op-ε c
  opHom c .snd .IsMonoidHom.pres· = op-· c
-}

{-
  module _ (Mᴰ : Monoidᴰ FM ℓᴰ) (Nᴰ : Monoidᴰ (F FM) ℓᴰ)
    (Fᴰ : ∀ {ℓ} (M : Monoid ℓ) (Mᴰ : Monoidᴰ M ℓᴰ) → Monoidᴰ (F M) ℓᴰ)
    (F-hom : ∀ {ℓ ℓ'} (M : Monoid ℓ) (N : Monoid ℓ') → MonoidHom M N → MonoidHom (F M) (F N))
    (F-homᴰ : ∀ {ℓ ℓᴰ ℓ' ℓᴰ'} {M : Monoid ℓ} {N : Monoid ℓ'} (Mᴰ : Monoidᴰ M ℓᴰ) → {!!})
    where
    private
      module Mᴰ = Monoidᴰ Mᴰ
      module Nᴰ = Monoidᴰ Nᴰ
    module _
      (iA : ∀ a → Mᴰ.eltᴰ ⟦ a ⟧)
      (iF : MonoidHomᴰ injHom Nᴰ Mᴰ)
      (iG : MonoidHom FM (F (FM)))
      (iGᴰ : MonoidHomᴰ iG Mᴰ Nᴰ)
      -- (iF  : MonoidHom FM (F (FM)))
      -- (iFᴰ : MonoidHomᴰ iF Mᴰ Nᴰ)

      (test : ∀ (x : F FM .fst) → Mᴰ.eltᴰ (injHom .fst x) → Nᴰ.eltᴰ x)
      (test2 : ∀ (x : F FM .fst) → Nᴰ.eltᴰ x → Mᴰ.eltᴰ ⟦ x ⟧inj)
      where

      elim : Section Mᴰ
      elim .fst = f where
        f : ∀ x → (Mᴰ.eltᴰ x)
        g : ∀ x → Nᴰ.eltᴰ x -- (iG .fst x)
        g x = {!iGᴰ .fst!}


        f ⟦ a ⟧ = iA a
        f ⟦ x ⟧inj = iF .fst (g x)
        f ε = Mᴰ.εᴰ
        f (x · y) = f x Mᴰ.·ᴰ f y
        f (identityᵣ x i) = Mᴰ.·IdRᴰ (f x) i
        f (identityₗ x i) = Mᴰ.·IdLᴰ (f x) i
        f (assoc x y z i) = Mᴰ.·Assocᴰ (f x) (f y) (f z) i
        f (inj-ε i) = {!!}
        f (inj-· x y i) = {!!}
        f (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2
          (λ x → Mᴰ.isSetEltᴰ)
          (f x) (f y) (cong f p) (cong f q)
          (trunc x y p q) i j

        

        -- f : ∀ x → (Mᴰ.eltᴰ x) × (Nᴰ.eltᴰ (iG .fst x))
        -- f ⟦ a ⟧ = iA a , iGᴰ .fst (iA a)
        -- f ⟦ x ⟧inj = iF .fst {!f !} , {!!}
        -- f ε = Mᴰ.εᴰ , iGᴰ .fst Mᴰ.εᴰ
        -- f (x · y) = f x .fst Mᴰ.·ᴰ f y .fst , {!!}
        -- f (identityᵣ x i) = {!!} -- Mᴰ.·IdRᴰ (f x) i
        -- f (identityₗ x i) = {!!} -- Mᴰ.·IdLᴰ (f x) i
        -- f (assoc x y z i) = {!!} -- Mᴰ.·Assocᴰ (f x) (f y) (f z) i
        -- f (inj-ε i) = {!!}
        -- f (inj-· x y i) = {!!}
        -- f (trunc x y p q i j) = {!!}
          -- isOfHLevel→isOfHLevelDep 2
          --   (λ x → Mᴰ.isSetEltᴰ)
          --   (f x) (f y) (cong f p) (cong f q)
          --   (trunc x y p q) i j



  module _ (N : Monoid ℓ''')
    (iA : A → ⟨ N ⟩)
    (iF : MonoidHom (F N) N)
    (F-hom : ∀ {ℓ ℓ'} (M : Monoid ℓ) (N : Monoid ℓ') → @++ MonoidHom M N → MonoidHom (F M) (F N))
    where
    rec : MonoidHom FM N
    rec .fst = f
      where
        f : ⟨ FM ⟩ → ⟨ N ⟩
        f ⟦ a ⟧ = iA a
        f ⟦ x ⟧inj = iF .fst (F-hom FM N rec .fst x)
        f ε = {!!}
        f (x · x₁) = {!!}
        f (identityᵣ x i) = {!!}
        f (identityₗ x i) = {!!}
        f (assoc x x₁ x₂ i) = {!!}
        f (inj-ε i) = {!!}
        f (inj-· x y i) = {!!}
        f (trunc x x₁ x₂ y i i₁) = {!!}
    rec .snd = {!!}
-}      




{-

  module _ (Mᴰ : Monoidᴰ FM ℓᴰ) where
    private
      module Mᴰ = Monoidᴰ Mᴰ
    module _
      (iA : ∀ a → Mᴰ.eltᴰ ⟦ a ⟧)
      (iB : ∀ b → MonoidHomᴰ (coHom b) Mᴰ Mᴰ)
      (iC : ∀ c → MonoidHomᴰ (opHom c) (Mᴰ ^opᴰ) Mᴰ)
      
      where
      elim : Section Mᴰ
      elim .fst = f where
        f : ∀ x → Mᴰ.eltᴰ x
        f ⟦ a ⟧ = iA a
        f (⟦ b ⟧co x) = iB b .fst (f x)
        f (co-ε b i) = iB b .snd .fst i
        f (co-· b x y i) = iB b .snd .snd (f x) (f y) i
        f (⟦ c ⟧op x) = iC c .fst (f x)
        f (op-ε c i) = iC c .snd .fst i
        f (op-· c x y i) = iC c .snd .snd (f x) (f y) i
        f ε = Mᴰ.εᴰ
        f (x · y) = f x Mᴰ.·ᴰ f y
        f (identityᵣ x i) = Mᴰ.·IdRᴰ (f x) i
        f (identityₗ x i) = Mᴰ.·IdLᴰ (f x) i
        f (assoc x y z i) = Mᴰ.·Assocᴰ (f x) (f y) (f z) i
        f (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2 (λ x → Mᴰ.isSetEltᴰ)
          (f x) (f y)
          (cong f p) (cong f q)
          (trunc x y p q)
          i j
      elim .snd .fst = refl
      elim .snd .snd x y = refl

  module _ (N : Monoid ℓ''')
    (iA : A → ⟨ N ⟩)
    (iB : B → MonoidHom N N)
    (iC : C → MonoidHom (N ^op) N)
    where
    rec : MonoidHom FM N
    rec = unWkn {ϕ = idMon _} s where
      s : Section (wkn FM N)
      s = elim (wkn FM N) iA
        (λ b → wknHom (coHom b) (iB b))
        λ c → wknHom (opHom c) (iC c)

  

  -- Case split (no recursion)
  module _
    (Mᴰ : Monoidᴰ FM ℓᴰ)
    -- (σᴰ : ∀ x → LocalSection (σ x) Mᴰ)
    where
    private
      module Mᴰ = Monoidᴰ Mᴰ
    module _
      (iA : ∀ a → Mᴰ.eltᴰ ⟦ a ⟧)
      (iB : ∀ b → LocalSection (coHom b) Mᴰ)
      (iC : ∀ c → LocalSection (opHom c) Mᴰ)
      where

      elimCases : Section Mᴰ
      elimCases .fst = f where
        f : ∀ x → Mᴰ.eltᴰ x
        f ⟦ a ⟧ = iA a
        f (⟦ b ⟧co x) = iB b .fst x
        f (⟦ c ⟧op x) = iC c .fst x
        f ε = Mᴰ.εᴰ
        f (x · y) = f x Mᴰ.·ᴰ f y
        f (identityᵣ x i) = Mᴰ.·IdRᴰ (f x) i
        f (identityₗ x i) = Mᴰ.·IdLᴰ (f x) i
        f (assoc x y z i) = Mᴰ.·Assocᴰ (f x) (f y) (f z) i
        f (co-ε b i) = iB b .snd .fst i
        f (co-· b x y i) = iB b .snd .snd x y i
        f (op-ε c i) = iC c .snd .fst i
        f (op-· c x y i) = iC c .snd .snd x y i
        f (trunc x y p q i j) = isOfHLevel→isOfHLevelDep 2 (λ x → Mᴰ.isSetEltᴰ)
          (f x) (f y)
          (cong f p) (cong f q)
          (trunc x y p q)
          i j
      elimCases .snd .fst = refl
      elimCases .snd .snd x y = refl
      
  module _ (N : Monoid ℓ''')
    (iA : A → ⟨ N ⟩)
    (iB : B → MonoidHom FM N)
    (iC : C → MonoidHom (FM ^op) N)
    where
    cases : MonoidHom FM N
    cases = unWkn {ϕ = idMon _} s where
      s : Section (wkn FM N)
      s = elimCases (wkn FM N)
        iA
        (λ b → MonoidHom→LocalSectionWkn {ϕ = coHom b} (iB b))
        (λ c → MonoidHom→LocalSectionWkn {ϕ = opHom c} (iC c))
       
  -- uniqueness principle for cases
  module _ {N : Monoid ℓ'''}
    {iA : A → ⟨ N ⟩}
    {iB : B → MonoidHom FM N}
    {iC : C → MonoidHom (FM ^op) N}
    {ψ : MonoidHom FM N}
    (agree-gen : ∀ a → iA a ≡ ψ .fst (gen a))
    (agree-co  : ∀ b → iB b ≡ ψ ∘hom coHom b)
    (agree-op  : ∀ c → iC c ≡ ψ ∘hom opHom c)
    where
    cases-uniq : cases N iA iB iC ≡ ψ
    cases-uniq = eqMonoidHom _ _ (funExt (sec .fst))
      where
        sec : Section (Eq (cases N iA iB iC) ψ)
        sec = elimCases (Eq (cases N iA iB iC) ψ)
          (λ a → agree-gen a) ls-co ls-op
            where
              ls-co : ∀ b → LocalSection (coHom b) (Eq (cases N iA iB iC) ψ)
              ls-co b = corecEq (cases N iA iB iC) ψ {P = FM} {ϕ = coHom b}
                (eqMonoidHom _ _ (cong fst (agree-co b)))

              ls-op : ∀ c → LocalSection (opHom c) (Eq (cases N iA iB iC) ψ)
              ls-op c = corecEq (cases N iA iB iC) ψ {P = FM ^op} {ϕ = opHom c}
                (eqMonoidHom _ _ (cong fst (agree-op c)))

  -- induction principle for cases
  module _ {N : Monoid ℓ'''} {ϕ ψ : MonoidHom FM N}
    (agree-gen : ∀ a → ϕ .fst (gen a) ≡ ψ .fst (gen a))
    (agree-co  : ∀ b → ϕ ∘hom coHom b ≡ ψ ∘hom coHom b)
    (agree-op  : ∀ c → ϕ ∘hom opHom c ≡ ψ ∘hom opHom c)
    where

    cases-ind : ϕ ≡ ψ
    cases-ind = sym (cases-uniq (λ a → refl) (λ b → refl) (λ c → refl)) ∙
      (cases-uniq agree-gen agree-co agree-op)


-- Here's a local elimination principle but only when we don't use the coHom/opHom
module _ (A : Type ℓ) where
  FMsimp : Monoid ℓ
  FMsimp = FM A ⊥ ⊥

  module _ {M : Monoid ℓ'}
      (Mᴰ : Monoidᴰ M ℓᴰ')
      (ϕ : MonoidHom FMsimp M) where
    private
      module Mᴰ = Monoidᴰ Mᴰ
    module _ (iA : ∀ a → Mᴰ.eltᴰ ( ϕ .fst (gen _ _ _ a))) where
      elimLocal : LocalSection ϕ Mᴰ
      elimLocal =
        _gs⋆h_
          {Mᴰ = Reindex {M = FMsimp}{N = M} ϕ Mᴰ}
          {Nᴰ = Mᴰ}
          {ϕ = ϕ}
          (elim A ⊥ ⊥ (Reindex ϕ Mᴰ) iA Empty.elim Empty.elim) (π ϕ Mᴰ)




-- Convenient shorthand for the free monoid on one generator

FM-1 : Monoid ℓ-zero
FM-1 = FM ⊤ ⊥ ⊥

FM-1-gen : ⟨ FM-1 ⟩
FM-1-gen = gen ⊤ ⊥ ⊥ tt

module _ (Mᴰ : Monoidᴰ FM-1 ℓᴰ) where
  private
    module Mᴰ = Monoidᴰ Mᴰ
   
  FM-1-elim : (pt : Mᴰ.eltᴰ ⟦ tt ⟧) → Section Mᴰ
  FM-1-elim pt = elim ⊤ ⊥ ⊥ Mᴰ (λ _ → pt) Empty.elim Empty.elim

module _ {M : Monoid ℓ'}
  (ϕ : MonoidHom FM-1 M)
  (Mᴰ : Monoidᴰ M ℓᴰ') where

  private
    module Mᴰ = Monoidᴰ Mᴰ

  FM-1-elimLocal : (pt : Mᴰ.eltᴰ (ϕ .fst (gen _ _ _ tt)))
    → LocalSection ϕ Mᴰ
  FM-1-elimLocal pt = elimLocal ⊤ Mᴰ ϕ (λ _ → pt)
    
module _ (N : Monoid ℓ''') (pt : ⟨ N ⟩) where

  FM-1-rec : MonoidHom FM-1 N
  FM-1-rec = rec ⊤ ⊥ ⊥ N (λ _ → pt) Empty.rec Empty.rec
  
module _ {N : Monoid ℓ'''} (ϕ ψ : MonoidHom FM-1 N)
  (agree-tt : ϕ .fst (gen _ _ _ tt) ≡ ψ .fst (gen _ _ _ tt))
  where

  FM-1-ind : ϕ ≡ ψ
  FM-1-ind = cases-ind ⊤ ⊥ ⊥ (λ _ → agree-tt) Empty.elim Empty.elim

-}
