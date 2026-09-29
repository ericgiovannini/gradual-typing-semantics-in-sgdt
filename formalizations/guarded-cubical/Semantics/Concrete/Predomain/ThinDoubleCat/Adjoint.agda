{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.Adjoint (k : Clock) where

open import Cubical.Foundations.Prelude

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Identity k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Compose k
open import Semantics.Concrete.Predomain.ThinDoubleCat.NatTrans.Base k

private
  variable
    ℓ : Level
    ℓob₁ ℓv₁ ℓh₁ ℓsq₁ ℓ≈₁ : Level
    ℓob₂ ℓv₂ ℓh₂ ℓsq₂ ℓ≈₂ : Level
    ℓob₃ ℓv₃ ℓh₃ ℓsq₃ ℓ≈₃ : Level
    l : Laxity
 
open ThinDoubleCat

module UnitCounit
  {C : ThinDoubleCat ℓob₁ ℓv₁ ℓh₁ ℓsq₁ ℓ≈₁}
  {D : ThinDoubleCat ℓob₂ ℓv₂ ℓh₂ ℓsq₂ ℓ≈₂}
  (F : FunctorWithLaxity l C D) (G : FunctorWithLaxity l D C)
  where

  private
    ℓ₁ : Level
    ℓ₁ = ℓ-max (ℓ-max ℓob₁ ℓv₁) (ℓ-max ℓh₁ ℓsq₁)

    ℓ₂ : Level
    ℓ₂ = ℓ-max (ℓ-max ℓob₂ ℓv₂) (ℓ-max ℓh₂ ℓsq₂)

    module C = ThinDoubleCat C
    module D = ThinDoubleCat D
    module F = FunctorWithLaxity F
    module G = FunctorWithLaxity G


  record TriangleIdentities
    (η : 𝟙⟨ C ⟩ ⇒ (G ∘F F))
    (ε : (F ∘F G) ⇒ 𝟙⟨ D ⟩)
    : Type (ℓ-max (ℓ-max ℓob₁ ℓv₁) (ℓ-max ℓob₂ ℓv₂)) where

{-
    Fη : ∀ c → D [ F ⟅ c ⟆ , F ⟅ G ⟅ F ⟅ c ⟆ ⟆ ⟆ ]v
    Fη c = subst2
      (λ p q → D [ F ⟅ p ⟆ , F ⟅ q ⟆ ]v)
      (Id-obj l c) (∘F-obj l F G c)
      (F ⟪ η ⟦ c ⟧ ⟫v)

    εF : ∀ c → D [ F ⟅ G ⟅ F ⟅ c ⟆ ⟆ ⟆ , F ⟅ c ⟆ ]v
    εF c = subst2
      (λ p q → D [ p , q ]v)
      (∘F-obj l G F _) (Id-obj l _)
      (ε ⟦ F ⟅ c ⟆ ⟧)

    ηG : ∀ d → C [ G ⟅ d ⟆ , G ⟅ F ⟅ G ⟅ d ⟆ ⟆ ⟆ ]v
    ηG d = subst2 (λ p q → C [ p , q ]v)
      (Id-obj l _) (∘F-obj l F G _)
      (η ⟦ G ⟅ d ⟆ ⟧)

    Gε : ∀ d → C [ G ⟅ F ⟅ G ⟅ d ⟆ ⟆ ⟆ , G ⟅ d ⟆ ]v
    Gε d = subst2 (λ p q → C [ G ⟅ p ⟆ , G ⟅ q ⟆ ]v)
      (∘F-obj l G F d) (Id-obj l d)
      (G ⟪ ε ⟦ d ⟧ ⟫v)

-- F c --> F (Id c) --> F (GF c) --> F (G (F c)) --> FG (F c) --> Id (F c) --> F c

    field
      Δ₁ : ∀ c → (Fη c) ⋆⟨ D ⟩v (εF c) ≡ D .idV {F ⟅ c ⟆}      
      Δ₂ : ∀ d → (ηG d) ⋆⟨ C ⟩v (Gε d) ≡ C .idV {G ⟅ d ⟆}
-}

    field
      Δ₁ : ∀ c → (F ⟪ η ⟦ c ⟧ ⟫v) ⋆⟨ D ⟩v (ε ⟦ F ⟅ c ⟆ ⟧) ≡ D .idV {F ⟅ c ⟆}
      Δ₂ : ∀ d → (η ⟦ G ⟅ d ⟆ ⟧) ⋆⟨ C ⟩v (G ⟪ ε ⟦ d ⟧ ⟫v) ≡ C .idV {G ⟅ d ⟆}
      

  -- Unit-counit definition of adjunction F ⊣ G
  record _⊣_ : Type (ℓ-max ℓ₁ ℓ₂) where

    field
      -- unit
      η : 𝟙⟨ C ⟩ ⇒ (G ∘F F)

      -- counit
      ε : (F ∘F G) ⇒ 𝟙⟨ D ⟩

      -- triangle identities
      triangleIdentities : TriangleIdentities η ε

      -- Note: there is no additional condition relating to
      -- bisimilarity of morphisms. The fact that the morphisms η/ε
      -- need to be monotone/bisim-preserving is built-into the fact
      -- that they are morphisisms in the category.
     

    open TriangleIdentities triangleIdentities public



-- Going from the unit-counit definition to the hom-bijection
-- definition.
--
-- What about a higher-order notion bisimilarity preservation, as
-- required in the hom-bijection defintion? Suppose f ≈ g : c → Ud. We
-- need to show that f⁺ ≈ g⁺ : Fc ⊸ d. We have
--
--      Ff        ε_d
--  Fc ----o FUd ----o d
--
--      ≈          ≈
--
--      Fg        ε_d
--  Fc ----o FUd ----o d
