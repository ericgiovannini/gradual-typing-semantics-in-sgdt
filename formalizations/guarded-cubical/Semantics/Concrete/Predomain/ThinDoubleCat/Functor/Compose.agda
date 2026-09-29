{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Compose (k : Clock) where

open import Cubical.Foundations.Prelude

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Base k

private
  variable
    ℓ : Level
    ℓob₁ ℓv₁ ℓh₁ ℓsq₁ ℓ≈₁ : Level
    ℓob₂ ℓv₂ ℓh₂ ℓsq₂ ℓ≈₂ : Level
    ℓob₃ ℓv₃ ℓh₃ ℓsq₃ ℓ≈₃ : Level
 
open ThinDoubleCat

module _
  {C : ThinDoubleCat ℓob₁ ℓv₁ ℓh₁ ℓsq₁ ℓ≈₁}
  {D : ThinDoubleCat ℓob₂ ℓv₂ ℓh₂ ℓsq₂ ℓ≈₂}
  {E : ThinDoubleCat ℓob₃ ℓv₃ ℓh₃ ℓsq₃ ℓ≈₃}
  where

  private
    module C = ThinDoubleCat C
    module D = ThinDoubleCat D
    module E = ThinDoubleCat E

  module _
    (G : FunctorBase D E)
    (F : FunctorBase C D)
    where

   private
     module F = FunctorBase F
     module G = FunctorBase G
     open FunctorBase

   funcCompBase : FunctorBase C E
   funcCompBase .F-ob x = G.⟅ F.⟅ x ⟆ ⟆
   funcCompBase .F-homV f = G.⟪ F.⟪ f ⟫v ⟫v
   funcCompBase .F-idV = cong (G.⟪_⟫v) (F .F-idV) ∙ G .F-idV
   funcCompBase .F-seqV f g = cong (G.⟪_⟫v) (F .F-seqV _ _) ∙ G .F-seqV _ _
   funcCompBase .F-homH c = G.⟪ F.⟪ c ⟫h ⟫h
   funcCompBase .F-idH = cong (G.⟪_⟫h) (F .F-idH) ∙ G .F-idH
   -- funcComp .F-seqH c c' = {!!}
   funcCompBase .F-sq {xᵢ} {yᵢ} {xₒ} {yₒ} {cᵢ} {cₒ} {f} {g} sq = G.⟪ F.⟪ sq ⟫sq ⟫sq
   funcCompBase .F-bisim f g f≈g = G .F-bisim (F.⟪ f ⟫v) (F.⟪ g ⟫v) (F .F-bisim f g f≈g)

  open FunctorWithLaxity

  _∘F_ : {l : Laxity} → FunctorWithLaxity l D E → FunctorWithLaxity l C D → FunctorWithLaxity l C E
  _∘F_ G F .base = funcCompBase (G .base) (F .base)
  _∘F_ {strict} G F .F-seqH r r' = {!cong (G ⟪_⟫h) (F .F-seqH _ _) ∙ G .F-seqH _ _!}
  _∘F_ {lax} G F .F-seqH r r' = {!!}
  _∘F_ {oplax} G F .F-seqH r r' = {!!}

{-
  module _
    (G : FunctorWithLaxity strict D E)
    (F : FunctorWithLaxity strict C D ) where

    private
      module G = FunctorWithLaxity G
      module F = FunctorWithLaxity F

    open FunctorWithLaxity

    strictFuncComp : FunctorWithLaxity strict C E
    strictFuncComp .base = funcCompBase G.base F.base
    strictFuncComp .F-seqH c c' = lift {!!}


  module _
    (G : FunctorWithLaxity lax D E)
    (F : FunctorWithLaxity lax C D ) where

    private
      module G = FunctorWithLaxity G
      module F = FunctorWithLaxity F

    open FunctorWithLaxity

    laxFuncComp : FunctorWithLaxity lax C E
    laxFuncComp .base = funcCompBase G.base F.base
    laxFuncComp .F-seqH c c' = lift {!!}


  module _
    (G : FunctorWithLaxity oplax D E)
    (F : FunctorWithLaxity oplax C D ) where

    private
      module G = FunctorWithLaxity G
      module F = FunctorWithLaxity F

    open FunctorWithLaxity

    oplaxFuncComp : FunctorWithLaxity oplax C E
    oplaxFuncComp .base = funcCompBase G.base F.base
    oplaxFuncComp .F-seqH c c' = lift {!!}


  infixr 30 _∘F_
  
  _∘F_ : {l : Laxity} → FunctorWithLaxity l D E → FunctorWithLaxity l C D → FunctorWithLaxity l C E
  _∘F_ {strict} = strictFuncComp
  _∘F_ {lax} = laxFuncComp
  _∘F_ {oplax} = oplaxFuncComp


  ∘F-obj : ∀ (l : Laxity)
    → (F : FunctorWithLaxity l C D)
    → (G : FunctorWithLaxity l D E)
    → (x : C .ob)
    → (G ∘F F) ⟅ x ⟆ ≡ G ⟅ F ⟅ x ⟆ ⟆
  ∘F-obj strict F G x = refl
  ∘F-obj lax F G x = refl
  ∘F-obj oplax F G x = refl

-}
