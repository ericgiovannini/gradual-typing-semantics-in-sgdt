{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ErrorDomain.Square (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat

open import Cubical.HITs.PropositionalTruncation renaming (rec to PTrec)


open import Common.Common
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.SimpleErrorDomain k
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions renaming (ℕ to NatP)
  renaming (module Clocked to ClockedConstructions)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Combinators
open import Semantics.Concrete.Predomain.SquareOpaque

open import Semantics.Concrete.Predomain.ErrorDomain k




private
  variable
    ℓ ℓ'  : Level
    ℓ≤ ℓ≈ : Level
    --
    ℓA  ℓ≤A  ℓ≈A     : Level
    ℓA' ℓ≤A' ℓ≈A'    : Level
    ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  : Level
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' : Level
    ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  : Level
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' : Level
    ℓc               : Level
    ℓcᵢ ℓcₒ          : Level
    --
    ℓB  ℓ≤B  ℓ≈B     : Level
    ℓB' ℓ≤B' ℓ≈B'    : Level
    ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ  : Level
    ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ' : Level
    ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ  : Level
    ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ' : Level
    ℓd               : Level
    ℓdᵢ ℓdₒ          : Level
    --
    ℓB₁   ℓ≤B₁   ℓ≈B₁   : Level
    ℓB₁'  ℓ≤B₁'  ℓ≈B₁'  : Level
    ℓB₂   ℓ≤B₂   ℓ≈B₂   : Level
    ℓB₂'  ℓ≤B₂'  ℓ≈B₂'  : Level
    ℓB₃   ℓ≤B₃   ℓ≈B₃   : Level
    ℓB₃'  ℓ≤B₃'  ℓ≈B₃'  : Level
    ℓB₄   ℓ≤B₄   ℓ≈B₄   : Level
    ℓd₁ ℓd₂ ℓd₃ ℓd' : Level

    ℓA₁   ℓ≤A₁   ℓ≈A₁   : Level
    ℓA₂   ℓ≤A₂   ℓ≈A₂   : Level
    ℓA₃   ℓ≤A₃   ℓ≈A₃   : Level
    ℓc' : Level

    ℓBᵢ₁  ℓ≤Bᵢ₁  ℓ≈Bᵢ₁  : Level
    ℓBₒ₁  ℓ≤Bₒ₁  ℓ≈Bₒ₁  : Level
    ℓBᵢ₂  ℓ≤Bᵢ₂  ℓ≈Bᵢ₂  : Level
    ℓBₒ₂  ℓ≤Bₒ₂  ℓ≈Bₒ₂  : Level
    ℓBᵢ₃  ℓ≤Bᵢ₃  ℓ≈Bᵢ₃  : Level
    ℓBₒ₃  ℓ≤Bₒ₃  ℓ≈Bₒ₃  : Level
    ℓdᵢ₁ ℓdₒ₁ ℓdᵢ₂ ℓdₒ₂ : Level



private
  ▹_ : Type ℓ -> Type ℓ
  ▹ A = ▹_,_ k A
  

  ------------------------  
  -- Error domain squares
  ------------------------
opaque
  ErrorDomSq :
    {Bᵢ  : ErrorDomain ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ}
    {Bᵢ' : ErrorDomain ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ'}
    {Bₒ  : ErrorDomain ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ} 
    {Bₒ' : ErrorDomain ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ'} →
    (dᵢ  : ErrorDomRel Bᵢ Bᵢ' ℓdᵢ) →
    (dₒ  : ErrorDomRel Bₒ Bₒ' ℓdₒ) →
    (ϕ   : ErrorDomMor Bᵢ  Bₒ) →
    (ϕ'  : ErrorDomMor Bᵢ' Bₒ') →
    Type (ℓ-max (ℓ-max ℓBᵢ ℓBᵢ') (ℓ-max ℓdᵢ ℓdₒ))
  ErrorDomSq dᵢ dₒ ϕ ϕ' =
    PSq (dᵢ .ErrorDomRel.UR) (dₒ .ErrorDomRel.UR)
         (ϕ .ErrorDomMor.f) (ϕ' .ErrorDomMor.f)


opaque
  unfolding ErrorDomSq
  isPropErrorDomSq :
    {Bᵢ  : ErrorDomain ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ}
    {Bᵢ' : ErrorDomain ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ'}
    {Bₒ  : ErrorDomain ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ} 
    {Bₒ' : ErrorDomain ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ'} →
    (dᵢ  : ErrorDomRel Bᵢ Bᵢ' ℓdᵢ) →
    (dₒ  : ErrorDomRel Bₒ Bₒ' ℓdₒ) →
    (ϕ   : ErrorDomMor Bᵢ  Bₒ) →
    (ϕ'  : ErrorDomMor Bᵢ' Bₒ') →
    isProp (ErrorDomSq dᵢ dₒ ϕ ϕ')
  isPropErrorDomSq dᵢ dₒ ϕ ϕ' =
    isPropPSq (dᵢ .ErrorDomRel.UR) (dₒ .ErrorDomRel.UR)
               (ϕ .ErrorDomMor.f) (ϕ' .ErrorDomMor.f)




module HorizontalCompUMP
  {Bᵢ₁ : ErrorDomain ℓBᵢ₁ ℓ≤Bᵢ₁ ℓ≈Bᵢ₁}
  {Bᵢ₂ : ErrorDomain ℓBᵢ₂ ℓ≤Bᵢ₂ ℓ≈Bᵢ₂}
  {Bᵢ₃ : ErrorDomain ℓBᵢ₃ ℓ≤Bᵢ₃ ℓ≈Bᵢ₃}
  {Bₒ₁ : ErrorDomain ℓBₒ₁ ℓ≤Bₒ₁ ℓ≈Bₒ₁}
  {Bₒ₂ : ErrorDomain ℓBₒ₂ ℓ≤Bₒ₂ ℓ≈Bₒ₂}
  {Bₒ₃ : ErrorDomain ℓBₒ₃ ℓ≤Bₒ₃ ℓ≈Bₒ₃}
  (d  : ErrorDomRel Bᵢ₁ Bᵢ₂ ℓd)
  (d' : ErrorDomRel Bᵢ₂ Bᵢ₃ ℓd')
  (ϕ₁  : ErrorDomMor Bᵢ₁ Bₒ₁)
  (ϕ₂  : ErrorDomMor Bᵢ₂ Bₒ₂)
  (ϕ₃  : ErrorDomMor Bᵢ₃ Bₒ₃)
  {ℓS : Level} (S : ErrorDomRel Bₒ₁ Bₒ₃ ℓS)
  where

  open ErrorDomRel
  open HorizontalComp d d' public -- brings modules d and d' in scope

  module ϕ₁ = ErrorDomMor ϕ₁
  module ϕ₂ = ErrorDomMor ϕ₂
  module ϕ₃ = ErrorDomMor ϕ₃

  module S = ErrorDomRel S

  -- To construct a square whose top edge is (d ⊙ed d') and whose
  -- bottom edge is a relation S between Bₒ₁ and Bₒ₃, it suffices to
  -- construct a square whose top edge is the *normal* composition
  -- of the underlying predomain relations of d and d' and whose
  -- bottom edge is the underlying predomain relation of S.
  --
  -- In other words, the client gets to assume that there exists
  -- (truncated) some intermediate b₂ such that b₁ d b₂ and b₂ d'
  -- b₃.  If under this assumption, the client proves (ϕ₁ b₁) S (ϕ₃
  -- b₃), then we can conclude that b₁ (d ⊙ed d') b₃ implies that
  -- (ϕ₁ b₁) S (ϕ₃ b₃).
  opaque
    unfolding PSq ErrorDomSq
    ElimHorizComp :
      (PSq (d.UR ⊙ d'.UR) S.UR ϕ₁.f ϕ₃.f) →
       ErrorDomSq (d ⊙ed d') S ϕ₁ ϕ₃
      -- (b₁ d.rel b₂ × b₂ d'.rel b₃) → S.EDRel (ϕ₁.fun b₁) (ϕ₃.fun b₃)) →
      -- ∀ b₁ b₃ → HCRel b₁ b₃ → S.EDRel (ϕ₁.fun b₁) (ϕ₃.fun b₃)
    ElimHorizComp α b₁ b₃ (inj .b₁ b₂ .b₃ R₁₂ R₂₃) =
      α b₁ b₃ ∣ b₂ , R₁₂ , R₂₃ ∣₁
    ElimHorizComp α b₁ b₃' (up-closed .b₁ b₃ .b₃' b₁Rb₃ b₃≤b₃') =
      S.is-monotone (ElimHorizComp α b₁ b₃ b₁Rb₃) (ϕ₃.isMon b₃≤b₃')
    ElimHorizComp α b₁' b₃ (dn-closed .b₁' b₁ .b₃ b₁'≤b₁ b₁Rb₃) =
      S.is-antitone (ϕ₁.isMon b₁'≤b₁) (ElimHorizComp α b₁ b₃ b₁Rb₃)
    ElimHorizComp α .(B₁.℧) b₃ (pres℧ .b₃) =
      transport (sym (cong₂ S._rel_ ϕ₁.f℧ refl)) (S.R℧ (ϕ₃.fun b₃))
    ElimHorizComp α .(B₁.θ $ b₁~) .(B₃.θ $ b₃~) (presθ b₁~ b₃~ H~) =
      transport
        (sym (cong₂ S._rel_ (ϕ₁.fθ b₁~) (ϕ₃.fθ b₃~)))
        (S.Rθ
          (λ t → ϕ₁.fun (b₁~ t))
          (λ t → ϕ₃.fun (b₃~ t))
          (λ t → ElimHorizComp α (b₁~ t) (b₃~ t) (H~ t)))
      -- S.Rθ b₁~ b₃~ (λ t → ElimHorizComp H (b₁~ t) (b₃~ t) (H~ t))
    ElimHorizComp H b₁ b₃ (is-prop .b₁ .b₃ p q i) =
      S.is-prop-valued
        (ϕ₁.fun b₁) (ϕ₃.fun b₃)
        (ElimHorizComp H b₁ b₃ p) (ElimHorizComp H b₁ b₃ q) i


  -- Since the relation S is prop-valued, we can actually get away
  -- with requiring only that there is a square whose top is the
  -- **non-truncated** composition of d and d'.  That is, the client
  -- gets to assume that there is some intermediate b₂ such that b₁
  -- d b₂ and b₂ d' b₃, and this is a Σ, not an ∃, so the user can
  -- directly access the intermediate element and the proofs of
  -- relatedness.

  dd'-non-trunc : ⟨ Bᵢ₁ ⟩ → ⟨ Bᵢ₃ ⟩ → Type (ℓ-max (ℓ-max ℓBᵢ₂ ℓd) ℓd')
  dd'-non-trunc = compRel (d.UR .PRel.R) (d'.UR .PRel.R)

  EHC-convenient :
    (TwoCell dd'-non-trunc (S.UR .PRel.R) (ϕ₁.f .PMor.f) (ϕ₃.f .PMor.f)) →
     ErrorDomSq (d ⊙ed d') S ϕ₁ ϕ₃
  EHC-convenient α = ElimHorizComp α'
    where
      opaque
        unfolding PSq
        α' : PSq (d.UR ⊙ d'.UR) S.UR ϕ₁.f ϕ₃.f
        α' x z x-dd'-z =
          PTrec
            (S.is-prop-valued (ϕ₁.f $ x) (ϕ₃.f $ z))
            (λ {(y , x-d-y , y-d'-z) → α x z (y , x-d-y , y-d'-z)})
            x-dd'-z




opaque
  unfolding PSq ErrorDomSq
  sq-idB⊙d-d : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain  ℓB' ℓ≤B' ℓ≈B'} (d : ErrorDomRel B B' ℓd) →
    ErrorDomSq (idEDRel B ⊙ed d) d IdE IdE
  sq-idB⊙d-d {B = B} {B' = B'} d = EHC-convenient d (λ { x y (z , xRz , zRy) → d .ErrorDomRel.is-antitone xRz zRy })
    where
      module d = ErrorDomRel d
      open HorizontalCompUMP (idEDRel B) d IdE IdE IdE


  sq-d⊙idB'-d : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain  ℓB' ℓ≤B' ℓ≈B'} (d : ErrorDomRel B B' ℓd) →
    ErrorDomSq (d ⊙ed idEDRel B') d IdE IdE
  sq-d⊙idB'-d {B = B} {B' = B'} d = EHC-convenient d (λ { x y (z , xRy , zRy) → d .ErrorDomRel.is-monotone xRy zRy })
    where
      module d = ErrorDomRel d
      open HorizontalCompUMP d (idEDRel B') IdE IdE IdE


  sq-d-idB⊙d : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain  ℓB' ℓ≤B' ℓ≈B'} (d : ErrorDomRel B B' ℓd) →
    ErrorDomSq d (idEDRel B ⊙ed d) IdE IdE
  sq-d-idB⊙d {B = B} d x y xRy = HorizontalComp.inj x x y (B.is-refl x) xRy
   where module B = ErrorDomainStr (B .snd)

  sq-d-d⊙idB' : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain  ℓB' ℓ≤B' ℓ≈B'} (d : ErrorDomRel B B' ℓd) →
    ErrorDomSq d (d ⊙ed idEDRel B') IdE IdE
  sq-d-d⊙idB' {B' = B'} d x y xRy = HorizontalComp.inj x y y xRy (B'.is-refl y)
     where module B' = ErrorDomainStr (B' .snd)





  -- Identity and composition of squares
  --------------------------------------


opaque
  unfolding PSq ErrorDomSq

  -- "Horizontal" identity squares.

  ED-IdSqH :
    {Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ}
    {Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ} →
    (ϕ : ErrorDomMor Bᵢ Bₒ) →
    ErrorDomSq (idEDRel Bᵢ) (idEDRel Bₒ) ϕ ϕ
  ED-IdSqH ϕ = Predom-IdSqH (ϕ .ErrorDomMor.f)

  -- "Vertical" identity squares.

  ED-IdSqV :
    {B : ErrorDomain ℓB ℓ≤B ℓ≈B}
    {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
    (d : ErrorDomRel B B' ℓc) →
    ErrorDomSq d d IdE IdE
  ED-IdSqV c x y xRy = xRy


  ED-CompSqV :
    {B₁  : ErrorDomain ℓB₁  ℓ≤B₁  ℓ≈B₁ }
    {B₁' : ErrorDomain ℓB₁' ℓ≤B₁' ℓ≈B₁'}
    {B₂  : ErrorDomain ℓB₂  ℓ≤B₂  ℓ≈B₂ }
    {B₂' : ErrorDomain ℓB₂' ℓ≤B₂' ℓ≈B₂'}
    {B₃  : ErrorDomain ℓB₃  ℓ≤B₃  ℓ≈B₃ }
    {B₃' : ErrorDomain ℓB₃' ℓ≤B₃' ℓ≈B₃'}
    {d₁  : ErrorDomRel B₁ B₁' ℓd₁}
    {d₂  : ErrorDomRel B₂ B₂' ℓd₂}
    {d₃  : ErrorDomRel B₃ B₃' ℓd₃}
    {ϕ₁  : ErrorDomMor B₁  B₂ }
    {ϕ₁' : ErrorDomMor B₁' B₂'}
    {ϕ₂  : ErrorDomMor B₂  B₃ }
    {ϕ₂' : ErrorDomMor B₂' B₃'} →
    ErrorDomSq d₁ d₂ ϕ₁ ϕ₁' →
    ErrorDomSq d₂ d₃ ϕ₂ ϕ₂' →
    ErrorDomSq d₁ d₃ (ϕ₂ ∘ed ϕ₁) (ϕ₂' ∘ed ϕ₁')
  ED-CompSqV {d₁ = d₁} {d₂ = d₂} {d₃ = d₃}
             {ϕ₁ = ϕ₁} {ϕ₁' = ϕ₁'} {ϕ₂ = ϕ₂} {ϕ₂' = ϕ₂'} α₁ α₂ =
    CompSqV {c₁ = d₁ .ErrorDomRel.UR} {c₂ = d₂ .ErrorDomRel.UR}
            {c₃ = d₃ .ErrorDomRel.UR} {f₁ = ϕ₁ .ErrorDomMor.f}
            {g₁ = ϕ₁' .ErrorDomMor.f} {f₂ = ϕ₂ .ErrorDomMor.f}
            {g₂ = ϕ₂' .ErrorDomMor.f} α₁ α₂


  -- _∘esqv_ = ED-CompSqV
  -- infixl 20 _∘esqv_


  ED-CompSqV-iterate :
    {B₁ : ErrorDomain ℓB₁  ℓ≤B₁  ℓ≈B₁}
    {B₂ : ErrorDomain ℓB₂  ℓ≤B₂  ℓ≈B₂}
    (d : ErrorDomRel B₁ B₂ ℓd) →
    (ϕ : ErrorDomMor B₁ B₁) →
    (ϕ' : ErrorDomMor B₂ B₂) →
    (ErrorDomSq d d ϕ ϕ') →
    (n : ℕ) → ErrorDomSq d d (ϕ ^ed n) (ϕ' ^ed n)
  ED-CompSqV-iterate d ϕ ϕ' α zero = ED-IdSqV d
  ED-CompSqV-iterate d ϕ ϕ' α (suc n) =
    ED-CompSqV {d₁ = d} {d₂ = d} {d₃ = d}
          {ϕ₁ = ϕ ^ed n} {ϕ₁' = ϕ' ^ed n} {ϕ₂ = ϕ} {ϕ₂' = ϕ'}
          (ED-CompSqV-iterate d ϕ ϕ' α n) α


opaque
  unfolding PSq ErrorDomSq
  ED-CompSqH :
    {Bᵢ₁ : ErrorDomain ℓBᵢ₁ ℓ≤Bᵢ₁ ℓ≈Bᵢ₁}
    {Bᵢ₂ : ErrorDomain ℓBᵢ₂ ℓ≤Bᵢ₂ ℓ≈Bᵢ₂}
    {Bᵢ₃ : ErrorDomain ℓBᵢ₃ ℓ≤Bᵢ₃ ℓ≈Bᵢ₃}
    {Bₒ₁ : ErrorDomain ℓBₒ₁ ℓ≤Bₒ₁ ℓ≈Bₒ₁}
    {Bₒ₂ : ErrorDomain ℓBₒ₂ ℓ≤Bₒ₂ ℓ≈Bₒ₂}
    {Bₒ₃ : ErrorDomain ℓBₒ₃ ℓ≤Bₒ₃ ℓ≈Bₒ₃}
    {dᵢ₁ : ErrorDomRel Bᵢ₁ Bᵢ₂ ℓdᵢ₁}
    {dᵢ₂ : ErrorDomRel Bᵢ₂ Bᵢ₃ ℓdᵢ₂}
    {dₒ₁ : ErrorDomRel Bₒ₁ Bₒ₂ ℓdₒ₁}
    {dₒ₂ : ErrorDomRel Bₒ₂ Bₒ₃ ℓdₒ₂}
    {ϕ₁  : ErrorDomMor Bᵢ₁ Bₒ₁}
    {ϕ₂  : ErrorDomMor Bᵢ₂ Bₒ₂}
    {ϕ₃  : ErrorDomMor Bᵢ₃ Bₒ₃} →
    ErrorDomSq dᵢ₁ dₒ₁ ϕ₁ ϕ₂ →
    ErrorDomSq dᵢ₂ dₒ₂ ϕ₂ ϕ₃ →
    ErrorDomSq (dᵢ₁ ⊙ed dᵢ₂) (dₒ₁ ⊙ed dₒ₂) ϕ₁ ϕ₃
  ED-CompSqH
    {dᵢ₁ = dᵢ₁} {dᵢ₂ = dᵢ₂} {dₒ₁ = dₒ₁} {dₒ₂ = dₒ₂}
    {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {ϕ₃ = ϕ₃} α β = EHC-convenient α'
      where
        open HorizontalCompUMP dᵢ₁ dᵢ₂ ϕ₁ ϕ₂ ϕ₃ (dₒ₁ ⊙ed dₒ₂)
        module Comp-dₒ₁-dₒ₂ = HorizontalComp dₒ₁ dₒ₂
        α' : TwoCell dd'-non-trunc (S.UR .PRel.R) (ϕ₁.f .PMor.f) (ϕ₃.f .PMor.f)
        α' x z (y , x-dᵢ₁-y , y-dᵢ₂-z) =
          -- we use the inj constructor of the free horizontal composition
          Comp-dₒ₁-dₒ₂.inj (ϕ₁.f $ x) (ϕ₂.f $ y) (ϕ₃.f $ z) (α x y x-dᵢ₁-y) (β y z y-dᵢ₂-z)


  -- _∘esqh_ = ED-CompSqH
  -- infixl 20 _∘esqh_


  U-sq :
    {Bᵢ  : ErrorDomain ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ}
    {Bᵢ' : ErrorDomain ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ'}
    {Bₒ  : ErrorDomain ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ} 
    {Bₒ' : ErrorDomain ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ'} →
    (dᵢ  : ErrorDomRel Bᵢ Bᵢ' ℓdᵢ) →
    (dₒ  : ErrorDomRel Bₒ Bₒ' ℓdₒ) →
    (ϕ   : ErrorDomMor Bᵢ  Bₒ) →
    (ϕ'  : ErrorDomMor Bᵢ' Bₒ') →
    ErrorDomSq dᵢ dₒ ϕ ϕ' →
    PSq (U-rel dᵢ) (U-rel dₒ) (U-mor ϕ) (U-mor ϕ')
  U-sq dᵢ dₒ f g sq = sq


  -- TODO lax functoriality of U with respect to relational composition





  ---------------------------
  -- Action of ⟶ on squares
  
module _
  {Aᵢ  : Predomain ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ}
  {Aᵢ' : Predomain ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
  {Aₒ  : Predomain ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ} 
  {Aₒ' : Predomain ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'}
  {Bᵢ  : ErrorDomain ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ}
  {Bᵢ' : ErrorDomain ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ'}
  {Bₒ  : ErrorDomain ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ} 
  {Bₒ' : ErrorDomain ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ'}
  {cᵢ  : PRel Aᵢ Aᵢ' ℓcᵢ}
  {cₒ  : PRel Aₒ Aₒ' ℓcₒ}
  {f   : PMor Aₒ  Aᵢ}   -- Notice the flip in direction!
  {g   : PMor Aₒ' Aᵢ'}  -- Notice the flip in direction!
  {dᵢ  : ErrorDomRel Bᵢ Bᵢ' ℓdᵢ}
  {dₒ  : ErrorDomRel Bₒ Bₒ' ℓdₒ}
  {ϕ   : ErrorDomMor Bᵢ  Bₒ} 
  {ϕ'  : ErrorDomMor Bᵢ' Bₒ'} where

  opaque
    unfolding PSq ErrorDomSq
    _⟶sq_ : PSq cₒ cᵢ f g → ErrorDomSq dᵢ dₒ ϕ ϕ' →
      ErrorDomSq (cᵢ ⟶rel dᵢ) (cₒ ⟶rel dₒ) (f ⟶mor ϕ) (g ⟶mor ϕ')
    α ⟶sq β =
      _==>psq_ {cᵢ₁ = cᵢ} {cₒ₁ = cₒ} {f₁ = f} {g₁ = g}
               {cᵢ₂ = dᵢ .ErrorDomRel.UR} {cₒ₂ = dₒ .ErrorDomRel.UR}
               {f₂ = ϕ .ErrorDomMor.f} {g₂ = ϕ' .ErrorDomMor.f} α β
     

    sqArrowId₁ : ∀ {A : Predomain ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
      ErrorDomSq ((idPRel A) ⟶rel (idEDRel B)) (idEDRel (A ⟶ob B)) IdE IdE
    sqArrowId₁ {A = A} f g f≤g x = f≤g x x (A .snd .PredomainStr.is-refl x)

    sqArrowId₂ : ∀ {A : Predomain ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
      ErrorDomSq  (idEDRel (A ⟶ob B)) ((idPRel A) ⟶rel (idEDRel B)) IdE IdE
    sqArrowId₂ f g f≤g x y x≤y = ≤mon→≤mon-het f g f≤g x y x≤y
