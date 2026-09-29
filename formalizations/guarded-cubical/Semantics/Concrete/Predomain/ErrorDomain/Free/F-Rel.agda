{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.Predomain.ErrorDomain.Free.F-Rel (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Relation.Binary.Base
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.HITs.PropositionalTruncation hiding (map) renaming (rec to PTrec)
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Empty
open import Cubical.Foundations.HLevels

open import Common.Common
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions hiding (𝔽)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Combinators
open import Semantics.Concrete.Predomain.SquareOpaque

open import Semantics.Concrete.Predomain.SimpleErrorDomain k
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.ErrorDomain.Square k
open import Semantics.Concrete.LockStepErrorOrdering k
open import Semantics.Concrete.WeakBisimilarity k

open import Semantics.Concrete.Predomain.Error
open import Semantics.Concrete.Predomain.Ext k

open import Semantics.Concrete.Predomain.ErrorDomain.Free.F-Object k



private
  variable
    ℓ ℓ' : Level
    ℓA  ℓ≤A  ℓ≈A  : Level
    ℓA' ℓ≤A' ℓ≈A' : Level
    ℓB  ℓ≤B  ℓ≈B  : Level
    ℓB' ℓ≤B' ℓ≈B' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ : Level
    ℓA₂ ℓ≤A₂ ℓ≈A₂ : Level
    ℓA₃ ℓ≤A₃ ℓ≈A₃ : Level
    ℓΓ ℓ≤Γ ℓ≈Γ : Level
    ℓC : Level
    ℓc ℓc' ℓd ℓR : Level
    ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  : Level
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' : Level
    ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  : Level
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' : Level
    ℓcᵢ ℓcₒ : Level
   


-----------------------------------------
-- 3. Action of F on horizontal morphisms
-----------------------------------------

module F-rel
  {A  : Predomain ℓA  ℓ≤A  ℓ≈A}
  {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  (c : PRel A A' ℓc) where

  private
    module A  = PredomainStr (A  .snd)
    module A' = PredomainStr (A' .snd)
    module c = PRel c

  open F-ob
  open ErrorDomRel
  open PRel

  private
    module Lc = LiftOrd ⟨ A ⟩ ⟨ A' ⟩ (c .PRel.R)
  open Lc.Properties

  opaque
    unfolding F-ob
    
    F-rel : ErrorDomRel (F-ob A) (F-ob A') (ℓ-max (ℓ-max ℓA ℓA') ℓc)
    F-rel .UR .R = Lc._⊑_
    F-rel .UR .is-prop-valued = isProp⊑
    F-rel .UR .is-antitone =
      DownwardClosed.⊑-downward ⟨ A ⟩ ⟨ A' ⟩ A._≤_ c.R (λ p q r → c.is-antitone) _ _ _
    F-rel .UR .is-monotone =
      UpwardClosed.⊑-upward ⟨ A ⟩ ⟨ A' ⟩ A'._≤_ c.R (λ p q r → c.is-monotone) _ _ _
    F-rel .R℧ = Lc.Properties.℧⊥
    F-rel .Rθ la~ la'~ = θ-monotone


open F-rel


-- The action of F on relations preserves identity.
opaque
  unfolding F-rel
  F-rel-presId : ∀ {A : Predomain ℓA ℓ≤A ℓ≈A} →
    F-rel (idPRel A) ≡ idEDRel (F-ob.F-ob A)
  F-rel-presId = eqEDRel _ _ refl -- both have the same underlying relation

-- Lax functoriality of F (i.e. there is a square from (F c ⊙ F c') to F (c ⊙ c'))
module F-rel-lax-functoriality
  {A₁ : Predomain ℓA₁  ℓ≤A₁  ℓ≈A₁}
  {A₂ : Predomain ℓA₂  ℓ≤A₂  ℓ≈A₂}
  {A₃ : Predomain ℓA₃  ℓ≤A₃  ℓ≈A₃}
  (c : PRel A₁ A₂ ℓc) (c' : PRel A₂ A₃ ℓc') where

  open F-ob
  open F-rel
  open HetTransitivity ⟨ A₁ ⟩ ⟨ A₂ ⟩ ⟨ A₃ ⟩ (c .PRel.R) (c' .PRel.R)

  open HorizontalComp
  open HorizontalCompUMP (F-rel c) (F-rel c') IdE IdE IdE (F-rel (c ⊙ c'))

  opaque
    unfolding F-ob F-rel PSq ErrorDomSq
    lax-functoriality : ErrorDomSq (F-rel c ⊙ed F-rel c') (F-rel (c ⊙ c')) IdE IdE
    lax-functoriality = ElimHorizComp α
      where
        -- By the universal property of the free composition, it
        -- suffices to build a predomain square whose top is the *usual*
        -- composition of the underlying relations:
        α : PSq ((U-rel (F-rel c)) ⊙ (U-rel (F-rel c')))
                 (U-rel (F-rel (c ⊙ c')))
                 Id Id
        α lx lz lx-LcLc'-lz =
          -- We use the fact that the lock-step error ordering is
          -- "heterogeneously transitive", i.e. if lx LR ly and ly LS lz,
          -- then lx L(R ∘ S) lz.
          PTrec
            (PRel.is-prop-valued (U-rel (F-rel (c ⊙ c'))) lx lz)
            (λ {(ly , lx-Lc-ly , ly-Lc'-lz) → het-trans lx ly lz lx-Lc-ly ly-Lc'-lz})
            lx-LcLc'-lz
