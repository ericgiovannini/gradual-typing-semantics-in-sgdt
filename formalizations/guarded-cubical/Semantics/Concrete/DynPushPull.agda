{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}
open import Common.Later

module Semantics.Concrete.DynPushPull (k : Clock) where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.Instances.Trivial as Trivial
open import Cubical.Algebra.Monoid.FreeProduct as FP hiding (elimFact)
open import Cubical.Data.Nat hiding (_·_ ; ℕ)

import Semantics.Concrete.DoublePoset.Constructions as PB
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.PBSquare
import Semantics.Concrete.DoublePoset.DblPosetCombinators as DPC
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.MonadRelationalResults k
open import Semantics.Concrete.DoublePoset.MonadCombinators k

open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Predomains.Perturbations k
open import Semantics.Concrete.Dyn k
import Semantics.Concrete.DynPerturb k as DP

open import Semantics.Concrete.Types k as Types
open import Semantics.Concrete.Perturbation.Relation.Base k

open PB using (_×dp_)
open ValTypeStr
open MapCombinator

private variable
  ℓ : Level
  A : Type ℓ

private
  ▹_ : {ℓ : Level} → Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A



open DynDef {ℓ-zero}
open LiftPredomain
open Guarded (next Dyn)
module Rel = Relations

open F-ob
open F-mor
open F-rel

-- The push-pull property for the three relations inj-nat, inj-prod,
-- and inj-arr:


-----------
-- inj-nat
-----------

inj-nat : VRelPP ℕ dyn' ℓ-zero
inj-nat .fst = Rel.inj-nat

-- Push
inj-nat .snd .fst = Trivial.rec , refl

-- Pull
-- δ : Ptb dyn
--
inj-nat .snd .snd = DP.elimFact _ _ (FP.elimFact _ _
  -- Left ×
  (corecVFact2 _ _ _ Trivial.corec (λ pD → λ { n .(nat _) (⊑-nat eq) → ⊑-nat eq}))
  -- Right ×
  (corecVFact2 _ _ _ Trivial.corec (λ pD → λ { n .(nat _) (⊑-nat eq) → ⊑-nat eq})))
  (FP.elimFact _ _
    -- U
    (elimNat _ _ ((tt , let sq : Σ[ pD ∈ DP.|PtbD| ] (PBSq Rel.inj-nat Rel.inj-nat Id (ι (dyn' .snd) pD))
                            sq = (DP.inj-arr-U .fst 1 , λ { n .(nat _) (⊑-nat eq) → ⊑-nat eq})
                        in sq) , refl))
    (FP.elimFact _ _
    -- domain
    (corecVFact2 _ _ _ Trivial.corec λ pD → λ { n .(nat _) (⊑-nat eq) → ⊑-nat eq})
    (FP.elimFact _ _
      -- F
      (elimNat _ _ ((tt , let sq : Σ[ pD ∈ DP.|PtbD| ] (PBSq Rel.inj-nat Rel.inj-nat Id (ι (dyn' .snd) pD))
                              sq = (DP.inj-arr-F .fst 1 , λ { n .(nat _) (⊑-nat eq) → ⊑-nat eq})
                          in sq) , refl))
      -- codomain
      (corecVFact2 _ _ _ Trivial.corec λ pD → λ { n .(nat _) (⊑-nat eq) → ⊑-nat eq}))))


----------------------------------------------------------------------------------------

-------------
-- inj-times
-------------


inj-times : VRelPP (dyn' × dyn') dyn' ℓ-zero
inj-times .fst = Rel.inj-times

-- Push
inj-times .snd .fst = FP.elimSection _
  (corecVFact1 _ _ _ DP.inj-times-left λ pD → λ { (d₁ , d₂) .(prod _ _) (⊑-prod p q) →
    ⊑-prod (PBMor.isMon (dyn' .snd .interpV .fst pD .fst) p) q})
  (corecVFact1 _ _ _ DP.inj-times-right λ pD → λ { (d₁ , d₂) .(prod _ _) (⊑-prod p q) →
    ⊑-prod p (Predom-IdSqH (ι (dyn' .snd) pD) _ _ q)})


-- Pull
inj-times .snd .snd = DP.elimFact _ _
  (FP.elimFact _ _
    -- Left ×
    (corecVFact2 _ _ _ i₁ λ pD → λ { (d₁ , d₂) .(prod _ _) (⊑-prod p q) →
      ⊑-prod (Predom-IdSqH (ι (dyn' .snd) pD) _ _ p) q})

    -- Right ×
    (corecVFact2 _ _ _ i₂ λ pD → λ { (d₁ , d₂) .(prod _ _) (⊑-prod p q) →
      ⊑-prod p (Predom-IdSqH (ι (dyn' .snd) pD) _ _ q)}))
  (FP.elimFact _ _
    -- U
    (elimNat _ _ ((FP.ε , (let sq : Σ[ pD ∈ DP.|PtbD| ] (PBSq Rel.inj-times Rel.inj-times Id (ι (dyn' .snd) pD))
                               sq = (DP.inj-arr-U .fst 1 , λ { (d₁ , d₂) .(prod _ _) (⊑-prod p q) → ⊑-prod p q})
                            in sq)) , refl))
    (FP.elimFact _ _

    -- domain
    (corecVFact2 _ _ _ ε-hom λ pD → λ { (d₁ , d₂) .(prod _ _) (⊑-prod p q) → ⊑-prod p q})
    (FP.elimFact _ _

    -- F
    (elimNat _ _ ((FP.ε , (let sq : Σ[ pD ∈ DP.|PtbD| ] (PBSq Rel.inj-times Rel.inj-times Id (ι (dyn' .snd) pD))
                               sq = (DP.inj-arr-F .fst 1 , λ { (d₁ , d₂) .(prod _ _) (⊑-prod p q) → ⊑-prod p q})
                            in sq)) , refl))

    -- codomain
    (corecVFact2 _ _ _ ε-hom λ pD → λ { (d₁ , d₂) .(prod _ _) (⊑-prod p q) → ⊑-prod p q}))))


----------------------------------------------------------------------------------------

-----------
-- inj-arr
-----------


inj-arr : VRelPP (U (dyn ⟶ F dyn)) dyn' ℓ-zero
inj-arr .fst = Rel.inj-arr

-- Push
inj-arr .snd .fst = FP.elimSection _

  -- U
  (elimNat _ _ ((FP.⟦ 1 ⟧₁ , (let sq : Σ[ pD ∈ DP.|PtbD| ] (PBSq Rel.inj-arr Rel.inj-arr (U-mor (Id ⟶mor δ*)) (ι (dyn' .snd) pD))
                                  sq = (DP.inj-arr-U .fst 1 , λ { f .(fun _) (⊑-fun p~) →
                                    ⊑-fun (λ t d → ErrorDomMor.isMon δ* (p~ t d))})
                               in {!sq!})) , refl))
  (FP.elimFact _ _

  -- domain
  (corecVFact1 _ _ _ DP.inj-arr-dom λ pD → λ { f .(fun _) (⊑-fun {f~ = .(next f)} {g~ = g~} p~) →
    ⊑-fun (λ t d → (p~ t) (ι (dyn .snd) pD $ d)) }) 
  (FP.elimFact _ _

  -- F
  (elimNat _ _ ((FP.⟦ ⟦ ⟦ 1 ⟧₁ ⟧₂ ⟧₂ , (let sq : Σ[ pD ∈ DP.|PtbD| ] (PBSq Rel.inj-arr Rel.inj-arr (U-mor (Id ⟶mor δ*)) (ι (dyn' .snd) pD))
                                            sq = (DP.inj-arr-F .fst 1 , λ { f .(fun _) (⊑-fun p~) →
                                             ⊑-fun (λ t d → ErrorDomMor.isMon δ* (p~ t d))})
                                       in {!!})) , refl))

  -- codomain
  (corecVFact1 _ _ _ DP.inj-arr-cod λ pD → λ { f .(fun _) (⊑-fun p~) →
    ⊑-fun (λ t d → PBMor.isMon (U-mor (F-mor (ι (dyn .snd) pD))) (p~ t d))})))


-- Pull
inj-arr .snd .snd = DP.elimFact _ _
  (FP.elimFact _ _
    -- Left ×
    (corecVFact2 _ _ _ ε-hom λ pD → λ { f .(fun _) (⊑-fun p~) → ⊑-fun p~ })

    -- Right ×
    (corecVFact2 _ _ _ ε-hom λ pD → λ { f .(fun _) (⊑-fun p~) → ⊑-fun p~ }))
  (FP.elimFact _ _
    -- U
    (elimNat _ _ {!!})
    (FP.elimFact _ _

    -- domain
    (corecVFact2 _ _ _ (i₂ ∘hom i₁) λ pD → λ { f .(fun _) (⊑-fun p~) →
      ⊑-fun λ t d → (p~ t) (ι (dyn .snd) pD $ d) })
    (FP.elimFact _ _

    -- F
    (elimNat _ _ ((FP.⟦ ⟦ ⟦ 1 ⟧₁ ⟧₂ ⟧₂ , (let sq : Σ[ pD ∈ DP.|PtbD| ] (PBSq Rel.inj-arr Rel.inj-arr (U-mor (Id ⟶mor δ*)) (ι (dyn' .snd) pD))
                                              sq = (DP.inj-arr-F .fst 1 , λ { f .(fun _) (⊑-fun p~) →
                                               ⊑-fun (λ t d → ErrorDomMor.isMon δ* (p~ t d))})
                                       in {!!})) , refl))

    -- codomain
    (corecVFact2 _ _ _ (i₂ ∘hom i₂ ∘hom i₂) λ pD → λ { f .(fun _) (⊑-fun p~) →
      ⊑-fun λ t d → PBMor.isMon (U-mor (F-mor (ι (dyn .snd) pD))) (p~ t d) }))))


