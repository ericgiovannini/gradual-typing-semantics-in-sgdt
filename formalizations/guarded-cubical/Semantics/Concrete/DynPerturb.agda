{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}



open import Common.Later

module Semantics.Concrete.DynPerturb (k : Clock) where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup

open import Cubical.Data.Nat hiding (_·_ ; ℕ)

open import Semantics.Concrete.Dyn k
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k

open import Semantics.Concrete.Predomains.PrePerturbations k


private variable
  ℓ : Level
  A : Type ℓ

private
  ▹_ : {ℓ : Level} → Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

-------------------------
-- Perturbations for Dyn
-------------------------

-- The monoid of perturbations for Dyn is defined as a
-- higher-inductive type.

-- Recall that Dyn ≅ ℕ + (Dyn × Dyn) + (Dyn ==> UF Dyn)
--                 ≅ ℕ + (Dyn × Dyn) + U (Dyn ⟶ F Dyn)
--                 
-- We define PtbD to be the least solution (i.e. initial algebra) in
-- the category of monoids to the equation
--
-- PtbD ≅ (PtbD ⊕ PtbD) ⊕ (ℕ ⊕ PtbD ^op ⊕ ℕ ⊕ PtbD)
--
data |PtbD| : Type where
  ε : |PtbD|
  _·_ : |PtbD| → |PtbD| → |PtbD|
  identityᵣ : ∀ x → x · ε ≡ x
  identityₗ  :  ∀ x → ε · x ≡ x
  assoc     : ∀ x y z → x · (y · z) ≡ (x · y) · z
  trunc : isSet |PtbD|
 
  ⟦_⟧×-left    : |PtbD| → |PtbD|
  ⟦_⟧×-right   : |PtbD| → |PtbD|
  ⟦_⟧arr-left  : |PtbD| → |PtbD|
  ⟦_⟧arr-right : |PtbD| → |PtbD|
  ⟦_⟧arr-U    : |PtbD|
  ⟦_⟧arr-F    : |PtbD|

  id-×-left    : ⟦ ε ⟧×-left ≡ ε
  id-×-right   : ⟦ ε ⟧×-right ≡ ε
  id-arr-left  : ⟦ ε ⟧arr-left ≡ ε
  id-arr-right : ⟦ ε ⟧arr-right ≡ ε

  comp-×-left    : ∀ p p' → ⟦ p · p' ⟧×-left    ≡ (⟦ p ⟧×-left · ⟦ p' ⟧×-left)
  comp-×-right   : ∀ p p' → ⟦ p · p' ⟧×-right   ≡ (⟦ p ⟧×-right · ⟦ p' ⟧×-right)
  -- arr-left is contravariant
  comp-arr-left  : ∀ p p' → ⟦ p · p' ⟧arr-left  ≡ (⟦ p' ⟧arr-left · ⟦ p ⟧arr-left)
  comp-arr-right : ∀ p p' → ⟦ p · p' ⟧arr-right ≡ (⟦ p ⟧arr-right · ⟦ p' ⟧arr-right)

open MonoidStr
PtbD : Monoid ℓ-zero
PtbD .fst = |PtbD|
PtbD .snd .MonoidStr.ε = |PtbD|.ε
PtbD .snd .MonoidStr._·_ = |PtbD|._·_
PtbD .snd .isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set = trunc
PtbD .snd .isMonoid .IsMonoid.isSemigroup .IsSemigroup.·Assoc = assoc
PtbD .snd .isMonoid .IsMonoid.·IdR = identityᵣ
PtbD .snd .isMonoid .IsMonoid.·IdL = identityₗ

-- recursion principle: PtbD is the initial algebra of the above functor
module _
       {M : Monoid ℓ}
       (×-left : MonoidHom M M)
       (×-right : MonoidHom M M)
       (arr-left : MonoidHom (M ^op) M)
       (arr-right : MonoidHom M M)
       (arr-U : ⟨ M ⟩)
       (arr-F : ⟨ M ⟩)
       where
  private
    |M| = ⟨ M ⟩
    module M = MonoidStr (M .snd)
    open IsSemigroup
    open IsMonoidHom

    |rec| : |PtbD| → |M|
    |rec| |PtbD|.ε = M.ε
    |rec| (p |PtbD|.· q) = (|rec| p) M.· (|rec| q)
    |rec| (identityᵣ p i) = M.·IdR (|rec| p) i
    |rec| (identityₗ p i) = M.·IdL (|rec| p) i
    |rec| (assoc p q r i) = M.isSemigroup .·Assoc (|rec| p) (|rec| q) (|rec| r) i
    |rec| (trunc p q p≡q p≡q' i j) =
      M.isSemigroup .is-set (|rec| p) (|rec| q) (cong |rec| p≡q) (cong |rec| p≡q') i j
    |rec| ⟦ p ⟧×-left = ×-left .fst (|rec| p)
    |rec| (id-×-left i) = ×-left .snd .presε i
    |rec| (comp-×-left p q i) = ×-left .snd .pres· (|rec| p) (|rec| q) i
    |rec| ⟦ p ⟧×-right = ×-right .fst (|rec| p)
    |rec| (id-×-right i) = ×-right .snd .presε i
    |rec| (comp-×-right p q i) = ×-right .snd .pres· (|rec| p) (|rec| q) i
    |rec| ⟦ p ⟧arr-left = arr-left .fst (|rec| p)
    |rec| (id-arr-left i) = arr-left .snd .presε i
    |rec| (comp-arr-left p q i) = arr-left .snd .pres· (|rec| q) (|rec| p) i
    |rec| ⟦ p ⟧arr-right = arr-right .fst (|rec| p)
    |rec| (id-arr-right i) = arr-right .snd .presε i
    |rec| (comp-arr-right p q i) = arr-right .snd .pres· (|rec| p) (|rec| q) i
    |rec| ⟦_⟧arr-U = arr-U
    |rec| ⟦_⟧arr-F = arr-F
  rec : MonoidHom PtbD M
  rec .fst = |rec|
  rec .snd .presε = refl
  rec .snd .pres· x y = refl


open DynDef {ℓ-zero}
open LiftPredomain
open Guarded (next Dyn)


-- Convenience function for defining endomorphisms on Dyn.
module _
  (caseNat :  ⟨ Endo ℕ ⟩)
  (caseProd : ⟨ Endo (Dyn' ×dp Dyn') ⟩)
  (caseFun :  ⟨ Endo (Dyn ==> 𝕃 Dyn) ⟩) where

  open Embeddings
  open DynRel
  open ClockedCombinators k

  mor : PBMor Dyn' Dyn'
  mor = recDyn'
      (emb-nat' ∘p caseNat .fst)
      (emb-times' ∘p caseProd .fst)
      (emb-▹arr' ∘p Map▹ (caseFun .fst))

  mapDyn : ⟨ Endo Dyn' ⟩
  mapDyn .fst = mor
  mapDyn .snd d d' (≈-nat eq) = ≈-nat (caseNat .snd _ _ eq)
  mapDyn .snd .(prod _ _) .(prod _ _)
    (≈-prod p q) =
      ≈-prod (caseProd .snd _ _ (p , q) .fst)
             (caseProd .snd _ _ (p , q) .snd)
  mapDyn .snd d d' (≈-fun p) = ≈-fun (Endo▹ caseFun .snd _ _ p)

-- Combinator for defining homomorphisms from a monoid A to Endo Dyn:
module _ {A : Monoid ℓ}
  (caseNat : MonoidHom A (Endo ℕ))
  (caseProd : MonoidHom A (Endo (Dyn' ×dp Dyn')))
  (caseFun : MonoidHom A (Endo (Dyn ==> 𝕃 Dyn))) where

  open IsMonoidHom
  module caseNat = IsMonoidHom (caseNat .snd)
  module caseProd = IsMonoidHom (caseProd .snd)
  module caseFun = IsMonoidHom (caseFun .snd)

  aux : ⟨ A ⟩ → ⟨ Endo Dyn' ⟩
  aux g = mapDyn (caseNat .fst g) (caseProd .fst g) (caseFun .fst g)

  mkEndoDynHom : MonoidHom A (Endo Dyn')
  mkEndoDynHom .fst = aux
  mkEndoDynHom .snd .presε =
    PrePtb≡ _ _ (funExt λ {
        (nat n) → cong nat (funExt⁻ (cong PBMor.f (cong fst caseNat.presε)) n)
      ; (prod d₁ d₂) → cong₂ prod
          (cong fst (funExt⁻ (cong PBMor.f (cong fst caseProd.presε)) (d₁ , d₂)))
          (cong snd (funExt⁻ (cong PBMor.f (cong fst caseProd.presε)) (d₁ , d₂)))
      ; (fun f~) → cong fun (later-ext λ t → funExt⁻ (cong PBMor.f (cong fst caseFun.presε)) (f~ t)) })
  mkEndoDynHom .snd .pres· x y = PrePtb≡ _ _ (funExt (λ {
        (nat n) → cong nat (funExt⁻ (cong PBMor.f (cong fst (caseNat.pres· x y))) n)
      ; (prod d₁ d₂) → cong₂ prod
          (cong fst (funExt⁻ (cong PBMor.f (cong fst (caseProd.pres· x y))) (d₁ , d₂)))
          (cong snd (funExt⁻ (cong PBMor.f (cong fst (caseProd.pres· x y))) (d₁ , d₂)))
      ; (fun f~) → cong fun (later-ext (λ t → funExt⁻ (cong PBMor.f (cong fst (caseFun.pres· x y))) (f~ t)))}))



-- Monoid homomorphism into the endomorphisms on Dyn
ι-dyn : MonoidHom PtbD (Endo Dyn)
ι-dyn = EndoDyn'→EndoDyn ∘hom rec
  -- ×-l
  (mkEndoDynHom ε-hom ×A-PrePtb ε-hom)
  -- ×-r
  (mkEndoDynHom ε-hom A×-PrePtb ε-hom)
  -- arr-dom
  arr-dom
  -- arr-cod
  arr-cod
  -- U
  (mapDyn PrePtbId PrePtbId (U-PrePtb (PrePtbId ⟶PrePtb (δ*FA-as-PrePtb Dyn)))) -- apply a delay in the codomain
  -- F
  (mapDyn PrePtbId PrePtbId (U-PrePtb (PrePtbId ⟶PrePtb (δ*FA-as-PrePtb Dyn)))) -- same as above

  where

    open Embeddings
    open IsMonoidHom
    open F-ob

    EndoDyn→EndoDyn' : MonoidHom (Endo Dyn) (Endo Dyn')
    EndoDyn→EndoDyn' .fst g = PrePtbRetract Dyn→Dyn' Dyn'→Dyn fold-unfold g
    EndoDyn→EndoDyn' .snd .presε = PrePtb≡ _ _ (cong PBMor.f fold-unfold)
    EndoDyn→EndoDyn' .snd .pres· g h =
      let eq = (sym (funExt (λ x →
            let y = h .fst .PBMor.f (transport (λ i → unfold-Dyn (~ i) .fst) x) in
            λ i → transport (λ j → unfold-Dyn j .fst) (g .fst .PBMor.f (unfold-fold i .PBMor.f y))))) in
      PrePtb≡ _ _ eq

    EndoDyn'→EndoDyn : MonoidHom (Endo Dyn') (Endo Dyn)
    EndoDyn'→EndoDyn .fst g = PrePtbRetract Dyn'→Dyn Dyn→Dyn' unfold-fold g 
    EndoDyn'→EndoDyn .snd .presε = PrePtb≡ _ _ (cong PBMor.f unfold-fold)
    EndoDyn'→EndoDyn .snd .pres· g h =
      let eq = (sym (funExt (λ x →
            let y = h .fst .PBMor.f (transport (λ i → unfold-Dyn i .fst) x) in
            λ i → transport (λ j → unfold-Dyn (~ j) .fst) (g .fst .PBMor.f (fold-unfold i .PBMor.f y))))) in
      PrePtb≡ _ _ eq
       
{-

Goal : 

(λ x →
   transp (λ i → fst (fix-eq Guarded.Dyn' (~ i))) i0
   (PBMor.f (g .fst)
    (PBMor.f (h .fst)
     (transp (λ i → fst (fix-eq Guarded.Dyn' i)) i0 x))))
≡
(λ x →
   transp (λ i → fst (fix-eq Guarded.Dyn' (~ i))) i0
   (PBMor.f (fst g)
    (transp (λ i → fst (fix-eq Guarded.Dyn' i)) i0
     (transp (λ i → fst (fix-eq Guarded.Dyn' (~ i))) i0
      (PBMor.f (fst h)
       (transp (λ i → fst (fix-eq Guarded.Dyn' i)) i0 x))))))

-}


    arr-dom : MonoidHom (Endo Dyn' ^op) (Endo Dyn')
    arr-dom = (mkEndoDynHom ε-hom ε-hom
    -- We take the provided endomorphism on Dyn' and convert it to an
    -- endomorphism on Dyn and apply that in the domain.
      (CEndo-B→Endo-UB
      ∘hom (A⟶-PrePtb {B = F-ob Dyn})
      ∘hom (EndoDyn'→EndoDyn ^opHom)))
   
   
    arr-cod :  MonoidHom (Endo Dyn') (Endo Dyn')
    arr-cod = mkEndoDynHom ε-hom ε-hom
    -- We take the provided endomorphism on Dyn', convert it to one on
    -- Dyn, then lift it to one on F Dyn, and apply that in the
    -- codomain.
     (CEndo-B→Endo-UB
      ∘hom ⟶B-PrePtb
      ∘hom Endo-A→CEndo-FA
      ∘hom EndoDyn'→EndoDyn)
      
    












-- module _
--   (caseNat :  ⟨ Endo ℕ ⟩)
--   (caseProd : ⟨ Endo (Dyn ×dp Dyn) ⟩)
--   (caseFun :  ⟨ Endo (Dyn ==> 𝕃 Dyn) ⟩) where

--   open Guarded (next Dyn)
--   open RecDyn
--   open Embeddings
--   open DynRel
--   open ClockedCombinators k

--   mor : PBMor Dyn Dyn
--   mor = recDyn
--       (emb-nat ∘p caseNat .fst)
--       (emb-times ∘p caseProd .fst)
--       (emb-▹arr ∘p Map▹ (caseFun .fst))

--   mapDyn : ⟨ Endo Dyn ⟩
--   mapDyn .fst = mor
--   mapDyn .snd d d' d≈d' = {!!}

--     where
--       lem : ∀ d d' → (d ≈d d') → {!!}



    -- ×l-fun : ⟨ Endo Dyn' ⟩ → ⟨ Endo Dyn' ⟩
    -- ×l-fun g = mapDyn PrePtbId (×A-PrePtb .fst g) PrePtbId

    -- ×l : MonoidHom (Endo Dyn') (Endo Dyn')
    -- ×l .fst = ×l-fun
    -- ×l .snd .presε = PrePtb≡ _ _ (funExt (λ {(nat _) → refl ; (prod _ _) → refl ; (fun _) → refl}))
    -- ×l .snd .pres· g₁ g₂ =
    --   PrePtb≡ _ _ (funExt λ {(nat _) → refl ; (prod _ _) → refl ; (fun _) → refl })

    -- ×r-fun : ⟨ Endo Dyn' ⟩ → ⟨ Endo Dyn' ⟩
    -- ×r-fun g = mapDyn PrePtbId (A×-PrePtb .fst g) PrePtbId

    -- ×r : MonoidHom (Endo Dyn') (Endo Dyn')
    -- ×r .fst = ×r-fun
    -- ×r .snd .presε = PrePtb≡ _ _ (funExt (λ {(nat _) → refl ; (prod _ _) → refl ; (fun _) → refl}))
    -- ×r .snd .pres· g₁ g₂ =
    --   PrePtb≡ _ _ (funExt (λ {(nat _) → refl ; (prod _ _) → refl ; (fun _) → refl}))
