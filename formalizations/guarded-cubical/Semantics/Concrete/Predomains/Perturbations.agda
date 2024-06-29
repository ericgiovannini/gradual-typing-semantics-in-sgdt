{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

{-

  This module contains definitions about *perturbations*.

  Given a predomain A, the perturbations for A consist of a monoid MA
  along with a homomorphism of monoids iA from MA to the monoid Endo A of
  predomain endomorphisms A → A that are bisimilar to the identity
  morphism. We may likewise define the perturbations on an error domain B.

  Despite the simplicity of the definition, we do not in this file
  define a record bundling a type with its perturbation monoid and
  homomorphism, as this is not a useful intermediate abstraction.

  We first define the notion of pre-perturbation: an endomorphism that
  is bisimilar to the identity, and show that the collection of
  pre-perturbations for a given type forms a monoid under composition.

-}

module Semantics.Concrete.Predomains.Perturbations (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (ℕ to Nat)


open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct


open import Common.Common
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.KleisliFunctors k

open import Semantics.Concrete.Predomains.PrePerturbations k

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓc ℓc' ℓd ℓd' : Level
  
    ℓA₁   ℓ≤A₁   ℓ≈A₁   : Level
    ℓA₁'  ℓ≤A₁'  ℓ≈A₁'  : Level
    ℓA₂   ℓ≤A₂   ℓ≈A₂   : Level
    ℓA₂'  ℓ≤A₂'  ℓ≈A₂'  : Level
    ℓA₃   ℓ≤A₃   ℓ≈A₃   : Level
    ℓA₃'  ℓ≤A₃'  ℓ≈A₃'  : Level

    ℓB₁   ℓ≤B₁   ℓ≈B₁   : Level
    ℓB₁'  ℓ≤B₁'  ℓ≈B₁'  : Level
    ℓB₂   ℓ≤B₂   ℓ≈B₂   : Level
    ℓB₂'  ℓ≤B₂'  ℓ≈B₂'  : Level
    ℓB₃   ℓ≤B₃   ℓ≈B₃   : Level
    ℓB₃'  ℓ≤B₃'  ℓ≈B₃'  : Level

    ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ : Level
    ℓAₒ ℓ≤Aₒ ℓ≈Aₒ : Level
    ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ : Level
    ℓBₒ ℓ≤Bₒ ℓ≈Bₒ : Level
   
    ℓc₁ ℓc₂ ℓc₃  : Level

    ℓMA₁ ℓMA₂ ℓMA₃ : Level
    ℓMB₁ ℓMB₂ ℓMB₃ : Level
    ℓMAᵢ ℓMAₒ ℓMBᵢ ℓMBₒ : Level

open PBMor



-- Notion of an endomorphism of value types "belonging to" the monoid
-- of perturbations under the specified homomorphism of monoids.
 
monoidContains : {X : PosetBisim ℓ ℓ≤ ℓ≈} →
  (f : PBMor X X) → (M : Monoid ℓM) → (hom : MonoidHom M (Endo X)) →
  Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈) ℓM)
monoidContains {X = X} f M hom =
  Σ[ p ∈ ⟨ M ⟩ ] ptbV M hom p ≡ f -- (hom .fst p ≡ f)

syntax monoidContains f M hom = f ∈[ hom ] M


-- record Foo
--   (B  : ErrorDomain ℓB  ℓ≤B  ℓ≈B)  (MB  : Monoid ℓMB)  (iB  : MonoidHom MB  (CEndo B)) : Type ℓB
--   where


-- "Action" of the arrow functor on perturbations.  That is, given a
-- monoid MA of perturbations on A with homomorphism into Endo(A) and
-- a monoid MB of perturbations on B with homomorphism into CEndo(B),
-- we define a monoid M-Arrow of perturbations on A ⟶ B with homomorphism
-- into CEndo(A ⟶ B).
module Arrow-Ptb
  {A  : PosetBisim  ℓA  ℓ≤A  ℓ≈A}  (MA  : Monoid ℓMA)
  (iA  : MonoidHom MA  (Endo A))
  {B  : ErrorDomain ℓB  ℓ≤B  ℓ≈B}  (MB  : Monoid ℓMB)
  (iB  : MonoidHom MB  (CEndo B)) where

  module MA = MonoidStr (MA .snd)
  module iA = IsMonoidHom (iA .snd)
  module MB = MonoidStr (MB .snd)
  module iB = IsMonoidHom (iB .snd)

  open IsMonoidHom

  M-Arrow : Monoid (ℓ-max ℓMA ℓMB)
  M-Arrow = (MA ^op) ⊕ MB

  i-Arrow : MonoidHom M-Arrow (CEndo (A ⟶ob B))
  i-Arrow = [ h1 ,hom h2 ]
    where
      open PresCompositionVertical
      
      h1 : MonoidHom (MA ^op) (CEndo (A ⟶ob B))
      
      -- using the action of ⟶ on pre-perturbations as defined in the
      -- PrePerturbations file
      h1 .fst m = (iA .fst m) ⟶PrePtb CPrePtbId
      h1 .snd .presε = EqEndomor→EqCPrePtb _ _ eq
        where
          eq : (ptbV MA iA MA.ε) ⟶mor IdE ≡ IdE
          eq = (cong₂ _⟶mor_ (cong fst iA.presε) refl) ∙ arrowPresIdVert
          -- The LHS is path-equal to id, since iA is a homomorphism of monoids.
          -- And then by functoriality of ⟶, we have (id ⟶mor id ≡ id).

      h1 .snd .pres· m n = EqEndomor→EqCPrePtb _ _ eq
        where
          eq : ((ptbV MA iA (n MA.· m)) ⟶mor IdE) ≡
               (((ptbV MA iA m) ⟶mor IdE) ∘ed ((ptbV MA iA n) ⟶mor IdE))
          eq = (cong₂ _⟶mor_ (cong fst (iA.pres· n m)) refl) ∙
               (arrowPresCompVertLeft _ _ IdE)
          -- The LHS is path-equal to ((ptbV n ∘ ptbV m) ⟶mor IdE),
          -- since iA is a homomorphism of monoids.  And then we can
          -- apply functoriality of ⟶.


      h2 : MonoidHom MB (CEndo (A ⟶ob B))
      h2 .fst m = PrePtbId ⟶PrePtb (iB .fst m)
      h2 .snd .presε = EqEndomor→EqCPrePtb _ _ eq
        where
          eq : Id ⟶mor  (ptbC MB iB MB.ε) ≡ IdE
          eq = (cong₂ _⟶mor_ refl (cong fst iB.presε)) ∙ arrowPresIdVert

      h2 .snd .pres· m n = EqEndomor→EqCPrePtb _ _ {!!}


-- "Action" of the F functor on perturbations.
--
-- This makes crucial use of the existence of a delay homomorphism
-- δ* : F A --o F A for every A We define this homomorphism to be
-- ext (δ ∘ η) where δ = θ ∘ next.
module F-Ptb
  {A  : PosetBisim  ℓA  ℓ≤A  ℓ≈A}
  (MA : Monoid ℓMA)
  (iA  : MonoidHom MA  (Endo A)) where

  --module MA = MonoidStr (MA .snd)
  --module iA = IsMonoidHom (iA .snd)

  open IsMonoidHom
  open F-ob

  M-FA  = NatM ⊕ MA

  iFA : MonoidHom M-FA (CEndo (F-ob A))
  iFA = [ h1 ,hom h2 ]
    where
      h1 : MonoidHom NatM (CEndo (F-ob A))
      h1 = NatM→.h (CEndo (F-ob A)) (δ*FA-as-PrePtb A)

      h2 : MonoidHom MA (CEndo (F-ob A))
      h2 = Endo-A→CEndo-FA ∘hom iA



-- "Action" of the U functor on perturbations.

module U-Ptb
  {B  : ErrorDomain  ℓB  ℓ≤B  ℓ≈B}
  (MB  : Monoid ℓMB)
  (iB  : MonoidHom MB  (CEndo B)) where

  -- We define the monoid corresponding to UB as the coproduct of ℕ
  -- with MB.
  M-UB  = NatM ⊕ MB

  -- The homomorphism into the monoid of endomorphisms.
  iUB : MonoidHom M-UB (Endo (U-ob B))
  iUB = [ h1 ,hom h2 ]
    where
      h1 : MonoidHom NatM (Endo (U-ob B))
      h1 = NatM→.h (Endo (U-ob B)) (δB-as-PrePtb B)

      h2 : MonoidHom MB (Endo (U-ob B))
      h2 = CEndo-B→Endo-UB ∘hom iB


-- "Action" of the product functor on perturbations.

module ×-Ptb
  {A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁}
  (MA₁ : Monoid ℓMA₁)
  (iA₁ : MonoidHom MA₁ (Endo A₁))
  {A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂}
  (MA₂ : Monoid ℓMA₂)
  (iA₂ : MonoidHom MA₂ (Endo A₂))
  where

  M-× = MA₁ ⊕ MA₂

  i× : MonoidHom M-× (Endo (A₁ ×dp A₂))
  i× = [ ×A-PrePtb ∘hom iA₁ ,hom A×-PrePtb ∘hom iA₂ ]

-- Kleisli arrow "actions" on perturbations.

module U-KlArrᴸ
  (Aᵢ : PosetBisim  ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ) (MAᵢ  : Monoid ℓMAᵢ) (iAᵢ  : MonoidHom MAᵢ (Endo Aᵢ))
  (Aₒ : PosetBisim  ℓAₒ ℓ≤Aₒ ℓ≈Aₒ) (MAₒ  : Monoid ℓMAₒ) (iAₒ  : MonoidHom MAₒ (Endo Aₒ))
  (ϕ : KlMorV Aₒ Aᵢ)
  (B : ErrorDomain ℓB ℓ≤B ℓ≈B) (MB : Monoid ℓMB) (iB : MonoidHom MB  (CEndo B))
  where


-- Kleisli product "actions" on perturbations.




----------------------------------------------------------------
-- Push-pull structures for predomain and error domain relations
----------------------------------------------------------------

record PushPullV
  (A  : PosetBisim ℓA ℓ≤A ℓ≈A)    (MA  : Monoid ℓMA)  (iA  : MonoidHom MA  (Endo A))
  (A' : PosetBisim ℓA' ℓ≤A' ℓ≈A') (MA' : Monoid ℓMA') (iA' : MonoidHom MA' (Endo A'))
  (c : PBRel A A' ℓc) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓMA ℓMA')) ℓc) where

  field
    push   : MonoidHom MA MA'
    pushSq : (pᴸ : ⟨ MA ⟩) → PBSq c c (ptbV MA iA pᴸ) (ptbV MA' iA' (push .fst pᴸ))
 
    pull   : MonoidHom MA' MA
    pullSq : (pᴿ : ⟨ MA' ⟩) → PBSq c c (ptbV MA iA (pull .fst pᴿ)) (ptbV MA' iA' pᴿ)

  -- Convenience function to extract the "pushed" endomorphism
  push-mor : (pᴸ : ⟨ MA ⟩) → PBMor A' A'
  push-mor pᴸ = ptbV MA' iA' (push .fst pᴸ)

  -- Convenience function to extract the "pulled" endomorphism
  pull-mor : (pᴿ : ⟨ MA' ⟩) → PBMor A A
  pull-mor pᴿ = ptbV MA iA (pull .fst pᴿ)



record PushPullC
  (B  : ErrorDomain ℓB  ℓ≤B  ℓ≈B)  (MB  : Monoid ℓMB)  (iB  : MonoidHom MB  (CEndo B))
  (B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B') (MB' : Monoid ℓMB') (iB' : MonoidHom MB' (CEndo B'))
  (d : ErrorDomRel B B' ℓd) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓMB ℓMB')) ℓd) where

  field

    push   : MonoidHom MB MB'
    pushSq : (pᴸ : ⟨ MB ⟩) → ErrorDomSq d d (ptbC MB iB pᴸ) (ptbC MB' iB' (push .fst pᴸ))

    pull   : MonoidHom MB' MB
    pullSq : (pᴿ : ⟨ MB' ⟩) →  ErrorDomSq d d (ptbC MB iB (pull .fst pᴿ)) (ptbC MB' iB' pᴿ)


  -- Convenience function to extract the "pushed" endomorphism
  push-mor : (pᴸ : ⟨ MB ⟩) → ErrorDomMor B' B'
  push-mor pᴸ = ptbC MB' iB' (push .fst pᴸ)

  -- Convenience function to extract the "pulled" endomorphism
  pull-mor : (pᴿ : ⟨ MB' ⟩) → ErrorDomMor B B
  pull-mor pᴿ = ptbC MB iB (pull .fst pᴿ)



------------------------------------------------
-- Constructions involving push-pull structures
------------------------------------------------

--
-- Push-pull structures for the identity relation
--
module PushPullV-Id
  {A : PosetBisim ℓA ℓ≤A ℓ≈A} {ℓM : Level} where

  open PushPullV

  idPPV : PushPullV {ℓMA = ℓM} A 𝟙M* (𝟙M*→ (Endo A)) A 𝟙M* (𝟙M*→ (Endo A)) (idPRel A)
  idPPV .push = idMon 𝟙M*
  idPPV .pushSq pᴸ = Predom-IdSqV (idPRel A)
  idPPV .pull = idMon 𝟙M*
  idPPV .pullSq pᴿ = Predom-IdSqV (idPRel A)


module PushPullC-Id
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {ℓM : Level} where

  open PushPullC

  idPPC : PushPullC {ℓMB = ℓM} B 𝟙M* (𝟙M*→ (CEndo B)) B 𝟙M* (𝟙M*→ (CEndo B)) (idEDRel B)
  idPPC .push = idMon 𝟙M*
  idPPC .pushSq pᴸ = ED-IdSqV (idEDRel B)
  idPPC .pull = idMon 𝟙M*
  idPPC .pullSq pᴿ = ED-IdSqV (idEDRel B)



--
-- Given a push-pull structure Πc for c and Πc' for c', we can
-- construct a push-pull structure for the composition c ⊙ c'.
--
module PushPullV-Compose
  {A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂} {A₃ : PosetBisim ℓA₃ ℓ≤A₃ ℓ≈A₃}
  (MA₁ : Monoid ℓMA₁)   (iA₁ : MonoidHom MA₁ (Endo A₁))
  (MA₂ : Monoid ℓMA₂)   (iA₂ : MonoidHom MA₂ (Endo A₂))
  (MA₃ : Monoid ℓMA₃)   (iA₃ : MonoidHom MA₃ (Endo A₃))
  (c  : PBRel A₁ A₂ ℓc)  (Πc  : PushPullV A₁ MA₁ iA₁ A₂ MA₂ iA₂ c)
  (c' : PBRel A₂ A₃ ℓc') (Πc' : PushPullV A₂ MA₂ iA₂ A₃ MA₃ iA₃ c') where

  open PushPullV
  module Πc  = PushPullV Πc
  module Πc' = PushPullV Πc'

  compPPV : PushPullV A₁ MA₁ iA₁ A₃ MA₃ iA₃ (c ⊙ c')
  compPPV .push = Πc'.push ∘hom Πc.push
  compPPV .pushSq pᴸ =
    CompSqH {f = ptbV MA₁ iA₁ pᴸ} {g = push-mor Πc pᴸ} {h = push-mor Πc' _}
            (Πc .pushSq pᴸ) (Πc' .pushSq _)
  
  compPPV .pull = Πc.pull ∘hom Πc'.pull
  compPPV .pullSq pᴿ =
    CompSqH {f = pull-mor Πc _} {g = pull-mor Πc' pᴿ} {h = ptbV MA₃ iA₃ pᴿ}
            (Πc .pullSq _) (Πc' .pullSq pᴿ)


--
-- Given a push-pull structure Πd for d and Πd' for d', we can
-- construct a push-pull structure for the composition d ⊙ d'.
--
module PushPullC-Compose
  {B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁} {B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂} {B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃}
  (MB₁ : Monoid ℓMB₁)   (iB₁ : MonoidHom MB₁ (CEndo B₁))
  (MB₂ : Monoid ℓMB₂)   (iB₂ : MonoidHom MB₂ (CEndo B₂))
  (MB₃ : Monoid ℓMB₃)   (iB₃ : MonoidHom MB₃ (CEndo B₃))
  (d  : ErrorDomRel B₁ B₂ ℓc)  (Πd  : PushPullC B₁ MB₁ iB₁ B₂ MB₂ iB₂ d)
  (d' : ErrorDomRel B₂ B₃ ℓc') (Πd' : PushPullC B₂ MB₂ iB₂ B₃ MB₃ iB₃ d') where

  open PushPullC
  module Πd  = PushPullC Πd
  module Πd' = PushPullC Πd'

  compPPC : PushPullC B₁ MB₁ iB₁ B₃ MB₃ iB₃ (d ⊙ed d')
  compPPC .push = Πd'.push ∘hom Πd.push
  compPPC .pushSq pᴸ =
    ED-CompSqH {ϕ₁ = ptbC MB₁ iB₁ pᴸ} {ϕ₂ = push-mor Πd pᴸ} {ϕ₃ = push-mor Πd' _}
            (Πd .pushSq pᴸ) (Πd' .pushSq _)
  
  compPPC .pull = Πd.pull ∘hom Πd'.pull
  compPPC .pullSq pᴿ =
    ED-CompSqH {ϕ₁ = pull-mor Πd _} {ϕ₂ = pull-mor Πd' pᴿ} {ϕ₃ = ptbC MB₃ iB₃ pᴿ}
            (Πd .pullSq _) (Πd' .pullSq pᴿ)



--
-- Given a push-pull structure Πc for c and Πd for d, we can construct
-- a push-pull structure for the (computation) relation c ⟶ d.
--
module ⟶PushPull
  {A  : PosetBisim  ℓA  ℓ≤A  ℓ≈A}  {MA  : Monoid ℓMA}  {iA  : MonoidHom MA  (Endo A)}
  {A' : PosetBisim  ℓA' ℓ≤A' ℓ≈A'} {MA' : Monoid ℓMA'} {iA' : MonoidHom MA' (Endo A')}
  {B  : ErrorDomain ℓB  ℓ≤B  ℓ≈B}  {MB  : Monoid ℓMB}  {iB  : MonoidHom MB  (CEndo B)}
  {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'} {MB' : Monoid ℓMB'} {iB' : MonoidHom MB' (CEndo B')}
  (c : PBRel A A' ℓc)       (Πc : PushPullV A MA iA A' MA' iA' c)
  (d : ErrorDomRel B B' ℓd) (Πd : PushPullC B MB iB B' MB' iB' d) where

  module Πc = PushPullV Πc
  module Πd = PushPullC Πd

  open IsMonoidHom

  module MA = MonoidStr (MA .snd)
  module iA = IsMonoidHom (iA .snd)

  module MA' = MonoidStr (MA' .snd)
  module iA' = IsMonoidHom (iA' .snd)

  module MB = MonoidStr (MB .snd)
  module iB = IsMonoidHom (iB .snd)
  
  module MB' = MonoidStr (MB' .snd)
  module iB' = IsMonoidHom (iB' .snd)

  open PushPullV renaming (push to pushV ; pull to pullV)
  open PushPullC renaming (push to pushC ; pull to pullC)
  module PPV = PushPullV
  module PPC = PushPullC

  module Ptb-ArrowAB   = Arrow-Ptb MA  iA  MB  iB
  module Ptb-ArrowA'B' = Arrow-Ptb MA' iA' MB' iB'

  -- The monoid of perturbations for A ⟶ B is the coproduct (in the
  -- category of monoids) of MA^op with MB
  M-A⟶B = (MA ^op) ⊕ MB
  M-A'⟶B' = (MA' ^op) ⊕ MB'

  i-A⟶B : MonoidHom M-A⟶B (CEndo (A ⟶ob B))
  i-A⟶B = Ptb-ArrowAB.i-Arrow

  i-A'⟶B' : MonoidHom M-A'⟶B' (CEndo (A' ⟶ob B'))
  i-A'⟶B' = Ptb-ArrowA'B'.i-Arrow


  module Push = Elim2 (MA ^op) MB ((MA' ^op) ⊕ MB')
    (λ p q → ErrorDomSq
      (c ⟶rel d) (c ⟶rel d)
      (ptbC ((MA ^op) ⊕ MB) i-A⟶B p)
      (ptbC ((MA' ^op) ⊕ MB') i-A'⟶B' q))
    (isPropErrorDomSq _ _ _ _)
    (i₁ ∘hom ((Πc .PPV.push) ^opHom))
    (i₂ ∘hom Πd .PPC.push)

  module Pull = Elim2 (MA' ^op) MB' ((MA ^op) ⊕ MB)
    (λ q p → ErrorDomSq
      (c ⟶rel d) (c ⟶rel d)
      (ptbC ((MA ^op) ⊕ MB) i-A⟶B p)
      (ptbC ((MA' ^op) ⊕ MB') i-A'⟶B' q))
    (isPropErrorDomSq _ _ _ _)
    (i₁ ∘hom ((Πc .PPV.pull) ^opHom))
    (i₂ ∘hom Πd .PPC.pull)
  

  ⟶PP : PushPullC
    (A  ⟶ob B)  ((MA  ^op) ⊕ MB)  i-A⟶B
    (A' ⟶ob B') ((MA' ^op) ⊕ MB') i-A'⟶B'
    (c ⟶rel d)
  ⟶PP .PPC.push = Push.hom
  ⟶PP .PPC.pushSq =
    Push.elim2
     (λ ma → Πc.pushSq ma ⟶sq ED-IdSqV d)
     (λ mb → (Predom-IdSqV c) ⟶sq (Πd.pushSq mb)) 
     (ED-IdSqV (c ⟶rel d))                         
     λ {x = x} {y = y} sq1 sq2 →
       ED-CompSqV {d₁ = c ⟶rel d} {d₂ = c ⟶rel d} {d₃ = c ⟶rel d}
                  {ϕ₁  = ptbC ((MA ^op) ⊕ MB) i-A⟶B y}
                  {ϕ₁' = ptbC ((MA' ^op) ⊕ MB') i-A'⟶B' (Push.hom .fst y) }
                  {ϕ₂  = ptbC ((MA ^op) ⊕ MB) i-A⟶B x}
                  {ϕ₂' = ptbC ((MA' ^op) ⊕ MB') i-A'⟶B' (Push.hom .fst x)}
                  sq2 sq1
                  
  ⟶PP .PPC.pull = Pull.hom 
  ⟶PP .PPC.pullSq = Pull.elim2
     (λ ma → Πc.pullSq ma ⟶sq ED-IdSqV d) 
     (λ mb → (Predom-IdSqV c) ⟶sq (Πd.pullSq mb)) 
     (ED-IdSqV (c ⟶rel d))                         
     λ {x = x} {y = y} sq1 sq2 →
       ED-CompSqV {d₁ = c ⟶rel d} {d₂ = c ⟶rel d} {d₃ = c ⟶rel d}
                  {ϕ₁  = ptbC ((MA ^op) ⊕ MB) i-A⟶B (Pull.hom .fst y)}
                  {ϕ₁' = ptbC ((MA' ^op) ⊕ MB') i-A'⟶B' y }
                  {ϕ₂  = ptbC ((MA ^op) ⊕ MB) i-A⟶B (Pull.hom .fst x)}
                  {ϕ₂' = ptbC ((MA' ^op) ⊕ MB') i-A'⟶B' x}
                  sq2 sq1                       


--
-- Given a push-pull structure Πc for c, we can construct a push-pull
-- structure for the lifted relation Fc.
--
module F-PushPull
  {A  : PosetBisim  ℓA  ℓ≤A  ℓ≈A}  {MA  : Monoid ℓMA}  {iA  : MonoidHom MA  (Endo A)}
  {A' : PosetBisim  ℓA' ℓ≤A' ℓ≈A'} {MA' : Monoid ℓMA'} {iA' : MonoidHom MA' (Endo A')}
  (c : PBRel A A' ℓc) (Πc : PushPullV A MA iA A' MA' iA' c)

  where

  open F-ob
  open F-rel

  module Πc = PushPullV Πc

  module PPV = PushPullV
  module PPC = PushPullC

  module Ptb-FA  = F-Ptb MA  iA 
  module Ptb-FA' = F-Ptb MA' iA'

  M-FA  = Ptb-FA.M-FA  -- NatM ⊕ MA
  M-FA' = Ptb-FA'.M-FA -- NatM ⊕ MA'

  iFA : MonoidHom Ptb-FA.M-FA (CEndo (F-ob A))
  iFA = Ptb-FA.iFA

  iFA' : MonoidHom Ptb-FA'.M-FA (CEndo (F-ob A'))
  iFA' = Ptb-FA'.iFA

  -- Eliminating from (NatP ⊕ MA) to (NatP ⊕ MA')
  module Push = Elim2 NatM MA M-FA'
    (λ pFA pFA' → ErrorDomSq
      (F-rel c) (F-rel c) (ptbC M-FA iFA pFA) (ptbC M-FA' iFA' pFA'))
    (isPropErrorDomSq _ _ _ _)
    i₁
    (i₂ ∘hom Πc.push)

  -- Eliminating from (NatP ⊕ MB') to (NatP ⊕ MB)
  module Pull = Elim2 NatM MA' M-FA
    (λ pFA' pFA → ErrorDomSq
      (F-rel c) (F-rel c) (ptbC M-FA iFA pFA) (ptbC M-FA' iFA' pFA'))
    (isPropErrorDomSq _ _ _ _)
    i₁
    (i₂ ∘hom Πc.pull)

  open F-sq

  F-PushPull : PushPullC (F-ob A) M-FA iFA (F-ob A') M-FA' iFA' (F-rel c)
  F-PushPull .PPC.push = Push.hom -- [ i₁ ,hom (i₂ ∘hom Πc.push) ]
  F-PushPull .PPC.pushSq =  Push.elim2 {!!}
      -- (λ n → transport
      --   (λ i → PBSq (U-rel d) (U-rel d) (sym (lem1 n) i) (sym (lem2 n) i))
      --   (sq-δB^n-δB'^n n))  -- NTS: VSq Ud Ud (δB ^ n) (δB' ^ n)

      (λ ma → F-sq c c (ptbV MA iA ma) (ptbV MA' iA' (Πc.push .fst ma)) (Πc.pushSq ma))

      (ED-IdSqV (F-rel c))

      (λ {x = x} {y = y} sq1 sq2 →
        ED-CompSqV {d₁ = F-rel c} {d₂ = F-rel c} {d₃ = F-rel c}
                {ϕ₁ = ptbC M-FA iFA y} {ϕ₁' = ptbC M-FA' iFA' (Push.hom .fst y)}
                {ϕ₂ = ptbC M-FA iFA x} {ϕ₂' = ptbC M-FA' iFA' (Push.hom .fst x)}
                sq2 sq1)


  F-PushPull .PPC.pull = Pull.hom -- [ i₁ ,hom (i₂ ∘hom Πc.pull) ]
  F-PushPull .PPC.pullSq = {!!}



--
-- Given a push-pull structure Πd for d, we can construct a push-pull
-- structure for the value relation Ud.
--
module U-PushPull
  {B  : ErrorDomain  ℓB  ℓ≤B  ℓ≈B}  {MB  : Monoid ℓMB}  {iB  : MonoidHom MB  (CEndo B)}
  {B' : ErrorDomain  ℓB' ℓ≤B' ℓ≈B'} {MB' : Monoid ℓMB'} {iB' : MonoidHom MB' (CEndo B')}
  (d : ErrorDomRel B B' ℓd) (Πd : PushPullC B MB iB B' MB' iB' d) where

  module B = ErrorDomainStr (B. snd)
  module B' = ErrorDomainStr (B' .snd)
  module d = ErrorDomRel d
  module Πd = PushPullC Πd

  module PtbUB  = U-Ptb MB  iB
  module PtbUB' = U-Ptb MB' iB'

  module PPV = PushPullV
  module PPC = PushPullC

  -- We define the monoid corresponding to UB as the coproduct of ℕ
  -- with MB.
  -- M-UB  = NatM ⊕ MB
  -- M-UB' = NatM ⊕ MB'

  M-UB = PtbUB.M-UB
  M-UB' = PtbUB'.M-UB

  -- The homomorphisms into the respective monoids of endomorphisms.
  iUB = PtbUB.iUB
  iUB' = PtbUB'.iUB

  -- Eliminating from (NatP ⊕ MB) to (NatP ⊕ MB')
  module Push = Elim2 NatM MB M-UB'
    (λ pUB pUB' → PBSq
      (U-rel d) (U-rel d) (ptbV M-UB iUB pUB) (ptbV M-UB' iUB' pUB'))
    (isPropPBSq _ _ _ _)
    i₁
    (i₂ ∘hom Πd.push)

  -- Eliminating from (NatP ⊕ MB') to (NatP ⊕ MB)
  module Pull = Elim2 NatM MB' M-UB
    (λ pUB' pUB → PBSq
      (U-rel d) (U-rel d) (ptbV M-UB iUB pUB) (ptbV M-UB' iUB' pUB'))
    (isPropPBSq _ _ _ _)
    i₁
    (i₂ ∘hom Πd.pull)


  sq-δB-δB' : PBSq (U-rel d) (U-rel d) B.δ B'.δ
  sq-δB-δB' b b' bRb' = d.Rθ (next b) (next b') (next bRb')

  sq-δB^n-δB'^n : ∀ (n : Nat) → PBSq (U-rel d) (U-rel d) (B.δ ^m n) (B'.δ ^m n)
  sq-δB^n-δB'^n n = CompSqV-iterate (U-rel d)  B.δ  B'.δ  sq-δB-δB' n

  lem1 : ∀ n → (ptbV M-UB iUB ⟦ n ⟧₁) ≡ (B.δ ^m n)
  lem1 zero = eqPBMor _ _ refl
  lem1 (suc n) = eqPBMor _ _ (
    f (ptbV M-UB iUB ⟦ suc n ⟧₁)
      ≡⟨ refl ⟩
    f B.δ ∘ f (ptbV M-UB iUB ⟦ n ⟧₁)
      ≡⟨ (λ i → (f B.δ) ∘ (f (lem1 n i))) ⟩
    f (B.δ ^m (suc n)) ∎)

  lem2 : ∀ n → (ptbV M-UB' iUB' (Push.h ⟦ n ⟧₁)) ≡ (B'.δ ^m n)
  lem2 zero = eqPBMor _ _ refl
  lem2 (suc n) = eqPBMor _ _ (λ i → (f B'.δ) ∘ (f (lem2 n i)))
  
  U-PushPull : PushPullV (U-ob B) M-UB iUB (U-ob B') M-UB' iUB' (U-rel d)
  U-PushPull .PPV.push = Push.hom
  U-PushPull .PPV.pushSq =
    Push.elim2
      (λ n → transport
        (λ i → PBSq (U-rel d) (U-rel d) (sym (lem1 n) i) (sym (lem2 n) i))
        (sq-δB^n-δB'^n n))  -- NTS: VSq Ud Ud (δB ^ n) (δB' ^ n)

      (λ mb → U-sq d d (ptbC MB iB mb) (ptbC MB' iB' (Πd.push .fst mb)) (Πd.pushSq mb))

      (Predom-IdSqV (U-rel d))

      (λ {x = x} {y = y} sq1 sq2 →
        CompSqV {c₁ = U-rel d} {c₂ = U-rel d} {c₃ = U-rel d}
                {f₁ = ptbV M-UB iUB y} {g₁ = ptbV M-UB' iUB' (Push.hom .fst y)}
                {f₂ = ptbV M-UB iUB x} {g₂ = ptbV M-UB' iUB' (Push.hom .fst x)}
                sq2 sq1)


  U-PushPull .PPV.pull = Pull.hom  -- [ i₁ ,hom (i₂ ∘hom Πd.pull) ]
  U-PushPull .PPV.pullSq = Pull.elim2
      (λ n → transport
        (λ i → PBSq (U-rel d) (U-rel d) (sym (lem1 n) i) (sym (lem2 n) i))
        (sq-δB^n-δB'^n n))  -- NTS: VSq Ud Ud (δB ^ n) (δB' ^ n)

      (λ mb' → U-sq d d (ptbC MB iB (Πd.pull .fst mb')) (ptbC MB' iB' mb') (Πd.pullSq mb'))

      (Predom-IdSqV (U-rel d))

      (λ {x = x} {y = y} sq1 sq2 →
        CompSqV {c₁ = U-rel d} {c₂ = U-rel d} {c₃ = U-rel d}
                {f₁ = ptbV M-UB iUB (Pull.hom .fst y)} {g₁ = ptbV M-UB' iUB' y}
                {f₂ = ptbV M-UB iUB (Pull.hom .fst x)} {g₂ = ptbV M-UB' iUB' x}
                sq2 sq1)
                
  


-- Given a push-pull structure Πc₁ for c₁ and Πc₂ for c₂, we can
-- construct a push-pull structure for c₁ × c₂
module PushPull× where
























-- The predomain squares where the top and bottom are both some fixed relation c
-- and the left and right are iterates of a fixed morphism f and g
-- form a monoid under vertical composition.

{-
module _ {A : PosetBisim ℓA ℓ≤A ℓ≈A} {A' : PosetBisim ℓA' ℓ≤A' ℓ≈A'} (c : PBRel A A' ℓc) where

  VSq = Σ[ f ∈ PBMor A A ] Σ[ g ∈ PBMor A' A' ] PBSq c c f g

  Comp-VSq : VSq → VSq → VSq
  Comp-VSq (f₁ , g₁ , α₁) (f₂ , g₂ , α₂) =
    (f₂ ∘p f₁) , (g₂ ∘p g₁) , (CompSqV {c₁ = c} {c₂ = c} {c₃ = c} α₁ α₂)

  PsqMonoid : Monoid (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓA ℓ≤A) ℓ≈A) ℓA') ℓ≤A') ℓ≈A') ℓc)
  PsqMonoid = makeMonoid {M = VSq} (Id , Id , Predom-IdSqV c) Comp-VSq {!!} {!!} {!!} {!!}
-}
{-
    CompSqV
    (isProp→isSet (isPropPBSq c c Id Id))
    (λ _ _ _ → isPropPBSq c c Id Id _ _)
    (λ _ → isPropPBSq c c Id Id _ _)
    (λ _ → isPropPBSq c c Id Id _ _)
-}


{-
Endofun : (X : hSet ℓ) → Monoid ℓ
Endofun X = makeMonoid {M = ⟨ X ⟩ → ⟨ X ⟩} id (λ g f → g ∘ f) (isSet→ (X .snd)) (λ _ _ _ → refl) (λ _ → refl) λ _ → refl

record PushPull'
  {ℓX ℓY ℓMX ℓMY ℓR : Level}
  (X : hSet ℓX) (Y : hSet ℓY)
  (R : ⟨ X ⟩ → ⟨ Y ⟩ → Type ℓR)
  (MX : Monoid ℓMX) (MY : Monoid ℓMY)
  (iX : ⟨ MX ⟩ → (⟨ X ⟩ → ⟨ X ⟩))
  (iY : ⟨ MY ⟩ → (⟨ Y ⟩ → ⟨ Y ⟩)) :
  Type (ℓ-max (ℓ-max (ℓ-max ℓX ℓY) (ℓ-max ℓMX ℓMY)) ℓR) where

  field
   push : (pᴸ : ⟨ MX ⟩) →
     Σ[ pᴿ ∈ ⟨ MY ⟩ ] TwoCell R R (iX pᴸ) (iY pᴿ) 
   pull : (pᴿ : ⟨ MY ⟩) →
     Σ[ pᴸ ∈ ⟨ MX ⟩ ] TwoCell R R (iX pᴸ) (iY pᴿ) 
-}


