{-
   TODO: rename "preperturbations" to "semantic perturbations".

   A (semantic) perturbation of a type is an endomorphism that is
   bisimilar to the identity, i.e., it "perturbs" the element but
   essentially does nothing.

-}


{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}


{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Later

module Semantics.Concrete.Predomains.PrePerturbations (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥


open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Sigma



open import Common.Common
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions renaming (ℕ to NatP)
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.Monad k
open import Semantics.Concrete.DoublePoset.MonadRelationalResults k
open import Semantics.Concrete.DoublePoset.MonadCombinators k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.KleisliFunctors k



private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ : Level

    ℓMA₁ ℓMA₂ ℓMA₃ : Level
    ℓMB₁ ℓMB₂ ℓMB₃ : Level

    A : PosetBisim ℓA ℓ≤A ℓ≈A
    A' : PosetBisim ℓA' ℓ≤A' ℓ≈A'

open PBMor

---------------------------
-- Value pre-perturbations
---------------------------

-- Given a predomain X, a *value pre-perturbation* on X is an
-- endomorphism on X that is bisimilar to the identity.

PrePtb : (A : PosetBisim ℓ ℓ' ℓ'') → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
PrePtb A = Σ[ f ∈ PBMor A A ] _≈mon_ {X = A} {Y = A} f Id

PrePtbId : {A : PosetBisim ℓ ℓ' ℓ''} → PrePtb A
PrePtbId .fst = Id
PrePtbId {A = A} .snd = ≈mon-refl {X = A} {Y = A} Id

PrePtb∘ : {A : PosetBisim ℓ ℓ' ℓ''} → PrePtb A → PrePtb A → PrePtb A
PrePtb∘ g f .fst = (g .fst) ∘p (f .fst)
PrePtb∘ g f .snd = λ x y x≈y → g .snd (f .fst $ x) y (f .snd x y x≈y)


-- Equality of pre-perturbations follows from equality of the underlying endomorphisms.

PrePtb≡ : {A : PosetBisim ℓ ℓ' ℓ''} →
  (f1 f2 : PrePtb A) →
  f1 .fst .f ≡ f2 .fst .f → f1 ≡ f2
PrePtb≡ f g eq = Σ≡Prop (λ h → ≈mon-prop h Id) (eqPBMor _ _ eq)

EqEndomor→EqPrePtb : {A : PosetBisim ℓ ℓ' ℓ''} →
  (f1 f2 : PrePtb A) →
  f1 .fst ≡ f2 .fst → f1 ≡ f2
EqEndomor→EqPrePtb f1 f2 eq = Σ≡Prop (λ h → ≈mon-prop h Id) eq

-- The pre-perturbations on A form a monoid under composition.

Endo : (A : PosetBisim ℓ ℓ' ℓ'') -> Monoid (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
Endo A = makeMonoid {M = PrePtb A}
  PrePtbId PrePtb∘ (isSetΣSndProp PBMorIsSet λ f → ≈mon-prop f Id)
  (λ f g h → PrePtb≡ _ _ refl)
  (λ f → PrePtb≡ _ _ refl)
  (λ f → PrePtb≡ _ _ refl)


-- For any error domain B, the delay morphism δB : B → B is in Endo (U B)

δB-as-PrePtb : (B : ErrorDomain ℓB ℓ≤B ℓ≈B) → PrePtb (U-ob B)
δB-as-PrePtb B .fst = B.δ
  where module B = ErrorDomainStr (B .snd)
δB-as-PrePtb B .snd = B.δ≈id
  where module B = ErrorDomainStr (B .snd)


-- Shorthand for obtaining the underlying morphism

ptbV : {A : PosetBisim ℓA ℓ≤A ℓ≈A} →
  (M : Monoid ℓM) (iA : MonoidHom M (Endo A)) → ⟨ M ⟩ → PBMor A A
ptbV M iA m = iA .fst m .fst



--------------------------------
-- Computation pre-perturbations
--------------------------------

open CompErrorDomMor


CPrePtb : (B : ErrorDomain ℓ ℓ' ℓ'') → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
CPrePtb B = Σ[ ϕ ∈ ErrorDomMor B B ]
  _≈mon_ {X = U-ob B} {Y = U-ob B} (U-mor ϕ) Id


CPrePtbId : {B : ErrorDomain ℓ ℓ' ℓ''} → CPrePtb B
CPrePtbId .fst = IdE
CPrePtbId {B = B} .snd = ≈mon-refl {X = U-ob B} {Y = U-ob B} Id

CPrePtb∘ : {B : ErrorDomain ℓ ℓ' ℓ''} → CPrePtb B → CPrePtb B → CPrePtb B
CPrePtb∘ ϕ' ϕ .fst = (ϕ' .fst) ∘ed (ϕ .fst)
CPrePtb∘ ϕ' ϕ .snd = λ x y x≈y → ϕ' .snd _ _ (ϕ .snd x y x≈y)


-- Equality of pre-perturbations follows from equality of the
-- underlying endomorphisms.
CPrePtb≡ : {B : ErrorDomain ℓ ℓ' ℓ''} → (ϕ ϕ' : CPrePtb B) →
  ϕ .fst .ErrorDomMor.f .PBMor.f ≡ ϕ' .fst .ErrorDomMor.f .PBMor.f →
  ϕ ≡ ϕ'
  -- ErrorDomMor.fun (ϕ .fst) ≡ ErrorDomMor.fun (ϕ' .fst) → ϕ ≡ ϕ'
  -- This formulation causes an error when we provide refl as an
  -- argument to makeMonoid in the definition of CEndo.
CPrePtb≡ ϕ ϕ' eq =
  Σ≡Prop (λ h → ≈mon-prop (U-mor h) Id) (eqEDMor (ϕ .fst) (ϕ' .fst) eq)


EqEndomor→EqCPrePtb : {B : ErrorDomain ℓ ℓ' ℓ''} → (ϕ ϕ' : CPrePtb B) →
  ϕ .fst ≡ ϕ' .fst → ϕ ≡ ϕ'
EqEndomor→EqCPrePtb ϕ ϕ' eq = Σ≡Prop (λ h → ≈mon-prop (U-mor h) Id) eq


-- The pre-perturbations on B form a monoid under composition.
CEndo : (B : ErrorDomain ℓ ℓ' ℓ'') -> Monoid (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
CEndo B = makeMonoid {M = CPrePtb B}
  CPrePtbId CPrePtb∘ (isSetΣSndProp EDMorIsSet (λ ϕ → ≈mon-prop (U-mor ϕ) Id))
  (λ f g h → CPrePtb≡ _ _ refl)
  (λ f → CPrePtb≡ _ _ refl)
  (λ f → CPrePtb≡ _ _ refl)


-- For any predomain A, the delay morphism δ* : FA --o FA is in CEndo FA

open F-ob

δ*FA-as-PrePtb : (A : PosetBisim ℓA ℓ≤A ℓ≈A) → CPrePtb (F-ob A)
δ*FA-as-PrePtb A .fst = δ*
  where module A = PosetBisimStr (A .snd)
δ*FA-as-PrePtb A .snd = δ*≈id
  where module A = PosetBisimStr (A .snd)



-- Shorthand for obtaining the underlying morphism

ptbC : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  (M : Monoid ℓM) (iB : MonoidHom M (CEndo B)) → ⟨ M ⟩ → ErrorDomMor B B
ptbC M iB m = iB .fst m .fst





------------------------------------------------------------------------


-- Action of × on pre-perturbations

_×PrePtb_ :
  {A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂}
  (f : PrePtb A₁) (g : PrePtb A₂) → PrePtb (A₁ ×dp A₂)
(f ×PrePtb g) .fst = (f .fst) ×mor (g .fst)
(f ×PrePtb g) .snd (x , y) (x' , y') (x≈x' , y≈y') =
  (f .snd x x' x≈x') , (g .snd y y' y≈y')


-- Convenience: action of ⟶ on pre-perturbations
module _ {A : PosetBisim ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} where
  _⟶PrePtb_ :
    (f : PrePtb A) (ϕ : CPrePtb B) → CPrePtb (A ⟶ob B)
  (f ⟶PrePtb ϕ) .fst = (f .fst) ⟶mor (ϕ .fst) --  : ErrorDomMor (A ⟶ob B) (A ⟶ob B)
  (f ⟶PrePtb ϕ) .snd g₁ g₂ g₁≈g₂ x y x≈y = ϕ .snd _ _ (g₁≈g₂ _ _ (f .snd _ _ x≈y))

-- The above function defines two homomorphisms
-- (Endo A)^op → CEndo (A ⟶ B) and (CEndo B) → CEndo (A ⟶ B).

A⟶-PrePtb : {A : PosetBisim ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  MonoidHom ((Endo A) ^op) (CEndo (A ⟶ob B))
A⟶-PrePtb .fst g = g ⟶PrePtb CPrePtbId
A⟶-PrePtb .snd .IsMonoidHom.presε =
  EqEndomor→EqCPrePtb _ _ arrowPresIdVert
A⟶-PrePtb .snd .IsMonoidHom.pres· g h =
  EqEndomor→EqCPrePtb _ _
    (arrowPresCompVertLeft (h .fst) (g .fst) (CPrePtbId .fst))

⟶B-PrePtb : {A : PosetBisim ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  MonoidHom (CEndo B) (CEndo (A ⟶ob B))
⟶B-PrePtb .fst ϕ = PrePtbId ⟶PrePtb ϕ
⟶B-PrePtb .snd .IsMonoidHom.presε =
  EqEndomor→EqCPrePtb _ _ arrowPresIdVert
⟶B-PrePtb .snd .IsMonoidHom.pres· ϕ ϕ' =
  EqEndomor→EqCPrePtb _ _
    (arrowPresCompVertRight (PrePtbId .fst) (ϕ' .fst) (ϕ .fst))


-- Kleisli actions on pre-perturbations

-- TODO
A⟶K-PrePtb : {A : PosetBisim ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  MonoidHom ((CEndo (F-ob A)) ^op) (Endo (U-ob (A ⟶ob B)))
A⟶K-PrePtb {B = B} .fst ϕ .fst = ϕ .fst ⟶Kᴸ B
A⟶K-PrePtb .fst ϕ .snd = {!!}
A⟶K-PrePtb .snd .IsMonoidHom.presε = EqEndomor→EqPrePtb _ _ (KlArrowMorphismᴸ-id _)
A⟶K-PrePtb .snd .IsMonoidHom.pres· = {!!}


-- TODO
⟶KB-PrePtb : {A : PosetBisim ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  MonoidHom (Endo (U-ob B)) (Endo (U-ob (A ⟶ob B)))
⟶KB-PrePtb {A = A} .fst g .fst = A ⟶Kᴿ g .fst
⟶KB-PrePtb {A = A} {B = B} .fst g .snd =
  λ f f' f≈f' x y x≈y →
    -- NTS: PBMor.f (g .fst) (PBMor.f f x) ≈ (PBMor.f f' y)
    g .snd (f $ x) (f' $ y) (f≈f' x y x≈y)
⟶KB-PrePtb .snd .IsMonoidHom.presε = EqEndomor→EqPrePtb _ _ (KlArrowMorphismᴿ-id _)
⟶KB-PrePtb .snd .IsMonoidHom.pres· = {!!}



-- Given a retraction from A to A', we can turn a pre-perturbation on
-- A into a pre-pertubration on A'.
PrePtbRetract : (f : PBMor A A') → (g : PBMor A' A) → (f ∘p g ≡ Id) →
  PrePtb A → PrePtb A'
PrePtbRetract f g fg≡id h .fst = f ∘p (h .fst) ∘p g
PrePtbRetract {A = A} {A' = A'} f g fg≡id (h , h≈id) .snd =
  transport (λ i → (f ∘p h ∘p g) ≈mon fg≡id i) f∘h∘g≈f∘g
  where
    f∘h∘g≈f∘g : (f ∘p h ∘p g) ≈mon (f ∘p g)
    f∘h∘g≈f∘g x y x≈y = f .pres≈ (h≈id (g $ x) (g $ y) (g .pres≈ x≈y))


-- Need g g' ≈ Id and ψ ψ' ≈ Id
-- PrePtbIso :
--   {A : PosetBisim ℓA ℓ≤A ℓ≈A}  {A' : PosetBisim ℓA' ℓ≤A' ℓ≈A'}
--   {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'} →
--   (g : PBMor A' A) (g' : PBMor A A') (ψ : ErrorDomMor B B') (ψ' : ErrorDomMor B' B) →
--   CPrePtb (A ⟶ob B) → CPrePtb (A' ⟶ob B')
-- PrePtbIso g g' ψ ψ' p .fst = (g ⟶mor ψ) ∘ed (g' ⟶mor ψ')
-- PrePtbIso g g' ψ ψ' p .snd g₁ g₂ g₁≈g₂ x y x≈y = {!ψ.pres≈ ?!}
--   where
--     module ψ = ErrorDomMor ψ
--     module ψ' = ErrorDomMor ψ'
--     module g = PBMor g
--     module g' = PBMor g'
--     module arr₁ = ErrorDomMor (g ⟶mor ψ)
--     module arr₂ = ErrorDomMor (g' ⟶mor ψ')


-- Action of the U functor on pre-perturbations

U-PrePtb :
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} → CPrePtb B → PrePtb (U-ob B)
U-PrePtb ϕ .fst = U-mor (ϕ .fst)
U-PrePtb ϕ .snd = ϕ .snd


-- The above action defines a monoid homomorphism from CEndo B to Endo UB.

CEndo-B→Endo-UB : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  MonoidHom (CEndo B) (Endo (U-ob B))
CEndo-B→Endo-UB .fst = U-PrePtb
CEndo-B→Endo-UB .snd .IsMonoidHom.presε = refl
CEndo-B→Endo-UB .snd .IsMonoidHom.pres· ϕ ϕ' = refl

-- Action of F on pre-perturbations

open F-ob
open F-mor

F-PrePtb : {A : PosetBisim ℓA ℓ≤A ℓ≈A} → PrePtb A → CPrePtb (F-ob A)
F-PrePtb f .fst = F-mor (f .fst)
F-PrePtb {A = A} f .snd =
  transport (λ i → U-mor (F-mor (f .fst)) ≈mon (lem2 i)) lem1
  where
    module A = PosetBisimStr (A .snd)
    open MapPresBisim
    open MapProperties
    
    lem1 : (U-mor (F-mor (f .fst))) ≈mon (U-mor (F-mor Id))
    lem1 = map-pres-≈
      ⟨ A ⟩ ⟨ A ⟩ A._≈_ A._≈_
      A.is-prop-valued-Bisim A.is-refl-Bisim A.is-sym
      (f .fst .PBMor.f) id (f .snd)

    lem2 : U-mor (F-mor Id) ≡ (Id {X = U-ob (F-ob A)})
    lem2 = eqPBMor _ _ (pres-id)

-- NTS  : map f ≈ id

-- Know : f ≈ id
-- Know : If f ≈ g, then map f ≈ map g
-- Know : map id ≡ id


-- F-PrePtb {A = A} f .snd x y x≈y =
--   transport (cong₂ UF._≈_ refl {!funExt⁻ pres-id ?!}) (F-mor (f .fst) .ErrorDomMor.f .PBMor.pres≈ x≈y)
--   where
    
--     module UF = PosetBisimStr ((U-ob (F-ob A)) .snd)
--     open MapProperties


-- The above action defines a monoid homomorphism from Endo A to CEndo FA.

Endo-A→CEndo-FA : {A : PosetBisim ℓA ℓ≤A ℓ≈A} →
  MonoidHom (Endo A) (CEndo (F-ob A))
Endo-A→CEndo-FA .fst = F-PrePtb
Endo-A→CEndo-FA .snd .IsMonoidHom.presε =
  EqEndomor→EqCPrePtb _ _ F-mor-pres-id
Endo-A→CEndo-FA .snd .IsMonoidHom.pres· f g =
  EqEndomor→EqCPrePtb _ _ (F-mor-pres-comp (f .fst) (g .fst))

-- Actions of A×_ and _×A on pre-perturbations
×A-PrePtb : MonoidHom (Endo A) (Endo (A ×dp A'))
×A-PrePtb .fst p .fst = ×-intro (p .fst ∘p π1 ) π2
×A-PrePtb .fst p .snd x y x≈y = (p .snd _ _ (x≈y .fst)) , (x≈y .snd)
×A-PrePtb .snd .IsMonoidHom.presε = refl
×A-PrePtb .snd .IsMonoidHom.pres· x y = refl

A×-PrePtb : MonoidHom (Endo A') (Endo (A ×dp A'))
A×-PrePtb .fst p .fst = ×-intro π1 (p .fst ∘p π2 )
A×-PrePtb .fst p .snd x y x≈y = x≈y .fst , (p .snd _ _ (x≈y .snd))
A×-PrePtb .snd .IsMonoidHom.presε = refl
A×-PrePtb .snd .IsMonoidHom.pres· x y = refl



-- Given a family of predomains B over a discrete type X, a distinguished value
-- x : X and perturbation px* : Bx → Bx, define a family of perturbations p_y over
-- (y : X) such that p_y = px* if y ≡ x, and p_y = Id otherwise.
module PtbIfEqual  {ℓX : Level} (X : Type ℓX) (dec : ∀ (x y : X) → Dec (x ≡ y))
  {ℓ ℓ≤ ℓ≈ : Level} {B : X → PosetBisim ℓ ℓ≤ ℓ≈} where

  isSetX : isSet X
  isSetX = Discrete→isSet dec


  PtbIfEqual : ∀ x → ⟨ Endo (B x) ⟩ → ∀ y → ⟨ Endo (B y) ⟩
  PtbIfEqual x px y with (dec x y)
  -- TODO: not sure about how this will behave definitionally
  ... | yes eq = subst (λ z → ⟨ Endo (B z) ⟩) eq px 
  ... | no ¬p = PrePtbId

  -- Beta laws
  PtbIfEqual-eq : ∀ x y p → (eq : x ≡ y) →
    PtbIfEqual x p y ≡ subst _ eq p
  PtbIfEqual-eq x y p eq with (dec x y)
  ... | yes eq' = λ i → subst (λ z → ⟨ Endo (B z) ⟩) (eq'≡eq i) p
    where
      eq'≡eq : eq' ≡ eq
      eq'≡eq = isSetX x y eq' eq
  ... | no neq = ⊥.rec (neq eq)

  PtbIfEqual-neq : ∀ x y p → (neq : ¬ (x ≡ y)) →
    PtbIfEqual x p y ≡ PrePtbId
  PtbIfEqual-neq x y p neq with (dec x y)
  ... | yes eq = ⊥.rec (neq eq)
  ... | no _ = refl


  -- Identity and composition
  
  PtbIfEqual-ε : ∀ x y →
    PtbIfEqual x (PrePtbId {A = B x}) y ≡ PrePtbId
  PtbIfEqual-ε x y with (dec x y)
  ... | yes eq = path2
    where
      path1 : PathP (λ i → ⟨ Endo (B (eq i)) ⟩) (PrePtbId {A = B x}) (PrePtbId {A = B y})
      path1 i = PrePtbId {A = B (eq i)}

      path2 : subst (λ z → ⟨ Endo (B z) ⟩) eq (PrePtbId {A = B x}) ≡ PrePtbId {A = B y}
      path2 = fromPathP path1
  ... | no _ = refl

  PtbIfEqual-comp : ∀ x y px px' →
    PtbIfEqual x (PrePtb∘ {A = B x} px px') y ≡ PrePtb∘ (PtbIfEqual x px y) (PtbIfEqual x px' y)
  PtbIfEqual-comp x y px px' with (dec x y)
  ... | yes eq = path
    where
      path : subst (λ z → ⟨ Endo (B z) ⟩) eq (PrePtb∘ px px') ≡
             PrePtb∘ (subst (λ z → ⟨ Endo (B z) ⟩) eq px)
                     (subst (λ z → ⟨ Endo (B z) ⟩) eq px')
      path = fromPathP (congP₂ (λ i → PrePtb∘ {A = B (eq i)}) (subst-filler _ eq px) (subst-filler _ eq px'))
  ... | no _ = refl

  --PtbIfEqual-hom : ∀ x → Section {!wkn!}


---------------------------
-- Pre-perturbations for Π
---------------------------
module _
  {ℓX : Level} (X : Type ℓX) (dec : ∀ (x y : X) → Dec (x ≡ y))
  {ℓ ℓ≤ ℓ≈ : Level} {B : X → PosetBisim ℓ ℓ≤ ℓ≈} where

  open PtbIfEqual X dec

  liftΠ : ((x : X) → ⟨ Endo (B x) ⟩) → ⟨ Endo (ΠP X B) ⟩
  liftΠ ps .fst = Π-mor _ _ _ (fst ∘ ps)
  liftΠ ps .snd bs bs' bs≈bs' x = ps x .snd (bs x) (bs' x) (bs≈bs' x)

  liftΠ-Id : liftΠ (λ x → PrePtbId) ≡ PrePtbId
  liftΠ-Id = PrePtb≡ _ _ refl -- surprised it works

  liftΠ-Comp : ∀ ps ps' →
    liftΠ (λ x → PrePtb∘ (ps x) (ps' x)) ≡ PrePtb∘ (liftΠ ps) (liftΠ ps')
  liftΠ-Comp ps ps' = PrePtb≡ _ _ refl -- surprised it works

  
  Π-PrePtb : (x : X) → MonoidHom (Endo (B x)) (Endo (ΠP X B))
  Π-PrePtb x .fst px = liftΠ (PtbIfEqual x px)
  Π-PrePtb x .snd .IsMonoidHom.presε =
    (cong liftΠ (funExt (λ y → PtbIfEqual-ε x y)) ∙ liftΠ-Id)
    -- (funExt (λ bs → funExt (λ y → decElim {A = {!!}} {!!} {!!} {!!})))
  Π-PrePtb x .snd .IsMonoidHom.pres· px px' =
    (cong liftΠ (funExt (λ y → PtbIfEqual-comp x y px px'))) ∙ (liftΠ-Comp _ _)


---------------------------
-- Pre-perturbations for Σ
---------------------------
module _
  {ℓX : Level} (X : hSet ℓX) (dec : ∀ (x y : ⟨ X ⟩) → Dec (x ≡ y))
  {ℓ ℓ≤ ℓ≈ : Level} {B : ⟨ X ⟩ → PosetBisim ℓ ℓ≤ ℓ≈} where
  
  open PosetBisimStr
  open PtbIfEqual ⟨ X ⟩ dec

  private
    module EndoB (x : ⟨ X ⟩) where
      open MonoidStr (Endo (B x) .snd) public

  -- Turn a family of semantic perturbations into a semantic
  -- perturbation on Σ X B.
  liftΣ : ((x : ⟨ X ⟩) → ⟨ Endo (B x) ⟩) → ⟨ Endo (ΣP X B) ⟩
  liftΣ ps .fst = Σ-mor _ _ _ (fst ∘ ps)
  liftΣ ps .snd (x₁ , b₁) (x₂ , b₂) (x₁≡x₂ , b₁₂≈b₂) =
    x₁≡x₂ , subst
      (λ z → (B x₂) .snd ._≈_ z b₂)
      (sym (fromPathP λ i → ps (x₁≡x₂ i) .fst .f (subst-filler (λ x → ⟨ B x ⟩) x₁≡x₂ b₁ i)))
      (ps x₂ .snd b₁₂ b₂ b₁₂≈b₂)
    where
      b₁₂ = subst (λ x → ⟨ B x ⟩) x₁≡x₂ b₁
      
    -- Goal   (subst T x₁≡x₂ (ps x₁ .fst .f b₁)) ≈ b₂
    -- Know     ps x₂ .fst .f (subst T x₁≡x₂ b₁) ≈ b₂
    -- Know     ps x₂ .fst .f b₁₂ ≡ subst T x₁≡x₂ (ps x₁ .fst .f b₁)

  liftΣ-Id : liftΣ (λ x → PrePtbId) ≡ PrePtbId
  liftΣ-Id = PrePtb≡ _ _ refl -- surprised it works

  liftΣ-Comp : ∀ ps ps' →
    liftΣ (λ x → PrePtb∘ (ps x) (ps' x)) ≡ PrePtb∘ (liftΣ ps) (liftΣ ps')
  liftΣ-Comp ps ps' = PrePtb≡ _ _ refl -- surprised it works


  Σ-PrePtb : (x : ⟨ X ⟩) → MonoidHom (Endo (B x)) (Endo (ΣP X B))
  Σ-PrePtb x .fst px = liftΣ (PtbIfEqual x px)
  Σ-PrePtb x .snd .IsMonoidHom.presε =
    (cong liftΣ (funExt (λ y → PtbIfEqual-ε x y))) ∙ liftΣ-Id
  Σ-PrePtb x .snd .IsMonoidHom.pres· px px' =
    (cong liftΣ (funExt (λ y → PtbIfEqual-comp x y px px'))) ∙ (liftΣ-Comp _ _)


-- Pre-perturbations for later
module _ {k : Clock} {ℓA ℓ≤A ℓ≈A : Level} {A : PosetBisim ℓA ℓ≤A ℓ≈A} where

  open Clocked k
  open ClockedCombinators k

  Endo▹ :
    ⟨ Endo A ⟩ → ⟨ Endo (PB▹ A) ⟩
  Endo▹ f .fst = Map▹ (f .fst)
  Endo▹ f .snd x~ x'~ x~≈x'~ t =  f .snd (x~ t) (x'~ t) (x~≈x'~ t)
  -- NTS: ▸ₜ[ f (x~ t) ≈ (x'~ t) ]
  -- Know: f ≈ id and ▸ₜ[ (x~ t) ≈ (x'≈ t) ]

  PrePtb▹ : MonoidHom (Endo A) (Endo (PB▹ A))
  PrePtb▹ .fst = Endo▹
  PrePtb▹ .snd .IsMonoidHom.presε = PrePtb≡ _ _ refl
  PrePtb▹ .snd .IsMonoidHom.pres· f g = PrePtb≡ _ _ refl


-- Iterated composition of pre-perturbations
-- Leaving in case it is needed...
{-
_^Vpreptb_ : {A : PosetBisim ℓA ℓ≤A ℓ≈A} → PrePtb A → ℕ → PrePtb A
(p ^Vpreptb n) .fst = (p .fst) ^m n
(p ^Vpreptb n) .snd = {!!}

_^Cpreptb_ : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} → CPrePtb B → ℕ → CPrePtb B
(p ^Cpreptb n) .fst = {!!} -- (p .fst) ^m n
  where open IteratedComp
(p ^Cpreptb n) .snd = {!!}
  where open IteratedComp


module NatMonoidHomomorphismFacts where
  open NatM→

  h-eq-V : ∀ {A : PosetBisim ℓA ℓ≤A ℓ≈A} →
    NatM→.f (Endo A) ≡ _^Vpreptb_
  h-eq-V {A = A} = funExt λ g → funExt (λ n → aux g n)
    where
      aux : ∀ g n →  NatM→.f (Endo A) g n ≡ (g ^Vpreptb n)
      aux g zero = PrePtb≡ _ _ refl
      aux g (suc n) = PrePtb≡ _ _ (funExt (λ x → {!!}))

  h-eq-C : ∀ {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
    NatM→.f (CEndo B) ≡ _^Cpreptb_
  h-eq-C = {!!}
-}



