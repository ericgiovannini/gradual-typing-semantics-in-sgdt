{-

   A (semantic) perturbation of a type is an endomorphism that is
   bisimilar to the identity, i.e., it "perturbs" the element but
   essentially does nothing.

-}


{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}


open import Common.Later

module Semantics.Concrete.Perturbation.Semantic (k : Clock) where

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
open import Cubical.Data.Sum


open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Sigma



open import Common.Common
open import Semantics.Concrete.LaterMonoid k
open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Constructions renaming (ℕ to NatP)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.Combinators
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.Monad k
open import Semantics.Concrete.Predomain.MonadRelationalResults k
open import Semantics.Concrete.Predomain.MonadCombinators k
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Predomain.Kleisli k



private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓA₃ ℓ≤A₃ ℓ≈A₃ : Level

    ℓMA₁ ℓMA₂ ℓMA₃ : Level
    ℓMB₁ ℓMB₂ ℓMB₃ : Level

    A : Predomain ℓA ℓ≤A ℓ≈A
    A' : Predomain ℓA' ℓ≤A' ℓ≈A'

open PMor

--------------------------------
-- Semantic value perturbations
--------------------------------

-- Given a predomain X, a *semantic value perturbation* on X is an
-- endomorphism on X that is bisimilar to the identity.

SemPtb : (A : Predomain ℓ ℓ' ℓ'') → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
SemPtb A = Σ[ f ∈ PMor A A ] _≈mon_ {X = A} {Y = A} f Id

SemPtbId : {A : Predomain ℓ ℓ' ℓ''} → SemPtb A
SemPtbId .fst = Id
SemPtbId {A = A} .snd = ≈mon-refl {X = A} {Y = A} Id

SemPtb∘ : {A : Predomain ℓ ℓ' ℓ''} → SemPtb A → SemPtb A → SemPtb A
SemPtb∘ g f .fst = (g .fst) ∘p (f .fst)
SemPtb∘ g f .snd = λ x y x≈y → g .snd (f .fst $ x) y (f .snd x y x≈y)


-- Equality of semantic perturbations follows from equality of the underlying endomorphisms.

SemPtb≡ : {A : Predomain ℓ ℓ' ℓ''} →
  (f1 f2 : SemPtb A) →
  f1 .fst .f ≡ f2 .fst .f → f1 ≡ f2
SemPtb≡ f g eq = Σ≡Prop (λ h → ≈mon-prop h Id) (eqPMor _ _ eq)

EqEndomor→EqSemPtb : {A : Predomain ℓ ℓ' ℓ''} →
  (f1 f2 : SemPtb A) →
  f1 .fst ≡ f2 .fst → f1 ≡ f2
EqEndomor→EqSemPtb f1 f2 eq = Σ≡Prop (λ h → ≈mon-prop h Id) eq

-- The semantic perturbations on A form a monoid under composition.

Endo : (A : Predomain ℓ ℓ' ℓ'') -> Monoid (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
Endo A = makeMonoid {M = SemPtb A}
  SemPtbId SemPtb∘ (isSetΣSndProp PMorIsSet λ f → ≈mon-prop f Id)
  (λ f g h → SemPtb≡ _ _ refl)
  (λ f → SemPtb≡ _ _ refl)
  (λ f → SemPtb≡ _ _ refl)


-- The endomorphisms (not necessarily bisimilar to identity) also form a monoid
|Endo| : (A : Predomain ℓ ℓ' ℓ'') -> Monoid (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
|Endo| A = makeMonoid {M = PMor A A}
  Id _∘p_ PMorIsSet
  (λ f g h → eqPMor _ _ refl) (λ f → eqPMor _ _ refl) (λ f → eqPMor _ _ refl)

-- For any error domain B, the delay morphism δB : B → B is in Endo (U B)

δB-as-SemPtb : (B : ErrorDomain ℓB ℓ≤B ℓ≈B) → SemPtb (U-ob B)
δB-as-SemPtb B .fst = B.δ
  where module B = ErrorDomainStr (B .snd)
δB-as-SemPtb B .snd = B.δ≈id
  where module B = ErrorDomainStr (B .snd)


-- Shorthand for obtaining the underlying morphism

ptbV : {A : Predomain ℓA ℓ≤A ℓ≈A} →
  (M : Monoid ℓM) (iA : MonoidHom M (Endo A)) → ⟨ M ⟩ → PMor A A
ptbV M iA m = iA .fst m .fst



--------------------------------------------
-- Semantic perturbations for error domains
--------------------------------------------

open CompErrorDomMor


CSemPtb : (B : ErrorDomain ℓ ℓ' ℓ'') → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
CSemPtb B = Σ[ ϕ ∈ ErrorDomMor B B ]
  _≈mon_ {X = U-ob B} {Y = U-ob B} (U-mor ϕ) Id


CSemPtbId : {B : ErrorDomain ℓ ℓ' ℓ''} → CSemPtb B
CSemPtbId .fst = IdE
CSemPtbId {B = B} .snd = ≈mon-refl {X = U-ob B} {Y = U-ob B} Id

CSemPtb∘ : {B : ErrorDomain ℓ ℓ' ℓ''} → CSemPtb B → CSemPtb B → CSemPtb B
CSemPtb∘ ϕ' ϕ .fst = (ϕ' .fst) ∘ed (ϕ .fst)
CSemPtb∘ ϕ' ϕ .snd = λ x y x≈y → ϕ' .snd _ _ (ϕ .snd x y x≈y)


-- Equality of semantic perturbations follows from equality of the
-- underlying endomorphisms.
CSemPtb≡ : {B : ErrorDomain ℓ ℓ' ℓ''} → (ϕ ϕ' : CSemPtb B) →
  ϕ .fst .ErrorDomMor.f .PMor.f ≡ ϕ' .fst .ErrorDomMor.f .PMor.f →
  ϕ ≡ ϕ'
  -- ErrorDomMor.fun (ϕ .fst) ≡ ErrorDomMor.fun (ϕ' .fst) → ϕ ≡ ϕ'
  -- This formulation causes an error when we provide refl as an
  -- argument to makeMonoid in the definition of CEndo.
CSemPtb≡ ϕ ϕ' eq =
  Σ≡Prop (λ h → ≈mon-prop (U-mor h) Id) (eqEDMor (ϕ .fst) (ϕ' .fst) eq)


EqEndomor→EqCSemPtb : {B : ErrorDomain ℓ ℓ' ℓ''} → (ϕ ϕ' : CSemPtb B) →
  ϕ .fst ≡ ϕ' .fst → ϕ ≡ ϕ'
EqEndomor→EqCSemPtb ϕ ϕ' eq = Σ≡Prop (λ h → ≈mon-prop (U-mor h) Id) eq


-- The semantic perturbations on B form a monoid under composition.
CEndo : (B : ErrorDomain ℓ ℓ' ℓ'') -> Monoid (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
CEndo B = makeMonoid {M = CSemPtb B}
  CSemPtbId CSemPtb∘ (isSetΣSndProp EDMorIsSet (λ ϕ → ≈mon-prop (U-mor ϕ) Id))
  (λ f g h → CSemPtb≡ _ _ refl)
  (λ f → CSemPtb≡ _ _ refl)
  (λ f → CSemPtb≡ _ _ refl)


-- For any predomain A, the delay morphism δ* : FA --o FA is in CEndo FA

open F-ob

δ*FA-as-SemPtb : (A : Predomain ℓA ℓ≤A ℓ≈A) → CSemPtb (F-ob A)
δ*FA-as-SemPtb A .fst = δ*
  where module A = PredomainStr (A .snd)
δ*FA-as-SemPtb A .snd = δ*≈id
  where module A = PredomainStr (A .snd)



-- Shorthand for obtaining the underlying morphism

ptbC : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  (M : Monoid ℓM) (iB : MonoidHom M (CEndo B)) → ⟨ M ⟩ → ErrorDomMor B B
ptbC M iB m = iB .fst m .fst





------------------------------------------------------------------------


-- Action of × on semantic perturbations

_×SemPtb_ :
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂}
  (f : SemPtb A₁) (g : SemPtb A₂) → SemPtb (A₁ ×dp A₂)
(f ×SemPtb g) .fst = (f .fst) ×mor (g .fst)
(f ×SemPtb g) .snd (x , y) (x' , y') (x≈x' , y≈y') =
  (f .snd x x' x≈x') , (g .snd y y' y≈y')

-- Action of ⊎ on semantic perturbations

_⊎SemPtb_ :
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁} {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂}
  (f : SemPtb A₁) (g : SemPtb A₂) → SemPtb (A₁ ⊎p A₂)
(f ⊎SemPtb g) .fst = f .fst ⊎-mor g .fst
(f ⊎SemPtb g) .snd (inl x₁) (inl y₁) x₁≈y₁ = lift (f .snd x₁ y₁ (lower x₁≈y₁))
(f ⊎SemPtb g) .snd (inr x₂) (inr y₂) x₂≈y₂ = lift (g .snd x₂ y₂ (lower x₂≈y₂))


-- Convenience: action of ⟶ on semantic perturbations
module _ {A : Predomain ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} where
  _⟶SemPtb_ :
    (f : SemPtb A) (ϕ : CSemPtb B) → CSemPtb (A ⟶ob B)
  (f ⟶SemPtb ϕ) .fst = (f .fst) ⟶mor (ϕ .fst) --  : ErrorDomMor (A ⟶ob B) (A ⟶ob B)
  (f ⟶SemPtb ϕ) .snd g₁ g₂ g₁≈g₂ x y x≈y = ϕ .snd _ _ (g₁≈g₂ _ _ (f .snd _ _ x≈y))

-- The above function defines two homomorphisms
-- (Endo A)^op → CEndo (A ⟶ B) and (CEndo B) → CEndo (A ⟶ B).

A⟶-SemPtb : {A : Predomain ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  MonoidHom ((Endo A) ^op) (CEndo (A ⟶ob B))
A⟶-SemPtb .fst g = g ⟶SemPtb CSemPtbId
A⟶-SemPtb .snd .IsMonoidHom.presε =
  EqEndomor→EqCSemPtb _ _ arrowPresIdVert
A⟶-SemPtb .snd .IsMonoidHom.pres· g h =
  EqEndomor→EqCSemPtb _ _
    (arrowPresCompVertLeft (h .fst) (g .fst) (CSemPtbId .fst))

⟶B-SemPtb : {A : Predomain ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  MonoidHom (CEndo B) (CEndo (A ⟶ob B))
⟶B-SemPtb .fst ϕ = SemPtbId ⟶SemPtb ϕ
⟶B-SemPtb .snd .IsMonoidHom.presε =
  EqEndomor→EqCSemPtb _ _ arrowPresIdVert
⟶B-SemPtb .snd .IsMonoidHom.pres· ϕ ϕ' =
  EqEndomor→EqCSemPtb _ _
    (arrowPresCompVertRight (SemPtbId .fst) (ϕ' .fst) (ϕ .fst))


-- Kleisli actions on semantic perturbations

-- ϕ ⟶K B

⟶KB-SemPtb : {A : Predomain ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  MonoidHom ((CEndo (F-ob A)) ^op) (Endo (U-ob (A ⟶ob B)))
⟶KB-SemPtb {B = B} .fst ϕ .fst = ϕ .fst ⟶Kᴸ B
⟶KB-SemPtb .fst ϕ .snd = {!!} -- follows from preservation of identity and bisimilarity
⟶KB-SemPtb .snd .IsMonoidHom.presε =
  EqEndomor→EqSemPtb _ _ (KlArrowMorphismᴸ-id _)
⟶KB-SemPtb .snd .IsMonoidHom.pres· ϕ ϕ' =
  EqEndomor→EqSemPtb _ _ (KlArrowMorphismᴸ-comp (ϕ .fst) (ϕ' .fst) _)



-- A ⟶K g

A⟶K-SemPtb : {A : Predomain ℓA ℓ≤A ℓ≈A} {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  MonoidHom (Endo (U-ob B)) (Endo (U-ob (A ⟶ob B)))
A⟶K-SemPtb {A = A} .fst g .fst = A ⟶Kᴿ g .fst
A⟶K-SemPtb {A = A} {B = B} .fst g .snd =
  λ f f' f≈f' x y x≈y →
    -- NTS: PMor.f (g .fst) (PMor.f f x) ≈ (PMor.f f' y)
    g .snd (f $ x) (f' $ y) (f≈f' x y x≈y)
A⟶K-SemPtb .snd .IsMonoidHom.presε =
  EqEndomor→EqSemPtb _ _ (KlArrowMorphismᴿ-id _)
A⟶K-SemPtb .snd .IsMonoidHom.pres· g g' =
  EqEndomor→EqSemPtb _ _ (KlArrowMorphismᴿ-comp _ (g' .fst) (g .fst))


-- TODO Kleisli ×



-- Given a retraction from A to A', we can turn a pre-perturbation on
-- A into a pre-pertubration on A'.
module _
  {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
  (f : PMor A A') (g : PMor A' A)
  (retr : retract (f .PMor.f) (g .PMor.f))
  where

  private
    gf≡id : g ∘p f ≡ Id
    gf≡id = eqPMor _ _ (funExt retr)

    aux : SemPtb A' → SemPtb A
    aux pA' .fst = g ∘p (pA' .fst) ∘p f
    aux pA' .snd = transport (λ i → (g ∘p (pA' .fst) ∘p f) ≈mon gf≡id i) g∘pA'∘f≈g∘f
      where
        g∘pA'∘f≈g∘f : (g ∘p (pA' .fst) ∘p f) ≈mon (g ∘p f)
        g∘pA'∘f≈g∘f x y x≈y = g .pres≈ (pA' .snd (f $ x) (f $ y) (f .pres≈ x≈y))

    aux-id : aux SemPtbId ≡ SemPtbId
    aux-id = SemPtb≡ _ _ (funExt retr)

    aux-comp : (sec : section (f .PMor.f) (g .PMor.f)) →
      ∀ p p' → aux (SemPtb∘ p p') ≡ SemPtb∘ (aux p) (aux p')
    aux-comp sec p p' = SemPtb≡ _ _ (funExt (λ x →
      cong (PMor.f g) (cong (PMor.f (p .fst)) (sym (sec _)))))

  SemPtbIso : (sec : section (f .PMor.f) (g .PMor.f)) →
    MonoidHom (Endo A') (Endo A)
  SemPtbIso sec .fst = aux
  SemPtbIso sec .snd .IsMonoidHom.presε = aux-id
  SemPtbIso sec .snd .IsMonoidHom.pres· = aux-comp sec


PredomIso→EndoHom : PredomIso A A' → MonoidHom (Endo A) (Endo A')
PredomIso→EndoHom isom = SemPtbIso isom.inv isom.fun isom.invRight isom.invLeft
  where
    module isom = PredomIso isom


-- A predomain isomorphism between A and A' induces an isomorphism
-- of monoids between Endo A and Endo A':
PredomIso→EndoHom-inv₁ : (isom : PredomIso A A') →
  (PredomIso→EndoHom isom) ∘hom (PredomIso→EndoHom (PredomIso-Inv isom)) ≡ idMon (Endo A')
PredomIso→EndoHom-inv₁ isom =
  eqMonoidHom _ _ (funExt (λ f → SemPtb≡ _ _ (funExt (λ x →
    isom.invRight _ ∙ cong (PMor.f (f .fst)) (isom.invRight _)))))
    where module isom = PredomIso isom

PredomIso→EndoHom-inv₂ : (isom : PredomIso A A') →
  (PredomIso→EndoHom (PredomIso-Inv isom)) ∘hom (PredomIso→EndoHom isom) ≡ idMon (Endo A)
PredomIso→EndoHom-inv₂ isom =
  eqMonoidHom _ _ (funExt (λ f → SemPtb≡ _ _ (funExt (λ x →
    isom.invLeft _ ∙ cong (PMor.f (f .fst)) (isom.invLeft _)))))
    where module isom = PredomIso isom

module _
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁}
  {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂}
  {A₃ : Predomain ℓA₃ ℓ≤A₃ ℓ≈A₃}
  (iso : PredomIso A₁ A₂)
  (iso' : PredomIso A₂ A₃)
  where
  
  PredomIso→EndoHom-comp : PredomIso→EndoHom (compPredomIso iso iso') ≡
    PredomIso→EndoHom iso' ∘hom PredomIso→EndoHom iso
  PredomIso→EndoHom-comp = eqMonoidHom _ _ (funExt (λ p → SemPtb≡ _ _ (funExt (λ x → refl))))


SemPtbRetract : (f : PMor A A') → (g : PMor A' A) → (f ∘p g ≡ Id) →
  SemPtb A → SemPtb A'
SemPtbRetract f g fg≡id h .fst = f ∘p (h .fst) ∘p g
SemPtbRetract {A = A} {A' = A'} f g fg≡id (h , h≈id) .snd =
  transport (λ i → (f ∘p h ∘p g) ≈mon fg≡id i) f∘h∘g≈f∘g
  where
    f∘h∘g≈f∘g : (f ∘p h ∘p g) ≈mon (f ∘p g)
    f∘h∘g≈f∘g x y x≈y = f .pres≈ (h≈id (g $ x) (g $ y) (g .pres≈ x≈y))




-- Need g g' ≈ Id and ψ ψ' ≈ Id
-- SemPtbIso :
--   {A : Predomain ℓA ℓ≤A ℓ≈A}  {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}
--   {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'} →
--   (g : PMor A' A) (g' : PMor A A') (ψ : ErrorDomMor B B') (ψ' : ErrorDomMor B' B) →
--   CSemPtb (A ⟶ob B) → CSemPtb (A' ⟶ob B')
-- SemPtbIso g g' ψ ψ' p .fst = (g ⟶mor ψ) ∘ed (g' ⟶mor ψ')
-- SemPtbIso g g' ψ ψ' p .snd g₁ g₂ g₁≈g₂ x y x≈y = {!ψ.pres≈ ?!}
--   where
--     module ψ = ErrorDomMor ψ
--     module ψ' = ErrorDomMor ψ'
--     module g = PMor g
--     module g' = PMor g'
--     module arr₁ = ErrorDomMor (g ⟶mor ψ)
--     module arr₂ = ErrorDomMor (g' ⟶mor ψ')


-- Action of the U functor on semantic perturbations

U-SemPtb :
  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} → CSemPtb B → SemPtb (U-ob B)
U-SemPtb ϕ .fst = U-mor (ϕ .fst)
U-SemPtb ϕ .snd = ϕ .snd


-- The above action defines a monoid homomorphism from CEndo B to Endo UB.

CEndo-B→Endo-UB : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
  MonoidHom (CEndo B) (Endo (U-ob B))
CEndo-B→Endo-UB .fst = U-SemPtb
CEndo-B→Endo-UB .snd .IsMonoidHom.presε = refl
CEndo-B→Endo-UB .snd .IsMonoidHom.pres· ϕ ϕ' = refl

-- Action of F on semantic perturbations

open F-ob
open F-mor

F-SemPtb : {A : Predomain ℓA ℓ≤A ℓ≈A} → SemPtb A → CSemPtb (F-ob A)
F-SemPtb f .fst = F-mor (f .fst)
F-SemPtb {A = A} f .snd =
  transport (λ i → U-mor (F-mor (f .fst)) ≈mon (lem2 i)) lem1
  where
    module A = PredomainStr (A .snd)
    open MapPresBisim
    open MapProperties
    
    lem1 : (U-mor (F-mor (f .fst))) ≈mon (U-mor (F-mor Id))
    lem1 = map-pres-≈
      ⟨ A ⟩ ⟨ A ⟩ A._≈_ A._≈_
      A.is-prop-valued-Bisim A.is-refl-Bisim A.is-sym
      (f .fst .PMor.f) id (f .snd)

    lem2 : U-mor (F-mor Id) ≡ (Id {X = U-ob (F-ob A)})
    lem2 = eqPMor _ _ (pres-id)

-- NTS  : map f ≈ id

-- Know : f ≈ id
-- Know : If f ≈ g, then map f ≈ map g
-- Know : map id ≡ id


-- F-SemPtb {A = A} f .snd x y x≈y =
--   transport (cong₂ UF._≈_ refl {!funExt⁻ pres-id ?!}) (F-mor (f .fst) .ErrorDomMor.f .PMor.pres≈ x≈y)
--   where
    
--     module UF = PredomainStr ((U-ob (F-ob A)) .snd)
--     open MapProperties


-- The above action defines a monoid homomorphism from Endo A to CEndo FA.

Endo-A→CEndo-FA : {A : Predomain ℓA ℓ≤A ℓ≈A} →
  MonoidHom (Endo A) (CEndo (F-ob A))
Endo-A→CEndo-FA .fst = F-SemPtb
Endo-A→CEndo-FA .snd .IsMonoidHom.presε =
  EqEndomor→EqCSemPtb _ _ F-mor-pres-id
Endo-A→CEndo-FA .snd .IsMonoidHom.pres· f g =
  EqEndomor→EqCSemPtb _ _ (F-mor-pres-comp (f .fst) (g .fst))

-- Actions of A×_ and _×A on semantic perturbations
×A-SemPtb : MonoidHom (Endo A) (Endo (A ×dp A'))
×A-SemPtb .fst p .fst = ×-intro (p .fst ∘p π1 ) π2
×A-SemPtb .fst p .snd x y x≈y = (p .snd _ _ (x≈y .fst)) , (x≈y .snd)
×A-SemPtb .snd .IsMonoidHom.presε = refl
×A-SemPtb .snd .IsMonoidHom.pres· x y = refl

A×-SemPtb : MonoidHom (Endo A') (Endo (A ×dp A'))
A×-SemPtb .fst p .fst = ×-intro π1 (p .fst ∘p π2 )
A×-SemPtb .fst p .snd x y x≈y = x≈y .fst , (p .snd _ _ (x≈y .snd))
A×-SemPtb .snd .IsMonoidHom.presε = refl
A×-SemPtb .snd .IsMonoidHom.pres· x y = refl

×A-SemPtb-Ind : (p₁ p₂ : ⟨ Endo A ⟩) →
  p₁ ≡ p₂ → ×A-SemPtb {A' = A'} .fst p₁ ≡ ×A-SemPtb .fst p₂
×A-SemPtb-Ind p₁ p₂ p₁≡p₂ = SemPtb≡ _ _
  (funExt (λ {(x , y) → ≡-× (funExt⁻ (cong (PMor.f ∘ fst) p₁≡p₂) x) refl}))

A×-SemPtb-Ind : (p₁ p₂ : ⟨ Endo A' ⟩) →
   p₁ ≡ p₂ → A×-SemPtb {A = A} .fst p₁ ≡ A×-SemPtb .fst p₂
A×-SemPtb-Ind p₁ p₂ p₁≡p₂ = SemPtb≡ _ _
  (funExt (λ {(x , y) → ≡-× refl (funExt⁻ (cong (PMor.f ∘ fst) p₁≡p₂) y)}))

×-SemPtb-Ind : (p p' : ⟨ Endo (A ×dp A') ⟩) →
  π1 ∘p (p .fst) ≡ π1 ∘p (p' .fst) →
  π2 ∘p (p .fst) ≡ π2 ∘p (p' .fst) →
  p ≡ p'
×-SemPtb-Ind p p' eq₁ eq₂ = SemPtb≡ _ _ (funExt (λ {(x , y) →
  ≡-× (funExt⁻ (cong PMor.f eq₁) (x , y)) (funExt⁻ (cong PMor.f eq₂) (x , y))}))


-- Actions of A⊎_ and _⊎A on semantic perturbations
module _ {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}  where

  private
    aux : SemPtb A → SemPtb (A ⊎p A')
    aux pA = pA ⊎SemPtb SemPtbId

    lem-id : aux SemPtbId ≡ SemPtbId {A = A ⊎p A'} 
    lem-id = SemPtb≡ _ _
      (funExt (λ { (inl _) → refl ; (inr _) → refl}))

    lem-comp : ∀ (f g : SemPtb A) → aux (SemPtb∘ f g) ≡ SemPtb∘ (aux f) (aux g)
      -- ((SemPtb∘ f g) ⊎SemPtb SemPtbId) ≡
      -- SemPtb∘ (f ⊎SemPtb SemPtbId) (g ⊎SemPtb SemPtbId)
    lem-comp f g = SemPtb≡ _ _ (funExt lem')
      where
        lem' : (x : ⟨ A ⊎p A' ⟩) →
                 (aux (SemPtb∘ f g) .fst .PMor.f x) ≡
                 (SemPtb∘ (aux f) (aux g) .fst .PMor.f x)
        lem' (inl x) = refl
        lem' (inr x) = refl
      
  ⊎A-SemPtb : MonoidHom (Endo A) (Endo (A ⊎p A'))
  ⊎A-SemPtb .fst = aux
  ⊎A-SemPtb .snd .IsMonoidHom.presε = lem-id
  ⊎A-SemPtb .snd .IsMonoidHom.pres· f g = lem-comp f g

module _ {A : Predomain ℓA ℓ≤A ℓ≈A} {A' : Predomain ℓA' ℓ≤A' ℓ≈A'}  where

  private
    aux : SemPtb A' → SemPtb (A ⊎p A')
    aux pA' = SemPtbId ⊎SemPtb pA'

    lem-id : aux SemPtbId ≡ SemPtbId {A = A ⊎p A'} 
    lem-id = SemPtb≡ _ _
      (funExt (λ { (inl _) → refl ; (inr _) → refl}))

    lem-comp : ∀ (f g : SemPtb A') → aux (SemPtb∘ f g) ≡ SemPtb∘ (aux f) (aux g)
    lem-comp f g = SemPtb≡ _ _ (funExt lem')
      where
        lem' : (x : ⟨ A ⊎p A' ⟩) →
                 (aux (SemPtb∘ f g) .fst .PMor.f x) ≡
                 (SemPtb∘ (aux f) (aux g) .fst .PMor.f x)
        lem' (inl x) = refl
        lem' (inr x) = refl
      
  A⊎-SemPtb : MonoidHom (Endo A') (Endo (A ⊎p A'))
  A⊎-SemPtb .fst = aux
  A⊎-SemPtb .snd .IsMonoidHom.presε = lem-id
  A⊎-SemPtb .snd .IsMonoidHom.pres· f g = lem-comp f g




module _
  {ℓX : Level} {X : Type ℓX}
  {ℓ ℓ≤ ℓ≈ : Level} {B : X → Predomain ℓ ℓ≤ ℓ≈} where

  PtbIfEqual : ∀ x → ⟨ Endo (B x) ⟩ → ∀ y → (Dec (x ≡ y)) → ⟨ Endo (B y) ⟩
  PtbIfEqual x px y = decRec
    -- TODO: not sure about how this will behave definitionally
    (λ eq → subst (λ z → ⟨ Endo (B z) ⟩) eq px)
    (λ _ → SemPtbId)

  -- (λ y → decRec
  --   (λ eq → SemPtbRetract
  --     (mTransport (cong B eq))
  --     (mTransport (sym (cong B eq)))
  --     (eqPMor _ _ (funExt (λ by → transportTransport⁻ (λ i → ⟨ B (eq i) ⟩) by)))
  --     px)
  --   (λ _ → SemPtbId)

  -- Beta laws
  PtbIfEqual-eq : ∀ x y p → (eq : x ≡ y) →
    PtbIfEqual x p y (yes eq) ≡ subst _ eq p
  PtbIfEqual-eq x y p eq = refl

  PtbIfEqual-neq : ∀ x y p → (neq : ¬ (x ≡ y)) →
    PtbIfEqual x p y (no neq) ≡ SemPtbId
  PtbIfEqual-neq x y p neq = refl


  PtbIfEqual-ε : ∀ x y (d : Dec (x ≡ y)) →
    PtbIfEqual x (SemPtbId {A = B x}) y d ≡ SemPtbId
  PtbIfEqual-ε x y (yes eq) = path
    where
      path : subst (λ z → ⟨ Endo (B z) ⟩) eq (SemPtbId {A = B x}) ≡ SemPtbId {A = B y}
      path = fromPathP (λ i → SemPtbId {A = B (eq i)})
  PtbIfEqual-ε x y (no neq) = refl


  PtbIfEqual-comp : ∀ x y (d : Dec (x ≡ y)) px px' →
    PtbIfEqual x (SemPtb∘ {A = B x} px px') y d ≡
    SemPtb∘ (PtbIfEqual x px y d) (PtbIfEqual x px' y d)
  PtbIfEqual-comp x y (yes eq) px px' = path
   where
      path : subst (λ z → ⟨ Endo (B z) ⟩) eq (SemPtb∘ px px') ≡
             SemPtb∘ (subst (λ z → ⟨ Endo (B z) ⟩) eq px)
                     (subst (λ z → ⟨ Endo (B z) ⟩) eq px')
      path = fromPathP (congP₂ (λ i → SemPtb∘ {A = B (eq i)}) (subst-filler _ eq px) (subst-filler _ eq px'))
  PtbIfEqual-comp x y (no neq) px px' = refl

{-
-- Given a family of predomains B over a discrete type X, a distinguished value
-- x : X and perturbation px* : Bx → Bx, define a family of perturbations p_y over
-- (y : X) such that p_y = px* if y ≡ x, and p_y = Id otherwise.
module PtbIfEqual'  {ℓX : Level} (X : Type ℓX) (dec : ∀ (x y : X) → Dec (x ≡ y))
  {ℓ ℓ≤ ℓ≈ : Level} {B : X → Predomain ℓ ℓ≤ ℓ≈} where

  isSetX : isSet X
  isSetX = Discrete→isSet dec


  PtbIfEqual : ∀ x → ⟨ Endo (B x) ⟩ → ∀ y → ⟨ Endo (B y) ⟩
  PtbIfEqual x px y with (dec x y)
  -- TODO: not sure about how this will behave definitionally
  ... | yes eq = subst (λ z → ⟨ Endo (B z) ⟩) eq px 
  ... | no ¬p = SemPtbId

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
    PtbIfEqual x p y ≡ SemPtbId
  PtbIfEqual-neq x y p neq with (dec x y)
  ... | yes eq = ⊥.rec (neq eq)
  ... | no _ = refl


  -- Identity and composition
  
  PtbIfEqual-ε : ∀ x y →
    PtbIfEqual x (SemPtbId {A = B x}) y ≡ SemPtbId
  PtbIfEqual-ε x y with (dec x y)
  ... | yes eq = path2
    where
      path1 : PathP (λ i → ⟨ Endo (B (eq i)) ⟩) (SemPtbId {A = B x}) (SemPtbId {A = B y})
      path1 i = SemPtbId {A = B (eq i)}

      path2 : subst (λ z → ⟨ Endo (B z) ⟩) eq (SemPtbId {A = B x}) ≡ SemPtbId {A = B y}
      path2 = fromPathP path1
  ... | no _ = refl

  PtbIfEqual-comp : ∀ x y px px' →
    PtbIfEqual x (SemPtb∘ {A = B x} px px') y ≡ SemPtb∘ (PtbIfEqual x px y) (PtbIfEqual x px' y)
  PtbIfEqual-comp x y px px' with (dec x y)
  ... | yes eq = path
    where
      path : subst (λ z → ⟨ Endo (B z) ⟩) eq (SemPtb∘ px px') ≡
             SemPtb∘ (subst (λ z → ⟨ Endo (B z) ⟩) eq px)
                     (subst (λ z → ⟨ Endo (B z) ⟩) eq px')
      path = fromPathP (congP₂ (λ i → SemPtb∘ {A = B (eq i)}) (subst-filler _ eq px) (subst-filler _ eq px'))
  ... | no _ = refl

  --PtbIfEqual-hom : ∀ x → Section {!wkn!}
-}

--------------------------------
-- Semantic perturbations for Π
--------------------------------
module _
  {ℓX : Level} (X : Type ℓX) (dec : ∀ (x y : X) → Dec (x ≡ y))
  {ℓ ℓ≤ ℓ≈ : Level} {B : X → Predomain ℓ ℓ≤ ℓ≈} where


  liftΠ : ((x : X) → ⟨ Endo (B x) ⟩) → ⟨ Endo (ΠP X B) ⟩
  liftΠ ps .fst = Π-mor _ _ _ (fst ∘ ps)
  liftΠ ps .snd bs bs' bs≈bs' x = ps x .snd (bs x) (bs' x) (bs≈bs' x)

  liftΠ-Id : liftΠ (λ x → SemPtbId) ≡ SemPtbId
  liftΠ-Id = SemPtb≡ _ _ refl

  liftΠ-Comp : ∀ ps ps' →
    liftΠ (λ x → SemPtb∘ (ps x) (ps' x)) ≡ SemPtb∘ (liftΠ ps) (liftΠ ps')
  liftΠ-Comp ps ps' = SemPtb≡ _ _ refl

  
  Π-SemPtb : (x : X) → MonoidHom (Endo (B x)) (Endo (ΠP X B))
  Π-SemPtb x .fst px = liftΠ (λ y → PtbIfEqual x px y (dec x y))
  Π-SemPtb x .snd .IsMonoidHom.presε =
    (cong liftΠ (funExt (λ y → PtbIfEqual-ε x y (dec x y))) ∙ liftΠ-Id)
    -- (funExt (λ bs → funExt (λ y → decElim {A = {!!}} {!!} {!!} {!!})))
  Π-SemPtb x .snd .IsMonoidHom.pres· px px' =
    (cong liftΠ (funExt (λ y → PtbIfEqual-comp x y (dec x y) px px'))) ∙ (liftΠ-Comp _ _)


---------------------------
-- Semantic Perturbations for Σ
---------------------------
module _
  {ℓX : Level} (X : hSet ℓX) (dec : ∀ (x y : ⟨ X ⟩) → Dec (x ≡ y))
  {ℓ ℓ≤ ℓ≈ : Level} {B : ⟨ X ⟩ → Predomain ℓ ℓ≤ ℓ≈} where
  
  open PredomainStr

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

  liftΣ-Id : liftΣ (λ x → SemPtbId) ≡ SemPtbId
  liftΣ-Id = SemPtb≡ _ _ refl

  liftΣ-Comp : ∀ ps ps' →
    liftΣ (λ x → SemPtb∘ (ps x) (ps' x)) ≡ SemPtb∘ (liftΣ ps) (liftΣ ps')
  liftΣ-Comp ps ps' = SemPtb≡ _ _ refl


  Σ-SemPtb : (x : ⟨ X ⟩) → MonoidHom (Endo (B x)) (Endo (ΣP X B))
  Σ-SemPtb x .fst px = liftΣ λ y → PtbIfEqual x px y (dec x y)
  Σ-SemPtb x .snd .IsMonoidHom.presε =
    (cong liftΣ (funExt (λ y → PtbIfEqual-ε x y (dec x y)))) ∙ liftΣ-Id
  Σ-SemPtb x .snd .IsMonoidHom.pres· px px' =
    (cong liftΣ (funExt (λ y → PtbIfEqual-comp x y (dec x y) px px'))) ∙ (liftΣ-Comp _ _)


  Σ-SemPtb-eq : ∀ x (px : ⟨ Endo (B x) ⟩) → (y : ⟨ X ⟩) → (eq : (x ≡ y)) → (by : ⟨ B y ⟩) →
    Σ-SemPtb x .fst px .fst .PMor.f (y , by) ≡
    (x , px .fst .PMor.f (subst _ (sym eq) by))
  Σ-SemPtb-eq x px y eq by = ΣPathP (sym eq , lem (dec x y))
    where
      lem : ∀ (x≡y? : Dec (x ≡ y)) →
        PathP (λ i → ⟨ B (eq (~ i)) ⟩) (PtbIfEqual x px y x≡y? .fst .f by) (px .fst .PMor.f _)
      lem (yes eq') = {!!}
      lem (no neq) = ⊥.rec (neq eq)

  Σ-SemPtb-neq : ∀ x (px : ⟨ Endo (B x) ⟩) → (y : ⟨ X ⟩) → (¬ (x ≡ y)) → (by : ⟨ B y ⟩) →
    Σ-SemPtb x .fst px .fst .PMor.f (y , by) ≡ (y , by)
  Σ-SemPtb-neq x px y neq by = ΣPathP (refl , lem (dec x y))
    where
      lem : ∀ (x≡y? : Dec (x ≡ y)) → (PtbIfEqual x px y x≡y?) .fst .f by ≡ by
      lem (yes eq) = ⊥.rec (neq eq)
      lem (no _) = refl

  Σ-Endo-pres-fst : (p : ⟨ Endo (ΣP X B) ⟩) →
    (x : ⟨ X ⟩) (b : ⟨ B x ⟩) → p .fst .PMor.f (x , b) .fst ≡ x
  Σ-Endo-pres-fst p x b =
    let bisim = p .snd (x , b) (x , b) ((ΣP X B) .snd .PredomainStr.is-refl-Bisim (x , b)) in
        bisim .fst

  Σ-SemPtb-ind : (x : ⟨ X ⟩) (px : ⟨ Endo (B x) ⟩) (p : ⟨ Endo (ΣP X B) ⟩) →
    ((x' : ⟨ X ⟩) (b' : ⟨ B x' ⟩) → ¬ (x ≡ x') → p .fst .PMor.f (x' , b') ≡ (x' , b'))
    → (Σ-SemPtb x .fst px) ≡ p
  Σ-SemPtb-ind x px p eq = SemPtb≡ _ _ (funExt λ { (x' , b) → ΣPathP (sym (Σ-Endo-pres-fst p x' b) , {!!})})
    where
      lem : (x' : ⟨ X ⟩) (b : ⟨ B x' ⟩) (x≡x'? : Dec (x ≡ x')) →
        PathP (λ i → ⟨ B (sym (Σ-Endo-pres-fst p x' b) i) ⟩)
          (PMor.f {Y = B x'} (PtbIfEqual x px x' x≡x'? .fst) b)
          (p .fst .PMor.f (x' , b) .snd)
      lem x' b (yes x≡x') = {!!}
      lem x' b (no x≢x') =
        transport (λ i → PathP (λ j → fst (B {!!})) _ _) (λ i → eq x' b x≢x' (~ i) .snd) -- eq x' b x≢x' (~ i) .snd
      


{-
  Σ-SemPtb-ind : (p₁ p₂ : ⟨ Endo (ΣP X B) ⟩) →
    (∀ (x : ⟨ X ⟩) (b : ⟨ B x ⟩) → p₁ .fst .PMor.f (x , b) ≡ p₂ .fst .PMor.f (x , b)) →
    p₁ ≡ p₂
  Σ-SemPtb-ind p₁ p₂ eq =
    SemPtb≡ _ _ (funExt (λ {(x , b) → ΣPathP ((cong fst (eq x b)) , {!!})}))
-}    

{-
  Σ-SemPtb-ind : (x : ⟨ X ⟩) (p₁ p₂ : ⟨ Endo (B x) ⟩) →
    p₁ ≡ p₂ → (Σ-SemPtb x .fst p₁) ≡ (Σ-SemPtb x .fst p₂)
  Σ-SemPtb-ind x p₁ p₂ p₁≡p₂ = SemPtb≡ _ _ (funExt λ s → ΣPathP (refl , lem2 s))
    where
      lem1 : (x' : ⟨ X ⟩) (b : ⟨ B x' ⟩) (x≡x'? : Dec (x ≡ x')) →
        PMor.f (fst (PtbIfEqual x p₁ x' x≡x'?)) b ≡
        PMor.f (fst (PtbIfEqual x p₂ x' x≡x'?)) b
      lem1 x' b (yes x≡x') = cong (subst (λ x → ⟨ B x ⟩) x≡x') (funExt⁻ (cong (PMor.f ∘ fst) p₁≡p₂) _)
      lem1 x' b (no x≢x') i = b -- for some reason, Agda does not accept refl here...

      lem2 : (s : Σ[ x' ∈ ⟨ X ⟩ ] ⟨ B x' ⟩)  →
        PMor.f (fst (PtbIfEqual x p₁ (s .fst) (dec x _))) (s .snd) ≡
        PMor.f (fst (PtbIfEqual x p₂ (s .fst) (dec x _))) (s .snd)
      lem2 (x' , b) = lem1 x' b (dec x x')
-}


-- Semantic Perturbations for later
module _ {ℓA ℓ≤A ℓ≈A : Level} {A : Predomain ℓA ℓ≤A ℓ≈A} where

  open Clocked k
  open ClockedCombinators k

  Endo▹ :
    ⟨ Endo A ⟩ → ⟨ Endo (P▹ A) ⟩
  Endo▹ f .fst = Map▹ (f .fst)
  Endo▹ f .snd x~ x'~ x~≈x'~ t =  f .snd (x~ t) (x'~ t) (x~≈x'~ t)
  -- NTS: ▸ₜ[ f (x~ t) ≈ (x'~ t) ]
  -- Know: f ≈ id and ▸ₜ[ (x~ t) ≈ (x'≈ t) ]

  SemPtb▹ : MonoidHom (Endo A) (Endo (P▹ A))
  SemPtb▹ .fst = Endo▹
  SemPtb▹ .snd .IsMonoidHom.presε = SemPtb≡ _ _ refl
  SemPtb▹ .snd .IsMonoidHom.pres· f g = SemPtb≡ _ _ refl


module _ {A~ : ▹ k , Predomain ℓA ℓ≤A ℓ≈A} where

  -- We can turn a "later" semantic perturbation f : ▸_t (SemPtb (A~ t))
  -- into a semantic perturbation ▸f : SemPtb (P▸ X~).
  -- Moreover, the transformation is a homomorphism of monoids.

  open Clocked k
  
  Endo▸ : MonoidHom (Monoid▸ (λ t → Endo (A~ t))) (Endo (P▸ A~))
  Endo▸ .fst f~ .fst = PMor▸ (λ t → f~ t .fst)
  Endo▸ .fst f~ .snd =
    λ x1~ x2~ x1~≈x2~ → (λ t → (f~ t .snd) (x1~ t) (x2~ t) (x1~≈x2~ t))
  Endo▸ .snd .IsMonoidHom.presε = refl
  Endo▸ .snd .IsMonoidHom.pres· f~ g~ = refl




-- Iterated composition of semantic perturbations
-- Leaving in case it is needed...
{-
_^Vpreptb_ : {A : Predomain ℓA ℓ≤A ℓ≈A} → SemPtb A → ℕ → SemPtb A
(p ^Vpreptb n) .fst = (p .fst) ^m n
(p ^Vpreptb n) .snd = {!!}

_^Cpreptb_ : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} → CSemPtb B → ℕ → CSemPtb B
(p ^Cpreptb n) .fst = {!!} -- (p .fst) ^m n
  where open IteratedComp
(p ^Cpreptb n) .snd = {!!}
  where open IteratedComp


module NatMonoidHomomorphismFacts where
  open NatM→

  h-eq-V : ∀ {A : Predomain ℓA ℓ≤A ℓ≈A} →
    NatM→.f (Endo A) ≡ _^Vpreptb_
  h-eq-V {A = A} = funExt λ g → funExt (λ n → aux g n)
    where
      aux : ∀ g n →  NatM→.f (Endo A) g n ≡ (g ^Vpreptb n)
      aux g zero = SemPtb≡ _ _ refl
      aux g (suc n) = SemPtb≡ _ _ (funExt (λ x → {!!}))

  h-eq-C : ∀ {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
    NatM→.f (CEndo B) ≡ _^Cpreptb_
  h-eq-C = {!!}
-}



