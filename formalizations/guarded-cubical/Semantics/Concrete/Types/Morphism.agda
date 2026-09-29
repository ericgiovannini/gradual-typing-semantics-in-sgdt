{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Common.Later

module Semantics.Concrete.Types.Morphism (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
-- open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Instances.CartesianProduct as Cart hiding (_×_)
open import Cubical.Algebra.Monoid.Displayed.Instances.Sigma

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Combinators
open import Semantics.Concrete.Predomain.Constructions as Predom hiding (π1 ; π2)
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Perturbation.Semantic k

open import Semantics.Concrete.Types.Base k
open import Semantics.Concrete.Types.Constructions k

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓc ℓd : Level

    ℓA₁  ℓ≤A₁  ℓ≈A₁  ℓMA₁  : Level
    ℓA₂  ℓ≤A₂  ℓ≈A₂  ℓMA₂  : Level
    ℓA₃  ℓ≤A₃  ℓ≈A₃  ℓMA₃  : Level
    ℓA₄  ℓ≤A₄  ℓ≈A₄  ℓMA₄  : Level
    ℓA₁' ℓ≤A₁' ℓ≈A₁' ℓMA₁' : Level
    ℓA₂' ℓ≤A₂' ℓ≈A₂' ℓMA₂' : Level


    ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  ℓMAᵢ  : Level
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' ℓMAᵢ' : Level
    ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  ℓMAₒ  : Level
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' ℓMAₒ' : Level
    ℓcᵢ ℓcₒ                : Level

    ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ  ℓMBᵢ  : Level
    ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ' ℓMBᵢ' : Level
    ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ  ℓMBₒ  : Level
    ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ' ℓMBₒ' : Level
    ℓdᵢ ℓdₒ                : Level

    ℓX ℓY ℓR : Level

open PMor


module _
  {A₁ : Predomain ℓA₁ ℓ≤A₁ ℓ≈A₁}
  {A₂ : Predomain ℓA₂ ℓ≤A₂ ℓ≈A₂}
  {A₃ : Predomain ℓA₃ ℓ≤A₃ ℓ≈A₃}
  {A₄ : Predomain ℓA₄ ℓ≤A₄ ℓ≈A₄} where

  ∘p-Assoc : (f : PMor A₁ A₂) (g : PMor A₂ A₃) (h : PMor A₃ A₄)
    → (h ∘p g) ∘p f ≡ h ∘p (g ∘p f)
  ∘p-Assoc f g h = sym (CompPD-Assoc f g h)


module _
  (A : ValType ℓA ℓ≤A ℓ≈A ℓMA) (A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA')
  (f : PMor (ValType→Predomain A) (ValType→Predomain A'))

  where
  private
    |A| = ValType→Predomain A
    |A'| = ValType→Predomain A'

    MA  = PtbV A
    MA' = PtbV A'
    module MA  = MonoidStr (MA .snd)
    module MA' = MonoidStr (MA' .snd)
    
    iA  = fst ∘ interpV A .fst
    iA' = fst ∘ interpV A' .fst
    module iA  = IsMonoidHom (interpV A .snd)
    module iA' = IsMonoidHom (interpV A' .snd)


  CommSq : (g : PMor |A| |A|) (h : PMor |A'| |A'|) → Type _
  CommSq g h = (f ∘p g) ≡ (h ∘p f)

  VMorCommSq : ⟨ MA ⟩ → ⟨ MA' ⟩ → Type _
  VMorCommSq pA pA' = CommSq (iA pA) (iA' pA')
  -- i.e. (f ∘p iA pA) ≡ (iA' pA' ∘p f) where each side is a morphism from A to A'

  --             f
  --        A ------> A'
  --        |         |
  --  iA pA |         | iA' pA'
  --        |         | 
  --        V         V
  --        A ------> A'
  --             f

  isPropVMorCommSq : ∀ pA pA' → isProp (VMorCommSq pA pA')
  isPropVMorCommSq pA pA' = PMorIsSet (f ∘p iA pA) (iA' pA' ∘p f)

  -- identity
  IdVMorCommSq : VMorCommSq MA.ε MA'.ε
  IdVMorCommSq = subst2 CommSq (cong fst (sym iA.presε)) (cong fst (sym iA'.presε)) refl -- NTS: f ∘p Id ≡ Id ∘p f

  -- composition
  CompVMorCommSq : ∀ {pA qA pA' qA'}
    → VMorCommSq pA pA'
    → VMorCommSq qA qA'
    → VMorCommSq (pA MA.· qA) (pA' MA'.· qA')
  CompVMorCommSq {pA} {qA} {pA'} {qA'} α β =
    subst2 CommSq
      (cong fst (sym (iA.pres· pA qA)))
      (cong fst (sym (iA'.pres· pA' qA')))
      comp-sq
      where
        comp-sq : CommSq (iA pA ∘p iA qA) (iA' pA' ∘p iA' qA')
        comp-sq = sym (∘p-Assoc _ _ _)
          ∙ cong₂ _∘p_ α refl
          ∙ ∘p-Assoc _ _ _
          ∙ cong₂ _∘p_ refl β
          ∙ sym (∘p-Assoc _ _ _)
        -- NTS: f ∘p (iA pA ∘p iA qA) ≡ (iA' pA' ∘p iA' qA') ∘p f
        -- α : f ∘p iA pA ≡ iA' pA' ∘p f
        -- β : f ∘p iA qA ≡ iA' qA' ∘p f

  opaque
    VMorComm : Monoidᴰ (MA Cart.× MA') (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓA ℓ≤A) ℓ≈A) ℓA') ℓ≤A') ℓ≈A')
    VMorComm = submonoid→Monoidᴰ sub
      where
        sub : Submonoid (MA Cart.× MA') (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓA ℓ≤A) ℓ≈A) ℓA') ℓ≤A') ℓ≈A')
        sub .Submonoid.eltᴰ (pA , pA') = VMorCommSq pA pA'
        sub .Submonoid.εᴰ = IdVMorCommSq
        sub .Submonoid._·ᴰ_ {x = (pA , pA')} {y = (qA , qA')} = CompVMorCommSq
        sub .Submonoid.isPropEltᴰ = isPropVMorCommSq _ _

  PtbAction = Section (Σl VMorComm)


module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
         {f : PMor (ValType→Predomain A) (ValType→Predomain A')} where

  private
    MA  = PtbV A
    MA' = PtbV A'

  opaque
    unfolding VMorComm
    corecVMorComm : ∀ {ℓm}{M : Monoid ℓm}{ϕ : MonoidHom M (PtbV A Cart.× PtbV A')}
      → (∀ x → VMorCommSq A A' f (ϕ .fst x .fst) (ϕ .fst x .snd))
      → LocalSection ϕ (VMorComm A A' f)
    corecVMorComm = mkSectionSubmonoid (λ _ → isPropVMorCommSq A A' f _ _)

  corecPtbAction : {ℓP : Level} {P : Monoid ℓP} {ϕ : MonoidHom P MA}
   → (ϕ' : MonoidHom P MA')
   → (∀ x → VMorCommSq A A' f (ϕ .fst x) (ϕ' .fst x))
   → LocalSection ϕ (Σl (VMorComm A A' f))
  corecPtbAction ϕ' sq = corecL ϕ' (corecVMorComm (λ x → sq x))


-- The subcategory of value types for which the morphisms have an action on perturbations

module _ (A : ValType ℓA ℓ≤A ℓ≈A ℓMA) (A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA') where
    
  private
    |A| = ValType→Predomain A
    |A'| = ValType→Predomain A'
    MA = PtbV A
    MA' = PtbV A'
    iA = fst ∘ interpV A .fst
    iA' = fst ∘ interpV A' .fst

  VMor : Type (ℓ-max
      (ℓ-max (ℓ-max ℓA ℓA')   (ℓ-max ℓ≤A ℓ≤A'))
      (ℓ-max (ℓ-max ℓ≈A ℓ≈A') (ℓ-max ℓMA ℓMA')))
  VMor = Σ[ f ∈ PMor |A| |A'| ] PtbAction A A' f

module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'} where

  private
    |A| = ValType→Predomain A
    |A'| = ValType→Predomain A'
    MA = PtbV A
    MA' = PtbV A'
    iA = fst ∘ interpV A .fst
    iA' = fst ∘ interpV A' .fst

  mkVMor : (f : PMor |A| |A'|) (h : PtbAction A A' f)
    → VMor A A'
  mkVMor f h = f , h

  module _ (f : VMor A A') where

    VMor→PMor : PMor (ValType→Predomain A) (ValType→Predomain A')
    VMor→PMor = fst f

    VMor→MonHom : MonoidHom MA MA'
    VMor→MonHom = fstL' ∘hom (corecΣ (idMon (PtbV A)) (f .snd))

    opaque
      unfolding VMorComm
      VMor→coherence : ∀ pA → VMorCommSq A A' (f .fst) pA (VMor→MonHom .fst pA)
      VMor→coherence pA = f .snd .fst pA .snd



module _
  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁} {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂} where

  π1 : VMor (A₁ × A₂) A₁
  π1 = mkVMor
    Predom.π1
    (FP.elim (Σl (VMorComm (A₁ × A₂) A₁ Predom.π1))
      (corecPtbAction (idMon _) (λ pA₁ → {!!}))
      (corecPtbAction ε-hom     (λ pA₂ → {!!})))
    -- (corecL {!!} {!!}) {!!})





















{-
module _ (A : ValType ℓA ℓ≤A ℓ≈A ℓMA) (A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA') where

  private
    |A| = ValType→Predomain A
    |A'| = ValType→Predomain A'
    MA = PtbV A
    MA' = PtbV A'
    iA = fst ∘ interpV A .fst
    iA' = fst ∘ interpV A' .fst

  VMor : Type (ℓ-max
      (ℓ-max (ℓ-max ℓA ℓA')   (ℓ-max ℓ≤A ℓ≤A'))
      (ℓ-max (ℓ-max ℓ≈A ℓ≈A') (ℓ-max ℓMA ℓMA')))
  VMor = Σ[ f ∈ PMor |A| |A'| ] Σ[ h ∈ MonoidHom MA MA' ]
    (∀ (pA : ⟨ MA ⟩) → (f ∘p iA pA) ≡ (iA' (h .fst pA) ∘p f))


module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'} where

  private
    |A| = ValType→Predomain A
    |A'| = ValType→Predomain A'
    MA = PtbV A
    MA' = PtbV A'
    iA = fst ∘ interpV A .fst
    iA' = fst ∘ interpV A' .fst

  mkVMor : (f : PMor |A| |A'|) → (h : MonoidHom MA MA')
    → (eq : ∀ (pA : ⟨ MA ⟩) → (f ∘p iA pA) ≡ (iA' (h .fst pA) ∘p f))
    → VMor A A'
  mkVMor f h eq = f , h , eq

  module _ (f : VMor A A') where
  
    VMor→PMor : PMor |A| |A'|
    VMor→PMor = f .fst

    VMor→MonoidHom : MonoidHom MA MA'
    VMor→MonoidHom = f .snd .fst

    VMor→coherence : _
    VMor→coherence = f .snd .snd



module _
  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁}
  {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂}
  {A₃ : ValType ℓA₃ ℓ≤A₃ ℓ≈A₃ ℓMA₃}
  where

  _∘v_ : VMor A₂ A₃ → VMor A₁ A₂ → VMor A₁ A₃
  g ∘v f = mkVMor
    (VMor→PMor g ∘p VMor→PMor f)
    (VMor→MonoidHom g ∘hom VMor→MonoidHom f)
    (λ pA₁ →
        ∘p-Assoc _ _ _
      ∙ cong₂ _∘p_ refl (VMor→coherence f pA₁)
      ∙ sym (∘p-Assoc _ _ _)
      ∙ cong₂ _∘p_ (VMor→coherence g (VMor→MonoidHom f .fst pA₁)) refl
      ∙ ∘p-Assoc _ _ _)


module _
  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁} {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂} where

  π1 : VMor (A₁ × A₂) A₁
  π1 = mkVMor
    Predom.π1
    (FP.rec (idMon (PtbV A₁)) ε-hom)
    {!!}

module _
  {A₁ : ValType ℓA₁ ℓ≤A₁ ℓ≈A₁ ℓMA₁} {A₁' : ValType ℓA₁' ℓ≤A₁' ℓ≈A₁' ℓMA₁'}
  {A₂ : ValType ℓA₂ ℓ≤A₂ ℓ≈A₂ ℓMA₂} {A₂' : ValType ℓA₂' ℓ≤A₂' ℓ≈A₂' ℓMA₂'} where

-}
  
