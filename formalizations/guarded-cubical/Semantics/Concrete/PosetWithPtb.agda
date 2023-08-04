{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.PosetWithPtb (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Reflection.RecordEquiv
open import Cubical.Relation.Binary.Poset
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HigherCategories.ThinDoubleCategory.ThinDoubleCat
-- open import Cubical.HigherCategories.ThinDoubleCategory.Constructions.BinProduct
open import Cubical.Foundations.Function

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.CommMonoid.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_ ; _^_)

open import Cubical.Categories.Category.Base

open import Common.Common

open import Semantics.Lift k
open import Semantics.LockStepErrorOrdering k
open import Semantics.Concrete.DynNew k
open import Common.Poset.Convenience
open import Common.Poset.Constructions
open import Common.Poset.Monotone
open import Common.Poset.MonotoneRelation
open import Semantics.MonotoneCombinators


-- open import Semantics.Abstract.Model.Model


-- open Model

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
  ▹_ : Type ℓ -> Type ℓ
  ▹ A = ▹_,_ k A

isSetMonoid : (M : Monoid ℓ) -> isSet ⟨ M ⟩
isSetMonoid M = M .snd .isMonoid .isSemigroup .is-set
  where
    open MonoidStr
    open IsMonoid
    open IsSemigroup

monoidId : (M : Monoid ℓ) -> ⟨ M ⟩
monoidId M = M .snd .ε
  where open MonoidStr

commMonoidId : (M : CommMonoid ℓ) -> ⟨ M ⟩
commMonoidId M = M .snd .ε
  where open CommMonoidStr

_×M_ : CommMonoid ℓ -> CommMonoid ℓ' -> CommMonoid (ℓ-max ℓ ℓ')
M1 ×M M2 = makeCommMonoid
  {M = ⟨ M1 ⟩ × ⟨ M2 ⟩}
  (commMonoidId M1 , commMonoidId M2)
  (λ { (m1 , m2) (m1' , m2') -> (m1 ·M1 m1') , (m2 ·M2 m2')})
  (isSet× (isSetCommMonoid M1) (isSetCommMonoid M2))
  (λ { (m1 , m2) (m1' , m2') (m1'' , m2'') ->
    ≡-× (M1 .snd .isMonoid .isSemigroup .·Assoc m1 m1' m1'') (M2 .snd .isMonoid .isSemigroup .·Assoc m2 m2' m2'') })
  (λ { (m1 , m2) -> ≡-× (M1 .snd .isMonoid .·IdR m1) ((M2 .snd .isMonoid .·IdR m2)) })
  λ { (m1 , m2) (m1' , m2') -> ≡-× (M1 .snd .·Comm m1 m1') (M2 .snd .·Comm m2 m2') }
    where
      open CommMonoidStr
      open IsMonoid
      open IsSemigroup
      _·M1_ = M1 .snd ._·_
      _·M2_ = M2 .snd ._·_

-- Monoid of all monotone endofunctions on a poset
EndoMonFun : (X : Poset ℓ ℓ') -> Monoid (ℓ-max ℓ ℓ')
EndoMonFun X = makeMonoid {M = MonFun X X} Id mCompU MonFunIsSet
  (λ f g h -> eqMon _ _ refl) (λ f -> eqMon _ _ refl) (λ f -> eqMon _ _ refl)

--
-- A poset along with a monoid of monotone perturbation functions
--
record PosetWithPtb (ℓ ℓ' ℓ'' : Level) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ''))) where
  field
    P       : Poset ℓ ℓ'
    Perturb : CommMonoid ℓ''
    perturb : MonoidHom (CommMonoid→Monoid Perturb) (EndoMonFun P) -- Perturb (EndoMonFun P)
    --TODO: needs to be injective map
    -- Perturb : ⟨ EndoMonFun P ⟩

  ptb-fun : ⟨ Perturb ⟩ -> ⟨ EndoMonFun P ⟩
  ptb-fun = perturb .fst

open PosetWithPtb



_==>PWP_ : PosetWithPtb ℓ ℓ' ℓ'' -> PosetWithPtb ℓ ℓ' ℓ'' -> PosetWithPtb (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ') ℓ''
A ==>PWP B = record {
  P = (A .P) ==> (B .P) ;
  Perturb = A .Perturb ×M B .Perturb ; -- A .Perturb ×M B .Perturb ;
  perturb =
    (λ { (δᴬ , δᴮ) -> ptb-fun A δᴬ ~-> ptb-fun B δᴮ }) ,
    monoidequiv (eqMon _ _ (funExt (λ g -> let pfA = cong (MonFun.f) (perturb A .snd .presε) in
                                           let pfB = cong (MonFun.f) (perturb B .snd .presε) in
                                           eqMon _ _ λ i -> pfB i ∘ MonFun.f g ∘ pfA i)))
                (λ { (ma , mb) (ma' , mb') → eqMon _ _ (funExt (λ g ->
                  let pfA = cong MonFun.f (perturb A .snd .pres· ma ma') in
                  let pfB = cong MonFun.f (perturb B .snd .pres· mb mb') in
                  let ma-comm = (MonFun.f (ptb-fun A ma)) ∘ (MonFun.f (ptb-fun A ma')) ≡⟨ sym (cong (MonFun.f) (perturb A .snd .pres· ma ma')) ⟩
                                 MonFun.f (fst (perturb A) ((CommMonoid→Monoid (Perturb A) .snd MonoidStr.· ma) ma'))
                                   ≡⟨ (λ i -> MonFun.f (ptb-fun A (Perturb A .snd .isCommMonoid .·Comm ma ma' i)))⟩
                                 _ ≡⟨ cong MonFun.f (perturb A .snd .pres· ma' ma) ⟩
                                 _ ∎ in
                  eqMon _ _ ((λ i -> pfB i ∘ MonFun.f g ∘  pfA i) ∙ (λ i -> MonFun.f (ptb-fun B mb) ∘ MonFun.f (ptb-fun B mb') ∘ MonFun.f g ∘ ma-comm i)) ))    } )  }
    where
      open IsMonoidHom
      open CommMonoidStr
      open IsCommMonoid
      

-- Monoid of natural numbers with addition
nat-monoid : CommMonoid ℓ-zero
nat-monoid = makeCommMonoid {M = Nat} zero _+_ isSetℕ +-assoc +-zero +-comm

open ClockedCombinators k

δ-splits-n : {A : Type ℓ} -> ∀ (n n' : Nat) -> (δ {X = A} ^ n) ∘ (δ ^ n') ≡ δ ^ (n + n')
δ-splits-n zero n' = ∘-idʳ (δ ^ n')
δ-splits-n (suc n) n' = ∘-assoc δ (δ ^ n) (δ ^ n') ∙ cong (λ a -> δ ∘ a) (δ-splits-n n n')

𝕃PWP : PosetWithPtb ℓ ℓ' ℓ'' -> PosetWithPtb ℓ ℓ' ℓ''
𝕃PWP A = record {
  P = LiftPoset.𝕃 (A .P) ;
  Perturb = nat-monoid ×M A .Perturb ;
  perturb =
    fix f' , -- f' (next f) / fix f'
    fix {!!} }
    where
      MA = nat-monoid ×M A .Perturb
      open LiftPoset
      open IsMonoidHom
      f' : ▹ (⟨ MA ⟩ -> MonFun (𝕃 (A .P)) (𝕃 (A .P))) ->
             (⟨ MA ⟩ -> MonFun (𝕃 (A .P)) (𝕃 (A .P)))
      f' rec (n , ma) = record {
        f = λ { (η a) -> (δ ^ n) (η (MonFun.f (ptb-fun A ma) a)) ;
                 ℧ -> (δ ^ n) ℧ ;
                (θ la~) -> θ (λ t -> MonFun.f (rec t ((n , ma))) (la~ t))} ;
        isMon = λ x → {!!} }
      f : ⟨ MA ⟩ -> MonFun (𝕃 (A .P)) (𝕃 (A .P))
      f ma = fix f' ma

      

      unfold-f : f ≡ f' (next f)
      unfold-f = fix-eq f'

      δ-fun : ∀ (n : Nat) (ma : ⟨ MA ⟩) -> (δ ^ n) ∘ (MonFun.f (f' (next f) ma)) ≡ (MonFun.f (f' (next f) ma)) ∘ (δ ^ n) -- (h ∘ (δ ^ n)) ≡ ((δ ^ n) ∘ h)
      δ-fun zero ma = refl
      δ-fun (suc n) ma = funExt (λ la -> cong δ (funExt⁻ (δ-fun n ma) la ∙ λ i -> MonFun.f (sym unfold-f i ma) ((δ ^ n) la)))

      {-
      δ-fun : ∀ (n : Nat) (ma : ⟨ MA ⟩) -> mCompU (Δ ^m n) (f' (next f) ma) ≡ mCompU (f' (next f) ma) (Δ ^m n) -- (h ∘ (δ ^ n)) ≡ ((δ ^ n) ∘ h)
      δ-fun zero ma = refl
      δ-fun (suc n) ma = eqMon _ _ (funExt (λ a -> cong δ {!funExt⁻ (cong MonFun.f (δ-fun n ma)) a!}))
      -}

      

      isHom' : ( ▹ IsMonoidHom (CommMonoid→Monoid (nat-monoid ×M A .Perturb) .snd) (f' (next f)) (EndoMonFun (𝕃 (A .P)) .snd))
              -> IsMonoidHom (CommMonoid→Monoid (nat-monoid ×M A .Perturb) .snd) (f' (next f)) (EndoMonFun (𝕃 (A .P)) .snd)
      isHom' IH = monoidequiv
        (eqMon _ _ (funExt (λ { (η a) -> {!!} ≡⟨ {!!} ⟩ {!!};
                                (θ la) -> {!!}; μ -> {!!} })))
        λ { (n , ma) (n' , ma') → eqMon _ _ (funExt λ { (η a) -> {!!} ; (θ la) -> {!!}; μ -> {!!} })}

--MonFun A A' -> MonFun B B' -> MonFun (A × B) (A'× B')
_×PWP_ : PosetWithPtb ℓ ℓ' ℓ'' -> PosetWithPtb ℓ ℓ' ℓ'' -> PosetWithPtb ℓ (ℓ-max ℓ' ℓ') ℓ''
A ×PWP B = record {
  P = (A .P) ×p (B .P) ;
  Perturb = A .Perturb ×M B .Perturb ;
  perturb =
    (λ { (ma , mb) -> PairFun (mCompU (ptb-fun A ma) π1) (mCompU (ptb-fun B mb) π2) }),
    monoidequiv
      (eqMon _ _
        (funExt (λ { (a , b) →
        ≡-× (funExt⁻ (cong MonFun.f (perturb A .snd .presε)) a)
             (funExt⁻ (cong MonFun.f (perturb B .snd .presε)) b) })))
     λ { (ma , mb) (ma' , mb') →
       eqMon _ _
             (funExt (λ { (a , b ) -> ≡-× (funExt⁻ (cong MonFun.f (perturb A .snd .pres· ma ma')) a)
                                           (funExt⁻ (cong MonFun.f (perturb B .snd .pres· mb mb')) b) })) }
  }
  where
    open MonoidStr
    open IsMonoidHom

--
-- Monotone functions on Posets with Perturbations
--
PosetWithPtb-Vert : {ℓ ℓ' ℓ'' : Level} (P1 P2 : PosetWithPtb ℓ ℓ' ℓ'') -> Type {!!} -- (ℓ-max ℓ ℓ')
PosetWithPtb-Vert P1 P2 = MonFun (P1 .P) (P2 .P)
-- TODO should there be a condition on preserving the perturbations?


--
-- Monotone relations on Posets with Perturbations
--

record FillersFor {ℓ ℓ'  ℓ'' ℓR : Level} (P1 P2 : PosetWithPtb ℓ ℓ' ℓ'') (R : MonRel (P1 .P) (P2 .P) ℓR) :
  Type (ℓ-max (ℓ-max ℓ ℓ'') ℓR) where
  open PosetWithPtb
  field
    fillerL-e : ∀ (δᴮ : ⟨ P2 .Perturb ⟩ ) ->
      Σ[ δᴬ ∈ ⟨ P1 .Perturb ⟩ ]
        TwoCell (R .MonRel.R) (R .MonRel.R)
              (MonFun.f (ptb-fun P1 δᴬ)) (MonFun.f (ptb-fun P2 δᴮ))
    fillerL-p : ∀ (δᴸᴮ : ⟨ 𝕃PWP  P2 .Perturb ⟩ ) ->
      Σ[ δᴸᴬ ∈ ⟨ 𝕃PWP  P1 .Perturb ⟩ ]
        TwoCell (LiftRelation._≾_ ⟨ P1 .P ⟩ ⟨ P2 .P ⟩ (R .MonRel.R))
                (LiftRelation._≾_ ⟨ P1 .P ⟩ ⟨ P2 .P ⟩ (R .MonRel.R))
             (MonFun.f (ptb-fun (𝕃PWP P1) δᴸᴬ)) (MonFun.f (ptb-fun (𝕃PWP P2) δᴸᴮ))
    fillerR-e : ∀ (δᴬ : ⟨ P1 .Perturb ⟩) ->
      Σ[ δᴮ ∈ ⟨ P2 .Perturb ⟩ ]
        TwoCell (R .MonRel.R) (R .MonRel.R)
              (MonFun.f (ptb-fun P1 δᴬ)) (MonFun.f (ptb-fun P2 δᴮ))
    fillerR-p : ∀ (δᴸᴬ : ⟨ 𝕃PWP P1 .Perturb ⟩ ) ->
      Σ[ δᴸᴮ ∈ ⟨ 𝕃PWP P2 .Perturb ⟩ ]
        TwoCell (LiftRelation._≾_ ⟨ P1 .P ⟩ ⟨ P2 .P ⟩ (R .MonRel.R)) 
                (LiftRelation._≾_ ⟨ P1 .P ⟩ ⟨ P2 .P ⟩ (R .MonRel.R))
              (MonFun.f (ptb-fun (𝕃PWP P1) δᴸᴬ)) (MonFun.f (ptb-fun (𝕃PWP P2) δᴸᴮ))


-- TODO: Show this is a set by showing that the Sigma type it is iso to
-- is a set (ΣIsSet2ndProp)
unquoteDecl FillersForIsoΣ = declareRecordIsoΣ FillersForIsoΣ (quote (FillersFor))

FillersFor-Set : ∀ {ℓ ℓ' ℓ'' ℓR : Level} {P1 P2 : PosetWithPtb ℓ ℓ'  ℓ''} {R : MonRel (P1 .P) (P2 .P) ℓR}->
  isSet (FillersFor P1 P2 R)
FillersFor-Set {P1 = P1} {P2 = P2} {R = R} = 
                     isSetRetract (Iso.fun FillersForIsoΣ) (Iso.inv FillersForIsoΣ) (Iso.leftInv FillersForIsoΣ) (
                           isSet× (isSetΠ (λ δᴮ → isSetΣSndProp (isSetMonoid (CommMonoid→Monoid (P1 .Perturb))) λ δᴬ → isPropTwoCell (R .MonRel.is-prop-valued)))
                             (isSet× (isSetΠ (λ δᴸᴮ → isSetΣSndProp (isSet× (isSetMonoid (CommMonoid→Monoid nat-monoid)) (isSetMonoid (CommMonoid→Monoid (P1 .Perturb))))
                               λ δᴸᴬ → isPropTwoCell (LiftMonRel.ℝ (P1 .P) (P2 .P) R .MonRel.is-prop-valued)))
                                 (isSet× (isSetΠ (λ δᴬ → isSetΣSndProp (isSetMonoid (CommMonoid→Monoid (P2 .Perturb))) (λ δᴮ → isPropTwoCell (R .MonRel.is-prop-valued))))
                                   (isSetΠ (λ δᴸᴬ → isSetΣSndProp (isSet× (isSetMonoid (CommMonoid→Monoid nat-monoid)) (isSetMonoid (CommMonoid→Monoid (P2 .Perturb))))
                                      (λ δᴸᴮ → isPropTwoCell (LiftMonRel.ℝ (P1 .P) (P2 .P) R .MonRel.is-prop-valued)))))))
