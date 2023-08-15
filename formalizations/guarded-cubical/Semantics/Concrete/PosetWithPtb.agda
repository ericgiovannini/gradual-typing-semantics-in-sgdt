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
                  let ma-comm =  sym (cong MonFun.f (perturb A .snd .pres· ma ma'))
                                 ∙ (λ i -> MonFun.f (ptb-fun A (Perturb A .snd .isCommMonoid .·Comm ma ma' i)))
                                 ∙ cong MonFun.f (perturb A .snd .pres· ma' ma) in
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
      open MonoidStr
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

      δ-mapL-comm : ∀ (ma : ⟨ A .Perturb ⟩) -> δ ∘ mapL (MonFun.f (ptb-fun A ma)) ≡ mapL (MonFun.f (ptb-fun A ma)) ∘ δ
      δ-mapL-comm ma = sym (funExt (λ la -> mapL-theta (MonFun.f (ptb-fun A ma)) (next la)))

      δ-fun : ∀ (n : Nat) (ma : ⟨ MA ⟩) -> (δ ^ n) ∘ (MonFun.f (f' (next f) ma)) ≡ (MonFun.f (f' (next f) ma)) ∘ (δ ^ n)
      δ-fun zero ma = refl
      δ-fun (suc n) ma = funExt λ la -> cong δ (funExt⁻ (δ-fun n ma) la ∙ λ i -> MonFun.f (sym unfold-f i ma) ((δ ^ n) la))

      δ-mapL : ∀ (n : Nat) (ma : ⟨ A .Perturb ⟩) -> (δ ^ n) ∘ mapL (MonFun.f (ptb-fun A ma)) ≡ mapL (MonFun.f (ptb-fun A ma)) ∘ (δ ^ n)
      δ-mapL zero ma = refl
      δ-mapL (suc n) ma = δ ∘ ((δ ^ n) ∘ mapL (MonFun.f (ptb-fun A ma))) ≡⟨ cong (λ m -> δ ∘ m ) (δ-mapL n ma) ⟩
                          δ ∘ mapL (MonFun.f (ptb-fun A ma)) ∘ (δ ^ n) ≡⟨ cong (λ m -> m ∘ (δ ^ n)) (δ-mapL-comm ma) ⟩
                          mapL (MonFun.f (ptb-fun A ma)) ∘ (δ ∘ (δ ^ n)) ∎

      

      {- funExt λ la -> (δ ∘ ((δ ^ n) ∘ mapL (MonFun.f (ptb-fun A ma)))) la
                                         ≡⟨ cong (λ m -> (δ ∘ m) la) (δ-mapL n ma) ⟩ 
                                         (δ ∘ mapL (MonFun.f (ptb-fun A ma)) ∘ (δ ^ n)) la
                                         ≡⟨ {!!} ⟩
                                         (mapL (MonFun.f (ptb-fun A ma)) ∘ (δ ∘ (δ ^ n))) la ∎ -}
                                         
      

      perturb≡map' :  ∀ (n : Nat) (ma : ⟨ A .Perturb ⟩) -> (▹ (MonFun.f (f' (next f) (n , ma)) ≡ (δ ^ n) ∘  mapL (MonFun.f (ptb-fun A ma)))
                                                       -> MonFun.f (f' (next f) (n , ma)) ≡ (δ ^ n) ∘  mapL (MonFun.f (ptb-fun A ma)))
      perturb≡map' n ma IH = funExt (λ { (η a) -> cong (δ ^ n) (sym (mapL-eta (MonFun.f (ptb-fun A ma)) a)) ;
                                     ℧ -> cong (δ ^ n) (sym (ext-err _)) ;
                                     (θ la) -> sym ( {!!} ≡⟨ cong (δ ^ n) (mapL-theta (MonFun.f (ptb-fun A ma)) la) ⟩
                                                     {!!} ≡⟨ {!!} ⟩ {!!} )
                                                     --(δ ^ n) (θ (mapL (MonFun.f (ptb-fun A ma)) <$> la))
                                   })

      perturb≡map : ∀ (n : Nat) (ma : ⟨ A .Perturb ⟩) -> MonFun.f (f' (next f) (n , ma)) ≡ (δ ^ n) ∘  mapL (MonFun.f (ptb-fun A ma))
      perturb≡map n ma = fix (perturb≡map' n ma)

      isHomPerturb : IsMonoidHom (CommMonoid→Monoid (nat-monoid ×M A .Perturb) .snd) (f' (next f)) (EndoMonFun (𝕃 (A .P)) .snd)
      isHomPerturb = monoidequiv (eqMon _ _ ((perturb≡map 0 (CommMonoid→Monoid (A .Perturb) .snd .ε))
                                            ∙ (cong (λ a → mapL (MonFun.f a)) (perturb A .snd .presε))
                                            ∙ funExt (λ x → mapL-id x)))
                                 λ { (n , ma) (n' , ma') ->
                                   eqMon _ _ (_ ≡⟨ perturb≡map (n + n') ( CommMonoid→Monoid (A .Perturb) .snd ._·_ ma ma') ⟩
                                              _ ≡⟨ cong ( λ h -> (δ ^ (n + n')) ∘ (mapL (MonFun.f h) )) (perturb A .snd .pres· ma ma') ⟩
                                              (δ ^ (n + n')) ∘ mapL ((MonFun.f (ptb-fun A ma)) ∘ (MonFun.f (ptb-fun A ma')))
                                              ≡⟨ cong (λ h -> (δ ^ (n + n')) ∘ h) (funExt λ y -> λ i -> mapL-comp (MonFun.f (ptb-fun A ma)) ((MonFun.f (ptb-fun A ma'))) y i) ⟩
                                              (δ ^ (n + n')) ∘ (mapL (MonFun.f (ptb-fun A ma)) ∘ mapL (MonFun.f (ptb-fun A ma'))) ≡⟨ (cong (λ d -> d ∘ _) (sym (δ-splits-n n n'))) ⟩
                                              δ ^ n ∘ δ ^ n' ∘ mapL (MonFun.f (ptb-fun A ma)) ∘ mapL (MonFun.f (ptb-fun A ma'))
                                              ≡⟨ cong (λ m -> (δ ^ n) ∘ m ∘ mapL (MonFun.f (ptb-fun A ma'))) (δ-mapL n' ma) ⟩
                                              δ ^ n ∘ mapL (MonFun.f (ptb-fun A ma)) ∘ δ ^ n' ∘ mapL (MonFun.f (ptb-fun A ma'))
                                              ≡⟨ cong₂ (λ a b → a ∘ b) (sym (perturb≡map n ma)) (sym (perturb≡map n' ma')) ⟩ _ ∎ ) }
       {-
       ( ? ≡⟨ perturb≡map (n + n') ( CommMonoid→Monoid (A .Perturb) .snd ._·_ ma ma') ⟩
         ? ≡⟨ cong ( λ h -> (δ ^ (n + n')) ∘ (mapL (MonFun.f h) )) (perturb A .snd .pres· ma ma') ⟩
         ? ≡⟨ cong (λ h -> (δ ^ (n + n')) ∘ h) {!!} ⟩
         ? ≡⟨ {!!} ⟩  )
       -}

      

      isHom' : ( ▹ IsMonoidHom (CommMonoid→Monoid (nat-monoid ×M A .Perturb) .snd) (f' (next f)) (EndoMonFun (𝕃 (A .P)) .snd))
              -> IsMonoidHom (CommMonoid→Monoid (nat-monoid ×M A .Perturb) .snd) (f' (next f)) (EndoMonFun (𝕃 (A .P)) .snd)
      isHom' IH = monoidequiv
        (eqMon _ _ (funExt (λ { (η a) -> let pfA = cong (MonFun.f) (perturb A .snd .presε) in  cong η (funExt⁻ pfA a);
                                (θ la) -> cong θ (funExt⁻ (λ t → {!!}) {!!});
                                ℧ -> refl})))
        λ { (n , ma) (n' , ma') → eqMon _ _ ( funExt λ {
           (η a) -> sym (funExt⁻ (sym (δ-fun n' (n , ma))) (η (MonFun.f (ptb-fun A ma') a))
                    ∙ funExt⁻ (δ-splits-n n' n) _
                    ∙ cong ((δ ^ (n' + n)) ∘ η) (funExt⁻ (cong MonFun.f (sym (perturb A .snd  .pres· ma ma'))) a)
                    ∙ (λ i → funExt (λ x → cong (λ m -> (δ ^ m) x) (+-comm n' n)) i _)) ;
           (θ la) -> {!!};
           ℧ -> {!!} }
        )}
        -- ((λ x → θ (λ _ → x)) ^ (n + n')) ℧ ≡ (λ ℧ → (δ ^ n) ℧) (δ ^ n' ℧)

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
