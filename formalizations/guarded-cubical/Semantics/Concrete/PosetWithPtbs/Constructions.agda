{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.PosetWithPtbs.Constructions (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Reflection.RecordEquiv
open import Cubical.Relation.Binary.Poset
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HigherCategories.ThinDoubleCategory.ThinDoubleCat
-- open import Cubical.HigherCategories.ThinDoubleCategory.Constructions.BinProduct
open import Cubical.Foundations.Function

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.CommMonoid.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_ ; _^_)
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base

open import Common.Common
open import Common.LaterProperties

open import Semantics.Lift k
open import Semantics.LockStepErrorOrdering k
-- open import Semantics.Concrete.DynNew k
open import Common.Poset.Convenience
open import Common.Poset.Constructions
open import Common.Poset.Monotone
open import Common.Poset.MonotoneRelation
open import Semantics.MonotoneCombinators

open import Semantics.Concrete.PosetWithPtbs.Base k

--open import Cubical.Algebra.Monoid.FreeProduct
--  renaming (ε to empty ; _·_ to _·free_ ; _⋆_ to _⋆M_)
-- open import Semantics.Abstract.Model.Model

-- open Model
open IsMonoidHom


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓA ℓ'A ℓ''A ℓB ℓ'B ℓ''B ℓC ℓ'C ℓ''C : Level

  ▹_ : Type ℓ -> Type ℓ
  ▹ A = ▹_,_ k A



-- Kleisli category of the Lift monad in the category of posets
_==>K_ : (A : Poset ℓA ℓ'A) (B : Poset ℓB ℓ'B) -> Type (ℓ-max (ℓ-max (ℓ-max ℓA ℓ'A) ℓB) ℓ'B)
A ==>K B = ⟨ A ==> 𝕃 B ⟩
  where open LiftPoset

-- Kleisli composition
_∘k_ : {A : Poset ℓA ℓ'A} {B : Poset ℓB ℓ'B} {C : Poset ℓC ℓ'C} ->
  B ==>K C -> A ==>K B -> A ==>K C
g ∘k f = mCompU (U mExt g) f
  where
    open LiftPoset
    open ClockedCombinators k

  

open PosetWithPtb



{- Change to accommodate the embedding and projection monoids
_==>PWP_ : PosetWithPtb ℓ ℓ' ℓ'' -> PosetWithPtb ℓ ℓ' ℓ'' ->
  PosetWithPtb (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ') ℓ''
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
      open MonoidStr
      module A = CommMonoidStr (A .Perturb .snd)
      module B = CommMonoidStr (B .Perturb .snd)
      _·A_ : ⟨ A .Perturb ⟩ → ⟨ A .Perturb ⟩ → ⟨ A .Perturb ⟩
      _·A_ = A._·_

      _·B_ : ⟨ B .Perturb ⟩ → ⟨ B .Perturb ⟩ → ⟨ B .Perturb ⟩
      _·B_ = B._·_
-}



open ClockedCombinators k



-- Perturbations on natural numbers
NatPWP : PosetWithPtb ℓ-zero ℓ-zero ℓ-zero
NatPWP .P = ℕ -- LiftPoset ℕ ℓ ℓ
NatPWP .Perturbᴱ = trivial-monoid
NatPWP .Perturbᴾ = trivial-monoid
NatPWP .perturbᴱ = trivial-monoid-hom (EndoMonFun ℕ)
NatPWP .perturbᴾ = trivial-monoid-hom (EndoMonFun ℕ)



-- Perturbations on Lift of a poset
open LiftPoset

-- δ as a homomorphism
Delayⁿ : {X : Poset ℓ ℓ'} ->
  MonoidHom (CommMonoid→Monoid nat-monoid) (EndoMonFun (𝕃 X))
Delayⁿ =
  (λ n -> Δ ^m n) ,
  monoidequiv
    (eqMon _ _ refl)
    (λ n n' -> eqMon _ _ (sym {!!}))
  where

    δ-splits-n : {A : Type ℓ} -> ∀ (n n' : Nat) ->
      (δ {X = A} ^ n) ∘ (δ ^ n') ≡ δ ^ (n + n')
    δ-splits-n zero n' = ∘-idʳ (δ ^ n')
    δ-splits-n (suc n) n' =
      ∘-assoc δ (δ ^ n) (δ ^ n') ∙ cong (λ a -> δ ∘ a) (δ-splits-n n n')


-- Map as a homomorphism
Map-hom : {X : Poset ℓ ℓ'} ->
  MonoidHom (EndoMonFun X) (EndoMonFun (𝕃 X))
Map-hom .fst = U mMap
Map-hom .snd .presε = eqMon _ _ (funExt mapL-id)
Map-hom .snd .pres· f g =
  eqMon _ _ (funExt (mapL-comp (MonFun.f f) (MonFun.f g)))

𝕃PWP : PosetWithPtb ℓ ℓ' ℓ'' -> PosetWithPtb ℓ ℓ' ℓ''
𝕃PWP A = record {
  P = LiftPoset.𝕃 (A .P) ;
  Perturbᴱ = nat-monoid ×CM A .Perturbᴱ ;
  Perturbᴾ = nat-monoid ×CM A .Perturbᴾ ;
  perturbᴱ = ((extend-domain-r _ Delayⁿ) ·hom (extend-domain-l _ Map-hom)
             [ (λ {(n , f) (n' , f') → eqMon _ _ (funExt (λ la -> sym (mapL-delay (MonFun.f f) la n')))}) ])
    ∘hom {!!} ;
  perturbᴾ = {!!}}

    
-- Product of two posets with perturbation
_×PWP_ : PosetWithPtb ℓ ℓ' ℓ'' -> PosetWithPtb ℓ ℓ' ℓ'' ->
  PosetWithPtb ℓ (ℓ-max ℓ' ℓ') ℓ''
A ×PWP B = record {
  P = (A .P) ×p (B .P) ;
  Perturbᴱ = A .Perturbᴱ ×CM B .Perturbᴱ ;
  Perturbᴾ = A .Perturbᴾ ×CM B .Perturbᴾ ;
  perturbᴱ =
    (λ { (ma , mb) ->
      PairFun (mCompU (ptb-funᴱ A ma) π1) (mCompU (ptb-funᴱ B mb) π2) }),
    monoidequiv
      (eqMon _ _
        (funExt (λ { (a , b) →
         ≡-× (funExt⁻ (cong MonFun.f (ptbAᴱ.presε)) a)
             (funExt⁻ (cong MonFun.f (ptbBᴱ.presε)) b) })))
      λ { (ma , mb) (ma' , mb') →
       eqMon _ _
        (funExt (λ { (a , b ) ->
         ≡-× (funExt⁻ (cong MonFun.f (ptbAᴱ.pres· ma ma')) a)
             (funExt⁻ (cong MonFun.f (ptbBᴱ.pres· mb mb')) b) })) } ;
  perturbᴾ = {!!} -- same as the above
  }
  where
    open MonoidStr
    open IsMonoidHom

    module ptbAᴱ = IsMonoidHom (A .perturbᴱ .snd)
    module ptbBᴱ = IsMonoidHom (B .perturbᴱ .snd)
    module ptbAᴾ = IsMonoidHom (A .perturbᴾ .snd)
    module ptbBᴾ = IsMonoidHom (B .perturbᴾ .snd)


-- Sum of two posets with perturbation
_⊎PWP_ : PosetWithPtb ℓA ℓ'A ℓ''A -> PosetWithPtb ℓB ℓ'B ℓ''B ->
  PosetWithPtb (ℓ-max ℓA ℓB) (ℓ-max ℓ'A ℓ'B) (ℓ-max ℓ''A ℓ''B)
A ⊎PWP B = record {
  P = A .P ⊎p B .P  ;
  Perturbᴱ = A .Perturbᴱ ×CM B .Perturbᴱ ;
  Perturbᴾ = A .Perturbᴾ ×CM B .Perturbᴾ ;
  perturbᴱ = ptb-e ;
  perturbᴾ = ptb-p
  }
  where
    module ptbAᴱ = IsMonoidHom (A .perturbᴱ .snd)
    module ptbBᴱ = IsMonoidHom (B .perturbᴱ .snd)
    module ptbAᴾ = IsMonoidHom (A .perturbᴾ .snd)
    module ptbBᴾ = IsMonoidHom (B .perturbᴾ .snd)

    ptb-e : MonoidHom _ _
    ptb-e .fst (δᴬ , δᴮ) =
      Case' (mCompU σ1 (ptb-funᴱ A δᴬ)) (mCompU σ2 (ptb-funᴱ B δᴮ))
    ptb-e .snd .presε = eqMon _ _ (funExt
      (λ { (inl a) → cong inl (funExt⁻ (cong MonFun.f ptbAᴱ.presε) a) ;
           (inr b) → cong inr (funExt⁻ (cong MonFun.f ptbBᴱ.presε) b)}))
    ptb-e .snd .pres· (δᴬ , δᴮ) (δᴬ' , δᴮ') =
      eqMon _ _ (funExt
      (λ { (inl a) → cong inl (funExt⁻ (cong MonFun.f (ptbAᴱ.pres· δᴬ δᴬ')) a) ;
           (inr b) → cong inr (funExt⁻ (cong MonFun.f (ptbBᴱ.pres· δᴮ δᴮ')) b) }))

    ptb-p : MonoidHom _ _
    ptb-p .fst (δᴬ , δᴮ) =
      Case' (mCompU σ1 (ptb-funᴾ A δᴬ)) (mCompU σ2 (ptb-funᴾ B δᴮ))
    ptb-p .snd .presε = eqMon _ _ (funExt
      (λ { (inl a) → cong inl (funExt⁻ (cong MonFun.f ptbAᴾ.presε) a) ;
           (inr b) → cong inr (funExt⁻ (cong MonFun.f ptbBᴾ.presε) b)}))
    ptb-p .snd .pres· (δᴬ , δᴮ) (δᴬ' , δᴮ') = {!!}




-- Perturbations on Kleisli functions
_==>L_ : PosetWithPtb ℓ ℓ' ℓ'' -> PosetWithPtb ℓ ℓ' ℓ'' ->
  PosetWithPtb (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ') ℓ''
A ==>L B = record {
  P = (A .P) ==> 𝕃 (B .P) ;
  Perturbᴱ = 𝕃PWP A .Perturbᴾ ×CM B .Perturbᴱ ;
  Perturbᴾ = A .Perturbᴱ ×CM 𝕃PWP B .Perturbᴾ ;
  perturbᴱ = ptb-emb ;
  perturbᴾ = {!!}

    }
    where
      open LiftPoset
      open IsMonoidHom
      open MonoidStr

      -- Embedding:
      -- We get a perturbation δᴸᴬ on lift of the domain,
      -- and a perturbation δᴮ on the codomain.

      module LA = CommMonoidStr (𝕃PWP A .Perturbᴾ .snd)
      module B = CommMonoidStr (B .Perturbᴱ .snd)

      module ptbLA = IsMonoidHom (𝕃PWP A .perturbᴾ .snd)
      module ptbB = IsMonoidHom (B .perturbᴱ .snd)

      -- ptb-emb : LA .Perturbᴾ ×M B.Perturbᴾ -> EndoMonFun (A ==> L B)
      ptb-emb : MonoidHom
        (CommMonoid→Monoid (𝕃PWP A .Perturbᴾ ×CM B .Perturbᴱ))
        (EndoMonFun (A .P ==> 𝕃 (B .P)))
      ptb-emb .fst (δᴸᴬ , δᴮ) = Curry
        (mMap' (With2nd (ptb-funᴱ B δᴮ))              ∘m
        (Uncurry mExt)                                ∘m
        With2nd (mCompU (ptb-funᴾ (𝕃PWP A) δᴸᴬ) mRet) ∘m
        π2)
        
      ptb-emb .snd .presε =
        (eqMon _ _ (funExt (λ g -> eqMon _ _ (funExt (λ a ->
        mapL (MonFun.f (ptb-funᴱ B B.ε)) (ext (MonFun.f g) (MonFun.f (ptb-funᴾ (𝕃PWP A) LA.ε) (η a)))
          ≡⟨ cong (mapL _) (cong (ext _) (cong₂ MonFun.f ptbLA.presε refl)) ⟩
        mapL (MonFun.f (ptb-funᴱ B B.ε)) (ext (MonFun.f g) (η a))
          ≡⟨ cong (mapL _) (ext-eta a _) ⟩
        mapL (MonFun.f (ptb-funᴱ B B.ε)) (MonFun.f g a)
          ≡⟨ cong₂ mapL (cong MonFun.f ptbB.presε) refl ⟩
        mapL id (MonFun.f g a)
          ≡⟨ mapL-id _ ⟩
        MonFun.f g a ∎)))))

      ptb-emb .snd .pres· (δᴸᴬ , δᴮ) (δᴸᴬ' , δᴮ') =
        let n = fst δᴸᴬ in
        eqMon _ _ (funExt (λ g -> eqMon _ _ (funExt (λ a -> 
          mapL (MonFun.f (ptb-funᴱ B (δᴮ B.· δᴮ')))
            (ext (MonFun.f g) (MonFun.f (ptb-funᴾ (𝕃PWP A) (δᴸᴬ LA.· δᴸᴬ')) (η a)))
           ≡⟨ {!!} ⟩
          mapL (MonFun.f (ptb-funᴱ B (δᴮ B.· δᴮ')))
            (ext (MonFun.f g) ((MonFun.f (ptb-funᴾ (𝕃PWP A) δᴸᴬ) ∘
                                MonFun.f (ptb-funᴾ (𝕃PWP A) δᴸᴬ')) (η a))) 
           ≡⟨ {!!} ⟩
          mapL (MonFun.f (ptb-funᴱ B (δᴮ B.· δᴮ')))
            (ext (MonFun.f g) ((MonFun.f (ptb-funᴾ (𝕃PWP A) δᴸᴬ') ∘
                                MonFun.f (ptb-funᴾ (𝕃PWP A) δᴸᴬ)) (η a)))
           ≡⟨ {!!} ⟩
          mapL ((MonFun.f (ptb-funᴱ B δᴮ) ∘ MonFun.f (ptb-funᴱ B δᴮ')))
           (ext (MonFun.f g)
           (MonFun.f (ptb-funᴾ (𝕃PWP A) δᴸᴬ')
             (MonFun.f (ptb-funᴾ (𝕃PWP A) δᴸᴬ) (η a))))
           ≡⟨ {!!} ⟩
          mapL ((MonFun.f (ptb-funᴱ B δᴮ))) (mapL ((MonFun.f (ptb-funᴱ B δᴮ')))
           (ext (MonFun.f g)
           (MonFun.f (ptb-funᴾ (𝕃PWP A) δᴸᴬ')
             ((δ ^ n) (η a)))))
           ≡⟨ {!!} ⟩
          mapL (MonFun.f (ptb-funᴱ B δᴮ))
            (ext (mapL (MonFun.f (ptb-funᴱ B δᴮ')) ∘ ext (MonFun.f g) ∘ MonFun.f (ptb-funᴾ (𝕃PWP A) δᴸᴬ') ∘ η)
              ((δ ^ n) (η a)))
           ≡⟨ {!!} ⟩
          mapL (MonFun.f (ptb-funᴱ B δᴮ))
            (ext (mapL (MonFun.f (ptb-funᴱ B δᴮ')) ∘ ext (MonFun.f g) ∘ MonFun.f (ptb-funᴾ (𝕃PWP A) δᴸᴬ') ∘ η)
              (MonFun.f (ptb-funᴾ (𝕃PWP A) δᴸᴬ) (η a))) ∎
        ))))

      
      -- Projection: We get a perturbation δᴬ on the domain and a
      -- perturbation δᴸᴮ on lift of the codomain.
      -- ptb-2 : MonoidHom
      --           (CommMonoid→Monoid (A .Perturb ×M 𝕃PWP B .Perturb))
      --           (EndoMonFun (A .P ==> 𝕃 (B .P)))
      -- ptb-2 = {!!}
      


-- later for monoids

M▹ : Monoid ℓ -> Monoid ℓ
M▹ M = makeMonoid {M = ▹ ⟨ M ⟩}
  (next ε)
  (λ x~ y~ t -> x~ t · y~ t)
  (isSet▹ (λ _ -> is-set))
  (λ x~ y~ z~ -> later-ext (λ t -> ·Assoc (x~ t) (y~ t) (z~ t)))
  (λ x~ -> later-ext (λ t -> ·IdR (x~ t)))
  (λ x~ -> later-ext (λ t -> ·IdL (x~ t)))
  where open MonoidStr (M .snd)

CM▹ : CommMonoid ℓ -> CommMonoid ℓ
CM▹ M .fst = ▹ ⟨ M ⟩
CM▹ M .snd = commmonoidstr
  (next M.ε) (λ x~ y~ t -> x~ t M.· y~ t)
  (iscommmonoid
    (M▹ (CommMonoid→Monoid M) .snd .isMonoid)
    (λ x~ y~ -> later-ext (λ t -> M.·Comm (x~ t) (y~ t))))
  where
    open MonoidStr
    module M = CommMonoidStr (M .snd)


-- theta for monoids
M▸ : ▹ Monoid ℓ -> Monoid ℓ
M▸ M~ = makeMonoid {M = ▸ (λ t -> ⟨ M~ t ⟩)}
  (λ t → M~ t .snd .ε)
  (λ x~ y~ t → M~ t .snd ._·_ (x~ t) (y~ t))
  (isSet▸ (λ t -> is-set (M~ t .snd)))
  (λ x~ y~ z~ ->
    later-ext (λ t -> ·Assoc (M~ t .snd) (x~ t) (y~ t) (z~ t)))
  (λ x~ -> later-ext (λ t → ·IdR (M~ t .snd) (x~ t)))
  (λ x~ -> later-ext λ t → ·IdL (M~ t .snd) (x~ t))
  where
    open MonoidStr

CM▸ : ▹ CommMonoid ℓ -> CommMonoid ℓ
CM▸ M~ .fst = ▸ (λ t -> ⟨ M~ t ⟩)
CM▸ M~ .snd = commmonoidstr
  (λ t -> M~ t .snd .ε)
  (λ x~ y~ t → M~ t .snd ._·_ (x~ t) (y~ t))
  (iscommmonoid
    (M▸ (λ t -> (CommMonoid→Monoid (M~ t))) .snd .isMonoid)
    λ x~ y~ -> later-ext (λ t -> ·Comm (M~ t .snd) (x~ t) (y~ t)))
  where
    open CommMonoidStr
    open MonoidStr



-- Homomorphisms between later monoids

open IsMonoidHom

-- ▹ (MonoidHom M N) -> MonoidHom (M▹ M) (M▹ N)

hom▹ : {M : Monoid ℓ} {N : Monoid ℓ'} (f : MonoidHom M N) ->
  MonoidHom (M▹ M) (M▹ N)
hom▹ {M = M} {N = N} f .fst = (map▹ (f .fst))
hom▹ {M = M} {N = N} f .snd .presε =
  later-ext λ t -> f .snd .presε
hom▹ {M = M} {N = N} f .snd .pres· x~ y~ =
  later-ext (λ t -> f .snd .pres· (x~ t) (y~ t))

hom▸ : {M~ : ▹ Monoid ℓ} {N~ : ▹ Monoid ℓ'}
  (f~ : ▸ (λ t -> MonoidHom (M~ t) (N~ t))) ->
  MonoidHom (M▸ M~) (M▸ N~)
hom▸ {M~ = M~} {N~ = N~} f~ .fst = λ m~ -> λ t -> f~ t .fst (m~ t)
hom▸ {M~ = M~} {N~ = N~} f~ .snd .presε =
  later-ext λ t -> f~ t .snd .presε
hom▸ {M~ = M~} {N~ = N~} f~ .snd .pres· x~ y~ =
  later-ext (λ t -> f~ t .snd .pres· (x~ t) (y~ t))


-- Notation for later on posets
P▹ = ▹' k
P▸ = ▸' k

-- We can turn a "later" monotone function f : ▹ (X ->mon X)
-- into a monotone function (▹ X) ->mon (▹ X), and moreover,
-- the transformation is a homomorphism.
Hom-▹EndoX-Endo▹X : {X : Poset ℓ ℓ'} ->
  MonoidHom (M▹ (EndoMonFun X)) (EndoMonFun (P▹ X)) 
Hom-▹EndoX-Endo▹X {X = X} .fst f~ .MonFun.f x~ =
  λ t -> MonFun.f (f~ t) (x~ t) -- or : map▹ MonFun.f f~ ⊛ x~
Hom-▹EndoX-Endo▹X {X = X} .fst f~ .MonFun.isMon {x~} {y~} x~≤y~ =
  λ t -> MonFun.isMon (f~ t) (x~≤y~ t)
Hom-▹EndoX-Endo▹X {X = X} .snd .presε = refl
Hom-▹EndoX-Endo▹X {X = X} .snd .pres· f~ g~ = refl

-- Dependent version of the above.
Hom-▸EndoX-Endo▸X : {X~ : ▹ Poset ℓ ℓ'} ->
  MonoidHom (M▸ (λ t -> (EndoMonFun (X~ t)))) (EndoMonFun (P▸ X~)) 
Hom-▸EndoX-Endo▸X {X~ = X~} .fst f~ .MonFun.f x~ =
  λ t -> MonFun.f (f~ t) (x~ t) -- or : map▹ MonFun.f f~ ⊛ x~
Hom-▸EndoX-Endo▸X {X~ = X~} .fst f~ .MonFun.isMon {x~} {y~} x~≤y~ =
  λ t -> MonFun.isMon (f~ t) (x~≤y~ t)
Hom-▸EndoX-Endo▸X {X~ = X~} .snd .presε = refl
Hom-▸EndoX-Endo▸X {X~ = X~} .snd .pres· f~ g~ = refl


-- "Later" for posets with perturbations
PWP▹ : PosetWithPtb ℓ ℓ' ℓ'' -> PosetWithPtb ℓ ℓ' ℓ''
PWP▹ X .P = P▹ (X .P)
PWP▹ X .Perturbᴱ = CM▹ (X .Perturbᴱ)
PWP▹ X .Perturbᴾ = CM▹ (X .Perturbᴾ)
PWP▹ X .perturbᴱ = Hom-▹EndoX-Endo▹X ∘hom (hom▹ (X .perturbᴱ))
PWP▹ X .perturbᴾ = Hom-▹EndoX-Endo▹X ∘hom (hom▹ (X .perturbᴾ))

-- X .Perturbᴱ -> ▹ (X ->m X) -> (▹ X ->m ▹ X)


-- "Theta" for posets with perturbations
PWP▸ : ▹ PosetWithPtb ℓ ℓ' ℓ'' -> PosetWithPtb ℓ ℓ' ℓ''
PWP▸ X~ .P = P▸ (λ t → X~ t .P)
PWP▸ X~ .Perturbᴱ = CM▸ (λ t -> X~ t .Perturbᴱ)
PWP▸ X~ .Perturbᴾ = CM▸ (λ t -> X~ t .Perturbᴾ)
PWP▸ X~ .perturbᴱ =
  (Hom-▸EndoX-Endo▸X {X~ = λ t -> X~ t .P}) ∘hom
  (hom▸ {M~ = λ t -> CommMonoid→Monoid (X~ t .Perturbᴱ)}
        {N~ = λ t -> EndoMonFun (X~ t .P)} (λ t -> X~ t .perturbᴱ))
PWP▸ X~ .perturbᴾ = Hom-▸EndoX-Endo▸X ∘hom (hom▸ (λ t -> X~ t .perturbᴾ))
-- PWP▸ X~ .perturbᴾ = Hom-▹EndoX-Endo▹X ∘hom (hom▹ ?)


{-
PWP▸ X~ .perturbᴾ = (λ x → record {
  f = λ p t → MonFun.f (ptb-funᴾ (X~ t) (x t)) (p t) ;
  isMon = {!!} }) ,
  {!!}
-}

-- Equation relating the above two definitions
PWP▸-next : (X : PosetWithPtb ℓ ℓ' ℓ'') -> PWP▸ (next X) ≡ PWP▹ X
PWP▸-next X = refl


-- Dyn as a Poset with Perturbation

{-
DynPWP' : ▹ (PosetWithPtb ℓ-zero ℓ-zero {!!}) ->
             PosetWithPtb ℓ-zero ℓ-zero {!!}
DynPWP' rec .P = DynP
DynPWP' rec .Perturbᴱ = {!!} -- CM▸ (λ t -> rec t .Perturbᴱ)
DynPWP' rec .Perturbᴾ = {!!} -- CM▸ (λ t -> rec t .Perturbᴾ)
DynPWP' rec .perturbᴱ = {!!} , {!!}
DynPWP' rec .perturbᴾ = {!!}
-}





--
-- Monotone functions on Posets with Perturbations
--
PosetWithPtb-Vert : {ℓ ℓ' ℓ'' : Level} (P1 P2 : PosetWithPtb ℓ ℓ' ℓ'') -> Type (ℓ-max ℓ ℓ') -- (ℓ-max ℓ ℓ')
PosetWithPtb-Vert P1 P2 = MonFun (P1 .P) (P2 .P)
-- TODO should there be a condition on preserving the perturbations?


--
-- Monotone relations on Posets with Perturbations
--

record FillersFor {ℓ ℓ'  ℓ'' ℓR : Level} (P1 P2 : PosetWithPtb ℓ ℓ' ℓ'') (R : MonRel (P1 .P) (P2 .P) ℓR) :
  Type (ℓ-max (ℓ-max ℓ ℓ'') ℓR) where
  open PosetWithPtb
  field
    fillerL-e : ∀ (δᴮ : ⟨ P2 .Perturbᴱ ⟩ ) ->
      Σ[ δᴬ ∈ ⟨ P1 .Perturbᴱ ⟩ ]
        TwoCell (R .MonRel.R) (R .MonRel.R)
              (MonFun.f (ptb-funᴱ P1 δᴬ)) (MonFun.f (ptb-funᴱ P2 δᴮ))
    fillerL-p : ∀ (δᴸᴮ : ⟨ 𝕃PWP P2 .Perturbᴾ ⟩ ) ->
      Σ[ δᴸᴬ ∈ ⟨ 𝕃PWP P1 .Perturbᴾ ⟩ ]
        TwoCell (LiftRelation._≾_ ⟨ P1 .P ⟩ ⟨ P2 .P ⟩ (R .MonRel.R))
                (LiftRelation._≾_ ⟨ P1 .P ⟩ ⟨ P2 .P ⟩ (R .MonRel.R))
             (MonFun.f (ptb-funᴾ (𝕃PWP P1) δᴸᴬ)) (MonFun.f (ptb-funᴾ (𝕃PWP P2) δᴸᴮ))
    fillerR-e : ∀ (δᴬ : ⟨ P1 .Perturbᴱ ⟩) ->
      Σ[ δᴮ ∈ ⟨ P2 .Perturbᴱ ⟩ ]
        TwoCell (R .MonRel.R) (R .MonRel.R)
              (MonFun.f (ptb-funᴱ P1 δᴬ)) (MonFun.f (ptb-funᴱ P2 δᴮ))
    fillerR-p : ∀ (δᴸᴬ : ⟨ 𝕃PWP P1 .Perturbᴾ ⟩ ) ->
      Σ[ δᴸᴮ ∈ ⟨ 𝕃PWP P2 .Perturbᴾ ⟩ ]
        TwoCell (LiftRelation._≾_ ⟨ P1 .P ⟩ ⟨ P2 .P ⟩ (R .MonRel.R)) 
                (LiftRelation._≾_ ⟨ P1 .P ⟩ ⟨ P2 .P ⟩ (R .MonRel.R))
              (MonFun.f (ptb-funᴾ (𝕃PWP P1) δᴸᴬ)) (MonFun.f (ptb-funᴾ (𝕃PWP P2) δᴸᴮ))


-- TODO: Show this is a set by showing that the Sigma type it is iso to
-- is a set (ΣIsSet2ndProp)
unquoteDecl FillersForIsoΣ = declareRecordIsoΣ FillersForIsoΣ (quote (FillersFor))

FillersFor-Set : ∀ {ℓ ℓ' ℓ'' ℓR : Level} {P1 P2 : PosetWithPtb ℓ ℓ'  ℓ''} {R : MonRel (P1 .P) (P2 .P) ℓR}->
  isSet (FillersFor P1 P2 R)
FillersFor-Set {P1 = P1} {P2 = P2} {R = R} = {!!}
{-
                     isSetRetract (Iso.fun FillersForIsoΣ) (Iso.inv FillersForIsoΣ) (Iso.leftInv FillersForIsoΣ) (
                           isSet× (isSetΠ (λ δᴮ → isSetΣSndProp (isSetMonoid (CommMonoid→Monoid (P1 .Perturbᴱ))) λ δᴬ → isPropTwoCell (R .MonRel.is-prop-valued)))
                             (isSet× (isSetΠ (λ δᴸᴮ → isSetΣSndProp (isSet× (isSetMonoid (CommMonoid→Monoid nat-monoid)) (isSetMonoid (CommMonoid→Monoid (P1 .Perturbᴾ))))
                               λ δᴸᴬ → isPropTwoCell (LiftMonRel.ℝ (P1 .P) (P2 .P) R .MonRel.is-prop-valued)))
                                 (isSet× (isSetΠ (λ δᴬ → isSetΣSndProp (isSetMonoid (CommMonoid→Monoid (P2 .Perturbᴱ))) (λ δᴮ → isPropTwoCell (R .MonRel.is-prop-valued))))
                                   (isSetΠ (λ δᴸᴬ → isSetΣSndProp (isSet× (isSetMonoid (CommMonoid→Monoid nat-monoid)) (isSetMonoid (CommMonoid→Monoid (P2 .Perturbᴾ))))
                                      (λ δᴸᴮ → isPropTwoCell (LiftMonRel.ℝ (P1 .P) (P2 .P) R .MonRel.is-prop-valued)))))))

-}
