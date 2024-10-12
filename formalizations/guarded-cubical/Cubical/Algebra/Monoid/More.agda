{-# OPTIONS --safe #-}

module Cubical.Algebra.Monoid.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Properties


open import Cubical.Data.Nat hiding (_·_ ; _^_)
open import Cubical.Data.Unit

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.CommMonoid.Base

open import Cubical.Data.Sigma

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv



private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


open IsMonoidHom

-- Isomorphism between IsMonoidHom and a sigma type
unquoteDecl IsMonoidHomIsoΣ = declareRecordIsoΣ IsMonoidHomIsoΣ (quote (IsMonoidHom))

isPropIsMonoidHom : {A : Type ℓ} {B : Type ℓ'}
  (M : MonoidStr A) (f : A → B) (N : MonoidStr B) →
  isProp (IsMonoidHom M f N)
isPropIsMonoidHom M f N =
  isPropRetract
    (Iso.fun IsMonoidHomIsoΣ) (Iso.inv IsMonoidHomIsoΣ) (Iso.leftInv IsMonoidHomIsoΣ)
    (isProp× (N.is-set _ _) (isPropΠ2 (λ x y → N.is-set _ _)))
  where
    module N = MonoidStr N



isSetIsMonoidHom : {A : Type ℓ} {B : Type ℓ'}
  (M : MonoidStr A) (f : A → B) (N : MonoidStr B) →
  isSet (IsMonoidHom M f N)
isSetIsMonoidHom M f N = isProp→isSet (isPropIsMonoidHom M f N)

isSetMonoidHom : (M : Monoid ℓ) (N : Monoid ℓ') →
  isSet (MonoidHom M N)
isSetMonoidHom M N =
  isSetΣ (isSet→ N.is-set) (λ h → isSetIsMonoidHom (M .snd) h (N .snd))
  where
    module N = MonoidStr (N .snd)

-- Equality of monoid homomorphisms follows from equality of the
-- underlying functions.

eqMonoidHom : {M : Monoid ℓ} {N : Monoid ℓ'} ->
  (f g : MonoidHom M N) ->
  fst f ≡ fst g -> f ≡ g
eqMonoidHom f g eq = Σ≡Prop (λ f → isPropIsMonoidHom _ _ _) eq

-- Constant homomorphism from M to N

ε-hom : {M : Monoid ℓ} {N : Monoid ℓ'} →
  MonoidHom M N
ε-hom {N = N} .fst _ = N.ε
  where module N = MonoidStr (N .snd)
ε-hom .snd .presε = refl
ε-hom {N = N} .snd .pres· = λ _ _ → sym (N.·IdR N.ε)
  where module N = MonoidStr (N .snd)


-- Opposite of a monoid

_^op : (M : Monoid ℓ) → Monoid ℓ
M ^op = makeMonoid {M = ⟨ M ⟩}
                   M.ε (λ x y → y M.· x)
                   M.is-set (λ x y z → sym (M.·Assoc z y x)) M.·IdL M.·IdR
  where
    module M = MonoidStr (M .snd)


_^opHom : {M : Monoid ℓ} {N : Monoid ℓ'} →
  MonoidHom M N → MonoidHom (M ^op) (N ^op)
(h ^opHom) .fst = h .fst
(h ^opHom) .snd .presε = h .snd .presε
(h ^opHom) .snd .pres· x y = h .snd .pres· y x

opRec : {M : Monoid ℓ} {N : Monoid ℓ'} →
  MonoidHom M (N ^op) → MonoidHom (M ^op) N
opRec ϕ^ .fst = ϕ^ .fst
opRec ϕ^ .snd .presε = ϕ^ .snd .presε
opRec ϕ^ .snd .pres· x y = ϕ^ .snd .pres· y x

opCoRec : {M : Monoid ℓ} {N : Monoid ℓ'}
  → MonoidHom (M ^op) N → MonoidHom M (N ^op)
opCoRec ϕ^ .fst = ϕ^ .fst
opCoRec ϕ^ .snd .presε = ϕ^ .snd .presε
opCoRec ϕ^ .snd .pres· x y = ϕ^ .snd .pres· y x

-- Homomorphism from (M^op)^op to M
M^op^op→M : {M : Monoid ℓ} →
  MonoidHom ((M ^op) ^op) M
M^op^op→M .fst x = x
M^op^op→M .snd .presε = refl
M^op^op→M .snd .pres· x y = refl


-- Homomorphism from M to (M^op)^op
M→M^op^op : {M : Monoid ℓ} →
  MonoidHom M ((M ^op) ^op)
M→M^op^op .fst x = x
M→M^op^op .snd .presε = refl
M→M^op^op .snd .pres· x y = refl

-- M^op^op→N : {M : Monoid ℓ} {N : Monoid ℓ'} →
--   MonoidHom M N → MonoidHom ((M ^op) ^op) N
-- M^op^op→N f = f ∘hom M^op^op→M

-- M→N^op^op : {M : Monoid ℓ} {N : Monoid ℓ'} →
--   MonoidHom M N → MonoidHom M ((N ^op) ^op)
-- M→N^op^op f = M→M^op^op ∘hom f

-- _^opHom' : {M : Monoid ℓ} {N : Monoid ℓ'} →
--   MonoidHom (M ^op) (N ^op) → MonoidHom M N
-- (h ^opHom') = M^op^op→M ∘hom (h ^opHom) ∘hom M→M^op^op


-- Identity monoid homomorphism

idMon : (M : Monoid ℓ) → MonoidHom M M
idMon M .fst = λ x → x
idMon M .snd .presε = refl
idMon M .snd .pres· _ _ = refl

-- Composition of monoid homomorphisms

_∘hom_ : {M : Monoid ℓ} {N : Monoid ℓ'} {P : Monoid ℓ''} ->
  MonoidHom N P -> MonoidHom M N -> MonoidHom M P
g ∘hom f = fst g ∘ fst f  ,
           monoidequiv
             ((cong (fst g) (snd f .presε)) ∙ (snd g .presε))
             λ m m' -> cong (fst g) (snd f .pres· m m') ∙ snd g .pres· _ _           

infixr 9 _∘hom_

∘hom-IdL : {M : Monoid ℓ} {N : Monoid ℓ'} →
  (f : MonoidHom M N)
  → idMon N ∘hom f ≡ f
∘hom-IdL f = eqMonoidHom _ _ refl

∘hom-IdR : {M : Monoid ℓ} {N : Monoid ℓ'} →
  (f : MonoidHom M N)
  → f ∘hom idMon M ≡ f
∘hom-IdR f = eqMonoidHom _ _ refl

∘hom-Assoc : {M : Monoid ℓ} {N : Monoid ℓ'} {P : Monoid ℓ''}{Q : Monoid ℓ'''} ->
  (f : MonoidHom M N) (g : MonoidHom N P) (h : MonoidHom P Q)
  -> (h ∘hom g) ∘hom f ≡ h ∘hom (g ∘hom f)
∘hom-Assoc f g h = eqMonoidHom _ _ refl

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


_×M_ : Monoid ℓ -> Monoid ℓ' -> Monoid (ℓ-max ℓ ℓ')
M1 ×M M2 = makeMonoid
  {M = ⟨ M1 ⟩ × ⟨ M2 ⟩}
  (M1.ε , M2.ε)
  (λ { (m1 , m2) (m1' , m2') -> (m1 M1.· m1') , (m2 M2.· m2')  })
  (isSet× M1.is-set M2.is-set)
  (λ  { (m1 , m2) (m1' , m2') (m1'' , m2'') ->
    ≡-× (M1.·Assoc m1 m1' m1'') (M2.·Assoc m2 m2' m2'') } )
  (λ { (m1 , m2) -> ≡-× (M1.·IdR m1) (M2.·IdR m2) })
  (λ { (m1 , m2) -> ≡-× (M1.·IdL m1) (M2.·IdL m2) })
    where
      open MonoidStr
      open IsMonoid
      open IsSemigroup
      module M1 = MonoidStr (M1 .snd)
      module M2 = MonoidStr (M2 .snd)
      _·M1_ = M1 .snd ._·_
      _·M2_ = M2 .snd ._·_

×M-intro : {M : Monoid ℓ} {N : Monoid ℓ'} {P : Monoid ℓ''} →
  MonoidHom M N → MonoidHom M P → MonoidHom M (N ×M P)
×M-intro f g .fst x = f .fst x , g .fst x
×M-intro f g .snd .presε = ≡-× (f .snd .presε) (g .snd .presε)
×M-intro f g .snd .pres· x y = ≡-× (f .snd .pres· x y) (g .snd .pres· x y)

_×CM_ : CommMonoid ℓ -> CommMonoid ℓ' -> CommMonoid (ℓ-max ℓ ℓ')
M1 ×CM M2 = makeCommMonoid
  {M = ⟨ M1 ⟩ × ⟨ M2 ⟩}
  (commMonoidId M1 , commMonoidId M2)
  (λ { (m1 , m2) (m1' , m2') -> (m1 ·M1 m1') , (m2 ·M2 m2')})
  (isSet× M1.is-set M2.is-set)
  (λ { (m1 , m2) (m1' , m2') (m1'' , m2'') ->
    ≡-× (M1 .snd .isMonoid .isSemigroup .·Assoc m1 m1' m1'')
        (M2 .snd .isMonoid .isSemigroup .·Assoc m2 m2' m2'') })
  (λ { (m1 , m2) -> ≡-×
    (M1 .snd .isMonoid .·IdR m1) ((M2 .snd .isMonoid .·IdR m2)) })
  λ { (m1 , m2) (m1' , m2') -> ≡-×
    (M1 .snd .·Comm m1 m1') (M2 .snd .·Comm m2 m2') }
    where
      module M1 = CommMonoidStr (M1 .snd)
      module M2 = CommMonoidStr (M2 .snd)
      open CommMonoidStr
      open IsMonoid
      open IsSemigroup
      _·M1_ = M1 .snd ._·_
      _·M2_ = M2 .snd ._·_


{-
CM→M-× : (M1 : CommMonoid ℓ) (M2 : CommMonoid ℓ') ->
    (CommMonoid→Monoid (M1 ×CM M2)) ≡
    (CommMonoid→Monoid M1 ×M CommMonoid→Monoid M2)
CM→M-× M1 M2 = equivFun (MonoidPath _ _) CM→M-×'
  where
    CM→M-×' :
      MonoidEquiv
        (CommMonoid→Monoid (M1 ×CM M2))
        (CommMonoid→Monoid M1 ×M CommMonoid→Monoid M2)
    CM→M-×' .fst = idEquiv ⟨ CommMonoid→Monoid (M1 ×CM M2) ⟩
    CM→M-×' .snd .presε = refl
    CM→M-×' .snd .pres· p p' = refl
-}

CM→M-× : (M1 : CommMonoid ℓ) (M2 : CommMonoid ℓ') ->
    MonoidHom
      (CommMonoid→Monoid (M1 ×CM M2))
      (CommMonoid→Monoid M1 ×M CommMonoid→Monoid M2)
CM→M-× M1 M2 .fst x = x
CM→M-× M1 M2 .snd .presε = refl
CM→M-× M1 M2 .snd .pres· p p' = refl



-- "Product" of homomorphisms between two fixed monoids
_·hom_[_] : {M : Monoid ℓ} -> {N : Monoid ℓ'} ->
  (f g : MonoidHom M N) ->
  (commutes : ∀ x y ->
    N .snd .MonoidStr._·_ (fst f y) (fst g x) ≡
    N .snd .MonoidStr._·_ (fst g x) (fst f y)) ->
  MonoidHom M N
_·hom_[_] {M = M} {N = N} f g commutes =
  (λ a -> fst f a ·N fst g a) ,
  monoidequiv
  -- (f ε_M) ·N (g ε_M) = ε_N
  ((λ i -> (f .snd .presε i) ·N (g .snd .presε i)) ∙
  (N .snd .isMonoid .·IdR (N .snd .ε)))

  -- f (x ·M y) ·N g (x ·M y) = ((f x) ·N (g x)) ·N ((f y) ·N (g y))
  pres-mult
  where
    open MonoidStr
    open IsSemigroup
    open IsMonoid
    open IsMonoidHom
    _·M_ = M .snd ._·_
    _·N_ = N .snd ._·_

    f-fun : ⟨ M ⟩ → ⟨ N ⟩
    f-fun = fst f

    g-fun : ⟨ M ⟩ → ⟨ N ⟩
    g-fun = fst g

    N-assoc :  (x y z : ⟨ N ⟩) → x ·N (y ·N z) ≡ (x ·N y) ·N z
    N-assoc = N .snd .isMonoid .isSemigroup .·Assoc

    pres-mult : (x y : fst M) →
                (fst f ((M .snd · x) y) ·N fst g ((M .snd · x) y)) ≡
                (N .snd · (fst f x ·N fst g x)) (fst f y ·N fst g y)
    pres-mult x y =
           (f-fun (x ·M y) ·N g-fun (x ·M y))
           ≡⟨ (λ i → f .snd .pres· x y i ·N g .snd .pres· x y i) ⟩

           ((f-fun x ·N f-fun y) ·N (g-fun x ·N g-fun y))
           ≡⟨ (N-assoc (f-fun x ·N f-fun y) (g-fun x) (g-fun y)) ⟩

           (((f-fun x ·N f-fun y) ·N g-fun x) ·N g-fun y)
           ≡⟨ (λ i -> (sym (N-assoc (f-fun x) (f-fun y) (g-fun x)) i) ·N g-fun y) ⟩

           ((f-fun x ·N ((f-fun y ·N g-fun x))) ·N g-fun y)
           ≡⟨ ((λ i -> (f-fun x ·N commutes x y i) ·N g-fun y)) ⟩

           ((f-fun x ·N ((g-fun x ·N f-fun y))) ·N g-fun y)
           ≡⟨ ((λ i -> (N-assoc (f-fun x) (g-fun x) (f-fun y) i) ·N g-fun y)) ⟩

           (((f-fun x ·N g-fun x) ·N f-fun y) ·N g-fun y)
           ≡⟨ sym (N-assoc (f-fun x ·N g-fun x) (f-fun y) (g-fun y)) ⟩

           ((f-fun x ·N g-fun x)) ·N (f-fun y ·N g-fun y) ∎




-- Extending the domain of a homomorphism, i.e.
-- If f is a homomorphism from N to P, then f is also
-- a homomorphism from M ×M N to P for any monoid M
extend-domain-l : {N : Monoid ℓ} {P : Monoid ℓ''} ->
  (M : Monoid ℓ') (f : MonoidHom N P) ->
  MonoidHom (M ×M N) P
extend-domain-l M f .fst (m , n) = f .fst n
extend-domain-l M f .snd .presε = f.presε
  where module f = IsMonoidHom (f .snd)
extend-domain-l M f .snd .pres· (m , n) (m' , n') = f.pres· n n'
  where module f = IsMonoidHom (f .snd)

-- This could be defined by composing extend-domain-l
-- with the "swap" homomorphism
extend-domain-r : {M : Monoid ℓ} {P : Monoid ℓ''} ->
  (N : Monoid ℓ') (f : MonoidHom M P) ->
  MonoidHom (M ×M N) P
extend-domain-r N f .fst (m , n) = f .fst m
extend-domain-r N f .snd .presε = f.presε
  where module f = IsMonoidHom (f .snd)
extend-domain-r N f .snd .pres· (m , n) (m' , n') = f.pres· m m'
  where module f = IsMonoidHom (f .snd)



-- Monoid of natural numbers with addition
nat-monoid : CommMonoid ℓ-zero
nat-monoid = makeCommMonoid {M = ℕ} zero _+_ isSetℕ +-assoc +-zero +-comm

NatM : Monoid ℓ-zero
NatM = makeMonoid {M = ℕ} zero _+_ isSetℕ +-assoc +-zero (λ _ → refl)


-- Universal property of the additive monoid of natural numbers.
module NatM→ {ℓM : Level} (M : Monoid ℓM) (x : ⟨ M ⟩) where

  module M = MonoidStr (M .snd)

  f : ℕ → ⟨ M ⟩
  f zero = M.ε
  f (suc n) = x M.· (f n)

  f1≡x : f 1 ≡ x
  f1≡x = M.·IdR x

  -- Existence: An element of a monoid M determines a homomorphism of monoids from NatM to M:
  h : MonoidHom NatM M
  h .fst = f
  h .snd .presε = refl
  h .snd .pres· = aux
    where
      aux : (n₁ n₂ : ℕ) → _
      aux zero n₂ = sym (M.·IdL _)
      aux (suc n₁) n₂ = (cong₂ M._·_ refl (aux n₁ n₂)) ∙ (M.·Assoc _ _ _)


  -- Uniqueness: A homomorphism out of NatM is determined by where it
  -- sends the element 1.  That is, any other homomorphism of monoids
  -- out of NatM that agrees with NatM→ on where it sends 1 must be
  -- equal to NatM→.
  uniqueness : (h' : MonoidHom NatM M) → (h' .fst 1 ≡ x) → h' ≡ h  -- (h' .fst 1 ≡ h .fst 1) → h' ≡ h
  uniqueness h' eq = eqMonoidHom _ _ (funExt aux)
    where
      module h' = IsMonoidHom (h' .snd)

      aux : ∀ n → (h' .fst n) ≡ (h .fst n)
      aux zero = h'.presε
      aux (suc n) = (h'.pres· 1 n) ∙ (cong₂ M._·_ eq (aux n))

NatM-ind : {M : Monoid ℓ} (h h' : MonoidHom NatM M) → (h .fst 1 ≡ h' .fst 1) → h ≡ h'
NatM-ind {M = M} h h' h1≡h'1 = NM.uniqueness h refl ∙ sym (NM.uniqueness h' (sym h1≡h'1)) where
  module NM = NatM→ M (h .fst 1)

𝟙M* : {ℓM : Level} → Monoid ℓM
𝟙M* = makeMonoid tt* (λ _ _ → tt*) isSetUnit* (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl)

-- (unique) homomorphism out of the trivial monoid
𝟙M*→ : {ℓM : Level} → (M : Monoid ℓ) -> MonoidHom (𝟙M* {ℓM = ℓM}) M
𝟙M*→ M .fst tt* = M.ε
  where module M = MonoidStr (M .snd)
𝟙M*→ M .snd .presε = refl
𝟙M*→ M .snd .pres· tt* tt* = sym (M.·IdR M.ε)
  where module M = MonoidStr (M .snd)


-- Trivial monoid
𝟙M : Monoid ℓ-zero
𝟙M = makeMonoid tt (λ _ _ → tt) isSetUnit (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl)

-- (unique) homomorphism out of the trivial monoid
𝟙M→ : (M : Monoid ℓ) -> MonoidHom 𝟙M M
𝟙M→ M .fst tt = M.ε
  where module M = MonoidStr (M .snd)
𝟙M→ M .snd .presε = refl
𝟙M→ M .snd .pres· tt tt = sym (M.·IdR M.ε)
  where module M = MonoidStr (M .snd)


-- Trivial monoid as a commutative monoid
trivial-monoid : CommMonoid ℓ-zero
trivial-monoid = makeCommMonoid
  tt (λ _ _ -> tt) isSetUnit (λ _ _ _ -> refl) (λ _ -> refl) (λ _ _ -> refl)

-- (unique) homomorphism out of the trivial monoid
trivial-monoid-hom : (M : Monoid ℓ) ->
  MonoidHom (CommMonoid→Monoid trivial-monoid) M
trivial-monoid-hom M .fst tt = ε
  where open MonoidStr (M .snd)
trivial-monoid-hom M .snd .presε = refl
trivial-monoid-hom M .snd .pres· tt tt = sym (·IdR ε)
  where open MonoidStr (M .snd)

-- sections and factorizations
module _ {M : Monoid ℓ}{N : Monoid ℓ'} where
  module _ {P : Monoid ℓ''} where
    factorization : MonoidHom M N → MonoidHom P N → Type _
    factorization π ϕ = Σ[ ϕ^ ∈ MonoidHom P M ] π ∘hom ϕ^ ≡ ϕ

  module _ (π : MonoidHom M N) where
    --elim Nat
    module _ (ϕ : MonoidHom NatM N) where
      elimNat : (Σ[ m ∈ ⟨ M ⟩ ] π .fst m ≡ ϕ .fst 1) → factorization π ϕ
      elimNat lift1 .fst = NatM→.h M (lift1 .fst)
      elimNat lift1 .snd = NatM-ind _ _ (cong (π .fst) (NatM→.f1≡x M _)
        ∙ lift1 .snd)

  sectionHom : MonoidHom M N → Type _
  sectionHom π = factorization π (idMon _)


module _ {M : Monoid ℓ}{N : Monoid ℓ'}{P : Monoid ℓ''}
  (π : MonoidHom M N)
  (ϕ : MonoidHom (P ^op) N)
  where
  elimOp :
    factorization (π ^opHom) (opCoRec {M = P}{N = N} ϕ)
    → factorization π ϕ
  elimOp opFact .fst = opRec (opFact .fst)
  elimOp opFact .snd = eqMonoidHom _ _ (cong fst (opFact .snd))


-- Isomorphism of monoids
-- IsMonoidIso : {A : Type ℓ} {B : Type ℓ'} (M : MonoidStr A) (isom : Iso A B) (N : MonoidStr B)
--   → Type (ℓ-max ℓ ℓ')
-- IsMonoidIso M e N = IsMonoidHom M (e .fst) N

-- MonoidEquiv : (M : Monoid ℓ) (N : Monoid ℓ') → Type (ℓ-max ℓ ℓ')
-- MonoidEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsMonoidEquiv (M .snd) e (N .snd)


record MonoidIso (M : Monoid ℓ) (N : Monoid ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor monoidiso
  field
    fun : MonoidHom M N
    inv : MonoidHom N M
    rightInv : section (fun .fst) (inv .fst)
    leftInv  : retract (fun .fst) (inv .fst)

module _
  {M : Monoid ℓ} {N : Monoid ℓ'}
  (fun : MonoidHom M N)
  (inv : MonoidHom N M)
  (rightInv : fun ∘hom inv ≡ idMon N)
  (leftInv  : inv ∘hom fun ≡ idMon M)
  where

  mkMonoidIso : MonoidIso M N
  mkMonoidIso .MonoidIso.fun = fun
  mkMonoidIso .MonoidIso.inv = inv
  mkMonoidIso .MonoidIso.rightInv = funExt⁻ (cong fst rightInv)
  mkMonoidIso .MonoidIso.leftInv = funExt⁻ (cong fst leftInv)
  

module _
  {M : Monoid ℓ} {N : Monoid ℓ'}
  (isom : MonoidIso M N) where

  private
    module isom = MonoidIso isom

  MonoidIso→RightInv : isom.fun ∘hom isom.inv ≡ idMon N
  MonoidIso→RightInv = eqMonoidHom _ _ (funExt isom.rightInv)

  MonoidIso→LeftInv : isom.inv ∘hom isom.fun ≡ idMon M
  MonoidIso→LeftInv = eqMonoidHom _ _ (funExt isom.leftInv)

  MonoidIso→TypeIso : Iso (M .fst) (N .fst)
  MonoidIso→TypeIso .Iso.fun = isom.fun .fst
  MonoidIso→TypeIso .Iso.inv = isom.inv .fst
  MonoidIso→TypeIso .Iso.rightInv = isom.rightInv
  MonoidIso→TypeIso .Iso.leftInv = isom.leftInv

  MonoidIso→MonoidEquiv : MonoidEquiv M N
  MonoidIso→MonoidEquiv .fst = isoToEquiv MonoidIso→TypeIso
  MonoidIso→MonoidEquiv .snd .presε = isom.fun .snd .presε
  MonoidIso→MonoidEquiv .snd .pres· = isom.fun .snd .pres·

  MonoidIso-Inv : MonoidIso N M
  MonoidIso-Inv .MonoidIso.fun = isom.inv
  MonoidIso-Inv .MonoidIso.inv = isom.fun
  MonoidIso-Inv .MonoidIso.rightInv = isom.leftInv
  MonoidIso-Inv .MonoidIso.leftInv = isom.rightInv

idMonoidIso : {M : Monoid ℓ} →
  MonoidIso M M
idMonoidIso .MonoidIso.fun = idMon _
idMonoidIso .MonoidIso.inv = idMon _
idMonoidIso .MonoidIso.rightInv x = refl
idMonoidIso .MonoidIso.leftInv x = refl

module _
  {M : Monoid ℓ} {N : Monoid ℓ'} {P : Monoid ℓ''}
  (f : MonoidIso M N)
  (g : MonoidIso N P)
  where

  private
    module f = MonoidIso f
    module g = MonoidIso g
  
  compMonoidIso : MonoidIso M P
  compMonoidIso .MonoidIso.fun = g.fun ∘hom f.fun
  compMonoidIso .MonoidIso.inv = f.inv ∘hom g.inv
  compMonoidIso .MonoidIso.rightInv x = (cong (fst g.fun) (f.rightInv _)) ∙ g.rightInv x
  compMonoidIso .MonoidIso.leftInv x = (cong (fst f.inv) (g.leftInv _)) ∙ f.leftInv x


{-
module _
  {M : Monoid ℓ} {N : Monoid ℓ'}
  (equiv : MonoidEquiv M N) where

  private
    hom : MonoidHom M N
    hom .fst = equiv .fst .fst
    hom .snd = equiv .snd

    inv : MonoidHom N M
    inv .fst = invEquiv (equiv .fst) .fst
    -- These follow from the fact that hom is a homomorphism
    -- and that the underlying types are isomorphic.
    inv .snd .presε =
      sym (invEq (equivAdjointEquiv (equiv .fst)) (equiv .snd .presε))
    inv .snd .pres· x y =
      sym (invEq (equivAdjointEquiv (equiv .fst)) {!equiv .snd .pres· ? ?!})

    isom : Iso ⟨ M ⟩ ⟨ N ⟩
    isom = equivToIso (equiv .fst)

  MonoidEquiv→MonoidIso : MonoidIso M N
  MonoidEquiv→MonoidIso .MonoidIso.fun = hom
  MonoidEquiv→MonoidIso .MonoidIso.inv = inv
  MonoidEquiv→MonoidIso .MonoidIso.rightInv = isom .Iso.rightInv
  MonoidEquiv→MonoidIso .MonoidIso.leftInv = isom .Iso.leftInv
-}
