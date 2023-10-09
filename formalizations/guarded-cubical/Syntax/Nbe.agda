module Syntax.Nbe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Syntax.IntensionalTerms
open import Syntax.IntensionalTerms.Induction
open import Syntax.Types

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T U R' S' T' U' : Ty

   γ γ' γ'' : Subst Δ Γ
   δ δ' δ'' : Subst Θ Δ
   θ θ' θ'' : Subst Z Θ

   V V' V'' : Val Γ S
   M M' M'' N N' : Comp Γ S
   E E' E'' F F' : EvCtx Γ S T
   ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

-- Part 1: define a semantics of contexts, i.e. every context
-- gets interpreted as an product of the Value presheaves
ctx-sem : ∀ (Γ : Ctx) → (Ctx → Type (ℓ-suc ℓ-zero))
ctx-sem [] Δ      = Unit*
ctx-sem (A ∷ Γ) Δ = ctx-sem Γ Δ × Val Δ A

_[_]sem : ctx-sem Γ Δ → Subst Θ Δ → ctx-sem Γ Θ
_[_]sem {Γ = []} tt* δ = tt*
_[_]sem {Γ = x ∷ Γ} (γ~ , v) δ = (γ~ [ δ ]sem) , (v [ δ ]v)

↑sem : ctx-sem Γ Θ → ctx-sem (R ∷ Γ) (R ∷ Θ)
↑sem γ~ = γ~ [ wk ]sem , var

-- Part 2: prove the presheaf semantics is equivalent to the yoneda
-- embedding (i.e. prove Yoneda preserves cartesian structure)

reify : ctx-sem Γ Δ → Subst Δ Γ
reify {Γ = []} γ~ = !s
reify {Γ = x ∷ Γ} (γ~ , v) = reify γ~ ,s v

reify-natural :
  ∀ {δ : Subst Θ Δ} {γ~ : ctx-sem Γ Δ} → reify γ~ ∘s δ ≡ reify (γ~ [ δ ]sem)
reify-natural {Γ = []} = []η
reify-natural {Γ = R ∷ Γ} =
  ,s-nat ∙ cong₂ _,s_ reify-natural refl

reflect : Subst Δ Γ → ctx-sem Γ Δ
reflect {Γ = []} γ = tt*
reflect {Γ = x ∷ Γ} γ = (reflect (wk ∘s γ)) , (var [ γ ]v)

univ-sem-subst : ctx-sem Γ Γ
univ-sem-subst = reflect ids

reify<-reflect≡id : (γ : Subst Δ Γ) → reify (reflect γ) ≡ γ
reify<-reflect≡id {Γ = []} γ = sym []η
reify<-reflect≡id {Γ = x ∷ Γ} γ = sym (,sη ∙ cong₂ _,s_ (sym (reify<-reflect≡id (wk ∘s γ))) refl)

reflect<-reify≡id : (γ~ : ctx-sem Γ Δ) → reflect (reify γ~) ≡ γ~
reflect<-reify≡id {Γ = []} γ~ = refl
reflect<-reify≡id {Γ = x ∷ Γ} γ~ = ΣPathP (cong reflect wkβ ∙ reflect<-reify≡id (γ~ .fst) , varβ)

-- Part 3:
--
-- Give a semantics of terms as "polymorphic transformations"
-- Simultaneously prove the correctness of this translation.

-- By proving correctness we can make the goal be contractible,
-- eliminating the need to prove we respect equations!

-- ordinary:
-- M : Comp Θ R
-- K : Comp (Θ , R) S

-- compromise: β but not η...
-- module _ where
--   module Bind = SynInd (λ _ → (Unit , isPropUnit)) (λ _ → (Unit , isPropUnit))
--     (λ {Γ}{R} M → (∀ {Δ}{S} (K : ∀ {Θ}(δv~ : ctx-sem (R ∷ Δ) Θ) → Comp Θ S) → (δ~ : ctx-sem Δ Γ) → singl (bind (K ((δ~ [ wk ]sem) , var)) [ M ]∙))
--     , isPropImplicitΠ2 (λ _ _ → isPropΠ2 (λ _ _ → isPropSingl)))
--     (λ _ → (Unit , isPropUnit))
--   open Bind.indCases
--   open SynInd.indCases
--   private
--     c : Bind.indCases
--     c .indIds = _
--     c .ind∘s = _
--     c .ind!s = _
--     c .ind,s = _
--     c .indwk = _
--     c .ind[]v = _
--     c .indVar = _
--     c .indZero = _
--     c .indSuc = _
--     c .indLda = _
--     c .indInjN = _
--     c .indInjArr = _
--     c .indMapDyn = _

--     c .ind[]∙ _ ihM K δ~ = isContrSingl _ .fst
--     c .ind[]c {M = x₂ [ M ]∙} x x₁ K δ~ = {!!}
--     c .ind[]c {M = plugId i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = plugAssoc i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = M [ x₂ ]c} x x₁ K δ~ = {!!}
--     c .ind[]c {M = substId i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = substAssoc i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = substPlugDist i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = err} x x₁ K δ~ = {!!}
--     c .ind[]c {M = strictness i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = ret} x x₁ K δ~ = {!!}
--     c .ind[]c {M = ret-β i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = app} x x₁ K δ~ = {!!}
--     c .ind[]c {M = fun-β i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = matchNat M M₁} x x₁ K δ~ = {!!}
--     c .ind[]c {M = matchNatβz M M₁ i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = matchNatβs M M₁ V i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = matchNatη i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = matchDyn M M₁} x x₁ K δ~ = {!!}
--     c .ind[]c {M = matchDynβn M M₁ V i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = matchDynβf M M₁ V i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = tick M} x x₁ K δ~ = {!!}
--     c .ind[]c {M = tick-strictness i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = tickSubst i} x x₁ K δ~ = {!!}
--     c .ind[]c {M = isSetComp M M₁ x₂ y i i₁} x x₁ K δ~ = {!!}
--     c .indErr = {!!}
--     c .indTick = {!!}
--     c .indRet = {!!}
--     c .indApp = {!!}
--     c .indMatchNat = {!!}
--     c .indMatchDyn = {!!}
--     c .ind∙ = {!!}
--     c .ind∘E = {!!}
--     c .ind[]e = {!!}
--     c .indbind = {!!}
--   sem-bind = Bind.indPc c

SubstSem : ∀ (γ : Subst Δ Γ) → hProp _
SubstSem γ .fst = ∀ {Θ}(δ~ : ctx-sem _ Θ) → singl (reflect (γ ∘s reify δ~))
SubstSem γ .snd = isPropImplicitΠ λ _ → isPropΠ λ _ → isPropSingl

ValSem : ∀ (V : Val Γ R) → hProp _
ValSem V .fst = ∀ {Θ}(γ~ : ctx-sem _ Θ) → singl (V [ reify γ~ ]v)
ValSem V .snd = isPropImplicitΠ λ _ → isPropΠ λ _ → isPropSingl

CompSem : ∀ (M : Comp Γ R) → hProp _
CompSem M .fst = ∀ {Θ}(γ~ : ctx-sem _ Θ) → singl (M [ reify γ~ ]c)
CompSem M .snd = isPropImplicitΠ λ _ → isPropΠ λ _ → isPropSingl

EvCtxSem : ∀ (E : EvCtx Γ R S) → hProp _
EvCtxSem E .fst = ∀ {Θ}(γ~ : ctx-sem _ Θ)(M : Comp _ _) → singl (E [ reify γ~ ]e [ M ]∙)
EvCtxSem E .snd = isPropImplicitΠ λ _ → isPropΠ2 λ _ _ → isPropSingl

module Sem = SynInd SubstSem ValSem CompSem EvCtxSem

open SynInd.indCases
sem-cases : Sem.indCases
sem-cases .indIds δ~ .fst = δ~
sem-cases .indIds δ~ .snd = cong reflect ∘IdL
   ∙ reflect<-reify≡id _
sem-cases .ind∘s ih ih' δ~ .fst = ih (ih' δ~ .fst) .fst
sem-cases .ind∘s ih ih' δ~ .snd =
  (cong reflect (sym ∘Assoc ∙ cong (_ ∘s_) (sym (reify<-reflect≡id _)))
  ∙ ih _ .snd)
  ∙ cong (λ x → ih x .fst) (ih' δ~ .snd)
sem-cases .ind!s δ~ .fst = tt*
sem-cases .ind!s δ~ .snd = refl
sem-cases .ind,s ihγ ihV δ~ .fst =
  ihγ δ~ .fst , ihV δ~ .fst 
sem-cases .ind,s ihγ ihV δ~ .snd = ΣPathP
  ( (cong reflect (∘Assoc ∙ cong₂ _∘s_ wkβ refl)
    ∙ ihγ δ~ .snd)
  , substAssoc
    ∙ cong _[ reify δ~ ]v varβ
    ∙ ihV δ~ .snd
  )
sem-cases .indwk δ~ .fst = δ~ .fst
sem-cases .indwk δ~ .snd =
  cong reflect wkβ
  ∙ reflect<-reify≡id _

sem-cases .ind[]v ihV ihγ γ~ .fst =
  ihV (ihγ γ~ .fst) .fst
sem-cases .ind[]v {V = V} ihV ihγ γ~ .snd =
  sym substAssoc
  ∙ cong (V [_]v) (sym (reify<-reflect≡id _))
  ∙ ihV _ .snd ∙ cong (λ x → ihV x .fst) (ihγ _ .snd)
sem-cases .indVar γ~ .fst = γ~ .snd
sem-cases .indVar γ~ .snd = varβ

sem-cases .indRet γ~ = isContrSingl _ .fst
sem-cases .indApp γ~ = isContrSingl _ .fst
sem-cases .indErr γ~ = isContrSingl _ .fst
sem-cases .indZero γ~ = isContrSingl _ .fst
sem-cases .indSuc γ~ = isContrSingl _ .fst
sem-cases .indInjN γ~ = isContrSingl _ .fst
sem-cases .indInjArr γ~ = isContrSingl _ .fst

sem-cases .indLda ihM[x] γ~ .fst =
  lda (ihM[x] (↑sem γ~) .fst)
sem-cases .indLda {M = M} ihM[x] γ~ .snd =
  lda-nat _ _
  ∙ cong lda (cong (M [_]c) (cong₂ _,s_ reify-natural refl))
  ∙ cong lda (ihM[x] _ .snd)
sem-cases .indMapDyn ihVn ihVd γ~ .fst = mapDyn (ihVn (tt* , var) .fst) (ihVd (tt* , var) .fst) [ !s ,s γ~ .snd ]v
sem-cases .indMapDyn {V = V}{V' = V'} ihVn ihVd γ~ .snd =
  cong (_[ !s ,s γ~ .snd ]v) (cong₂ mapDyn
    (sym substId ∙ cong (V [_]v) ids-sole ∙ ihVn (tt* , var) .snd)
    (sym substId ∙ cong (V' [_]v) ids-sole ∙ ihVd (tt* , var) .snd))

sem-cases .ind[]∙ ihE ihM γ~ .fst = ihE γ~ (ihM γ~ .fst) .fst
sem-cases .ind[]∙ ihE ihM γ~ .snd =
  substPlugDist
  ∙ ihE γ~ _ .snd ∙ cong (λ x → ihE _ x .fst) (ihM _ .snd)
sem-cases .ind[]c ihM ihγ γ~ .fst =
  ihM (ihγ γ~ .fst) .fst
sem-cases .ind[]c {M = M} ihM ihγ γ~ .snd =
  sym substAssoc ∙ cong (M [_]c) (sym (reify<-reflect≡id _))
  ∙ ihM _ .snd ∙ cong (λ x → ihM x .fst) (ihγ γ~ .snd)
sem-cases .indTick ihM γ~ .fst = tick (ihM γ~ .fst)
sem-cases .indTick ihM γ~ .snd = tickSubst ∙ cong tick (ihM γ~ .snd)
sem-cases .indMatchNat ihM ihM' γ~ .fst =
  matchNat (ihM (γ~ .fst) .fst) (ihM' (↑sem (γ~ .fst)) .fst) [ ids ,s γ~ .snd ]c
sem-cases .indMatchNat {M' = M'} ihM ihM' γ~ .snd =
  matchNat-nat'
  ∙ cong (_[ ids ,s γ~ .snd ]c) (cong₂ matchNat (ihM _ .snd)
    (cong (M' [_]c) (cong (_,s var) reify-natural) ∙ ihM' _ .snd))
sem-cases .indMatchDyn ihM ihM' γ~ .fst =
  matchDyn (ihM  (↑sem (γ~ .fst)) .fst)
           (ihM' (↑sem (γ~ .fst)) .fst)
           [ ids ,s γ~ .snd ]c
sem-cases .indMatchDyn {M = M}{M' = M'} ihM ihM' γ~ .snd =
  matchDyn-nat'
  ∙ cong (_[ ids ,s γ~ .snd ]c)
    (cong₂ matchDyn
      (cong (M  [_]c) (cong (_,s var) reify-natural) ∙ ihM  _ .snd)
      (cong (M' [_]c) (cong (_,s var) reify-natural) ∙ ihM' _ .snd))

sem-cases .ind∙ γ~ M .fst = M
sem-cases .ind∙ γ~ M .snd =
  cong (_[ M ]∙) ∙substDist
  ∙ plugId
sem-cases .ind∘E ihE ihF γ~ M .fst =
  ihE γ~ (ihF γ~ M .fst) .fst
sem-cases .ind∘E ihE ihF γ~ M .snd =
  cong (_[ M ]∙) ∘substDist
  ∙ plugAssoc
  ∙ ihE γ~ _ .snd
  ∙ cong (λ x → ihE γ~ x .fst) (ihF _ _ .snd)
sem-cases .ind[]e ihE ihγ γ~ M .fst =
  ihE (ihγ γ~ .fst) M .fst
sem-cases .ind[]e {E = E} ihE ihγ γ~ M .snd =
  cong (_[ M ]∙) (sym substAssoc)
  ∙ cong (_[ M ]∙) (cong (E [_]e) (sym (reify<-reflect≡id _)))
  ∙ ihE _ _ .snd
  ∙ cong (λ x → ihE x M .fst) (ihγ γ~ .snd)
-- sem-bind N (λ γ~ → ih-M[x] γ~ .fst) γ~ .fst  
sem-cases .indbind ih-M[x] γ~ N .fst =
  bind (ih-M[x] ((γ~ [ wk ]sem) , var) .fst) [ N ]∙
sem-cases .indbind {M = M} ih-M[x] γ~ N .snd =
  cong (_[ N ]∙) (bind-nat ∙ cong bind (cong (M [_]c) (cong (_,s var) reify-natural))) -- | TODO: bind natural
  ∙ (cong (_[ N ]∙)) (cong bind (ih-M[x] _ .snd))
  -- ∙ sem-bind N (λ γ~ → ih-M[x] γ~ .fst) γ~ .snd
-- sem-cases .indIds δ~ .fst = δ~
-- sem-cases .indIds δ~ .snd = cong reflect ∘IdL
--   ∙ reflect<-reify≡id _

-- | The actual "tactics"
ssimpl : Subst Δ Γ → Subst Δ Γ
ssimpl γ = reify (Sem.indPs sem-cases γ univ-sem-subst .fst)

ssimpl-eq : (γ : Subst Δ Γ) → γ ≡ ssimpl γ
ssimpl-eq γ =
  sym (reify<-reflect≡id _)
  ∙ cong reify
      (cong reflect (sym ∘IdR ∙ cong₂ _∘s_ refl (sym (reify<-reflect≡id ids)))
      ∙ (Sem.indPs sem-cases γ univ-sem-subst .snd))

by-ssimpl : {γ γ' : Subst Δ Γ} → ssimpl γ ≡ ssimpl γ' → γ ≡ γ'
by-ssimpl p = ssimpl-eq _ ∙ p ∙ sym (ssimpl-eq _)


vsimpl : Val Γ R → Val Γ R
vsimpl V = Sem.indPv sem-cases V univ-sem-subst .fst

vsimpl-eq : (V : Val Γ R) → V ≡ vsimpl V
vsimpl-eq V =
  sym substId
  ∙ cong (V [_]v) (sym (reify<-reflect≡id _))
  ∙ Sem.indPv sem-cases V univ-sem-subst .snd

by-vsimpl : {V V' : Val Γ R} → vsimpl V ≡ vsimpl V' → V ≡ V'
by-vsimpl p = vsimpl-eq _ ∙ p ∙ sym (vsimpl-eq _)

csimpl : Comp Γ R → Comp Γ R
csimpl M = Sem.indPc sem-cases M univ-sem-subst .fst

csimpl-eq : (M : Comp Γ R) → M ≡ csimpl M
csimpl-eq M =
  sym substId
  ∙ cong (M [_]c) (sym (reify<-reflect≡id _))
  ∙ Sem.indPc sem-cases M univ-sem-subst .snd

by-csimpl : {M N : Comp Γ R} → csimpl M ≡ csimpl N → M ≡ N
by-csimpl p = csimpl-eq _ ∙ p ∙ sym (csimpl-eq _)

