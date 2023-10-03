module Syntax.Nbe where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Syntax.IntensionalTerms
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

-- Part 1: define a semantics of contexts, i.e. every context
-- gets interpreted as an product of the Value presheaves
ctx-sem : ∀ (Γ : Ctx) → (Ctx → Type (ℓ-suc ℓ-zero))
ctx-sem [] Δ      = Unit*
ctx-sem (A ∷ Γ) Δ = ctx-sem Γ Δ × Val Δ A

data CompNF (Γ : Ctx) : (R : Ty) → Type (ℓ-suc ℓ-zero) where
  errNF : CompNF Γ R
  retNF : Val Γ R → CompNF Γ R
  bindNF : Comp Γ R → CompNF (R ∷ Γ) S → CompNF Γ S
  tickNF : CompNF Γ R → CompNF Γ R
  neuNF : Comp Γ R → CompNF Γ R

bindNF' : CompNF Γ R → CompNF (R ∷ Γ) S → CompNF Γ S
bindNF' errNF K = errNF
bindNF' (retNF x) K = {!K [ ids ,s x ]cnf!}
bindNF' (bindNF x Mnf) K = {!!}
bindNF' (tickNF Mnf) K = tickNF (bindNF' Mnf K)
bindNF' (neuNF x) K = neuNF {!!}

_[_]sem : ctx-sem Γ Δ → Subst Θ Δ → ctx-sem Γ Θ
_[_]sem {Γ = []} tt* δ = tt*
_[_]sem {Γ = x ∷ Γ} (γ~ , v) δ = (γ~ [ δ ]sem) , (v [ δ ]v)

wk-ctx-sem : ctx-sem Γ Θ → ctx-sem Γ (R ∷ Θ)
wk-ctx-sem γ~ = γ~ [ wk ]sem

-- Part 2: prove the presheaf semantics is equivalent to the yoneda
-- embedding (i.e. prove Yoneda preserves cartesian structure)

reify : ctx-sem Γ Δ → Subst Δ Γ
reify {Γ = []} γ~ = !s
reify {Γ = x ∷ Γ} (γ~ , v) = reify γ~ ,s v

reflect : Subst Δ Γ → ctx-sem Γ Δ
reflect {Γ = []} γ = tt*
reflect {Γ = x ∷ Γ} γ = (reflect (wk ∘s γ)) , (var [ γ ]v)

reify<-reflect≡id : (γ : Subst Δ Γ) → reify (reflect γ) ≡ γ
reify<-reflect≡id {Γ = []} γ = sym []η
reify<-reflect≡id {Γ = x ∷ Γ} γ = sym (,sη ∙ cong₂ _,s_ (sym (reify<-reflect≡id (wk ∘s γ))) refl)

reflect<-reify≡id : (γ~ : ctx-sem Γ Δ) → reflect (reify γ~) ≡ γ~
reflect<-reify≡id {Γ = []} γ~ = refl
reflect<-reify≡id {Γ = x ∷ Γ} γ~ = ΣPathP (cong reflect wkβ ∙ reflect<-reify≡id (γ~ .fst) , varβ)

-- Part 3: give a semantics of terms as "polymorphic transformations"
-- These will all end up being natural but fortunately we don't need that.

ev-sem' : EvCtx Γ R S → ∀ {Θ} → ctx-sem Γ Θ → CompNF Θ R → CompNF Θ S
comp-sem' : Comp Γ R → ∀ {Θ} → ctx-sem Γ Θ → CompNF Θ R

ev-sem' ∙E x M~ = M~
ev-sem' (E ∘E E₁) x M~ = {!!}
ev-sem' (∘IdL i) x M~ = {!!}
ev-sem' (∘IdR i) x M~ = {!!}
ev-sem' (∘Assoc i) x M~ = {!!}
ev-sem' (E [ x₁ ]e) x M~ = {!!}
ev-sem' (substId i) x M~ = {!!}
ev-sem' (substAssoc i) x M~ = {!!}
ev-sem' (∙substDist i) x M~ = {!!}
ev-sem' (∘substDist i) x M~ = {!!}
ev-sem' (bind N[x]) x M~ = {!!}
ev-sem' (ret-η i) x M~ = {!!}
ev-sem' (isSetEvCtx E E₁ x₁ y i i₁) x M~ = {!!}

comp-sem' (E [ M ]∙) x = {!!}
comp-sem' (plugId i) x = {!!}
comp-sem' (plugAssoc i) x = {!!}
comp-sem' (M [ x₁ ]c) x = {!!}
comp-sem' (substId i) x = {!!}
comp-sem' (substAssoc i) x = {!!}
comp-sem' (substPlugDist i) x = {!!}
comp-sem' err x = {!!}
comp-sem' (strictness i) x = {!!}
comp-sem' ret x = {!!}
comp-sem' (ret-β i) x = {!!}
comp-sem' app x = {!!}
comp-sem' (fun-β i) x = {!!}
comp-sem' (matchNat M M₁) x = {!!}
comp-sem' (matchNatβz M M₁ i) x = {!!}
comp-sem' (matchNatβs M M₁ V i) x = {!!}
comp-sem' (matchNatη i) x = {!!}
comp-sem' (matchDyn M M₁) x = {!!}
comp-sem' (matchDynβn M M₁ V i) x = {!!}
comp-sem' (matchDynβf M M₁ V i) x = {!!}
comp-sem' (tick M) x = {!!}
comp-sem' (tick-strictness i) x = {!!}
comp-sem' (isSetComp M M₁ x₁ y i i₁) x = {!!}


subst-sem : Subst Δ Γ → ∀ {Θ} → ctx-sem Δ Θ → ctx-sem Γ Θ
val-sem : Val Γ R → ∀ {Θ} → ctx-sem Γ Θ → Val Θ R
comp-sem : Comp Γ R → ∀ {Θ} → ctx-sem Γ Θ → Comp Θ R
ev-sem : EvCtx Γ R S → ∀ {Θ} → ctx-sem Γ Θ → Comp Θ R → Comp Θ S

subst-sem ids x = x
subst-sem (γ ∘s δ) x = subst-sem γ (subst-sem δ x)
subst-sem !s = λ _ → tt*
subst-sem (γ ,s v) x = (subst-sem γ x) , (val-sem v x)
subst-sem wk = fst

-- these equations should essentially hold by refl
subst-sem ([]η i) = λ _ → tt*
subst-sem (∘IdL {γ = γ} i) = subst-sem γ
subst-sem (∘IdR i) = {!!}
subst-sem (∘Assoc i) = {!!}
subst-sem (wkβ i) = {!!}
subst-sem (,sη i) = {!!}
subst-sem (isSetSubst γ γ₁ x y i i₁) = {!!}

val-sem (V [ γ ]v) x = val-sem V (subst-sem γ x)
val-sem var x = x .snd
val-sem zro x = zro [ !s ]v
val-sem suc (_ , n) = suc [ !s ,s n ]v
val-sem (lda M[x]) x = lda (comp-sem M[x] ((x [ wk ]sem) , var))

val-sem injectN x = {!!}
val-sem (injectArr V) x = {!!}
val-sem (mapDyn V V₁) x = {!!}

-- don't bother proving these until you have to
val-sem (varβ i) x = {!!}
val-sem (substId i) x = {!!}
val-sem (substAssoc i) x = {!!}
val-sem (fun-η i) x = {!!}
val-sem (isSetVal V V₁ x₁ y i i₁) x = {!!}

comp-sem (E [ M ]∙) x = ev-sem E x (comp-sem M x)
comp-sem (M [ γ ]c) x = comp-sem M (subst-sem γ x)
comp-sem err x = err [ !s ]c
comp-sem ret (_ , v) = ret [ !s ,s v ]c
comp-sem app ((_ , f) , x) = app [ !s ,s f ,s x ]c
comp-sem (matchNat Mz Ms) (x , d) =
  matchNat (comp-sem Mz x)
           (comp-sem Ms ((x [ wk ]sem) , var))
           [ ids ,s d ]c 
comp-sem (matchDyn Mn Md) (x , d) =
  matchDyn (comp-sem Mn ((x [ wk ]sem) , var))
           (comp-sem Md ((x [ wk ]sem) , var))
           [ ids ,s d ]c
comp-sem (tick M) x =
  tick (comp-sem M x)
comp-sem (plugId i) x = {!!}
comp-sem (plugAssoc i) x = {!!}
comp-sem (substId i) x = {!!}
comp-sem (substAssoc i) x = {!!}
comp-sem (substPlugDist i) x = {!!}
comp-sem (strictness i) x = {!!}

comp-sem (ret-β i) x = {!!}
comp-sem (fun-β i) x = {!!}
comp-sem (matchNatβz M M₁ i) x = {!!}
comp-sem (matchNatβs M M₁ V i) x = {!!}
comp-sem (matchNatη i) x = {!!}
comp-sem (matchDynβn M M₁ V i) x = {!!}
comp-sem (matchDynβf M M₁ V i) x = {!!}
comp-sem (tick-strictness i) x = {!!}
comp-sem (isSetComp M M₁ x₁ y i i₁) x = {!!}

ev-sem ∙E x M = M
ev-sem (E ∘E E₁) x M = ev-sem E x (ev-sem E₁ x M)
ev-sem (E [ γ ]e) x M = ev-sem E (subst-sem γ x) M
ev-sem (bind K) x M = bind (comp-sem K ((x [ wk ]sem) , var)) [ M ]∙

ev-sem (∘IdL i) x M = {!!}
ev-sem (∘IdR i) x M = {!!}
ev-sem (∘Assoc i) x M = {!!}
ev-sem (substId i) x M = {!!}
ev-sem (substAssoc i) x M = {!!}
ev-sem (∙substDist i) x M = M
ev-sem (∘substDist i) x M = {!!}

ev-sem (ret-η i) x M = {!!}
ev-sem (isSetEvCtx E E₁ x₁ y i i₁) x M = {!!}

-- Part 4: Show the semantics of terms is equivalent to the yoneda
-- embedding of terms UP TO the equivalence between ctx-sem and Subst.

subst-correct : ∀ (γ : Subst Δ Γ)(δ~ : ctx-sem Δ Θ) → γ ∘s (reify δ~) ≡ reify (subst-sem γ δ~)
val-correct : ∀ (V : Val Δ S)(δ~ : ctx-sem Δ Θ) → V [ reify δ~ ]v ≡ val-sem V δ~
comp-correct : ∀ (M : Comp Δ S)(δ~ : ctx-sem Δ Θ) → M [ reify δ~ ]c ≡ comp-sem M δ~
ev-correct : ∀ (E : EvCtx Δ S R)(δ~ : ctx-sem Δ Θ) → E [ reify δ~ ]e [ M ]∙ ≡ ev-sem E δ~ M

subst-correct ids δ~ = ∘IdL
subst-correct (γ ∘s γ') δ~ = sym ∘Assoc
  ∙ cong (γ ∘s_) (subst-correct γ' δ~ )
  ∙ subst-correct γ _
subst-correct !s δ~ = []η
-- This is the naturality of ,s we discussed
subst-correct (γ ,s v) δ~ = {!!}
subst-correct wk δ~ = wkβ
-- This all should follow by isSet stuff
subst-correct (∘IdL i) δ~ = {!!}
subst-correct (∘IdR i) δ~ = {!!}
subst-correct (∘Assoc i) δ~ = {!!}
subst-correct (isSetSubst γ γ₁ x y i i₁) δ~ = {!!}
subst-correct ([]η i) δ~ = {!!}
subst-correct (wkβ i) δ~ = {!!}
subst-correct (,sη i) δ~ = {!!}

val-correct V δ~ = {!!}

comp-correct M δ~ = {!!}
ev-correct E δ~ = {!!}

-- Part 5: Now we get out a kind of "normalization" proof
normalize-val : (V : Val Γ S) → Val Γ S
normalize-val V = val-sem V (reflect ids)

normalize-v-correct : ∀ (V : Val Γ S) → V ≡ normalize-val V
normalize-v-correct V = (sym substId ∙ cong (V [_]v) (sym (reify<-reflect≡id _))) ∙ val-correct V (reflect ids)
