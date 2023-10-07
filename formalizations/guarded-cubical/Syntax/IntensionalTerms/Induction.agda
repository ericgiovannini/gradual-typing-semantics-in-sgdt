module Syntax.IntensionalTerms.Induction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
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
   ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

module SynInd
  (Ps : ∀ {Δ} {Γ} → Subst Δ Γ → hProp ℓ)
  (Pv : ∀ {Γ} {R} → Val Γ R → hProp ℓ')
  (Pc : ∀ {Γ} {R} → Comp Γ R → hProp ℓ'')
  (Pe : ∀ {Γ R S} → EvCtx Γ R S → hProp ℓ''')
  where

  record indCases : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓ'''))) where
    field
      indIds : ⟨ Ps {Γ} ids ⟩
      ind∘s : ⟨ Ps γ ⟩ → ⟨ Ps θ ⟩ → ⟨ Ps (γ ∘s θ) ⟩
      ind!s : ⟨ Ps {Δ} !s ⟩
      ind,s : ⟨ Ps {Θ}{Γ} γ ⟩ → ⟨ Pv {R = R} V ⟩ → ⟨ Ps (γ ,s V) ⟩
      indwk : ⟨ Ps (wk {S = S}{Γ = Γ}) ⟩

      ind[]v : ⟨ Pv V ⟩ → ⟨ Ps γ ⟩ → ⟨ Pv (V [ γ ]v)⟩
      indVar : ⟨ Pv {Γ = (R ∷ Γ)} var ⟩
      indZero : ⟨ Pv zro ⟩
      indSuc : ⟨ Pv suc ⟩
      indLda : ⟨ Pc M ⟩ → ⟨ Pv (lda M) ⟩
      indInjN : ⟨ Pv injectN ⟩
      indInjArr : ⟨ Pv injectArr ⟩
      indMapDyn : ⟨ Pv V ⟩ → ⟨ Pv V' ⟩
                → ⟨ Pv (mapDyn V V') ⟩

      ind[]∙ : ⟨ Pe E ⟩ → ⟨ Pc M ⟩ → ⟨ Pc (E [ M ]∙)⟩
      ind[]c : ⟨ Pc M ⟩ → ⟨ Ps γ ⟩ → ⟨ Pc (M [ γ ]c)⟩
      indErr : ⟨ Pc {R = R} err ⟩
      indTick : ⟨ Pc M ⟩ → ⟨ Pc (tick M) ⟩
      indRet : ⟨ Pc {R = R} ret ⟩
      indApp : ⟨ Pc (app {S = S}{T = T}) ⟩
      indMatchNat : ⟨ Pc M ⟩ → ⟨ Pc M' ⟩ → ⟨ Pc (matchNat M M' )⟩
      indMatchDyn : ⟨ Pc M ⟩ → ⟨ Pc M' ⟩ → ⟨ Pc (matchDyn M M' )⟩

      ind∙ : ⟨ Pe {Γ}{R} ∙E ⟩
      ind∘E : ⟨ Pe E ⟩ → ⟨ Pe F ⟩ → ⟨ Pe (E ∘E F) ⟩
      ind[]e : ⟨ Pe E ⟩ → ⟨ Ps γ ⟩ → ⟨ Pe (E [ γ ]e)⟩
      indbind : ⟨ Pc M ⟩ → ⟨ Pe (bind M) ⟩

  module _ (ic : indCases) where
    open indCases ic
    indPs : ∀ (γ : Subst Δ Γ) → ⟨ Ps γ ⟩
    indPv : ∀ (V : Val Γ R) → ⟨ Pv V ⟩
    indPc : ∀ (M : Comp Γ R) → ⟨ Pc M ⟩
    indPe : ∀ (E : EvCtx Γ R S) → ⟨ Pe E ⟩

    indPs ids = indIds
    indPs (γ ∘s γ₁) = ind∘s (indPs γ) (indPs γ₁)
    indPs !s = ind!s
    indPs (γ ,s V) = ind,s (indPs γ) (indPv V)
    indPs wk = indwk
    indPs (∘IdL {γ = γ} i) =
     isProp→PathP ((λ i → Ps (∘IdL {γ = γ} i) .snd)) (ind∘s indIds (indPs γ)) (indPs γ) i
    indPs (∘IdR {γ = γ} i) = isProp→PathP (((λ i → Ps (∘IdR {γ = γ} i) .snd)))
      ((ind∘s (indPs γ) indIds)) ((indPs γ)) i
    indPs (∘Assoc {γ = γ}{δ = δ}{θ = θ} i) =
      isProp→PathP (λ i → Ps (∘Assoc {γ = γ} {δ = δ} {θ = θ} i) .snd)
        (ind∘s (indPs γ) (ind∘s (indPs δ) (indPs θ)))
        (ind∘s (ind∘s (indPs γ) (indPs δ)) (indPs θ))
        i
    indPs ([]η {γ = γ} i) = isProp→PathP (λ i → Ps ([]η {γ = γ} i) .snd)
      (indPs γ) ind!s i
    indPs (wkβ {δ = δ}{V = V} i) = isProp→PathP (λ i → Ps (wkβ {δ = δ}{V = V} i) .snd)
      (ind∘s indwk (ind,s (indPs δ) (indPv V))) (indPs δ) i
    indPs (,sη {δ = δ} i) = isProp→PathP (λ i → Ps (,sη {δ = δ} i) .snd)
      (indPs δ) (ind,s (ind∘s indwk (indPs δ)) (ind[]v indVar (indPs δ))) i
    indPs (isSetSubst γ γ' p q i j) = isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (Ps x .snd))
      (indPs γ)
      (indPs γ')
      (λ j → indPs (p j))
      (λ j → indPs (q j))
      (isSetSubst γ γ' p q) i j

    indPv (V [ γ ]v) = ind[]v (indPv V) (indPs γ)
    indPv var = indVar
    indPv zro = indZero
    indPv suc = indSuc
    indPv (lda M) = indLda (indPc M)
    indPv injectN = indInjN
    indPv injectArr = indInjArr
    indPv (mapDyn V V') = indMapDyn (indPv V) (indPv V')
    -- avert your eyes
    indPv (substId {V = V} i) =
      isProp→PathP (λ i → Pv (substId i) .snd) (ind[]v (indPv V) indIds) (indPv V) i
    indPv (substAssoc {V = V}{δ = δ}{γ = γ} i) = isProp→PathP (λ i → Pv (substAssoc i) .snd)
     (ind[]v (indPv V) (ind∘s (indPs δ) (indPs γ)))
     (ind[]v (ind[]v (indPv V) (indPs δ)) (indPs γ))
     i

    indPv (varβ {δ = δ}{V = V} i) = isProp→PathP (λ i → Pv (varβ i) .snd)
      (ind[]v indVar (ind,s (indPs δ) (indPv V)))
      (indPv V)
      i

    indPv (fun-η {V = V} i) = isProp→PathP (λ i → Pv (fun-η i) .snd)
      (indPv V)
      (indLda (ind[]c indApp (ind,s (ind,s ind!s (ind[]v (indPv V) indwk)) indVar)))
      i
    indPv (isSetVal V V' p q i j) = isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (Pv x .snd))
      (indPv V)
      (indPv V')
      (λ j → indPv (p j))
      (λ j → indPv (q j))
      (isSetVal V V' p q)
      i j

    indPc (E [ M ]∙) = ind[]∙ (indPe E) (indPc M)
    indPc (M [ γ ]c) = ind[]c (indPc M) (indPs γ)
    indPc err = indErr
    indPc (tick M) = indTick (indPc M)
    indPc ret = indRet
    indPc app = indApp
    indPc (matchNat M M₁) = indMatchNat (indPc M) (indPc M₁)
    indPc (matchDyn M M₁) = indMatchDyn (indPc M) (indPc M₁)
    -- macros did this
    indPc (plugId {M = M} i) = isProp→PathP (λ i → Pc (plugId i) .snd) (ind[]∙ ind∙ (indPc M)) (indPc M) i
    indPc (plugAssoc {F = F}{E = E}{M = M} i) = isProp→PathP (λ i → Pc (plugAssoc i) .snd) (ind[]∙ (ind∘E (indPe F) (indPe E)) (indPc M)) (ind[]∙ (indPe F) (ind[]∙ (indPe E) (indPc M))) i
    indPc (substId {M = M} i) = isProp→PathP (λ i → Pc (substId i) .snd) (ind[]c (indPc M) indIds) (indPc M) i
    indPc (substAssoc {M = M}{δ = δ}{γ = γ} i) = isProp→PathP (λ i → Pc (substAssoc i) .snd) (ind[]c (indPc M) (ind∘s (indPs δ) (indPs γ))) (ind[]c (ind[]c (indPc M) (indPs δ)) (indPs γ)) i
    indPc (substPlugDist {E = E}{M = M}{γ = γ} i) = isProp→PathP (λ i → Pc (substPlugDist i) .snd) (ind[]c (ind[]∙ (indPe E) (indPc M)) (indPs γ)) (ind[]∙ (ind[]e (indPe E) (indPs γ)) (ind[]c (indPc M) (indPs γ))) i
    indPc (strictness {E = E} i) = isProp→PathP (λ i → Pc (strictness i) .snd) (ind[]∙ (indPe E) (ind[]c indErr ind!s)) (ind[]c indErr ind!s) i
    indPc (ret-β {M = M} i) = isProp→PathP (λ i → Pc (ret-β i) .snd) (ind[]∙ (ind[]e (indbind (indPc M)) indwk) (ind[]c indRet (ind,s ind!s indVar))) (indPc M) i
    indPc (fun-β {M = M} i) = isProp→PathP (λ i → Pc (fun-β i) .snd) (ind[]c indApp (ind,s (ind,s ind!s (ind[]v (indLda (indPc M)) indwk)) indVar)) (indPc M) i
    indPc (matchNatβz M N i) = isProp→PathP (λ i → Pc (matchNatβz M N i) .snd) (ind[]c (indMatchNat (indPc M) (indPc N)) (ind,s indIds (ind[]v indZero ind!s))) (indPc M) i
    indPc (matchNatβs M N i) = isProp→PathP (λ i → Pc (matchNatβs M N i) .snd) (ind[]c (indMatchNat (indPc M) (indPc N)) (ind,s indwk (ind[]v indSuc (ind,s ind!s indVar)))) (indPc N) i
    indPc (matchNatη {M = M} i) = isProp→PathP (λ i → Pc (matchNatη i) .snd) (indPc M) (indMatchNat (ind[]c (indPc M) (ind,s indIds (ind[]v indZero ind!s))) (ind[]c (indPc M) (ind,s indwk (ind[]v indSuc (ind,s ind!s indVar))))) i
    indPc (matchDynβn M N V i) = isProp→PathP (λ i → Pc (matchDynβn M N V i) .snd) (ind[]c (indMatchDyn (indPc M) (indPc N)) (ind,s indIds (ind[]v indInjN (ind,s ind!s (indPv V))))) (ind[]c (indPc M) (ind,s indIds (indPv V))) i
    indPc (matchDynβf M N V i) = isProp→PathP (λ i → Pc (matchDynβf M N V i) .snd) (ind[]c (indMatchDyn (indPc M) (indPc N)) (ind,s indIds (ind[]v indInjArr (ind,s ind!s (indPv V))))) (ind[]c (indPc N) (ind,s indIds (indPv V))) i
    indPc (matchDynSubst M N γ i) = isProp→PathP (λ i → Pc (matchDynSubst M N γ i) .snd) (ind[]c (indMatchDyn (indPc M) (indPc N)) (ind,s (ind∘s (indPs γ) indwk) indVar)) (indMatchDyn (ind[]c (indPc M) (ind,s (ind∘s (indPs γ) indwk) indVar)) (ind[]c (indPc N) (ind,s (ind∘s (indPs γ) indwk) indVar))) i
    indPc (tick-strictness {E = E}{M = M} i) = isProp→PathP (λ i → Pc (tick-strictness i) .snd) (ind[]∙ (indPe E) (indTick (indPc M))) (indTick (ind[]∙ (indPe E) (indPc M))) i
    indPc (tickSubst {M = M}{γ = γ} i) = isProp→PathP (λ i → Pc (tickSubst i) .snd) (ind[]c (indTick (indPc M)) (indPs γ)) (indTick (ind[]c (indPc M) (indPs γ))) i
    indPc (isSetComp M N p q i j) = isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (Pc x .snd))
      (indPc M)
      (indPc N)
      (λ j → indPc (p j))
      (λ j → indPc (q j))
      (isSetComp M N p q)
      i j

    indPe ∙E = ind∙
    indPe (E ∘E E₁) = ind∘E (indPe E) (indPe E₁)
    indPe (E [ γ ]e) = ind[]e (indPe E) (indPs γ)
    indPe (bind M) = indbind (indPc M)
    indPe (∘IdL {E = E} i) = isProp→PathP (λ i → Pe (∘IdL i) .snd) (ind∘E ind∙ (indPe E)) (indPe E) i
    indPe (∘IdR {E = E} i) = isProp→PathP (λ i → Pe (∘IdR i) .snd) (ind∘E (indPe E) ind∙) (indPe E) i
    indPe (∘Assoc {E = E}{F = F}{F' = F'} i) = isProp→PathP (λ i → Pe (∘Assoc i) .snd) (ind∘E (indPe E) (ind∘E (indPe F) (indPe F'))) (ind∘E (ind∘E (indPe E) (indPe F)) (indPe F')) i
    indPe (substId {E = E} i) = isProp→PathP (λ i → Pe (substId i) .snd) (ind[]e (indPe E) indIds) (indPe E) i
    indPe (substAssoc {E = E}{γ = γ}{δ = δ} i) = isProp→PathP (λ i → Pe (substAssoc i) .snd) (ind[]e (indPe E) (ind∘s (indPs γ) (indPs δ))) (ind[]e (ind[]e (indPe E) (indPs γ)) (indPs δ)) i
    indPe (∙substDist {γ = γ} i) = isProp→PathP (λ i → Pe (∙substDist i) .snd) (ind[]e ind∙ (indPs γ)) (ind∙) i
    indPe (∘substDist {E = E}{F = F}{γ = γ} i) = isProp→PathP (λ i → Pe (∘substDist i) .snd) (ind[]e (ind∘E (indPe E) (indPe F)) (indPs γ)) (ind∘E (ind[]e (indPe E) (indPs γ)) (ind[]e (indPe F) (indPs γ))) i
    indPe (ret-η {E = E} i) = isProp→PathP (λ i → Pe (ret-η i) .snd) (indPe E) (indbind (ind[]∙ (ind[]e (indPe E) indwk) (ind[]c indRet (ind,s ind!s indVar)))) i
    indPe (isSetEvCtx E F p q i j) = isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (Pe x .snd))
      (indPe E)
      (indPe F)
      (λ j → indPe (p j))
      (λ j → indPe (q j))
      (isSetEvCtx E F p q)
      i j
