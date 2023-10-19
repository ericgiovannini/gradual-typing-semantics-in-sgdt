{-# OPTIONS --lossy-unification #-}


module Syntax.IntensionalTerms.Elim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.List

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
   ℓs ℓv ℓe ℓc : Level


module Elim
  (Bs : ∀ {Δ} {Γ} → Subst Δ Γ → Type ℓs)
  (Bv : ∀ {Γ} {R} → Val Γ R → Type ℓv)
  (Bc : ∀ {Γ} {R} → Comp Γ R → Type ℓc)
  (Be : ∀ {Γ R S} → EvCtx Γ R S → Type ℓe)
  where

  record Cases : Type (ℓ-max (ℓ-max ℓs ℓv) (ℓ-max ℓc ℓe)) where
    field
      -- Substitutions
      casesIds : Bs {Γ} ids
      cases∘s  : Bs γ → Bs δ → Bs (γ ∘s δ)
      cases!s  : Bs {Δ} !s
      cases,s  : Bs {Δ = Δ} {Γ = Γ} γ → Bv {R = R} V → Bs (γ ,s V)
      casesWk  : Bs (wk {S = S} {Γ = Γ})


      -- Values
      cases[]v   : Bv V → Bs γ → Bv (V [ γ ]v)
      casesVar   : Bv {Γ = (R ∷ Γ)} var
      casesZro   : Bv zro
      casesSuc   : Bv suc
      casesLda   : Bc M → Bv (lda M)
      casesInjN  : Bv injectN 
      casesInjArr : Bv injectArr 
      casesMapDyn : Bv V  →  Bv V' →  Bv (mapDyn V V')

      -- Computations
      cases[]∙    :  Be E  →  Bc M  →  Bc (E [ M ]∙)
      cases[]c    :  Bc M  →  Bs γ  →  Bc (M [ γ ]c)
      casesErr    :  Bc {R = R} err 
      casesTick   :  Bc M  →  Bc (tick M) 
      casesRet    :  Bc {R = R} ret 
      casesApp    :  Bc (app {S = S}{T = T}) 
      casesMatchNat :  Bc M  →  Bc M'  →  Bc (matchNat M M' )
      casesMatchDyn :  Bc M  →  Bc M'  →  Bc (matchDyn M M' )
      

      -- Evaluation Contexts
      cases∙E   :  Be {Γ = Γ}{R = R} ∙E 
      cases∘E   :  Be E  →  Be F  →  Be (E ∘E F) 
      cases[]e  :  Be E  →  Bs γ  →  Be (E [ γ ]e)
      casesBind :  Bc M  →  Be (bind M)

    -- ↑subst : Subst Δ Γ → Subst (R ∷ Δ) (R ∷ Γ)
    -- ↑subst γ = γ ∘s wk ,s var
    ↑Bs : Bs γ → Bs (↑subst {R = R} γ)
    ↑Bs bγ = cases,s (cases∘s bγ casesWk) casesVar

    field

      ------------------------------------
      -- Equations
      ------------------------------------
      
      -- Substitutions
      cases∘IdL-S : ∀ (b : Bs γ) →
        PathP (λ i -> Bs (∘IdL {γ = γ} i))
              (cases∘s casesIds b) b
      cases∘IdR-S : ∀ (b : Bs γ) →
        PathP (λ i -> Bs (∘IdR {γ = γ} i))
              (cases∘s b casesIds) b
      cases∘Assoc-S : ∀ (bγ : Bs γ) (bδ : Bs δ) (bθ : Bs θ) →
        PathP (λ i -> Bs (∘Assoc {γ = γ} {δ = δ} {θ = θ} i))
              (cases∘s bγ (cases∘s bδ bθ)) (cases∘s (cases∘s bγ bδ) bθ)
      cases[]η : ∀ (b : Bs γ) →
        PathP (λ i -> Bs ([]η {γ = γ} i))
              b cases!s
      casesWkβ : ∀ (bδ : Bs δ) (bV : Bv V) →
        PathP (λ i -> Bs (wkβ {δ = δ} {V = V} i))
              (cases∘s casesWk (cases,s bδ bV)) bδ
      cases,sη : ∀ (bδ : Bs δ) →
        PathP (λ i -> Bs (,sη {δ = δ} i))
              bδ (cases,s (cases∘s casesWk bδ) (cases[]v casesVar bδ))
      casesIsSetSubst : ∀ (γ : Subst Δ Γ) → isSet (Bs γ)


      -- Values
      casesSubstId-V : ∀ (b : Bv V) →
        PathP (λ i -> Bv (substId {V = V} i)) (cases[]v b casesIds) b
      casesSubstAssoc-V : ∀ (bV : Bv V) (bδ : Bs δ) (bγ : Bs γ) →
        PathP (λ i -> Bv (substAssoc {V = V} {δ = δ} {γ = γ} i))
              (cases[]v bV (cases∘s bδ bγ)) (cases[]v (cases[]v bV bδ) bγ)
      casesVarβ : ∀ (bδ : Bs δ) (bV : Bv V) →
        PathP (λ i -> Bv (varβ {δ = δ} {V = V} i))
              (cases[]v casesVar (cases,s bδ bV)) bV
      casesFun-η : ∀ (bV : Bv V) →
        PathP (λ i -> Bv (fun-η {V = V} i))
              bV
              (casesLda (cases[]c casesApp (cases,s (cases,s cases!s (cases[]v bV casesWk)) casesVar)))
      casesIsSetVal : ∀ (V : Val Γ S) → isSet (Bv V)


      -- Computations
      casesPlugId       : ∀ (bM : Bc M) →
        PathP (λ i -> Bc (plugId {M = M} i)) (cases[]∙ cases∙E bM) bM
        
      casesPlugAssoc    : ∀ (bF : Be F) (bE : Be E) (bM : Bc M) →
        PathP (λ i -> Bc (plugAssoc {F = F} {E = E} {M = M} i))
              (cases[]∙ (cases∘E bF bE) bM) (cases[]∙ bF (cases[]∙ bE bM))
              
      casesSubstId-C     : ∀ (bM : Bc M) →
        PathP (λ i -> Bc (substId {M = M} i)) (cases[]c bM casesIds) bM
        
      casesSubstAssoc-C   : ∀ (bM : Bc M) (bδ : Bs δ) (bγ : Bs γ) →
        PathP (λ i -> Bc (substAssoc {M = M} {δ = δ} {γ = γ} i))
              (cases[]c bM (cases∘s bδ bγ)) (cases[]c (cases[]c bM bδ) bγ)
              
      casesSubstPlugDist : ∀ (bE : Be E) (bM : Bc M) (bγ : Bs γ) →
        PathP (λ i -> Bc (substPlugDist {E = E} {M = M} {γ = γ} i))
              (cases[]c (cases[]∙ bE bM) bγ) (cases[]∙ (cases[]e bE bγ) (cases[]c bM bγ))
              
      casesStrictness : ∀ (bE : Be E) →
        PathP (λ i -> Bc (strictness {E = E} i))
              (cases[]∙ bE (cases[]c casesErr cases!s)) (cases[]c casesErr cases!s)
              
      casesRet-β : ∀ (bM : Bc M) →
        PathP (λ i -> Bc (ret-β {M = M} i))
              (cases[]∙ (cases[]e (casesBind bM) casesWk)
                        (cases[]c casesRet (cases,s cases!s casesVar)))
              bM
              
      casesFun-β : ∀ (bM : Bc M) →
        PathP (λ i -> Bc (fun-β {M = M} i))
              (cases[]c casesApp
                        (cases,s (cases,s cases!s (cases[]v (casesLda bM) casesWk)) casesVar))
              bM

      casesMatchNatβz : ∀ {Kz : Comp Γ S} {Ks : Comp (nat ∷ Γ) S}
                           (bKz : Bc Kz)   (bKs : Bc Ks) →
        PathP (λ i -> Bc (matchNatβz Kz Ks i))
              (cases[]c (casesMatchNat bKz bKs) (cases,s casesIds (cases[]v casesZro cases!s)))
              bKz
      casesMatchNatβs : ∀ {Kz : Comp Γ S} {Ks : Comp (nat ∷ Γ) S}
                          (bKz : Bc Kz)   (bKs : Bc Ks) →
        PathP (λ i -> Bc (matchNatβs Kz Ks i))
              (cases[]c
                (casesMatchNat bKz bKs)
                (cases,s casesWk (cases[]v casesSuc (cases,s cases!s casesVar))))
              bKs
              
      casesMatchNatη : ∀ {M : Comp (nat ∷ Γ) S} (bM : Bc M) →
        PathP (λ i -> Bc (matchNatη {M = M} i))
              bM
              (casesMatchNat
                (cases[]c bM (cases,s casesIds (cases[]v casesZro cases!s)))
                (cases[]c bM (cases,s casesWk (cases[]v casesSuc (cases,s cases!s casesVar)))))

      casesMatchDynβn : {Kn : Comp (nat ∷ Γ) S} {Kf : Comp ((dyn ⇀ dyn) ∷ Γ) S} {V : Val Γ nat}
                        (bKn : Bc Kn) (bKf : Bc Kf) (bV : Bv V) →
        PathP (λ i -> Bc (matchDynβn Kn Kf V i))
              (cases[]c
                (casesMatchDyn bKn bKf)
                (cases,s casesIds (cases[]v casesInjN (cases,s cases!s bV))))
              (cases[]c bKn (cases,s casesIds bV))

      casesMatchDynβf : {Kn : Comp (nat ∷ Γ) S} {Kf : Comp ((dyn ⇀ dyn) ∷ Γ) S} {V : Val Γ (dyn ⇀ dyn)}
                        (bKn : Bc Kn) (bKf : Bc Kf) (bV : Bv V) →
        PathP (λ i -> Bc (matchDynβf Kn Kf V i))
              (cases[]c
                (casesMatchDyn bKn bKf)
                (cases,s casesIds (cases[]v casesInjArr (cases,s cases!s bV))))
              (cases[]c bKf (cases,s casesIds bV))

      casesMatchDynSubst : {Kn : Comp (nat ∷ Γ) R} {Kf : Comp ((dyn ⇀ dyn) ∷ Γ) R} {γ : Subst Δ Γ}
                           (bKn : Bc Kn) (bKf : Bc Kf) (bγ : Bs γ) →
        PathP (λ i -> Bc (matchDynSubst Kn Kf γ i))
              (cases[]c (casesMatchDyn bKn bKf) (↑Bs bγ))
              (casesMatchDyn (cases[]c bKn (↑Bs bγ)) (cases[]c bKf (↑Bs bγ)))

      casesTick-strictness : ∀ (bM : Bc M) (bE : Be E) →
        PathP (λ i -> Bc (tick-strictness {E = E} {M = M} i))
              (cases[]∙ bE (casesTick bM)) (casesTick (cases[]∙ bE bM))

      casesTickSubst : ∀ (bM : Bc M) (bγ : Bs γ) →
        PathP (λ i -> Bc (tickSubst {M = M} {γ = γ} i))
              (cases[]c (casesTick bM) bγ) (casesTick (cases[]c bM bγ))

      casesIsSetComp : ∀ (M : Comp Γ S) → isSet (Bc M)
              

      -- Evaluation Contexts
      cases∘IdL-E : ∀ (bE : Be E) →
        PathP (λ i -> Be (∘IdL {E = E} i))
              (cases∘E cases∙E bE) bE
      cases∘IdR-E : ∀ (bE : Be E) →
        PathP (λ i -> Be (∘IdR {E = E} i))
              (cases∘E bE cases∙E) bE
      cases∘Assoc-E : ∀ (bE : Be E) (bF : Be F) (bF' : Be F') →
        PathP (λ i -> Be (∘Assoc {E = E} {F = F} {F' = F'} i))
              (cases∘E bE (cases∘E bF bF')) (cases∘E (cases∘E bE bF) bF')
      casesSubstId-E : ∀ (bE : Be E) →
        PathP (λ i -> Be (substId {E = E} i))
              (cases[]e bE casesIds) bE
      casesSubstAssoc-E : ∀ (bE : Be E) (bγ : Bs γ) (bδ : Bs δ) →
        PathP (λ i -> Be (substAssoc {E = E} {γ = γ} {δ = δ} i))
              (cases[]e bE (cases∘s bγ bδ)) (cases[]e (cases[]e bE bγ) bδ)
      cases∙substDist : ∀ (bγ : Bs γ) →
        PathP (λ i -> Be {S = S} (∙substDist {γ = γ} i))
              (cases[]e cases∙E bγ) cases∙E
      cases∘substDist : ∀ (bE : Be E) (bF : Be F) (bγ : Bs γ) →
        PathP (λ i -> Be (∘substDist {E = E} {F = F} {γ = γ} i))
              (cases[]e (cases∘E bE bF) bγ) (cases∘E (cases[]e bE bγ) (cases[]e bF bγ))
      casesRet-η : ∀ (bE : Be E) →
        PathP (λ i -> Be (ret-η {E = E} i))
              bE
              (casesBind (cases[]∙ (cases[]e bE casesWk)
                                   (cases[]c casesRet (cases,s cases!s casesVar))))

      casesIsSetEvCtx : ∀ (E : EvCtx Γ S T) → isSet (Be E)



  module _ (cases : Cases) where
    open Cases cases

    casesBs : ∀ (γ : Subst Δ Γ) → Bs γ
    casesBv : ∀ (V : Val Γ R) → Bv V
    casesBc : ∀ (M : Comp Γ R) → Bc M
    casesBe : ∀ (E : EvCtx Γ R S) → Be E

    -- Substitutions
    casesBs ids = casesIds
    casesBs (γ ∘s δ) = cases∘s (casesBs γ) (casesBs δ)
    casesBs !s = cases!s
    casesBs (γ ,s V) = cases,s (casesBs γ) (casesBv V)
    casesBs wk = casesWk

    casesBs (∘IdL {γ = γ} i) = cases∘IdL-S (casesBs γ) i
    casesBs (∘IdR {γ = γ} i) = cases∘IdR-S (casesBs γ) i
    casesBs (∘Assoc {γ = γ} {δ = δ} {θ = θ} i) =
      cases∘Assoc-S (casesBs γ) (casesBs δ) (casesBs θ) i
    casesBs ([]η {γ = γ} i) = cases[]η (casesBs γ) i
    casesBs (wkβ {δ = δ} {V = V} i) = casesWkβ (casesBs δ) (casesBv V) i
    casesBs (,sη {δ = δ} i) = cases,sη (casesBs δ) i
    casesBs (isSetSubst γ γ' p q i j) =
      isOfHLevel→isOfHLevelDep 2 casesIsSetSubst (casesBs γ) (casesBs γ')
        (cong casesBs p) (cong casesBs q) (isSetSubst γ γ' p q) i j


    -- Values
    casesBv (V [ γ ]v) = cases[]v (casesBv V) (casesBs γ)
    casesBv var = casesVar
    casesBv zro = casesZro
    casesBv suc = casesSuc
    casesBv (lda M) = casesLda (casesBc M)
    casesBv injectN = casesInjN
    casesBv injectArr = casesInjArr
    casesBv (mapDyn Vn Vf) = casesMapDyn (casesBv Vn) (casesBv Vf)
    
    casesBv (substId {V = V} i) = casesSubstId-V (casesBv V) i
    casesBv (substAssoc {V = V} {δ = δ} {γ = γ} i) =
      casesSubstAssoc-V (casesBv V) (casesBs δ) (casesBs γ) i
    casesBv (varβ {δ = δ} {V = V} i) = casesVarβ (casesBs δ) (casesBv V) i
    casesBv (fun-η {V = V} i) = casesFun-η (casesBv V) i
    casesBv (isSetVal V V' p q i j) =
      isOfHLevel→isOfHLevelDep 2 casesIsSetVal (casesBv V) (casesBv V')
        (cong casesBv p) (cong casesBv q) (isSetVal V V' p q) i j



    -- Computations
    casesBc (E [ M ]∙) = cases[]∙ (casesBe E) (casesBc M)
    casesBc (M [ γ ]c) = cases[]c (casesBc M) (casesBs γ)
    casesBc err = casesErr
    casesBc ret = casesRet
    casesBc app = casesApp
    casesBc (matchNat M M') = casesMatchNat (casesBc M) (casesBc M')
    casesBc (matchDyn M M') = casesMatchDyn (casesBc M) (casesBc M')
    casesBc (tick M) = casesTick (casesBc M)

    casesBc (plugId {M = M} i) = casesPlugId (casesBc M) i
    casesBc (plugAssoc {F = F} {E = E} {M = M} i) =
      casesPlugAssoc (casesBe F) (casesBe E) (casesBc M) i
    casesBc (substId {M = M} i) = casesSubstId-C (casesBc M) i
    casesBc (substAssoc {M = M} {δ = δ} {γ = γ} i) =
      casesSubstAssoc-C (casesBc M) (casesBs δ) (casesBs γ) i
    casesBc (substPlugDist {E = E} {M = M} {γ = γ} i) =
      casesSubstPlugDist (casesBe E) (casesBc M) (casesBs γ) i
    casesBc (strictness {E = E} i) = casesStrictness (casesBe E) i
    casesBc (ret-β {M = M} i) = casesRet-β (casesBc M) i
    casesBc (fun-β {M = M} i) = casesFun-β (casesBc M) i
    casesBc (matchNatβz M M' i) = casesMatchNatβz (casesBc M) (casesBc M') i
    casesBc (matchNatβs M M' i) = casesMatchNatβs (casesBc M) (casesBc M') i
    casesBc (matchNatη {M = M} i) = casesMatchNatη (casesBc M) i
    casesBc (matchDynβn M M' V i) = casesMatchDynβn (casesBc M) (casesBc M') (casesBv V) i
    casesBc (matchDynβf M M' V i) = casesMatchDynβf (casesBc M) (casesBc M') (casesBv V) i
    casesBc (matchDynSubst M M' γ i) = casesMatchDynSubst (casesBc M) (casesBc M') (casesBs γ) i
    casesBc (tick-strictness {E = E} {M = M} i) = casesTick-strictness (casesBc M) (casesBe E ) i
    casesBc (tickSubst {M = M} {γ = γ} i) = casesTickSubst (casesBc M) (casesBs γ) i
    casesBc (isSetComp M M' p q i j) =
      isOfHLevel→isOfHLevelDep 2 casesIsSetComp (casesBc M) (casesBc M')
        (cong casesBc p) (cong casesBc q) (isSetComp M M' p q) i j


    -- Evaluation Contexts
    casesBe ∙E = cases∙E
    casesBe (E ∘E F) = cases∘E (casesBe E) (casesBe F)
    casesBe (∘IdL {E = E} i) = cases∘IdL-E (casesBe E) i
    casesBe (∘IdR {E = E} i) = cases∘IdR-E (casesBe E) i
    casesBe (∘Assoc {E = E} {F = F} {F' = F'} i) =
      cases∘Assoc-E (casesBe E) (casesBe F) (casesBe F') i
    casesBe (E [ γ ]e) = cases[]e (casesBe E) (casesBs γ)
    casesBe (bind M) = casesBind (casesBc M)

    casesBe (substId {E = E} i) = casesSubstId-E (casesBe E) i
    casesBe (substAssoc {E = E} {γ = γ} {δ = δ} i) =
      casesSubstAssoc-E (casesBe E) (casesBs γ) (casesBs δ) i
    casesBe (∙substDist {γ = γ} i) = cases∙substDist (casesBs γ) i
    casesBe (∘substDist {E = E} {F = F} {γ = γ} i) =
      cases∘substDist (casesBe E) (casesBe F) (casesBs γ) i
    casesBe (ret-η {E = E} i) = casesRet-η (casesBe E) i
    casesBe (isSetEvCtx E F p q i j) =
      isOfHLevel→isOfHLevelDep 2 casesIsSetEvCtx (casesBe E) (casesBe F)
        (cong casesBe p) (cong casesBe q) (isSetEvCtx E F p q) i j

   

