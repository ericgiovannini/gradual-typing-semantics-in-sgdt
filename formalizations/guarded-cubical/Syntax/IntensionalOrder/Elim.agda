{-# OPTIONS --lossy-unification #-}


module Syntax.IntensionalOrder.Elim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.List

open import Syntax.IntensionalTerms
open import Syntax.IntensionalOrder
open import Syntax.Types

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T U R' S' T' U' R'' S'' T'' U'' : Ty

   γ γ' γ'' δ δ' δ'' θ θ' θ'' : Subst Δ Γ

   V V' V'' : Val Γ S
   M M' M'' N N' : Comp Γ S
   E E' E'' F F' : EvCtx Γ S T
   ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓs ℓv ℓe ℓc : Level
   B B' C C' D D' : Θ ⊑ctx Θ'
   c c' c'' d d' d'' : S ⊑ S'
   
   γ⊑γ' γ'⊑γ'' γ⊑γ'' δ⊑δ' : Subst⊑ C D γ γ'
   V⊑V' V'⊑V'' V⊑V'' : Val⊑ C c V V'
   M⊑M' M'⊑M'' M⊑M'' N⊑N' : Comp⊑ C c M M'
   E⊑E' E'⊑E'' E⊑E'' F⊑F' : EvCtx⊑ C c d E E'

module Elim
  (Bs : ∀ (Δ Δ' Γ Γ' : Ctx) (C : Δ ⊑ctx Δ')
          (D : Γ ⊑ctx Γ') (γ : Subst Δ Γ) (γ' : Subst Δ' Γ') →
          Subst⊑ C D γ γ' → Type ℓs)
  (Bv : ∀ (Γ Γ' : Ctx) (S S' : Ty) (C : Γ ⊑ctx Γ') (c : S ⊑ S')
          (V : Val Γ S) (V' : Val Γ' S') → Val⊑ C c V V' → Type ℓv)
  (Bc : ∀ (Γ Γ' : Ctx) (S S' : Ty) (C : Γ ⊑ctx Γ') (c : S ⊑ S') (M : Comp Γ S)
          (M' : Comp Γ' S') -> Comp⊑ C c M M' → Type ℓc)
  (Be : ∀ (Γ Γ' : Ctx) (S S' T T' : Ty) (C : Γ ⊑ctx Γ') (c : S ⊑ S') (d : T ⊑ T')
          (E : EvCtx Γ S T) (E' : EvCtx Γ' S' T')  -> EvCtx⊑ C c d E E' → Type ℓe)
  where

  record Cases : Type (ℓ-max (ℓ-max ℓs ℓv) (ℓ-max ℓc ℓe)) where
    field

      -- Substitutions
      casesReflexiveSubst : ∀ Δ Γ γ →
        Bs Δ Δ Γ Γ (refl-⊑ctx Δ) (refl-⊑ctx Γ) γ γ reflexive-subst
      cases!s : ∀ Γ Γ' C → Bs Γ Γ' [] [] C (refl-⊑ctx []) !s !s !s
      cases,s : ∀ Δ Δ' Γ Γ' C D γ γ' S S' c V V'
                (γ⊑γ' : Subst⊑ C D γ γ') (V⊑V' : Val⊑ C c V V') ->
                Bs Δ Δ' Γ Γ' C D γ γ' γ⊑γ' ->
                Bv Δ Δ' S S' C c V V' V⊑V' ->
                Bs Δ Δ' (S ∷ Γ) (S' ∷ Γ') C (c ∷ D) (γ ,s V) (γ' ,s V') (γ⊑γ' ,s V⊑V')
      cases∘s : ∀ Θ Θ' Δ Δ' Γ Γ' B C D γ γ' δ δ'
                (γ⊑γ' : Subst⊑ C D γ γ') (δ⊑δ' : Subst⊑ B C δ δ') →
                Bs Δ Δ' Γ Γ' C D γ γ' γ⊑γ' → Bs Θ Θ' Δ Δ' B C δ δ' δ⊑δ' →
                Bs Θ Θ' Γ Γ' B D (γ ∘s δ) (γ' ∘s δ') (γ⊑γ' ∘s δ⊑δ')
      casesIds : ∀ Δ Δ' C → ((Bs Δ Δ' Δ Δ' C C ids) ids) _ids_
      casesWk : ∀ Δ Δ' S S' C c →  Bs (S ∷ Δ) (S' ∷ Δ') Δ Δ' (c ∷ C) C wk wk wk
     -- casesIsProp⊑Subst : 
   {-   casesHetTransSubst :
        ∀ Δ Δ' Δ'' Γ Γ' Γ'' B B' C C' D D' γ γ' γ'' γ⊑γ' γ'⊑γ'' →
        Bs Δ Δ' Γ Γ' C D γ γ' γ⊑γ' →
        Bs Δ' Δ'' Γ' Γ'' C' D' γ' γ'' γ'⊑γ'' →
        Bs Δ Δ'' Γ Γ'' B B' γ γ'' (hetTrans {B = B} {B' = B'} γ⊑γ' γ'⊑γ'')-}

      -- Values
      casesReflexiveVal : ∀ Γ S V →
        Bv Γ Γ S S (refl-⊑ctx Γ) (refl-⊑ S) V V reflexive-val
      cases[]v : ∀ Θ Θ' Δ Δ' S S' B C c γ γ' V V'
                 (V⊑V' : Val⊑ C c V V') (γ⊑γ' : Subst⊑ B C γ γ')  →
                 Bv Δ Δ' S S' C c V V' V⊑V' →
                 Bs Θ Θ' Δ Δ' B C γ γ' γ⊑γ' →
                 Bv Θ Θ' S S' B c (V [ γ ]v) (V' [ γ' ]v) (V⊑V' [ γ⊑γ' ]v)
      casesVar : ∀ Γ Γ' S S' C c → Bv (S ∷ Γ) (S' ∷ Γ') S S' (c ∷ C) c var var var
      casesZro : Bv [] [] nat nat [] nat zro zro zro
      casesSuc : Bv (nat ∷ []) (nat ∷ []) nat nat (nat ∷ []) nat suc suc suc
      casesLda : ∀ Γ Γ' S S' T T' C c d M M' M⊑M' →
                 Bc (S ∷ Γ) (S' ∷ Γ') T T' (c ∷ C) d M M' M⊑M' →
                 Bv Γ Γ' (S ⇀ T) (S' ⇀ T') C (c ⇀ d) (lda M) (lda M') (lda M⊑M')
      casesInjNatUpL :
        ∀ V V' V⊑V' → Bv [] [] nat dyn [] inj-nat V V' V⊑V' →
        Bv [] [] dyn dyn [] dyn (injectN [ !s ,s V ]v) V' (injNatUpL V⊑V')
      casesInjNatUpL' :
        Bv (nat ∷ []) (dyn ∷ []) dyn dyn (inj-nat ∷ []) dyn injectN var injNatUpL'
      casesInjNatUpR :
        ∀ V V' V⊑V' → Bv [] [] nat nat [] nat V V' V⊑V' →
        Bv [] [] nat dyn [] inj-nat V (injectN [ !s ,s V' ]v) (injNatUpR V⊑V')
      casesInjNatUpR' :
        Bv (nat ∷ []) (nat ∷ []) nat dyn (nat ∷ []) inj-nat var injectN injNatUpR'
      casesInjArrUpL :
        ∀ S V V' c V⊑V' → Bv [] [] S dyn [] (inj-arr c) V V' V⊑V' →
        Bv [] [] dyn dyn [] dyn (injectArr ∘V' (emb c ∘V V)) V' (injArrUpL V⊑V')
      casesInjArrUpR :
        ∀ V V' V⊑V' →
        Bv [] [] (dyn ⇀ dyn) (dyn ⇀ dyn) [] (dyn ⇀ dyn) V V' V⊑V' →
        Bv [] [] (dyn ⇀ dyn) dyn [] (inj-arr (refl-⊑ (dyn ⇀ dyn))) V
          (injectArr [ !s ,s V' ]v) (injArrUpR V⊑V')
      casesMapDyn-nat : ∀ Vn Vn' Vf Vn⊑Vn' →
        Bv (nat ∷ []) (nat ∷ []) nat nat (nat ∷ []) nat Vn Vn' Vn⊑Vn' →
        Bv (nat ∷ []) (dyn ∷ []) nat dyn (inj-nat ∷ []) inj-nat Vn (mapDyn Vn' Vf)
          (mapDyn-nat {Vn = Vn} {Vn' = Vn'} {Vf = Vf} Vn⊑Vn')
      casesMapDyn-arr : ∀ S c Vn Vs Vf Vs⊑Vf →
        Bv (S ∷ []) ((dyn ⇀ dyn) ∷ []) S (dyn ⇀ dyn) (c ∷ []) c Vs Vf Vs⊑Vf →
        Bv (S ∷ []) (dyn ∷ []) S dyn (inj-arr c ∷ []) (inj-arr c) Vs (mapDyn Vn Vf)
          (mapDyn-arr {Vn = Vn} {Vs = Vs} {Vf = Vf} Vs⊑Vf)
      -- casesHetTransVal : Bv V⊑V' -> Bv V'⊑V'' -> Bv V⊑V''

      -- Evaluation Contexts
      casesReflexiveEval :
        ∀ Γ S E → Be Γ Γ S S S S (refl-⊑ctx Γ) (refl-⊑ S) (refl-⊑ S) E E reflexive-eval
      cases∙E : ∀ Γ Γ' S S' C c → Be Γ Γ' S S' S S' C c c ∙E ∙E ∙E
      cases∘E : ∀ Γ Γ' R R' S S' T T' C b c d E E' F F' E⊑E' F⊑F' →
        Be Γ Γ' S S' T T' C c d E E' E⊑E' →
        Be Γ Γ' R R' S S' C b c F F' F⊑F' →
        Be Γ Γ' R R' T T' C b d (E ∘E F) (E' ∘E F') (E⊑E' ∘E F⊑F')
      cases[]e  : ∀ Γ Γ' Δ Δ' S S' T T' B C c d E E' γ γ' E⊑E' γ⊑γ' →
        Be Γ Γ' S S' T T' C c d E E' E⊑E' →
        Bs Δ Δ' Γ Γ' B C γ γ' γ⊑γ' →
        Be Δ Δ' S S' T T' B c d (E [ γ ]e) (E' [ γ' ]e) (E⊑E' [ γ⊑γ' ]e)
      casesBind : ∀ Γ Γ' S S' C c M M' M⊑M' →
        Bc (S ∷ Γ) (S' ∷ Γ') S S' (c ∷ C) c M M' M⊑M' →
        Be Γ Γ' S S' S S' C c c (bind M) (bind M') (bind M⊑M')
 --     casesHetTransEval : Be E⊑E' -> Be E'⊑E'' -> Be E⊑E''

      -- Computations
      casesReflexiveComp :
        ∀ Γ S M → Bc Γ Γ S S (refl-⊑ctx Γ) (refl-⊑ S) M M reflexive-comp
      cases[]∙ : ∀ Γ Γ' S S' T T' C c d E E' M M' E⊑E' M⊑M' →
                 Be Γ Γ' S S' T T' C c d E E' E⊑E' →
                 Bc Γ Γ' S S' C c M M' M⊑M' →
                 Bc Γ Γ' T T' C d (E [ M ]∙) (E' [ M' ]∙) (E⊑E' [ M⊑M' ]∙)
      cases[]c : ∀ Δ Δ' Γ Γ' S S' C D c M M' γ γ' M⊑M' γ⊑γ' →
                 Bc Γ Γ' S S' C c M M' M⊑M' →
                 Bs Δ Δ' Γ Γ' D C γ γ' γ⊑γ' →
                 Bc Δ Δ' S S' D c (M [ γ ]c) (M' [ γ' ]c) (M⊑M' [ γ⊑γ' ]c)
      casesErr : ∀ S S' c → Bc [] [] S S' [] c err err err
      casesRet : ∀ S S' c → Bc (S ∷ []) [ S' ] S S' (c ∷ []) c ret ret ret
      casesApp : ∀ S S' T T' c d →
        Bc (S ∷ (S ⇀ T) ∷ []) (S' ∷ (S' ⇀ T') ∷ []) T T' (c ∷ ((c ⇀ d) ∷ [])) d app app app
      casesMatchNat : ∀ Γ Γ' S S' C c Kz Kz' Kz⊑Kz' Ks Ks' Ks⊑Ks' →
        Bc Γ Γ' S S' C c Kz Kz' Kz⊑Kz' →
        Bc (nat ∷ Γ) (nat ∷ Γ') S S' (nat ∷ C) c Ks Ks' Ks⊑Ks' →
        Bc (nat ∷ Γ) (nat ∷ Γ') S S' (nat ∷ C) c
          (matchNat Kz Ks) (matchNat Kz' Ks') (matchNat Kz⊑Kz' Ks⊑Ks')
      casesErr⊥ : ∀ Γ S M → Bc Γ Γ S S (refl-⊑ctx Γ) (refl-⊑ S) err' M err⊥
    {-  casesHetTransComp : Bc M⊑M' -> Bc M'⊑M'' -> Bc M⊑M'' -}



  module _ (cases : Cases) where
    open Cases cases

    {-# NON_COVERING #-}
    casesBs :
      ∀ (Δ Δ' Γ Γ' : Ctx) (C : Δ ⊑ctx Δ') (D : Γ ⊑ctx Γ')
        (γ : Subst Δ Γ) (γ' : Subst Δ' Γ') → (γ⊑γ' : Subst⊑ C D γ γ') →
        Bs Δ Δ' Γ Γ' C D γ γ' γ⊑γ'
    {-# NON_COVERING #-}
    casesBv :
      ∀ (Γ Γ' : Ctx) (S S' : Ty) (C : Γ ⊑ctx Γ') (c : S ⊑ S')
        (V : Val Γ S) (V' : Val Γ' S') → (V⊑V' : Val⊑ C c V V') →
        Bv Γ Γ' S S' C c V V' V⊑V'
    {-# NON_COVERING #-}
    casesBc :
      ∀ (Γ Γ' : Ctx) (S S' : Ty) (C : Γ ⊑ctx Γ') (c : S ⊑ S')
        (M : Comp Γ S) (M' : Comp Γ' S') (M⊑M' : Comp⊑ C c M M') →
        Bc Γ Γ' S S' C c M M' M⊑M'
    {-# NON_COVERING #-}
    casesBe :
      ∀ (Γ Γ' : Ctx) (S S' T T' : Ty) (C : Γ ⊑ctx Γ') (c : S ⊑ S') (d : T ⊑ T')
        (E : EvCtx Γ S T) (E' : EvCtx Γ' S' T') (E⊑E' : EvCtx⊑ C c d E E') →
        Be Γ Γ' S S' T T' C c d E E' E⊑E'

    
    casesBs Δ .Δ Γ .Γ .(refl-⊑ctx Δ) .(refl-⊑ctx Γ) γ .γ reflexive-subst = casesReflexiveSubst Δ Γ γ 
    casesBs Δ Δ' .[] .[] C .[] .!s .!s !s = cases!s Δ Δ' C 
    casesBs Δ Δ' .(_ ∷ _) .(_ ∷ _) C .(_ ∷ _) .(_ ,s _) .(_ ,s _) (γ⊑γ' ,s V⊑V') =
      cases,s Δ Δ' _ _ C _ _ _ _ _ _ _ _ γ⊑γ' V⊑V' (casesBs Δ Δ' _ _ C _ _ _ γ⊑γ') (casesBv Δ Δ' _ _ C _ _ _ V⊑V')
    casesBs Δ Δ' Γ Γ' C D .(_ ∘s _) .(_ ∘s _) (γ⊑γ' ∘s δ⊑δ') =
      cases∘s Δ Δ' _ _ Γ Γ' C _ D _ _ _ _ γ⊑γ' δ⊑δ' (casesBs _ _ Γ Γ' _ D _ _ γ⊑γ') (casesBs Δ Δ' _ _ C _ _ _ δ⊑δ')
    casesBs Δ Δ' .Δ .Δ' C .C .ids .ids _ids_ = casesIds Δ Δ' C
    casesBs .(_ ∷ Γ) .(_ ∷ Γ') Γ Γ' .(_ ∷ D) D .wk .wk wk = casesWk Γ Γ' _ _ D _ 
   -- casesBs Δ Δ' Γ Γ' C D γ γ' (isProp⊑ γ⊑γ' γ⊑γ'' i) = {!!}
   {- casesBs Δ Δ'' Γ Γ'' C D γ γ'' (hetTrans γ⊑γ' γ⊑γ'') =
      casesHetTransSubst Δ _ Δ'' Γ _ Γ'' {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
        (casesBs Δ _ Γ _ _ _ γ _ γ⊑γ')
        (casesBs {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} γ⊑γ'') -}
   

    casesBv Γ .Γ S .S .(refl-⊑ctx Γ) .(refl-⊑ S) V .V reflexive-val =
      casesReflexiveVal Γ S V
    casesBv Γ Γ' S S' C c .(V [ γ ]v) .(V' [ γ' ]v) (_[_]v {c = c} {V = V} {V' = V'} {B = B} {γ = γ} {γ' = γ'} V⊑V' γ⊑γ') =
      cases[]v Γ Γ' _ _ S S' C _ c γ γ' V V' V⊑V' γ⊑γ'
        (casesBv _ _ S S' _ c V V' V⊑V')
        (casesBs Γ Γ' _ _ B _ γ γ' γ⊑γ')
    casesBv .(S ∷ _) .(S' ∷ _) S S' .(c ∷ _) c .var .var var =
      casesVar _ _ S S' _ c
    casesBv .[] .[] .nat .nat .[] .nat .zro .zro zro = casesZro
    casesBv .(nat ∷ []) .(nat ∷ []) .nat .nat .(nat ∷ []) .nat .suc .suc suc = casesSuc
    casesBv Γ Γ' .(_ ⇀ _) .(_ ⇀ _) C .(_ ⇀ _) .(lda M) .(lda M') (lda {M = M} {M' = M'} M⊑M') =
      casesLda Γ Γ' _ _ _ _ C _ _ M M' M⊑M'
        (casesBc (_ ∷ Γ) (_ ∷ Γ') _ _ (_ ∷ C) _ M M' M⊑M')
    casesBv .[] .[] .dyn .dyn .[] .dyn .(injectN [ !s ,s V ]v) V' (injNatUpL {V = V} V⊑V') =
      casesInjNatUpL V V' V⊑V' (casesBv [] [] nat dyn [] inj-nat V V' V⊑V')
    casesBv .(nat ∷ []) .(dyn ∷ []) .dyn .dyn .(inj-nat ∷ []) .dyn .injectN .var injNatUpL' = casesInjNatUpL'
    casesBv .[] .[] .nat .dyn .[] .inj-nat V .(injectN [ !s ,s V' ]v) (injNatUpR {V' = V'} V⊑V') =
      casesInjNatUpR V V' V⊑V' (casesBv [] [] nat nat [] nat V V' V⊑V')
    casesBv .(nat ∷ []) .(nat ∷ []) .nat .dyn .(nat ∷ []) .inj-nat .var .injectN injNatUpR' = casesInjNatUpR'
    casesBv .[] .[] .dyn .dyn .[] .dyn .(injectArr ∘V' (emb c ∘V V)) V' (injArrUpL {c = c} {V = V} V⊑V') =
      casesInjArrUpL _ V V' c V⊑V' (casesBv [] [] _ dyn [] (inj-arr c) V V' V⊑V')
    casesBv .[] .[] .(dyn ⇀ dyn) .dyn .[] .(inj-arr (refl-⊑ (dyn ⇀ dyn))) V .(injectArr [ !s ,s V' ]v) (injArrUpR {V' = V'} V⊑V') =
      casesInjArrUpR V V' V⊑V' (casesBv [] [] (dyn ⇀ dyn) (dyn ⇀ dyn) [] (dyn ⇀ dyn) V V' V⊑V')
    casesBv .(S ∷ []) .(dyn ∷ []) S .dyn .(inj-arr _ ∷ []) .(inj-arr _) Vs .(mapDyn Vn Vf) (mapDyn-arr {Vn = Vn} {Vs = Vs} {Vf = Vf} Vs⊑Vf) =
      casesMapDyn-arr S _ Vn Vs Vf Vs⊑Vf
        (casesBv (S ∷ []) ((dyn ⇀ dyn) ∷ []) S (dyn ⇀ dyn) (_ ∷ []) _ Vs Vf Vs⊑Vf)
    -- casesBv Γ Γ' S S' C c V V' (isProp⊑ V⊑V' V⊑V'' i) = ?
    -- casesBv Γ Γ' S S' C c V V' (hetTrans V⊑V' V⊑V'') = {!!}

    -- rename x
    casesBc Γ .Γ S .S .(refl-⊑ctx Γ) .(refl-⊑ S) M .M reflexive-comp = casesReflexiveComp Γ S M
    casesBc Γ Γ' S S' C c .(_ [ _ ]∙) .(_ [ _ ]∙) (E⊑E' [ M⊑M' ]∙) =
      cases[]∙ Γ Γ' _ _ S S' C _ c _ _ _ _ E⊑E' M⊑M' (casesBe Γ Γ' _ _ S S' C _ c _ _ E⊑E') (casesBc Γ Γ' _ _ C _ _ _ M⊑M')
    casesBc Γ Γ' S S' C c .(_ [ _ ]c) .(_ [ _ ]c) (M⊑M' [ γ⊑γ' ]c) = cases[]c Γ Γ' _ _ S S' _ C c _ _ _  _ M⊑M' γ⊑γ' (casesBc _ _ S S' _ c _ _ M⊑M') (casesBs Γ Γ' _ _ C _ _ _ γ⊑γ')
    casesBc .[] .[] S S' .[] c .err .err err = casesErr S S' c
    casesBc .(S ∷ []) .(S' ∷ []) S S' .(c ∷ []) c .ret .ret ret = casesRet S S' c
    casesBc .(_ ∷ (_ ⇀ S) ∷ []) .(_ ∷ (_ ⇀ S') ∷ []) S S' .(_ ∷ ((_ ⇀ c) ∷ [])) c .app .app app = casesApp _ _ S S' _ c
    casesBc .(nat ∷ _) .(nat ∷ _) S S' .(nat ∷ _) c .(matchNat _ _) .(matchNat _ _) (matchNat M⊑M' M⊑M'') =
      casesMatchNat _ _ S S' _ c _ _ M⊑M' _ _ M⊑M'' (casesBc _ _ S S' _ c _ _ M⊑M') (casesBc (nat ∷ _) (nat ∷ _) S S' (nat ∷ _) c _ _ M⊑M'')
    casesBc Γ .Γ S .S .(refl-⊑ctx Γ) .(refl-⊑ S) .err' M' err⊥ = casesErr⊥ Γ S M'
 --   casesBc Γ Γ' S S' .(trans-⊑ctx _ _) .(trans-⊑ _ _) M M' (hetTrans M⊑M' M⊑M'') = ?
 --   casesBc Γ Γ' S S' C c M M' (isProp⊑ M⊑M' M⊑M'' i) = ? 

  {-  casesBe Γ .Γ S .S .S .S .(refl-⊑ctx Γ) .(refl-⊑ S) .(refl-⊑ S) E .E reflexive-eval = ?
    casesBe Γ Γ' S S' .S .S' C c .c .∙E .∙E ∙E = ?
    casesBe Γ Γ' S S' T T' C c d .(_ ∘E _) .(_ ∘E _) (E⊑E' ∘E E⊑E'') = ?
    casesBe Γ Γ' S S' T T' C c d .(_ [ _ ]e) .(_ [ _ ]e) (E⊑E' [ x ]e) = ?
    casesBe Γ Γ' S S' T T' C c d .(bind _) .(bind _) (bind x) = ? -}
  --  casesBe Γ Γ' S S' T T' .(trans-⊑ctx _ _) .(trans-⊑ _ _) .(trans-⊑ _ _) E E' (hetTrans E⊑E' E⊑E'') = ?
  --  casesBe Γ Γ' S S' T T' C c d E E' (isProp⊑ E⊑E' E⊑E'' i) = ?


    {-  cases∘s  : Bs γ⊑γ' → Bs δ⊑δ' → Bs (γ⊑γ' ∘s δ⊑δ')
      casesWk  : Bs {Γ = Δ} {Γ' = Δ} {D = C} (wk {c = c} {C = C}) -- how to set c.S and c.S'
      casesHetTransSubst : Bs γ⊑γ' -> Bs γ'⊑γ'' -> Bs γ⊑γ''

      -- Values
      casesReflexiveVal : Bv {V' = V} reflexive-val
      cases[]v : Bv V⊑V' -> Bs γ⊑γ' -> Bv (V⊑V' [ γ⊑γ' ]v)
      casesVar : Bv {Γ = S ∷ Γ} {Γ' = S' ∷ Γ'} {c = c} (var {C = D})
      casesZro   : Bv zro
      casesSuc   : Bv suc
      casesLda   : Bc {C = c ∷ C} M⊑M' → Bv (lda M⊑M')
      casesInjNatUpR : Bv {C = []} {c = nat} V⊑V' -> Bv (injNatUpR V⊑V') 
      casesInjArrUpL : Bv {C = []} {c = (dyn ⇀ dyn)} V⊑V' -> Bv (injNatUpL {!V⊑V'!}) 
      casesMapDyn-nat : Bv {C = (nat ∷ [])} {c = nat} V⊑V' ->
                        Bv (mapDyn-nat {Vf = V} V⊑V')
      casesMapDyn-arr : Bv {C = c ∷ []} {c = c} V⊑V' ->
                        Bv (mapDyn-arr {Vn = V} V⊑V')
      casesHetTransVal : Bv V⊑V' -> Bv V'⊑V'' -> Bv V⊑V''

      -- Evaluation Contexts
      casesReflexiveEval : Be {E' = E} reflexive-eval
      cases∙E : Be {C = C} {d = c} ∙E
      cases∘E   :  Be E⊑E' → Be F⊑F' → Be (E⊑E' ∘E F⊑F')
      cases[]e  :  Be E⊑E' → Bs γ⊑γ' → Be (E⊑E' [ γ⊑γ' ]e)
      casesBind :  Bc M⊑M'  →  Be (bind M⊑M')
      casesHetTransEval : Be E⊑E' -> Be E'⊑E'' -> Be E⊑E''

      -- Computations
      casesReflexiveComp : Bc {M' = M} reflexive-comp
      cases[]∙ : Be E⊑E' → Bc M⊑M' → Bc (E⊑E' [ M⊑M' ]∙)
      cases[]c : Bc M⊑M' → Bs γ⊑γ' → Bc (M⊑M' [ γ⊑γ' ]c)
      casesErr : Bc {c = c} err
      casesRet : Bc {c = c} ret
      casesApp : Bc {C = (c ∷ c ⇀ d ∷ [])} {c = d} app
      casesMatchNat : Bc M⊑M' → Bc N⊑N' → Bc (matchNat M⊑M' N⊑N')
      casesErr⊥ : Bc {M' = M} err⊥
      casesHetTransComp : Bc M⊑M' -> Bc M'⊑M'' -> Bc M⊑M'' -}

{-

  module _ (cases : Cases) where
    open Cases cases

    casesBs : ∀ (γ⊑γ' : Subst⊑ C D γ γ') → Bs γ⊑γ'
    casesBv : ∀ (V⊑V' : Val⊑ C c V V') → Bv V⊑V'
    casesBc : ∀ (M⊑M' : Comp⊑ C c M M') → Bc M⊑M'
    casesBe : ∀ (E⊑E' : EvCtx⊑ C c d E E') → Be E⊑E'

    
    casesBs reflexive-subst = casesReflexiveSubst
    casesBs !s = cases!s
    casesBs (γ⊑γ' ,s V⊑V') = cases,s (casesBs γ⊑γ') (casesBv V⊑V')
    casesBs (γ⊑γ' ∘s δ⊑δ') = cases∘s (casesBs γ⊑γ') (casesBs δ⊑δ')
    casesBs wk = ?
    casesBs _ = ?

    casesBv reflexive-val = casesReflexiveVal
    casesBv (V⊑V' [ γ⊑γ' ]v) = cases[]v (casesBv V⊑V') (casesBs γ⊑γ')
    casesBv var = casesVar
    casesBv zro = casesZro
    casesBv suc = casesSuc
    casesBv (lda M⊑M') = casesLda (casesBc M⊑M')
    casesBv (injNatUp V⊑V') = casesInjNatUp (casesBv V⊑V')
    casesBv (injArrUp V⊑V') = casesInjArrUp (casesBv V⊑V')
    casesBv (mapDyn-nat V⊑V') = casesMapDyn-nat (casesBv V⊑V')
    casesBv (mapDyn-arr V⊑V') = casesMapDyn-arr (casesBv V⊑V')
    casesBv _ = ?

    casesBc reflexive-comp = casesReflexiveComp
    casesBc (E⊑E' [ M⊑M' ]∙) = cases[]∙ (casesBe E⊑E') (casesBc M⊑M')
    casesBc (M⊑M' [ γ⊑γ' ]c) = cases[]c (casesBc M⊑M') (casesBs γ⊑γ')
    casesBc err = casesErr
    casesBc ret = casesRet
    casesBc app = casesApp
    casesBc (matchNat M⊑M' N⊑N') = casesMatchNat (casesBc M⊑M') (casesBc N⊑N')
    casesBc err⊥ = casesErr⊥
    casesBc _ = ?

    casesBe reflexive-eval = casesReflexiveEval
    casesBe ∙E = cases∙E
    casesBe (E⊑E' ∘E F⊑F') = cases∘E (casesBe E⊑E') (casesBe F⊑F')
    casesBe (E⊑E' [ γ⊑γ' ]e) = cases[]e (casesBe E⊑E') (casesBs γ⊑γ')
    casesBe (bind M⊑M') = casesBind (casesBc M⊑M')
    casesBe _ = ?
   
    

-}
