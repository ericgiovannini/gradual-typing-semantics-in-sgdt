{-# OPTIONS --cubical #-}

{-# OPTIONS --allow-unsolved-metas #-}

module Syntax.IntensionalTerms  where

-- The intensional syntax, which is quotiented by βη equivalence and
-- order equivalence but where casts take observable steps.

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Cubical.Data.Prod hiding (map)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.Empty renaming (rec to exFalso)

open import Syntax.Types
open import Syntax.Perturbation

open TyPrec
open CtxPrec

-- Lemma for naturality of substitution
-- (M, N)(γ) = (M[γ] , N[γ])

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T U R' S' T' U' : Ty
   B B' C C' D D' : Γ ⊑ctx Γ'
   b b' c c' d d' : S ⊑ S'

-- Substitutions, Values, Computations and Evaluation contexts,
-- *not* quotiented by intensional order equivalence.
data Subst : (Δ : Ctx) (Γ : Ctx) → Type

data Val : (Γ : Ctx) (S : Ty) → Type

data EvCtx : (Γ : Ctx) (S : Ty) (T : Ty) → Type

data Comp : (Γ : Ctx) (S : Ty) → Type




private
  variable
    γ γ' γ'' : Subst Δ Γ
    δ δ' δ'' : Subst Θ Δ
    θ θ' θ'' : Subst Z Θ

    V V' V'' : Val Γ S
    M M' M'' N N' : Comp Γ S
    E E' E'' F F' : EvCtx Γ S T

-- This isn't actually induction-recursion, this is just a hack to get
-- around limitations of Agda's mutual recursion for HITs
-- https://github.com/agda/agda/issues/5362
_[_]vP : Val Γ S → Subst Δ Γ → Val Δ S
_[_]cP : Comp Γ S → Subst Δ Γ → Comp Δ S
_[_]∙P : EvCtx Γ S T → Comp Γ S → Comp Γ T
varP : Val (S ∷ Γ) S
retP : Comp [ S ] S
appP : Comp (S ∷ (S ⇀ T) ∷ []) T

data Subst where
  -- Subst is a cat
  ids : Subst Γ Γ
  _∘s_ : Subst Δ Θ → Subst Γ Δ → Subst Γ Θ
  ∘IdL : ids ∘s γ ≡ γ
  ∘IdR : γ ∘s ids ≡ γ
  ∘Assoc : γ ∘s (δ ∘s θ) ≡ (γ ∘s δ) ∘s θ
  isSetSubst : isSet (Subst Δ Γ)
  -- isPosetSubst : Subst⊑ (refl-⊑ctx Δ) (refl-⊑ctx Γ) γ γ'
  --              → Subst⊑ (refl-⊑ctx Δ) (refl-⊑ctx Γ) γ' γ
  --              → γ ≡ γ'

  -- [] is terminal
  !s : Subst Γ []
  []η : γ ≡ !s

  -- universal property of S ∷ Γ
  -- β (other one is in Val), η and naturality
  _,s_ : Subst Γ Δ → Val Γ S → Subst Γ (S ∷ Δ)
  wk : Subst (S ∷ Γ) Γ
  wkβ : wk ∘s (δ ,s V) ≡ δ
  ,sη : δ ≡ (wk ∘s δ ,s varP [ δ ]vP)

-- copied from similar operators
infixl 4 _,s_
infixr 9 _∘s_


data Val where
  -- values form a presheaf over substitutions
  _[_]v : Val Γ S → Subst Δ Γ → Val Δ S
  substId : V [ ids ]v ≡ V
  substAssoc : V [ δ ∘s γ ]v ≡ (V [ δ ]v) [ γ ]v

  -- with explicit substitutions we only need the one variable, which we can combine with weakening
  var : Val (S ∷ Γ) S
  varβ : var [ δ ,s V ]v ≡ V

  -- by making these function symbols we avoid more substitution equations
  zro : Val [] nat
  suc : Val [ nat ] nat

  lda : Comp (S ∷ Γ) T -> Val Γ (S ⇀ T) -- TODO: prove substitution under lambdas is admissible
  -- V = λ x. V x
  fun-η : V ≡ lda (appP [ (!s ,s (V [ wk ]v)) ,s var ]cP)

  -- Do these make sense?
  injectN   : Val [ nat ] dyn
  injectArr : Val [ S ] (dyn ⇀ dyn) -> Val [ S ] dyn
  mapDyn : Val [ nat ] nat → Val [ dyn ⇀ dyn ] (dyn ⇀ dyn) → Val [ dyn ] dyn
  --mapDynβn : ?
  --mapDynβf : ?

  -- These are now admissible
  {-
  up : (S⊑T : TyPrec) -> Val [ ty-left S⊑T ] (ty-right S⊑T)
  δl  : (S⊑T : TyPrec) → Val [ ty-left S⊑T ] (ty-left S⊑T)
  δr  : (S⊑T : TyPrec) → Val [ ty-right S⊑T ] (ty-right S⊑T)
  -}

  isSetVal : isSet (Val Γ S)
  -- isPosetVal : Val⊑ (refl-⊑ctx Γ) (refl-⊑ S) V V'
  --            → Val⊑ (refl-⊑ctx Γ) (refl-⊑ S) V' V
  --            → V ≡ V'

_[_]vP = _[_]v
varP = var



data EvCtx where
  ∙E : EvCtx Γ S S
  _∘E_ : EvCtx Γ T U → EvCtx Γ S T → EvCtx Γ S U
  ∘IdL : ∙E ∘E E ≡ E
  ∘IdR : E ∘E ∙E ≡ E
  ∘Assoc : E ∘E (F ∘E F') ≡ (E ∘E F) ∘E F'

  _[_]e : EvCtx Γ S T → Subst Δ Γ → EvCtx Δ S T
  substId : E [ ids ]e ≡ E
  substAssoc : E [ γ ∘s δ ]e ≡ E [ γ ]e [ δ ]e

  ∙substDist : ∙E {S = S} [ γ ]e ≡ ∙E
  ∘substDist : (E ∘E F) [ γ ]e ≡ (E [ γ ]e) ∘E (F [ γ ]e)

  bind : Comp (S ∷ Γ) T → EvCtx Γ S T
  -- E[∙] ≡ x <- ∙; E[ret x]
  ret-η : E ≡ bind (E [ wk ]e [ retP [ !s ,s var ]cP ]∙P)

  -- These are now admissible
  {-
  dn : (S⊑T : TyPrec) → EvCtx [] (ty-right S⊑T) (ty-left S⊑T)
  δl  : (S⊑T : TyPrec) → EvCtx [] (ty-left S⊑T) (ty-left S⊑T)
  δr  : (S⊑T : TyPrec) → EvCtx [] (ty-right S⊑T) (ty-right S⊑T)
  -}

  isSetEvCtx : isSet (EvCtx Γ S T)
  -- isPosetEvCtx : EvCtx⊑ (refl-⊑ctx Γ) (refl-⊑ S) (refl-⊑ T) E E'
  --              → EvCtx⊑ (refl-⊑ctx Γ) (refl-⊑ S) (refl-⊑ T) E' E
  --              → E ≡ E'

data Comp where
  _[_]∙ : EvCtx Γ S T → Comp Γ S → Comp Γ T
  plugId : ∙E [ M ]∙ ≡ M
  plugAssoc : (F ∘E E) [ M ]∙ ≡ F [ E [ M ]∙ ]∙

  _[_]c : Comp Δ S → Subst Γ Δ → Comp Γ S
  -- presheaf
  substId : M [ ids ]c ≡ M
  substAssoc : M [ δ ∘s γ ]c ≡ (M [ δ ]c) [ γ ]c

  -- Interchange law
  substPlugDist : (E [ M ]∙) [ γ ]c ≡ (E [ γ ]e) [ M [ γ ]c ]∙

  err : Comp [] S
  -- E[err] ≡ err
  strictness : E [ err [ !s ]c ]∙ ≡ err [ !s ]c

  ret : Comp [ S ] S
  -- x <- ret x; M ≡ M
  ret-β : (bind M [ wk ]e [ ret [ !s ,s var ]c ]∙) ≡ M

  app : Comp (S ∷ S ⇀ T ∷ []) T
  -- (λ x. M) x ≡ M
  fun-β : app [ (!s ,s ((lda M) [ wk ]v)) ,s var ]c ≡ M

  matchNat : Comp Γ S → Comp (nat ∷ Γ) S → Comp (nat ∷ Γ) S
  -- match 0 Kz (x . Ks) ≡ Kz
  matchNatβz : (Kz : Comp Γ S)(Ks : Comp (nat ∷ Γ) S)
             → matchNat Kz Ks [ ids ,s (zro [ !s ]v) ]c ≡ Kz
  -- match (S V) Kz (x . Ks) ≡ Ks [ V / x ]
  matchNatβs : (Kz : Comp Γ S)(Ks : Comp (nat ∷ Γ) S) (V : Val Γ nat)
             → matchNat Kz Ks [ ids ,s (suc [ !s ,s V ]v) ]c ≡ (Ks [ ids ,s V ]c)
  -- M[x] ≡ match x (M[0/x]) (x. M[S x/x])
  matchNatη : M ≡ matchNat
       (M [ ids ,s (zro [ !s ]v) ]c)
       (M [ wk ,s (suc [ !s ,s var ]v) ]c)

 
  matchDyn : Comp (nat ∷ Γ) S → Comp ((dyn ⇀ dyn) ∷ Γ) S → Comp (dyn ∷ Γ) S
  
  matchDynβn : (Kn : Comp (nat ∷ Γ) S) (Kf : Comp ((dyn ⇀ dyn) ∷ Γ) S)
               (V : Val Γ nat) ->
    matchDyn Kn Kf [ ids ,s (injectN [ !s ,s V ]v) ]c ≡
    Kn [ ids ,s V ]c
    
  matchDynβf : (Kn : Comp (nat ∷ Γ) S) (Kf : Comp ((dyn ⇀ dyn) ∷ Γ) S)
               (V : Val Γ (dyn ⇀ dyn)) ->
    matchDyn Kn Kf [ ids ,s ((injectArr var) [ !s ,s V ]v) ]c ≡
    Kf [ ids ,s V ]c

{-
  matchDynβf' : (Kn : Comp (nat ∷ Γ) S) (Kf : Comp ((dyn ⇀ dyn) ∷ Γ) S)
                (V : Val Γ T) (V-up : Val [ T ] (dyn ⇀ dyn)) ->
    matchDyn Kn Kf [ ids ,s ((injectArr V-up) [ !s ,s V ]v) ]c ≡
    Kf [ ids ,s (V-up [ !s ,s V ]v) ]c
-}

  tick : Comp Γ S -> Comp Γ S
  
  -- tick commutes with ev ctxs
  tick-strictness : ∀ {M} -> E [ tick M ]∙ ≡ tick (E [ M ]∙)

  isSetComp : isSet (Comp Γ S)
  -- isPosetComp : Comp⊑ (refl-⊑ctx Γ) (refl-⊑ S) M M'
  --             → Comp⊑ (refl-⊑ctx Γ) (refl-⊑ S) M' M
  --             → M ≡ M'

appP = app
retP = ret
_[_]cP = _[_]c
_[_]∙P = _[_]∙


-- Convenience definitions

_∘V_ : Val (S ∷ Γ) T -> Val Γ S -> Val Γ T
V ∘V W  =  V [ ids ,s W ]v

_∘V'_ : Val [ S ] T -> Val Γ S -> Val Γ T
V ∘V' W = (V [ !s ,s var ]v) ∘V W

compCompose : Comp (S ∷ Γ) T -> Comp Γ S -> Comp Γ T
compCompose N M = (bind N) [ M ]∙

vToE : Val [ S ] T → EvCtx [] S T
vToE V = bind (ret [ !s ,s V ]c)



-- Sequencing computations via bind and [ _ ]∙
bind' : Comp Γ S -> Comp (S ∷ Γ) T -> Comp Γ T
bind' M N = (bind N) [ M ]∙


-- Shorthand for seq
_>>_ : Comp Γ S -> Comp (S ∷ Γ) T -> Comp Γ T
_>>_ = bind'

ret' : Val Γ S → Comp Γ S
ret' V = ret [ !s ,s V ]c

-- Sequencing with a value
seqVal : Comp Γ S -> Val (S ∷ Γ) T -> Comp Γ T
seqVal M V = bind' M (ret' V)

eToC : EvCtx [] S T → Comp [ S ] T
eToC E = (E [ wk ]e) [ ret' var ]∙


zro' : Val Γ nat
zro' = zro [ !s ]v

suc' : Val Γ nat -> Val Γ nat
suc' V = suc [ !s ,s V ]v

err' : Comp Γ S
err' = err [ !s ]c

app' : Comp (S ∷ S ⇀ T ∷ Γ) T
app' = app [ (!s ,s (var [ wk ]v)) ,s var ]c

app'' : Comp Γ (S ⇀ T) -> Comp Γ S -> Comp Γ T
app'' M N = M >> ((N [ wk ]c) >> app')

appVal : (Vf : Val Γ (S ⇀ T)) (Va : Val Γ S) → Comp Γ T
appVal Vf Va = app [ !s ,s Vf ,s Va ]c

π2 : Val (S ∷ T ∷ Γ) T
π2 = var [ wk ]v

reverseArg : Subst (S ∷ T ∷ Γ) (T ∷ S ∷ Γ)
reverseArg = (wk ∘s wk ,s var) ,s (var [ wk ]v)

drop2nd : Subst (S ∷ T ∷ U ∷ Γ) (S ∷ U ∷ Γ)
drop2nd = ((wk ∘s wk ∘s wk) ,s (var [ wk ∘s wk ]v)) ,s  var 

{-
upE : ∀ S⊑T → EvCtx [] (ty-left S⊑T) (ty-right S⊑T)
upE S⊑T = vToE (up S⊑T)
-}


-- Substitution principles

var-subst :  ∀ {S : Ty} {Γ Δ : Ctx}
   {γ : Subst (S ∷ Γ) Δ} {γ' : Subst Δ Γ}
   {V : Val (S ∷ Γ) S}   {V' : Val Δ S} ->
  (var [ (γ ,s V) ∘s (γ' ,s V') ]v) ≡ (V [ γ' ,s V' ]v)
var-subst = substAssoc ∙ {!!} ∙ {!!}

-- Useful substitution principle
-- ,sη : δ ≡ (wk ∘s δ ,s varP [ δ ]vP)
-- wkβ : wk ∘s (δ ,s V) ≡ δ
subst-naturality : ∀ {S : Ty} {Γ Δ : Ctx} {γ : Subst (S ∷ Γ) Δ} {γ' : Subst Δ Γ} {V : Val (S ∷ Γ) S} {V' : Val Δ S} ->
  (γ ,s V) ∘s (γ' ,s V') ≡
  ((γ ∘s (γ' ,s V')) ,s (V [ γ' ,s V' ]v))
  -- (γ ∘s (γ' ,s V') ,s (var [ γ' ,s V' ]v))
subst-naturality {S} {Γ} {Δ} {γ} {γ'} {V} {V'} =
  ,sη ∙
  (λ i -> ∘Assoc {γ = wk} {δ = γ ,s V} {θ = γ' ,s V'} i ,s (var [ (γ ,s V) ∘s (γ' ,s V') ]v)) ∙
  (λ i -> (wkβ {δ = γ} {V = V} i ∘s (γ' ,s V')) ,s (var [ (γ ,s V) ∘s (γ' ,s V') ]v)) ∙
  λ i -> γ ∘s (γ' ,s V') ,s var-subst {γ = γ} {γ' = γ'} {V = V} {V' = V'} i

 -- (wk ∘s (γ ,s V) ∘s (γ' ,s V') ,s
 -- (varP [ (γ ,s V) ∘s (γ' ,s V') ]vP))
 --      ≡ (γ ∘s (γ' ,s V') ,s (V [ γ' ,s V' ]v))

!s-nat : (γ : Subst Γ []) → !s ∘s γ ≡ !s
!s-nat γ = []η

!s-ext : {γ : Subst Γ []} → γ ≡ δ
!s-ext = []η ∙ sym []η

,s-nat : (γ ,s V) ∘s δ ≡ ((γ ∘s δ) ,s (V [ δ ]v))
,s-nat =
  ,sη ∙ cong₂ _,s_ (∘Assoc ∙ cong₂ (_∘s_) wkβ refl)
               (substAssoc ∙ cong₂ _[_]v varβ refl)

,s-ext : wk ∘s γ ≡ wk ∘s δ → (var [ γ ]v ≡ var [ δ ]v) → γ ≡ δ
,s-ext wkp varp = ,sη ∙ cong₂ _,s_ wkp varp ∙ sym ,sη


app'-nat : (γ : Subst Δ Γ) (Vf : Val Γ (S ⇀ T)) (Va : Val Γ S)
         → appVal Vf Va [ γ ]c ≡ appVal (Vf [ γ ]v) (Va [ γ ]v)
app'-nat γ Vf Va =
  sym substAssoc
  ∙ cong (app [_]c) (,s-nat ∙ cong₂ _,s_ (,s-nat  ∙ cong₂ _,s_ []η refl) refl)

lda-nat : (γ : Subst Δ Γ) (M : Comp (S ∷ Γ) T)
        → (lda M) [ γ ]v ≡ lda (M [ γ ∘s wk ,s var ]c)
lda-nat {Δ = Δ}{Γ = Γ}{S = S} γ M =
  fun-η
  ∙ cong lda (cong (app [_]c) (cong₂ _,s_ (cong₂ _,s_ (sym ([]η)) (sym substAssoc
                                                                 ∙ cong (lda M [_]v) (sym wkβ)
                                                                 ∙ substAssoc))
                                                      (sym varβ)
                              ∙ cong (_,s (var [ the-subst ]v)) (sym ,s-nat)
                              ∙ sym ,s-nat)
             ∙ substAssoc
             ∙ cong (_[ the-subst ]c) fun-β) where
  the-subst : Subst (S ∷ Δ) (S ∷ Γ)
  the-subst = γ ∘s wk ,s var

fun-β' : (M : Comp (S ∷ Γ) T) (V : Val Γ S)
       → appVal (lda M) V ≡ M [ ids ,s V ]c
fun-β' M V =
  cong (app [_]c) (cong₂ _,s_ (cong₂ _,s_ (sym []η) ((sym substId ∙ cong (lda M [_]v) (sym wkβ)) ∙ substAssoc) ∙ sym ,s-nat)
                              (sym varβ)
                  ∙ sym ,s-nat)
  ∙ substAssoc
  ∙ cong (_[ ids ,s V ]c) fun-β

fun-η' : V ≡ lda (appVal (V [ wk ]v) var)
fun-η' = fun-η


bind-nat : (bind M) [ γ ]e ≡ bind (M [ γ ∘s wk ,s var ]c)
bind-nat {M = M} {γ = γ} = ret-η ∙ cong bind (cong (_[ ret [ !s ,s var ]c ]∙) (sym substAssoc)
                             ∙ cong₂ _[_]∙ (cong (bind M [_]e) (sym wkβ) ∙ substAssoc)
                                           (cong (ret [_]c) (cong₂ _,s_ !s-ext (sym varβ) ∙ sym ,s-nat) ∙ substAssoc)
                             ∙ sym substPlugDist
                             ∙ cong (_[ γ ∘s wk ,s var ]c) ret-β)

bind'-nat : (bind' M N) [ γ ]c ≡ bind' (M [ γ ]c) (N [ γ ∘s wk ,s var ]c)
bind'-nat = substPlugDist ∙ cong₂ _[_]∙ bind-nat refl

ret-β' : bind' (ret' V) M ≡ (M [ ids ,s V ]c)
ret-β' =
  (cong₂ _[_]∙ ((sym substId ∙ cong₂ _[_]e refl (sym wkβ)) ∙ substAssoc)
               (cong (ret [_]c) (,s-ext !s-ext (varβ ∙ (sym varβ ∙ sym varβ) ∙ cong (var [_]v) (sym ,s-nat))) ∙ substAssoc)
  ∙ sym substPlugDist)
  ∙ cong₂ _[_]c ret-β refl

ret-η' : M ≡ bind' M (ret' var)
ret-η' = sym plugId ∙ cong₂ _[_]∙ (ret-η ∙ cong bind (cong₂ _[_]∙ ∙substDist refl ∙ plugId)) refl

ret'-nat : (ret' V) [ γ ]c ≡ ret' (V [ γ ]v)
ret'-nat = (sym substAssoc) ∙
           (cong₂ _[_]c refl (,s-nat ∙ cong₂ _,s_ []η refl))

{-
∘V-lda : ∀ {M : Comp (S ∷ []) T} {N : Comp (T ∷ S ∷ []) U} ->
  lda (M >> N) ≡ ((lda (app >> (N [ !s ,s (var [ wk ]v) ,s var ]c)) [ !s ,s var ]v) ∘V lda M)



--  Comp (R' ∷ [ R ⇀ S ]) S'
∘V-lda' : ∀ {Q R S T U} {M : Comp {!!} {!!}} {N : Comp {!!} S} -> {!!}
  (((lda M) [ !s ,s var ]v) ∘V lda N) ≡ lda (N >> {!!})
-}




-- "Compiling" a perturbation to a term

Pertᴱ→Val : Pertᴱ S -> Val [ S ] S
Pertᴾ→EC : Pertᴾ S -> EvCtx [] S S


Pertᴱ→Val id = var
Pertᴱ→Val (δi ⇀ δo) =
  lda (((Pertᴾ→EC δi [ !s ]e) [ ret' var ]∙) >>
      ((app [ drop2nd ]c) >>
      ((vToE (Pertᴱ→Val δo) [ !s ]e) [ ret' var ]∙)))
Pertᴱ→Val (PertD δn δf) = mapDyn (Pertᴱ→Val δn) (Pertᴱ→Val δf) -- Need match on dyn to be a value...

Pertᴾ→EC (δPert δs) = bind (tick (ret' var)) ∘E Pertᴾ→EC δs
Pertᴾ→EC id = ∙E
Pertᴾ→EC (δi ⇀ δo) = bind (ret' (lda (
     ((vToE (Pertᴱ→Val δi) [ !s ]e) [ ret' var ]∙) >>
      ((app [ drop2nd ]c) >>
       ((Pertᴾ→EC δo [ !s ]e) [ ret' var ]∙)))))
Pertᴾ→EC (PertD δn δf) = bind (matchDyn
  (((Pertᴾ→EC δn [ !s ]e) [ ret' var ]∙) >> ret' (injectN [ wk ]v))
  (((Pertᴾ→EC δf [ !s ]e) [ ret' var ]∙) >> ret' (injectArr var [ wk ]v)))


-- The four cast rule delay terms are admissible in the syntax

δl-e : S ⊑ T -> Val [ S ] S
δl-e c = Pertᴱ→Val (δl-e-pert c)

δr-e : S ⊑ T -> Val [ T ] T
δr-e c = Pertᴱ→Val (δr-e-pert c)

δl-p : S ⊑ T -> EvCtx [] S S
δl-p c = Pertᴾ→EC (δl-p-pert c)

δr-p : S ⊑ T -> EvCtx [] T T
δr-p c = Pertᴾ→EC (δr-p-pert c)


-- Up and downcasts are admissible in the syntax

proj : S ⊑ T -> EvCtx [] T S
emb  : S ⊑ T -> Val [ S ] T

proj nat = ∙E
proj dyn = ∙E
proj (ci ⇀ co) =
  bind (ret' (lda ((ret' (emb ci) [ !s ,s var ]c) >>
       ((app [ drop2nd ]c) >>
       ((proj co [ !s ]e) [ ret' var ]∙)))))
proj inj-nat =
  bind (matchDyn (ret' var) (err [ wk ]c))
proj (inj-arr c) =
  bind (matchDyn (err [ wk ]c) ((proj c [ !s ]e) [ ret' var ]∙))

emb nat = var
emb dyn = var
emb (ci ⇀ co) =
  lda
  (((proj ci [ !s ]e) [ ret' var ]∙) >>
  ((app [ drop2nd ]c) >>
  ((vToE (emb co) [ !s ]e) [ ret' var ]∙)))
emb inj-nat = injectN
emb (inj-arr c) = injectArr (emb c)


-- We can show that emb (c ∘ d) ≡ emb d ∘ emb c
-- and similarly for proj


-- Useful lemma about composing with var
-- ,sη : δ ≡ (wk ∘s δ ,s varP [ δ ]vP)
-- wkβ : wk ∘s (δ ,s V) ≡ δ
∘V-IdR : (V : Val [ S ] T) ->
  ((V [ !s ,s var ]v) ∘V var) ≡ V
∘V-IdR V =
  (V [ !s ,s var ]v [ ids ,s var ]v)
    ≡⟨ {!!} ⟩
  (V [ wk ∘s wk ,s var ]v [ ids ,s var ]v)
    ≡⟨ {!!} ⟩
  (V [ wk ∘s wk ,s var ]v [ ids ,s var ]v)
    ≡⟨ {!!} ⟩
  V ∎
{-
  ≡⟨ sym substAssoc ⟩
  (V [ (!s ,s var) ∘s (ids ,s var) ]v)
    ≡⟨ {!!} ⟩
  (V [ ids ]v)
    ≡⟨ substId ⟩
  V ∎)
-}
  where

    lem2 : ∀ {S} -> (_,s_ {S = S} !s var) ≡ ids
    lem2 =
      !s ,s var
        ≡⟨ (λ i -> (sym ([]η {γ = wk}) i) ,s var) ⟩
      wk ,s var
        ≡⟨ (λ i -> (sym (∘IdR {γ = wk}) i) ,s (sym (substId {V = var}) i)) ⟩
      (wk ∘s ids) ,s (var [ ids ]v)
        ≡⟨ sym ,sη ⟩
      ids ∎

 
    -- ,sη : δ ≡ (wk ∘s δ ,s varP [ δ ]vP)
    -- wkβ : wk ∘s (δ ,s V) ≡ δ
    -- varβ : var [ δ ,s V ]v ≡ V
    subst-technical : ∀ {S} -> (_,s_ {S = S} !s var) ∘s ((ids ,s var)) ≡ ids
    subst-technical =
      let δ = (var [ (!s ,s var) ∘s (ids ,s var) ]v) in
      (!s ,s var) ∘s (ids ,s var)
       ≡⟨ ,sη ⟩      
      wk ∘s ((!s ,s var) ∘s (ids ,s var))   ,s  δ
       ≡⟨ (λ i -> ∘Assoc i  ,s  δ) ⟩
      (wk ∘s (!s ,s var)) ∘s (ids ,s var)   ,s  δ
       ≡⟨ (λ i -> wkβ i ∘s (ids ,s var) ,s δ) ⟩
      !s ∘s (ids ,s var)  ,s  δ
       ≡⟨ (λ i -> []η i   ,s  δ) ⟩
      !s   ,s   (var [ (!s ,s var) ∘s (ids ,s var) ]v)
       ≡⟨ (λ i -> !s ,s substAssoc i) ⟩
      !s   ,s   (var [ (!s ,s var) ]v [ (ids ,s var) ]v)
       ≡⟨ (λ i -> !s ,s (varβ i [ ids ,s var ]v)) ⟩
      !s ,s (var [ ids ,s var ]v)
       ≡⟨ (λ i -> !s ,s varβ i) ⟩
      !s ,s var
       ≡⟨ {!!} ⟩
      (wk ,s var)
       ≡⟨ (λ i -> sym ∘IdR i ,s sym substId i) ⟩
      (wk ∘s ids ,s var [ ids ]v)
       ≡⟨ sym ,sη ⟩
      ids ∎

{-
      wk ∘s ((!s ,s var) ∘s (ids ,s var)) ,s (var [ (!s ,s var) ]v [ (ids ,s var) ]v)
       ≡⟨ {!!} ⟩
      wk ∘s ((!s ,s var) ∘s (ids ,s var)) ,s (var [ (ids ,s var) ]v)
       ≡⟨ {!!} ⟩
      wk ∘s ((!s ,s var) ∘s (ids ,s var)) ,s var
       ≡⟨ {!!} ⟩
      !s ∘s (ids ,s var) ,s var
       ≡⟨ {!!} ⟩
      !s ,s var
       ≡⟨ {!!} ⟩
      (wk ,s var)
       ≡⟨ {!!} ⟩
      ids ∎

-}

--  varβ : var [ δ ,s V ]v ≡ V
--lda-nat : (γ : Subst Δ Γ) (M : Comp (S ∷ Γ) T)
--        → (lda M) [ γ ]v ≡ lda (M [ γ ∘s wk ,s var ]c)
-- ,s-nat : (γ ,s V) ∘s δ ≡ ((γ ∘s δ) ,s (V [ δ ]v))
-- substPlugDist : (E [ M ]∙) [ γ ]c ≡ (E [ γ ]e) [ M [ γ ]c ]∙

up-comp : (c : R ⊑ S) (d : S ⊑ T) ->
  emb (c ∘⊑ d) ≡ ((emb d [ !s ,s var ]v) ∘V emb c)
dn-comp : (c : R ⊑ S) (d : S ⊑ T) ->
  proj (c ∘⊑ d) ≡ (proj c ∘E proj d)

up-comp nat nat =
  var
    ≡⟨ sym varβ ⟩
  (var [ ids ,s var ]v)
    ≡⟨ (λ i -> (varβ {δ = !s} {V = var}) (~ i) [ ids ,s var ]v) ⟩
  (var [ !s ,s var ]v [ ids ,s var ]v) ∎
up-comp nat inj-nat = {!!}
  where
    lem : injectN ≡ ((injectN [ {!!} ]v) ∘V var)
    lem = {!!}
up-comp dyn dyn = {!!}
up-comp (ci ⇀ co) (ei ⇀ eo) =
  lda (((proj (trans-⊑ ci ei) [ !s ]e) [ ret' var ]∙) >>
      ((app [ drop2nd ]c) >>
      ((vToE (emb (trans-⊑ co eo)) [ !s ]e) [ ret' var ]∙)))
      
  ≡⟨ (λ i -> lda (((dn-comp ci ei i [ !s ]e) [ ret' var ]∙) >>
      ((app [ drop2nd ]c) >>
      ((vToE (up-comp co eo i) [ !s ]e) [ ret' var ]∙)))) ⟩
  
  lda ((((proj ci ∘E proj ei) [ !s ]e) [ ret' var ]∙) >>
      ((app [ drop2nd ]c) >>
      ((vToE ((emb eo [ !s ,s var ]v) ∘V emb co ) [ !s ]e) [ ret' var ]∙)))

  ≡⟨ {!!} ⟩
  
  lda (((((proj ci [ !s ]e) ∘E (proj ei [ !s ]e))) [ ret' var ]∙) >>
      ((app [ drop2nd ]c) >>
      ((vToE ((emb eo [ !s ,s var ]v) ∘V emb co ) [ !s ]e) [ ret' var ]∙)))

  ≡⟨ cong lda {!!} ⟩

{-
  lda (((((proj ei [ !s ]e))) [ ret' var ]∙) >>
      (((proj ci [ !s ]e) [ ret' var ]∙) >> 
      ((app [ {!!} ]c) >>
      (((vToE (emb co ) [ !s ]e) [ ret' var ]∙) >>
      ((vToE (emb eo) [ !s ]e) [ ret' var ]∙)))))

  ≡⟨ cong lda {!!} ⟩
-}

  lda (M1 [ (!s ∘s wk ,s (lda M2 [ wk ]v)) ,s var ]c)
      
  ≡⟨ cong lda (cong₂ _[_]c refl (cong₂ _,s_ (sym ,s-nat) refl)) ⟩
  
  lda (M1 [ ((!s ,s lda M2) ∘s wk) ,s var ]c)
      
  ≡⟨ sym (lda-nat _ _) ⟩
  
  ((lda M1) [ !s ,s lda M2 ]v)
          
  ≡⟨ cong₂ _[_]v refl (sym lem) ⟩
  
  ((lda M1) [ (!s ,s var) ∘s (ids ,s lda M2) ]v)
          
  ≡⟨ substAssoc ⟩
  
  ((lda M1) [ !s ,s var ]v) ∘V lda M2 ∎
  where
   -- bind-nat : (bind M) [ γ ]e ≡ bind (M [ γ ∘s wk ,s var ]c)

    M1 = ((proj ei [ !s ]e) [ ret' var ]∙) >>
           ((app [ drop2nd ]c) >> ((vToE (emb eo) [ !s ]e) [ ret' var ]∙))
    M2 = ((proj ci [ !s ]e) [ ret' var ]∙) >>
           ((app [ drop2nd ]c) >> ((vToE (emb co) [ !s ]e) [ ret' var ]∙))
           
    P = lda (M1 [ (!s ∘s wk ,s (lda M2 [ wk ]v)) ,s var ]c)

    eq : P ≡ lda (((proj ei [ !s ]e) [ ret' var ]∙) >>
                 (((app [ drop2nd ]c) >> ((vToE (emb eo) [ !s ]e) [ ret' var ]∙))
                 [ (!s ∘s wk ,s (lda M2 [ wk ]v) ,s var) ∘s wk ,s var ]c))
    eq = cong lda
      (substPlugDist
       ∙ (cong₂ _[_]∙ bind-nat (substPlugDist
                                  ∙ cong₂ _[_]∙
                                        (sym substAssoc ∙ cong₂ _[_]e refl []η)
                                        (ret'-nat ∙ cong ret' varβ))))


    lem : ∀ {V : Val Γ S} -> (!s ,s var) ∘s (ids ,s V) ≡ (!s ,s V)
    lem = ,s-nat ∙ (cong₂ _,s_ []η varβ)
    -- ,s-nat : (γ ,s V) ∘s δ ≡ ((γ ∘s δ) ,s (V [ δ ]v))
    -- varβ : var [ δ ,s V ]v ≡ V


up-comp (ci ⇀ co) (inj-arr (ei ⇀ eo)) = {!!}
up-comp inj-nat dyn = {!!}
up-comp (inj-arr c) dyn = {!!}



dn-comp nat nat = sym ∘IdL
dn-comp nat inj-nat = sym ∘IdL
dn-comp dyn dyn = sym ∘IdL
dn-comp (ci ⇀ co) (ei ⇀ eo) = {!!}
dn-comp (ci ⇀ co) (inj-arr (ei ⇀ eo)) = {!!}
dn-comp inj-nat dyn = sym ∘IdR
dn-comp (inj-arr c) dyn = sym ∘IdR












-- -- TODO: admissibility of Reflexivity of each ⊑
{-
refl-Subst⊑ : ∀ γ → Subst⊑ (refl-⊑ctx Δ) (refl-⊑ctx Γ) γ γ
refl-Subst⊑ γ = {!!}

refl-Val⊑ : ∀ V → Val⊑ (refl-⊑ctx Γ) (refl-⊑ S) V V
refl-Val⊑ V = {!!}

refl-Comp⊑ : ∀ M → Comp⊑ (refl-⊑ctx Γ) (refl-⊑ S) M M
refl-Comp⊑ M = {!!}

refl-EvCtx⊑ : ∀ E → EvCtx⊑ (refl-⊑ctx Γ) (refl-⊑ S) (refl-⊑ S) E E
refl-EvCtx⊑ E = {!!}
-}
