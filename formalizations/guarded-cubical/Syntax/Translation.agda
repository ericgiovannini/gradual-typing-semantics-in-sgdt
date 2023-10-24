{-# OPTIONS --lossy-unification #-}


module Syntax.Translation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Sum
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.Empty renaming (rec to exFalso)
open import Cubical.Data.Sigma

open import Syntax.Types
open import Syntax.Surface
open import Syntax.IntensionalTerms
open import Syntax.IntensionalOrder
open import Syntax.SyntacticBisimilarity

open TyPrec
open CtxPrec


-- Surface syntax and logic to intensional syntax and logic

private
  variable
    Γ Γ' : Ctx
    S S' T : Ty
    S⊑T : TyPrec
    B B' C C' D D' : Γ ⊑ctx Γ'
    b b' c c' d d' : S ⊑ S'

var-to-val : ∀ {Γ S} -> (x : Γ ∋ S) -> Val Γ S
-- vz :  S ∷ Γ ∋ S
var-to-val vz = var
-- vs : (x : Γ ∋ T) -> (S ∷ Γ ∋ T)
var-to-val (vs {T = T} x) = (var-to-val x) [ wk ]v

ι : Tm Γ S -> Comp Γ S
ι (var x) = ret' (var-to-val x)
ι (lda M) = ret' (lda (ι M))
ι (app M N) = app'' (ι M) (ι N)
ι err = err'
ι (up S⊑T M) = {!!} -- (upE S⊑T [ !s ]e) [ ι M ]∙
ι (dn S⊑T M) = {!!} -- (dn S⊑T [ !s ]e) [ ι M ]∙
ι zro = ret' zro'
ι (suc M) = (ι M) >> (ret' (suc' var)) -- (bind (ret' (suc' var))) [ ι M ]∙
ι (matchNat M Kz Ks) = {!!}


⊑theorem : ∀ {Γ S Γ' T C c} -> (M : Tm Γ S) (N : Tm Γ' T) ->
  TmPrec C c M N ->
  Σ[ M' ∈ Comp Γ S ] Σ[ N' ∈ Comp Γ' T ]
    (ι(M) ≈c M') × Comp⊑ C c M' N' × (N' ≈c ι(N))
⊑theorem {Γ = Γ} {S = S} {Γ' = Γ'} {T = T} M N (var x) = {!!}
⊑theorem (lda M) (lda M') (lda p) = {!!}
⊑theorem (app M1 N1) (app M2 N2) (app p q) with ⊑theorem M1 M2 p | ⊑theorem N1 N2 q
... | (M1' , M2' , M1≈M1' , M1'⊑M2' , M2'≈M2) |
      (N1' , N2' , N1≈N1' , N1'⊑N2' , N2'≈N2)  =
      app'' M1' N1' ,
      app'' M2' N2' ,
      ≈-plugE (≈-bind (≈-plugE (≈-bind ≈-refl) (≈-substC N1≈N1' ≈-refl))) M1≈M1' ,
      (bind (bind (app [ !s ,s (var [ wk ]v) ,s var ]c) [ N1'⊑N2' [ wk ]c ]∙) [ M1'⊑M2' ]∙) ,
      ≈-plugE (≈-bind (≈-plugE (≈-bind ≈-refl) (≈-substC N2'≈N2 ≈-refl))) M2'≈M2
⊑theorem .err .err err =
  err' , err' , ≈-refl , (err [ !s ]c) , ≈-refl
⊑theorem .zro .zro zro = {!!}
⊑theorem (suc M) (suc M') (suc x) = {!!}
⊑theorem (matchNat N Kz Ks) (matchNat N' Kz' Ks') (matchNat p q r) = {!!}
⊑theorem (up S⊑T M) N (upL .S⊑T x) = {!!}
⊑theorem M (up _ M') (upR _ x) = {!!}
⊑theorem (dn _ M) N (dnL _ x) = {!!}
⊑theorem M (dn S⊑T M') (dnR .S⊑T x) = {!!}


{- translation-prec (lda M) (lda M') (lda x)
translation-prec (app M N) (app M' N') (app x x₁)
translation-prec .err .err err
translation-prec .zro .zro zro
translation-prec (suc M) (suc M') (suc x)
translation-prec (matchNat N Kz Ks) (matchNat N' Kz' Ks')
  (matchNat x x₁ x₂)
translation-prec (up S⊑T M) N (upL .S⊑T x)

-}
