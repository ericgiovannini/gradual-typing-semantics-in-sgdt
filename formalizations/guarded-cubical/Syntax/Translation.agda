{- Translation from surface syntax/precision to fine grained syntax/logic -}
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
open import Syntax.FineGrained.Terms
open import Syntax.FineGrained.Order

open TyPrec
open CtxPrec

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
ι (up S⊑T M) = (upE S⊑T [ !s ]e) [ ι M ]∙
ι (dn S⊑T M) = (dn S⊑T [ !s ]e) [ ι M ]∙ -- (dn S⊑T [ !s ]e) [ ι M ]∙
ι zro = ret' zro'
ι (suc M) = bind' (ι M) (ret' (suc' var))
ι (matchNat M Kz Ks) = bind' (ι M) (matchNat (ι Kz) (ι Ks))

-- TODO
-- syntactic-graduality
--   : ∀ {M}{M'}
--   → TmPrec C c M M'
--   → Comp⊑ C c (ι M) (ι M')
-- syntactic-graduality (var x) = {!!}
-- syntactic-graduality (lda M⊑M') = {!!}
-- syntactic-graduality (app M⊑M' M⊑M'') = {!!}
-- syntactic-graduality err = {!!}
-- syntactic-graduality zro = {!!}
-- syntactic-graduality (suc M⊑M') = {!!}
-- syntactic-graduality (matchNat M⊑M' M⊑M'' M⊑M''') = {!!}
-- syntactic-graduality (upL S⊑T M⊑M') = {!!}
-- syntactic-graduality (upR S⊑T M⊑M') = {!!}
-- syntactic-graduality (dnL S⊑T M⊑M') = {!!}
-- syntactic-graduality (dnR S⊑T M⊑M') = {!!}
