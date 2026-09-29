{-

  A language intended as the target of a translation from the gradual
  surface calculus.

  The casts in the surface language will be translated into
  "contracts" expressed in this language.

-}
module Syntax.Contracts where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List

open import Syntax.Types

open TyPrec
open CtxPrec


private
  variable
    Γ Γ' : Ctx
    R S S' T : Ty
    S⊑T : TyPrec
    B B' C C' D D' : Γ ⊑ctx Γ'
    b b' c c' d d' : S ⊑ S'


data Tm : Ctx -> Ty -> Set where
  var : Γ ∋ T -> Tm Γ T
  lda : Tm (S ∷ Γ) T -> Tm Γ (S ⇀ T)
  app : Tm Γ (S ⇀ T) -> Tm Γ S -> Tm Γ T
  err : Tm Γ S
  zro : Tm Γ nat
  suc : Tm Γ nat -> Tm Γ nat
  matchNat : Tm Γ nat -> Tm Γ S -> Tm (nat ∷ Γ) S -> Tm Γ S
  letTimes : Tm Γ (S × T) -> Tm (S ∷ T ∷ Γ) R → Tm Γ R
  pair : Tm Γ S → Tm Γ T → Tm Γ (S × T)

  -- injections and case match for dyn:

  inj-nat : Tm Γ nat → Tm Γ dyn
  inj-arr : Tm Γ (dyn ⇀ dyn) → Tm Γ dyn
  inj-times : Tm Γ (dyn × dyn) → Tm Γ dyn

  matchDyn : ∀ {S}
    → Tm Γ dyn
    → Tm (nat ∷ Γ) S
    → Tm (dyn ⇀ dyn ∷ Γ) S
    → Tm (dyn × dyn ∷ Γ) S
    → Tm Γ S
  
-- convenience syntax
`let : Tm (S ∷ Γ) T → Tm Γ S → Tm Γ T
`let M N = app (lda M) N


-- Renaming and substitution

rename : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Δ ∋ S)
  → (∀ {S} → Tm Γ S → Tm Δ S)
rename ρ (var x) = var (ρ x)
rename ρ {S = Sᵢ ⇀ Sₒ} (lda M) = lda (rename (ext ρ) M)
rename ρ (app M N) = app (rename ρ M) (rename ρ N)
rename ρ err = err
rename ρ zro = zro
rename ρ (suc M) = suc (rename ρ M)
rename ρ (matchNat N Kz Ks) = matchNat (rename ρ N) (rename ρ Kz) (rename (ext ρ) Ks)
rename ρ (letTimes M N) = letTimes (rename ρ M) (rename (ext (ext ρ)) N)
rename ρ (pair M N) = pair (rename ρ M) (rename ρ N)
rename ρ (inj-nat M) = inj-nat (rename ρ M)
rename ρ (inj-arr M) = inj-arr (rename ρ M)
rename ρ (inj-times M) = inj-times (rename ρ M)
rename ρ (matchDyn M Kn K→ K×) =
  matchDyn (rename ρ M) (rename (ext ρ) Kn) (rename (ext ρ) K→) (rename (ext ρ) K×)


exts : ∀ {Γ Δ}
  → (∀ {S} →       Γ ∋ S → Tm Δ S)
  → (∀ {S T} → T ∷ Γ ∋ S → Tm (T ∷ Δ) S)
exts ρ vz = var vz
exts ρ (vs x) = rename vs (ρ x)

wk : ∀ {Γ S T}
  → Tm Γ S
  → Tm (T ∷ Γ) S
wk M = rename vs M

sub : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Tm Δ S)
  → (∀ {S} → Tm Γ S → Tm Δ S)
sub σ (var x) = σ x
sub σ (lda M) = lda (sub (exts σ) M)
sub σ (app M N) = app (sub σ M) (sub σ N)
sub σ err = err
sub σ zro = zro
sub σ (suc M) = suc (sub σ M)
sub σ (matchNat N Kz Ks) = matchNat (sub σ N) (sub σ Kz) (sub (exts σ) Ks)
sub σ (letTimes M N) = letTimes (sub σ M) (sub (exts (exts σ)) N)
sub σ (pair M N) = pair (sub σ M) (sub σ N)
sub ρ (inj-nat M) = inj-nat (sub ρ M)
sub ρ (inj-arr M) = inj-arr (sub ρ M)
sub ρ (inj-times M) = inj-times (sub ρ M)
sub ρ (matchDyn M Kn K→ K×) =
  matchDyn (sub ρ M) (sub (exts ρ) Kn) (sub (exts ρ) K→) (sub (exts ρ) K×)


_[_]tm : ∀ {Γ S T}
  → Tm (T ∷ Γ) S
  → Tm Γ T
  → Tm Γ S
_[_]tm {Γ} {S} {T} N M = sub {T ∷ Γ} {Γ} σ {S} N --subst {Γ , B} {Γ} σ {A} N
  where
    σ : ∀ {S'} → (T ∷ Γ ∋ S') → Tm Γ S'
    σ vz = M
    σ (vs x) = var x
