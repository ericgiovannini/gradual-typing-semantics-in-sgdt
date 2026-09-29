{-

  A language based on fine-grained call-by-value, intended as the
  target of a translation from the gradual surface calculus.

  The casts in the surface language will be translated into
  "contracts" expressed in this language.

-}
module Syntax.ContractsFineGrained where

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
    R S S' T U : Ty
    S⊑T : TyPrec
    B B' C C' D D' : Γ ⊑ctx Γ'
    b b' c c' d d' : S ⊑ S'


data Val   (Γ : Ctx) : (S : Ty) → Type
data Comp  (Γ : Ctx) : (S : Ty) → Type
data EvCtx (Γ : Ctx) : (S : Ty) → (T : Ty) → Type


data Val Γ where
  var : Γ ∋ T → Val Γ T
  lda : Comp (S ∷ Γ) T → Val Γ (S ⇀ T)
  zro : Val Γ nat
  suc : Val Γ nat → Val Γ nat
  inj-nat : Val Γ nat → Val Γ dyn
  inj-arr : Val Γ (dyn ⇀ dyn) → Val Γ dyn
  inj-times : Val Γ (dyn × dyn) → Val Γ dyn


data Comp Γ where
  _[_]∙ : EvCtx Γ S T → Comp Γ S → Comp Γ T
  err : Comp Γ S
  ret : Val Γ S → Comp Γ S
  app : Comp Γ (S ⇀ T) → Comp Γ S → Comp Γ T -- should the args be Comp?
  

data EvCtx Γ where
  ∙E : EvCtx Γ S S
  _∘E_ : EvCtx Γ T U → EvCtx Γ S T → EvCtx Γ S U
  bind : Comp (S ∷ Γ) T → EvCtx Γ S T
  matchNat : Comp Γ S → Comp (nat ∷ Γ) S → EvCtx Γ nat S
  matchDyn :
      Comp (nat ∷ Γ) S
    → Comp (dyn ⇀ dyn ∷ Γ) S
    → Comp (dyn × dyn ∷ Γ) S
    → EvCtx Γ dyn S



-- Renaming and substitution

renameV : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Δ ∋ S)
  → (∀ {S} → Val Γ S → Val Δ S)

renameC : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Δ ∋ S)
  → (∀ {S} → Comp Γ S → Comp Δ S)

renameE : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Δ ∋ S)
  → (∀ {T S} → EvCtx Γ T S → EvCtx Δ T S)

renameV ρ (var x) = var (ρ x)
renameV ρ (lda M) = lda (renameC (ext ρ) M)
renameV ρ zro = zro
renameV ρ (suc M) = suc (renameV ρ M)
renameV ρ (inj-nat M) = inj-nat (renameV ρ M)
renameV ρ (inj-arr M) = inj-arr (renameV ρ M)
renameV ρ (inj-times M) = inj-times (renameV ρ M)

renameC ρ (E [ M ]∙) = (renameE ρ E) [ renameC ρ M ]∙
renameC ρ err = err
renameC ρ (ret V) = ret (renameV ρ V)
renameC ρ (app M N) = app (renameC ρ M) (renameC ρ N)

renameE ρ ∙E = ∙E
renameE ρ (E₁ ∘E E₂) = (renameE ρ E₁) ∘E (renameE ρ E₂)
renameE ρ (bind M) = bind (renameC (ext ρ) M)
renameE ρ (matchNat Kz Ks) = matchNat (renameC ρ Kz) (renameC (ext ρ) Ks)
renameE ρ (matchDyn Kn K⇀ K×) =
  matchDyn (renameC (ext ρ) Kn) (renameC (ext ρ) K⇀) (renameC (ext ρ) K×)






extsV : ∀ {Γ Δ}
  → (∀ {S} →       Γ ∋ S → Val Δ S)
  → (∀ {S T} → T ∷ Γ ∋ S → Val (T ∷ Δ) S)
extsV ρ vz = var vz
extsV ρ (vs x) = renameV vs (ρ x)

extsC : ∀ {Γ Δ}
  → (∀ {S} →       Γ ∋ S → Comp Δ S)
  → (∀ {S T} → T ∷ Γ ∋ S → Comp (T ∷ Δ) S)
extsC ρ vz = ret (var vz)
extsC ρ (vs x) = renameC vs (ρ x)

extsE : ∀ {Γ Δ}
  → (∀ {U S} →       Γ ∋ S → EvCtx Δ U S)
  → (∀ {U S T} → T ∷ Γ ∋ S → EvCtx (T ∷ Δ) U S)
extsE ρ vz = bind (ret (var (vs vz)))
extsE ρ (vs x) = renameE vs (ρ x)


{-
subV : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Val Δ S)
  → (∀ {S} → Val Γ S → Val Δ S)

subC : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Comp Δ S)
  → (∀ {S} → Comp Γ S → Comp Δ S)

subE : ∀ {Γ Δ}
  → (∀ {S T} → Γ ∋ T → EvCtx Δ S T)
  → (∀ {S T} → EvCtx Γ S T → EvCtx Δ S T)
-}
  



subV : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Val Δ S)
  → (∀ {S} → Val Γ S → Val Δ S)

subC : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Val Δ S)
  → (∀ {S} → Comp Γ S → Comp Δ S)

subE : ∀ {Γ Δ}
  → (∀ {S} → Γ ∋ S → Val Δ S)
  → (∀ {S T} → EvCtx Γ S T → EvCtx Δ S T)


subV σ (var x) = σ x
subV σ (lda M) = lda (subC (extsV σ) M) 
subV σ zro = zro
subV σ (suc V) = suc (subV σ V)
subV σ (inj-nat V) = inj-nat (subV σ V)
subV σ (inj-arr V) = inj-arr (subV σ V)
subV σ (inj-times V) = inj-times (subV σ V)

subC σ (E [ M ]∙) = (subE σ E) [ subC σ M ]∙
subC σ err = err
subC σ (ret V) = ret (subV σ V) -- bind (extsC σ {!!}) [ ret {!!} ]∙ -- ret (subV {!!} V)
subC σ (app M N) = app (subC σ M) (subC σ N)

subE σ ∙E = ∙E
subE σ (E₁ ∘E E₂) = (subE σ E₁) ∘E (subE σ E₂)
subE σ (bind M) = bind (subC (extsV σ) M)
subE σ (matchNat Kz Ks) = matchNat (subC σ Kz) (subC (extsV σ) Ks)
subE σ (matchDyn Kn K⇀ K×) = matchDyn (subC (extsV σ) Kn) (subC (extsV σ) K⇀) (subC (extsV σ) K×)


_[_]V : ∀ {Γ S T}
  → Val (T ∷ Γ) S
  → Val Γ T
  → Val Γ S
_[_]V {Γ} {S} {T} N M = subV {T ∷ Γ} {Γ} σ {S} N
  where
    σ : ∀ {S'} → (T ∷ Γ ∋ S') → Val Γ S'
    σ vz = M
    σ (vs x) = var x


_[_]C : ∀ {Γ S T}
  → Comp (T ∷ Γ) S
  → Val Γ T
  → Comp Γ S
_[_]C {Γ} {S} {T} N M = subC {T ∷ Γ} {Γ} σ {S} N
  where
    σ : ∀ {S'} → (T ∷ Γ ∋ S') → Val Γ S'
    σ vz = M
    σ (vs x) = var x




-- downcast a dyn to a nat and upcast it back

test : Comp (dyn ∷ []) dyn
test = matchDyn (ret (inj-nat (var vz))) err err [ ret (var vz) ]∙
