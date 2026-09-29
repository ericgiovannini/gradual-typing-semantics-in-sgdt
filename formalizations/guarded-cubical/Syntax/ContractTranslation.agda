
module Syntax.ContractTranslation  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List

open import Syntax.Types
open import Syntax.Surface
open import Syntax.Contracts renaming (Tm to Tm* ; wk to wk*)

open TyPrec
open CtxPrec


private
  variable
    Γ Γ' : Ctx
    R S S' T : Ty
    S⊑T : TyPrec
    B B' C C' D D' : Γ ⊑ctx Γ'
    b b' c c' d d' : S ⊑ S'


⟦_⟧up : ∀ (c : S ⊑ T) → Tm* Γ S → Tm* Γ T
⟦_⟧dn : ∀ (c : S ⊑ T) → Tm* Γ T → Tm* Γ S

-- upcasts
⟦ refl-⊑ ⟧up M = M
⟦ trans-⊑ {S} {U} {T} c₁ c₂ ⟧up = ⟦ c₂ ⟧up ∘ ⟦ c₁ ⟧up
⟦ c₁ ⇀ c₂ ⟧up M = lda (⟦ c₂ ⟧up (app (wk* M) (⟦ c₁ ⟧dn (var vz)))) -- downcast in domain, upcast in codomain
⟦ c₁ × c₂ ⟧up M =
  letTimes M (pair
    (⟦ c₁ ⟧up (var vz))
    (⟦ c₂ ⟧up (var (vs vz))))
⟦ inj-nat ⟧up = inj-nat
⟦ inj-arr ⟧up = inj-arr
⟦ inj-times ⟧up = inj-times

-- downcasts
⟦ refl-⊑ ⟧dn M = M
⟦ trans-⊑ {S} {U} {T} c₁ c₂ ⟧dn = ⟦ c₁ ⟧dn ∘ ⟦ c₂ ⟧dn
⟦ c₁ ⇀ c₂ ⟧dn M = lda (⟦ c₂ ⟧dn (app (wk* M) (⟦ c₁ ⟧up (var vz))))
⟦ c₁ × c₂ ⟧dn M =
  letTimes M (pair
    (⟦ c₁ ⟧dn (var vz))
    (⟦ c₂ ⟧dn (var (vs vz))))
⟦ inj-nat ⟧dn M = matchDyn M (var vz) err err
⟦ inj-arr ⟧dn M = matchDyn M err (var vz) err
⟦ inj-times ⟧dn M = matchDyn M err err (var vz)


-- Term translation:

⟦_⟧ : ∀ {Γ S} → Tm Γ S → Tm* Γ S
⟦ var x ⟧ = var x
⟦ lda M ⟧ = lda ⟦ M ⟧
⟦ app M N ⟧ = app ⟦ M ⟧ ⟦ N ⟧
⟦ err ⟧ = err
⟦ up S⊑T M ⟧ = ⟦ S⊑T .ty-prec ⟧up ⟦ M ⟧
⟦ dn S⊑T M ⟧ = ⟦ S⊑T .ty-prec ⟧dn ⟦ M ⟧
⟦ zro ⟧ = zro
⟦ suc M ⟧ = suc ⟦ M ⟧
⟦ matchNat M Kz Ks ⟧ = matchNat ⟦ M ⟧ ⟦ Kz ⟧ ⟦ Ks ⟧
⟦ letTimes M N ⟧ = letTimes ⟦ M ⟧ ⟦ N ⟧
⟦ pair M N ⟧ = pair ⟦ M ⟧ ⟦ N ⟧
  
