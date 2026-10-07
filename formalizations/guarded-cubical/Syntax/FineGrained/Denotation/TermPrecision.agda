{-
  Denotational semantics of term precision, i.e., graduality.

  A term precision derivation Δ ⊢ M ⊑ M' : c denotes an extensional
  square: a strict square between morphisms N ≈ ⟦M⟧ and N' ≈ ⟦M'⟧.
  The congruence rules are interpreted by the corresponding square and
  bisimilarity lemmas of Denotation.Squares; EquivTyPrec by the
  quasi-order-equivalence of the two denoted relations; and the four
  cast rules by the quasi-representability squares of the cast's
  relation, pushed or pulled along the other relation. In the cast
  rules and EquivTyPrec the perturbations that appear are bisimilar to
  the identity, which is what the "≈" components of the extensional
  square absorb (Section 6.4.3 of the paper).

  Type-checking note: the predomain arguments of the bisimilarity
  congruence lemmas (bind-≈, natCase-≈) are given explicitly, in the
  canonical form ValType→Predomain ⟦ _ ⟧ctx, and the square for app is
  inlined. Leaving these to be inferred makes Agda solve them by
  η-expanding record metavariables, after which conversion checking
  of the resulting terms does not finish in reasonable time.
-}
{-# OPTIONS --rewriting --lossy-unification #-}
open import Common.Later
module Syntax.FineGrained.Denotation.TermPrecision (k : Clock) where

open import Cubical.Foundations.Prelude renaming (comp to compose)
open import Cubical.Foundations.Structure
open import Cubical.Data.List
open import Cubical.Data.Nat using (zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)

open import Semantics.Concrete.Predomain.Base
open import Semantics.Concrete.Predomain.Morphism renaming (Comp to Compose)
open import Semantics.Concrete.Predomain.Convenience
open import Semantics.Concrete.Predomain.Constructions
  using (_×dp_ ; π1 ; π2 ; UnitP ; UnitP!)
open import Semantics.Concrete.Predomain.Combinators
  using (Curry ; App ; PairFun ; K ; SwapPair ; _×mor_ ; mSuc)
open import Semantics.Concrete.Predomain.Relation
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.ErrorDomain k
open import Semantics.Concrete.Predomain.FreeErrorDomain k
open import Semantics.Concrete.Perturbation.Semantic k using (F-SemPtb)
open import Semantics.Concrete.Perturbation.QuasiRepresentation k
open import Semantics.Concrete.Perturbation.QuasiRepresentation.QuasiEquivalence k
open import Semantics.Concrete.Perturbation.Relation k
  using (pushV ; pushVSq ; pullV ; pullVSq ; pushC ; pushCSq ; pullC ; pullCSq)
open import Semantics.Concrete.Types k as SemTypes hiding (_×_)
open import Semantics.Concrete.Relations k as Rel hiding (_×_)
open import Semantics.Concrete.ExtensionalModel k

open import Syntax.Types
open import Syntax.FineGrained.Terms hiding (π2)
open import Syntax.FineGrained.Order
open import Syntax.FineGrained.Denotation.Types k
open import Syntax.FineGrained.Denotation.TypePrecision k
open import Syntax.FineGrained.Denotation.Terms k
open import Syntax.FineGrained.Denotation.Combinators k
open import Syntax.FineGrained.Denotation.Squares k

open TyPrec
open PMor
open ErrorDomMor
open ExtAsEDMorphism
open F-ob
open F-mor
open F-rel
open F-sq

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T R' S' T' : Ty
   B B' C C' D D' : Γ ⊑ctx Γ'
   b b' c c' d d' : S ⊑ S'
   γ γ' γ'' : Subst Δ Γ
   δ δ' δ'' : Subst Θ Δ
   θ θ' θ'' : Subst Z Θ
   V V' V'' : Val Γ S
   M M' M'' N N' : Comp Γ S
   E E' E'' : EvCtx Γ S T


-- Endpoints of precision derivations, so that they can be named in
-- clauses without naming implicit arguments.
tyL tyR : S ⊑ T → Ty
tyL {S = S} _ = S
tyR {T = T} _ = T

ctxL ctxR : Γ ⊑ctx Γ' → Ctx
ctxL {Γ = Γ} _ = Γ
ctxR {Γ' = Γ'} _ = Γ'

-- Underlying predomain relations of type and context precision.
rel : S ⊑ T → PRel (ValType→Predomain ⟦ S ⟧ty) (ValType→Predomain ⟦ T ⟧ty) ℓ-zero
rel c = ⟦ c ⟧ty⊑ .fst .fst

ctx : Γ ⊑ctx Γ' → PRel (ValType→Predomain ⟦ Γ ⟧ctx) (ValType→Predomain ⟦ Γ' ⟧ctx) ℓ-zero
ctx C = ⟦ C ⟧ctx⊑ .fst .fst

-- The relation denoted by the reflexivity context precision is the
-- order of the context's predomain.
ctx-refl-to : ∀ Γ {x y} → ctx (refl-⊑ctx Γ) .PRel.R x y →
  rel-≤ (ValType→Predomain ⟦ Γ ⟧ctx) x y
ctx-refl-to [] p = p
ctx-refl-to (S ∷ Γ) (p , q) = ctx-refl-to Γ p , q

ctx-refl-from : ∀ Γ {x y} → rel-≤ (ValType→Predomain ⟦ Γ ⟧ctx) x y →
  ctx (refl-⊑ctx Γ) .PRel.R x y
ctx-refl-from [] p = p
ctx-refl-from (S ∷ Γ) (p , q) = ctx-refl-from Γ p , q


-- The denotation of an upcast applied to a computation is the
-- functorial action of F on the embedding.
upC-eq : (c : S ⊑ T) (M : Comp Γ S) →
  ⟦ upC (mkTyPrec c) M ⟧C ≡ U-mor (F-mor (embV _ _ _ (⟦ c ⟧ty⊑ .snd .fst))) ∘p ⟦ M ⟧C
upC-eq c M = eqPMor _ _ (funExt (λ γ →
  funExt⁻ (cong ErrorDomMor.fun (upE-eq (embV _ _ _ (⟦ c ⟧ty⊑ .snd .fst)))) (⟦ M ⟧C .f γ)))


-- The reflexivity square for an evaluation context, with the
-- predomain of the transitivity step given explicitly.
E-refl-sq : (E : EvCtx Γ S T) →
  ErrorDomSq (F-rel (idPRel (ValType→Predomain ⟦ S ⟧ty)))
             (ctx (refl-⊑ctx Γ) ⟶rel F-rel (idPRel (ValType→Predomain ⟦ T ⟧ty)))
             ⟦ E ⟧E ⟦ E ⟧E
E-refl-sq {Γ = Γ} {T = T} E b b' b≤b' x y r =
  transitive-≤ (U-ob (F-ob (ValType→Predomain ⟦ T ⟧ty))) _ _ _
    (⟦ E ⟧E .fun b .isMon (ctx-refl-to Γ r))
    (⟦ E ⟧E .f .isMon b≤b' y)


-- Abbreviations for the predomains and error domains that occur as
-- (explicit) arguments of the bisimilarity lemmas below.
𝒞 : Ctx → Predomain ℓ-zero ℓ-zero ℓ-zero
𝒞 Γ = ValType→Predomain ⟦ Γ ⟧ctx

𝒱 : Ty → Predomain ℓ-zero ℓ-zero ℓ-zero
𝒱 S = ValType→Predomain ⟦ S ⟧ty

ℱ : Ty → ErrorDomain ℓ-zero ℓ-zero ℓ-zero
ℱ S = CompType→ErrorDomain (SemTypes.F ⟦ S ⟧ty)

𝒰ℱ : Ty → Predomain ℓ-zero ℓ-zero ℓ-zero
𝒰ℱ S = U-ob (ℱ S)

𝒜 : Ctx → Ty → ErrorDomain ℓ-zero ℓ-zero ℓ-zero
𝒜 Γ T = CompType→ErrorDomain (⟦ Γ ⟧ctx SemTypes.⟶ SemTypes.F ⟦ T ⟧ty)

-- Reflexivity of bisimilarity of morphisms, with the predomains given
-- explicitly (leaving them to be inferred produces unsolved
-- metavariables).
≈reflV : (A B : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero) (f : ValMor A B) →
  _≈mon_ {X = ValType→Predomain A} {Y = ValType→Predomain B} f f
≈reflV A B f = ≈mon-refl f

≈reflO : (A : ValType ℓ-zero ℓ-zero ℓ-zero ℓ-zero) (B : CompType ℓ-zero ℓ-zero ℓ-zero ℓ-zero)
  (f : ObliqueMor A B) →
  _≈mon_ {X = ValType→Predomain A} {Y = U-ob (CompType→ErrorDomain B)} f f
≈reflO A B f = ≈mon-refl f

≈reflE : (B B' : CompType ℓ-zero ℓ-zero ℓ-zero ℓ-zero) (ϕ : CompMor B B') →
  _≈mon_ {X = U-ob (CompType→ErrorDomain B)} {Y = U-ob (CompType→ErrorDomain B')} (ϕ .f) (ϕ .f)
≈reflE B B' ϕ = ≈mon-refl (ϕ .f)

-- The same, keyed on a syntactic object so that its context and type
-- need not be named in a clause.
S-refl-≈ : (γ : Subst Δ Γ) → _≈mon_ {X = ValType→Predomain ⟦ Δ ⟧ctx} {Y = ValType→Predomain ⟦ Γ ⟧ctx} ⟦ γ ⟧S ⟦ γ ⟧S
S-refl-≈ γ = ≈mon-refl ⟦ γ ⟧S

V-refl-≈ : (V : Val Γ S) → _≈mon_ {X = ValType→Predomain ⟦ Γ ⟧ctx} {Y = ValType→Predomain ⟦ S ⟧ty} ⟦ V ⟧V ⟦ V ⟧V
V-refl-≈ V = ≈mon-refl ⟦ V ⟧V

C-refl-≈ : (M : Comp Γ S) (f : ObliqueMor ⟦ Γ ⟧ctx (SemTypes.F ⟦ S ⟧ty)) →
  _≈mon_ {X = ValType→Predomain ⟦ Γ ⟧ctx} {Y = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ S ⟧ty))} f f
C-refl-≈ M f = ≈mon-refl f

E-refl-≈ : (E : EvCtx Γ S T) →
  _≈mon_ {X = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ S ⟧ty))}
         {Y = U-ob (CompType→ErrorDomain (⟦ Γ ⟧ctx SemTypes.⟶ SemTypes.F ⟦ T ⟧ty))}
         (⟦ E ⟧E .f) (⟦ E ⟧E .f)
E-refl-≈ E = ≈mon-refl (⟦ E ⟧E .f)


⟦_⟧S⊑ : Subst⊑ C D γ γ'  → ValTypeSq ⟦ C ⟧ctx⊑ ⟦ D ⟧ctx⊑ ⟦ γ ⟧S ⟦ γ' ⟧S
⟦_⟧V⊑ : Val⊑ C c V V'    → ValTypeSq ⟦ C ⟧ctx⊑ ⟦ c ⟧ty⊑ ⟦ V ⟧V ⟦ V' ⟧V
⟦_⟧E⊑ : EvCtx⊑ C c d E E' →
  CompTypeSq (Rel.F ⟦ c ⟧ty⊑) (⟦ C ⟧ctx⊑ Rel.⟶ Rel.F ⟦ d ⟧ty⊑) ⟦ E ⟧E ⟦ E' ⟧E
⟦_⟧C⊑ : Comp⊑ C c M M'   → ObliqueExtSq ⟦ C ⟧ctx⊑ (Rel.F ⟦ c ⟧ty⊑) ⟦ M ⟧C ⟦ M' ⟧C


-- Substitutions
⟦ reflexive {γ = γ} ⟧S⊑ =
  ⟦ γ ⟧S , S-refl-≈ γ , ⟦ γ ⟧S , S-refl-≈ γ ,
  λ x y r → ctx-refl-from _ (⟦ γ ⟧S .isMon (ctx-refl-to _ r))
⟦ !s {C = C} ⟧S⊑ =
  UnitP! , ≈reflV ⟦ ctxL C ⟧ctx ⟦ [] ⟧ctx UnitP! ,
  UnitP! , ≈reflV ⟦ ctxR C ⟧ctx ⟦ [] ⟧ctx UnitP! , λ _ _ _ → refl
⟦ _,s_ {C = C} {D = D} {γ = γ} {γ' = γ'} {c = c} {V = V} {V' = V'} s v ⟧S⊑ =
  let (Nγ , γ≈ , Nγ' , γ'≈ , sq₁) = ⟦ s ⟧S⊑
      (NV , V≈ , NV' , V'≈ , sq₂) = ⟦ v ⟧V⊑
  in PairFun Nγ NV ,
     PairFun-≈ {Γ = 𝒞 (ctxL C)} {A₁ = 𝒞 (ctxL D)} {A₂ = 𝒱 (tyL c)}
       {f₁ = ⟦ γ ⟧S} {f₁' = Nγ} {f₂ = ⟦ V ⟧V} {f₂' = NV} γ≈ V≈ ,
     PairFun Nγ' NV' ,
     PairFun-≈ {Γ = 𝒞 (ctxR C)} {A₁ = 𝒞 (ctxR D)} {A₂ = 𝒱 (tyR c)}
       {f₁ = ⟦ γ' ⟧S} {f₁' = Nγ'} {f₂ = ⟦ V' ⟧V} {f₂' = NV'} γ'≈ V'≈ ,
     PairFun-sq (ctx C) (ctx D) (rel c) sq₁ sq₂
⟦ _∘s_ {C = C} {D = D} {γ = γ} {γ' = γ'} {B = B} {δ = δ} {δ' = δ'} s t ⟧S⊑ =
  let (Nγ , γ≈ , Nγ' , γ'≈ , sq₁) = ⟦ s ⟧S⊑
      (Nδ , δ≈ , Nδ' , δ'≈ , sq₂) = ⟦ t ⟧S⊑
  in Nγ ∘p Nδ ,
     ≈mon-comp {X = 𝒞 (ctxL B)} {Y = 𝒞 (ctxL C)} {Z = 𝒞 (ctxL D)}
       {f = ⟦ δ ⟧S} {g = Nδ} {f' = ⟦ γ ⟧S} {g' = Nγ} δ≈ γ≈ ,
     Nγ' ∘p Nδ' ,
     ≈mon-comp {X = 𝒞 (ctxR B)} {Y = 𝒞 (ctxR C)} {Z = 𝒞 (ctxR D)}
       {f = ⟦ δ' ⟧S} {g = Nδ'} {f' = ⟦ γ' ⟧S} {g' = Nγ'} δ'≈ γ'≈ ,
     CompSqV {c₁ = ctx B} {c₂ = ctx C} {c₃ = ctx D} sq₂ sq₁
⟦ _ids_ {C = C} ⟧S⊑ =
  Id , ≈reflV ⟦ ctxL C ⟧ctx ⟦ ctxL C ⟧ctx Id ,
  Id , ≈reflV ⟦ ctxR C ⟧ctx ⟦ ctxR C ⟧ctx Id , Predom-IdSqV (ctx C)
⟦ wk {c = c} {C = C} ⟧S⊑ =
  π1 , ≈reflV ⟦ tyL c ∷ ctxL C ⟧ctx ⟦ ctxL C ⟧ctx π1 ,
  π1 , ≈reflV ⟦ tyR c ∷ ctxR C ⟧ctx ⟦ ctxR C ⟧ctx π1 , π1-sq (ctx C) (rel c)

-- Values
⟦ reflexive {V = V} ⟧V⊑ =
  ⟦ V ⟧V , V-refl-≈ V , ⟦ V ⟧V , V-refl-≈ V ,
  λ x y r → ⟦ V ⟧V .isMon (ctx-refl-to _ r)
⟦ _[_]v {C = C} {c = c} {V = V} {V' = V'} {B = B} {γ = γ} {γ' = γ'} v s ⟧V⊑ =
  let (NV , V≈ , NV' , V'≈ , sq₁) = ⟦ v ⟧V⊑
      (Nγ , γ≈ , Nγ' , γ'≈ , sq₂) = ⟦ s ⟧S⊑
  in NV ∘p Nγ ,
     ≈mon-comp {X = 𝒞 (ctxL B)} {Y = 𝒞 (ctxL C)} {Z = 𝒱 (tyL c)}
       {f = ⟦ γ ⟧S} {g = Nγ} {f' = ⟦ V ⟧V} {g' = NV} γ≈ V≈ ,
     NV' ∘p Nγ' ,
     ≈mon-comp {X = 𝒞 (ctxR B)} {Y = 𝒞 (ctxR C)} {Z = 𝒱 (tyR c)}
       {f = ⟦ γ' ⟧S} {g = Nγ'} {f' = ⟦ V' ⟧V} {g' = NV'} γ'≈ V'≈ ,
     CompSqV {c₁ = ctx B} {c₂ = ctx C} {c₃ = rel c} sq₂ sq₁
⟦ var {c = c} {C = C} ⟧V⊑ =
  π2 , ≈reflV ⟦ tyL c ∷ ctxL C ⟧ctx ⟦ tyL c ⟧ty π2 ,
  π2 , ≈reflV ⟦ tyR c ∷ ctxR C ⟧ctx ⟦ tyR c ⟧ty π2 , π2-sq (ctx C) (rel c)
⟦ zro ⟧V⊑ =
  K _ zero , ≈reflV ⟦ [] ⟧ctx ⟦ nat ⟧ty (K _ zero) ,
  K _ zero , ≈reflV ⟦ [] ⟧ctx ⟦ nat ⟧ty (K _ zero) , λ _ _ _ → refl
⟦ suc ⟧V⊑ =
  mSuc ∘p π2 , ≈reflV ⟦ nat ∷ [] ⟧ctx ⟦ nat ⟧ty (mSuc ∘p π2) ,
  mSuc ∘p π2 , ≈reflV ⟦ nat ∷ [] ⟧ctx ⟦ nat ⟧ty (mSuc ∘p π2) , suc-sq (idPRel UnitP)
⟦ lda {c = c} {C = C} {d = d} {M = M} {M' = M'} m ⟧V⊑ =
  let (N , M≈N , N' , N'≈M' , sq) = ⟦ m ⟧C⊑
  in Curry N ,
     Curry-≈ {Γ = 𝒞 (ctxL C)} {Aᵢ = 𝒱 (tyL c)} {Aₒ = 𝒰ℱ (tyL d)} {g = ⟦ M ⟧C} {g₂ = N} M≈N ,
     Curry N' ,
     Curry-≈ {Γ = 𝒞 (ctxR C)} {Aᵢ = 𝒱 (tyR c)} {Aₒ = 𝒰ℱ (tyR d)} {g = ⟦ M' ⟧C} {g₂ = N'}
       (≈mon-sym {X = 𝒞 (tyR c ∷ ctxR C)} {Y = 𝒰ℱ (tyR d)} N' ⟦ M' ⟧C N'≈M') ,
     Curry-sq (ctx C) (rel c) (U-rel (F-rel (rel d))) sq

-- Evaluation contexts
⟦ reflexive {E = E} ⟧E⊑ = ⟦ E ⟧E , E-refl-≈ E , ⟦ E ⟧E , E-refl-≈ E , E-refl-sq E
⟦ ∙E {C = C} {c = c} ⟧E⊑ =
  K-arrow , ≈reflE (SemTypes.F ⟦ tyL c ⟧ty) (⟦ ctxL C ⟧ctx SemTypes.⟶ SemTypes.F ⟦ tyL c ⟧ty) K-arrow ,
  K-arrow , ≈reflE (SemTypes.F ⟦ tyR c ⟧ty) (⟦ ctxR C ⟧ctx SemTypes.⟶ SemTypes.F ⟦ tyR c ⟧ty) K-arrow ,
  K-arrow-sq (ctx C) (F-rel (rel c))
⟦ _∘E_ {C = C} {c = c} {d = d} {E = E} {E' = E'} {b = b} {F = F} {F' = F'} e f ⟧E⊑ =
  let (NE , E≈ , NE' , E'≈ , sq₁) = ⟦ e ⟧E⊑
      (NF , F≈ , NF' , F'≈ , sq₂) = ⟦ f ⟧E⊑
  in compE NE NF ,
     compE-≈ {Γ = 𝒞 (ctxL C)} {B₁ = ℱ (tyL b)} {B₂ = ℱ (tyL c)} {B₃ = ℱ (tyL d)}
       {E' = ⟦ E ⟧E} {E'₂ = NE} {E = ⟦ F ⟧E} {E₂ = NF} E≈ F≈ ,
     compE NE' NF' ,
     compE-≈ {Γ = 𝒞 (ctxR C)} {B₁ = ℱ (tyR b)} {B₂ = ℱ (tyR c)} {B₃ = ℱ (tyR d)}
       {E' = ⟦ E' ⟧E} {E'₂ = NE'} {E = ⟦ F' ⟧E} {E₂ = NF'} E'≈ F'≈ ,
     compE-sq (ctx C) (F-rel (rel b)) (F-rel (rel c)) (F-rel (rel d))
       {E' = NE} {F' = NE'} {E = NF} {F = NF'} sq₁ sq₂
⟦ _[_]e {C = C} {c = c} {d = d} {E = E} {E' = E'} {B = B} {γ = γ} {γ' = γ'} e s ⟧E⊑ =
  let (NE , E≈ , NE' , E'≈ , sq₁) = ⟦ e ⟧E⊑
      (Nγ , γ≈ , Nγ' , γ'≈ , sq₂) = ⟦ s ⟧S⊑
  in (Nγ ⟶mor IdE) ∘ed NE ,
     substE-≈ {Δ = 𝒞 (ctxL B)} {Γ = 𝒞 (ctxL C)} {Bᵢ = ℱ (tyL c)} {Bₒ = ℱ (tyL d)}
       {s = ⟦ γ ⟧S} {s₂ = Nγ} {E = ⟦ E ⟧E} {E₂ = NE} γ≈ E≈ ,
     (Nγ' ⟶mor IdE) ∘ed NE' ,
     substE-≈ {Δ = 𝒞 (ctxR B)} {Γ = 𝒞 (ctxR C)} {Bᵢ = ℱ (tyR c)} {Bₒ = ℱ (tyR d)}
       {s = ⟦ γ' ⟧S} {s₂ = Nγ'} {E = ⟦ E' ⟧E} {E₂ = NE'} γ'≈ E'≈ ,
     substE-sq (ctx B) (ctx C) (F-rel (rel c)) (F-rel (rel d))
       {s = Nγ} {s' = Nγ'} {E = NE} {E' = NE'} sq₂ sq₁
⟦ bind {c = c} {C = C} {d = d} {M = M} {M' = M'} m ⟧E⊑ =
  let (N , M≈N , N' , N'≈M' , sq) = ⟦ m ⟧C⊑
  in Ext (Curry (N ∘p SwapPair)) ,
     bind-≈ {Γ = 𝒞 (ctxL C)} {A = 𝒱 (tyL c)} {B = ℱ (tyL d)} {M = ⟦ M ⟧C} {M₂ = N} M≈N ,
     Ext (Curry (N' ∘p SwapPair)) ,
     bind-≈ {Γ = 𝒞 (ctxR C)} {A = 𝒱 (tyR c)} {B = ℱ (tyR d)} {M = ⟦ M' ⟧C} {M₂ = N'}
       (≈mon-sym {X = 𝒞 (tyR c ∷ ctxR C)} {Y = 𝒰ℱ (tyR d)} N' ⟦ M' ⟧C N'≈M') ,
     bind-sq (ctx C) (rel c) (F-rel (rel d)) sq

-- Computations
⟦ reflexive {M = M} ⟧C⊑ =
  ⟦ M ⟧C , C-refl-≈ M ⟦ M ⟧C , ⟦ M ⟧C , C-refl-≈ M ⟦ M ⟧C ,
  λ x y r → ⟦ M ⟧C .isMon (ctx-refl-to _ r)
⟦ _[_]∙ {C = C} {c = c} {d = d} {E = E} {E' = E'} {M = M} {M' = M'} e m ⟧C⊑ =
  let (NE , E≈ , NE' , E'≈ , sq₁) = ⟦ e ⟧E⊑
      (NM , M≈ , NM' , NM'≈ , sq₂) = ⟦ m ⟧C⊑
  in plugE NE NM ,
     plug-≈ {Γ = 𝒞 (ctxL C)} {Bᵢ = ℱ (tyL c)} {Bₒ = ℱ (tyL d)}
       {E = ⟦ E ⟧E} {E₂ = NE} {M = ⟦ M ⟧C} {M₂ = NM} E≈ M≈ ,
     plugE NE' NM' ,
     plug-≈ {Γ = 𝒞 (ctxR C)} {Bᵢ = ℱ (tyR c)} {Bₒ = ℱ (tyR d)}
       {E = NE'} {E₂ = ⟦ E' ⟧E} {M = NM'} {M₂ = ⟦ M' ⟧C}
       (≈mon-sym {X = 𝒰ℱ (tyR c)} {Y = U-ob (𝒜 (ctxR C) (tyR d))} (⟦ E' ⟧E .f) (NE' .f) E'≈) NM'≈ ,
     plug-sq (ctx C) (F-rel (rel c)) (F-rel (rel d)) {E = NE} {E' = NE'} {M = NM} {M' = NM'} sq₁ sq₂
⟦ _[_]c {C = C} {c = c} {M = M} {M' = M'} {D = D} {γ = γ} {γ' = γ'} m s ⟧C⊑ =
  let (NM , M≈ , NM' , NM'≈ , sq₁) = ⟦ m ⟧C⊑
      (Nγ , γ≈ , Nγ' , γ'≈ , sq₂) = ⟦ s ⟧S⊑
  in NM ∘p Nγ ,
     ≈mon-comp {X = 𝒞 (ctxL D)} {Y = 𝒞 (ctxL C)} {Z = 𝒰ℱ (tyL c)}
       {f = ⟦ γ ⟧S} {g = Nγ} {f' = ⟦ M ⟧C} {g' = NM} γ≈ M≈ ,
     NM' ∘p Nγ' ,
     ≈mon-comp {X = 𝒞 (ctxR D)} {Y = 𝒞 (ctxR C)} {Z = 𝒰ℱ (tyR c)}
       {f = Nγ'} {g = ⟦ γ' ⟧S} {f' = NM'} {g' = ⟦ M' ⟧C}
       (≈mon-sym {X = 𝒞 (ctxR D)} {Y = 𝒞 (ctxR C)} ⟦ γ' ⟧S Nγ' γ'≈) NM'≈ ,
     CompSqV {c₁ = ctx D} {c₂ = ctx C} {c₃ = U-rel (F-rel (rel c))} sq₂ sq₁
⟦ err {c = c} ⟧C⊑ =
  ℧-mor , ≈reflO ⟦ [] ⟧ctx (SemTypes.F ⟦ tyL c ⟧ty) ℧-mor ,
  ℧-mor , ≈reflO ⟦ [] ⟧ctx (SemTypes.F ⟦ tyR c ⟧ty) ℧-mor ,
  λ _ _ _ → F-rel (rel c) .ErrorDomRel.R℧ _
⟦ ret {c = c} ⟧C⊑ =
  η-mor ∘p π2 , ≈reflO ⟦ tyL c ∷ [] ⟧ctx (SemTypes.F ⟦ tyL c ⟧ty) (η-mor ∘p π2) ,
  η-mor ∘p π2 , ≈reflO ⟦ tyR c ∷ [] ⟧ctx (SemTypes.F ⟦ tyR c ⟧ty) (η-mor ∘p π2) ,
  λ _ _ p → η-sq (rel c) _ _ (p .snd)
⟦ app {c = c} {d = d} ⟧C⊑ =
  ⟦ app ⟧C , ≈reflO ⟦ tyL c ∷ (tyL c ⇀ tyL d) ∷ [] ⟧ctx (SemTypes.F ⟦ tyL d ⟧ty) ⟦ app ⟧C ,
  ⟦ app ⟧C , ≈reflO ⟦ tyR c ∷ (tyR c ⇀ tyR d) ∷ [] ⟧ctx (SemTypes.F ⟦ tyR d ⟧ty) ⟦ app ⟧C ,
  λ _ _ ((_ , α) , q) → α _ _ q
⟦ matchNat {C = C} {c = c} {Kz = Kz} {Kz' = Kz'} {Ks = Ks} {Ks' = Ks'} z s ⟧C⊑ =
  let (Nz , z≈ , Nz' , Nz'≈ , sq₁) = ⟦ z ⟧C⊑
      (Ns , s≈ , Ns' , Ns'≈ , sq₂) = ⟦ s ⟧C⊑
  in natCase Nz Ns ,
     natCase-≈ {Γ = 𝒞 (ctxL C)} {B = 𝒰ℱ (tyL c)}
       {z = ⟦ Kz ⟧C} {z' = Nz} {s = ⟦ Ks ⟧C} {s' = Ns} z≈ s≈ ,
     natCase Nz' Ns' ,
     natCase-≈ {Γ = 𝒞 (ctxR C)} {B = 𝒰ℱ (tyR c)}
       {z = Nz'} {z' = ⟦ Kz' ⟧C} {s = Ns'} {s' = ⟦ Ks' ⟧C} Nz'≈ Ns'≈ ,
     natCase-sq (ctx C) (U-rel (F-rel (rel c))) sq₁ sq₂
⟦ err⊥ {M = M} ⟧C⊑ =
  ℧-mor ∘p UnitP! , C-refl-≈ M (℧-mor ∘p UnitP!) , ⟦ M ⟧C , C-refl-≈ M ⟦ M ⟧C ,
  λ _ y _ → F-rel (idPRel _) .ErrorDomRel.R℧ (⟦ M ⟧C .f y)

-- Equivalent type precision derivations: the quasi-order-equivalence
-- gives perturbations δ₁, δ₁' and a square between the two relations,
-- lifted through U ∘ F.
⟦ EquivTyPrec {C = C} {c = c} {M = M} {M' = M'} {c' = c'} m q ⟧C⊑ =
  let (N , M≈N , N' , N'≈M' , sq) = ⟦ m ⟧C⊑
      e = ⟦ q ⟧ty⊑-≈
      p₁  = interpV ⟦ tyL c ⟧ty .fst (QuasiOrderEquivV.δ₁ e)
      p₁' = interpV ⟦ tyR c ⟧ty .fst (QuasiOrderEquivV.δ₁' e)
      |Γ|  = ValType→Predomain ⟦ ctxL C ⟧ctx
      |Γ'| = ValType→Predomain ⟦ ctxR C ⟧ctx
      UFS = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyL c ⟧ty))
      UFT = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyR c ⟧ty))
  in U-mor (F-mor (p₁ .fst)) ∘p N ,
     ≈mon-comp {X = |Γ|} {Y = UFS} {Z = UFS}
       {f = ⟦ M ⟧C} {g = N} {f' = Id} {g' = U-mor (F-mor (p₁ .fst))}
       M≈N (≈mon-sym {X = UFS} {Y = UFS} (U-mor (F-mor (p₁ .fst))) Id
              (F-SemPtb {A = ValType→Predomain ⟦ tyL c ⟧ty} p₁ .snd)) ,
     U-mor (F-mor (p₁' .fst)) ∘p N' ,
     ≈mon-comp {X = |Γ'|} {Y = UFT} {Z = UFT}
       {f = N'} {g = ⟦ M' ⟧C} {f' = U-mor (F-mor (p₁' .fst))} {g' = Id}
       N'≈M' (F-SemPtb {A = ValType→Predomain ⟦ tyR c ⟧ty} p₁' .snd) ,
     CompSqV {c₁ = ctx C} {c₂ = U-rel (F-rel (rel c))} {c₃ = U-rel (F-rel (rel c'))}
       sq (UF-sq (rel c) (rel c') (p₁ .fst) (p₁' .fst) (QuasiOrderEquivV.sq-c-c' e))

-- UpL: the embedding e of c, against the perturbation δr of c pushed
-- along d.
⟦ UpL {C = C} {c = c} {d = d} {M = M} {M' = M'} m ⟧C⊑ =
  let (N , M≈N , N' , N'≈M' , sq) = ⟦ m ⟧C⊑
      ρc = ⟦ c ⟧ty⊑ .snd .fst
      e  = embV ⟦ tyL c ⟧ty ⟦ tyR c ⟧ty (rel c) ρc
      δr = δreV ⟦ tyL c ⟧ty ⟦ tyR c ⟧ty (rel c) ρc
      iδr = interpV ⟦ tyR c ⟧ty .fst δr
      p' = interpV ⟦ tyR d ⟧ty .fst (pushV (⟦ d ⟧ty⊑ .fst) .fst δr)
      |Γ|  = ValType→Predomain ⟦ ctxL C ⟧ctx
      |Γ'| = ValType→Predomain ⟦ ctxR C ⟧ctx
      UFS = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyL c ⟧ty))
      UFT = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyR c ⟧ty))
      UFU = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyR d ⟧ty))
  in U-mor (F-mor e) ∘p N ,
     subst (λ h → _≈mon_ {X = |Γ|} {Y = UFT} h (U-mor (F-mor e) ∘p N)) (sym (upC-eq c M))
       (≈mon-comp {X = |Γ|} {Y = UFS} {Z = UFT}
         {f = ⟦ M ⟧C} {g = N} {f' = U-mor (F-mor e)} {g' = U-mor (F-mor e)}
         M≈N (≈mon-refl (U-mor (F-mor e)))) ,
     U-mor (F-mor (p' .fst)) ∘p N' ,
     ≈mon-comp {X = |Γ'|} {Y = UFU} {Z = UFU}
       {f = N'} {g = ⟦ M' ⟧C} {f' = U-mor (F-mor (p' .fst))} {g' = Id}
       N'≈M' (F-SemPtb {A = ValType→Predomain ⟦ tyR d ⟧ty} p' .snd) ,
     CompSqV {c₁ = ctx C} {c₂ = U-rel (F-rel (rel c ⊙ rel d))} {c₃ = U-rel (F-rel (rel d))}
       sq (UF-sq (rel c ⊙ rel d) (rel d) e (p' .fst)
            (UpL-sq (rel c) (rel d) {e = e} {δ = iδr .fst} {δ' = p' .fst}
              (UpLV ⟦ tyL c ⟧ty ⟦ tyR c ⟧ty (rel c) ρc) (pushVSq (⟦ d ⟧ty⊑ .fst) δr)))

-- UpR: the perturbation δl of d pulled along c, against the embedding
-- of d.
⟦ UpR {C = C} {c = c} {M = M} {M' = M'} {d = d} m ⟧C⊑ =
  let (N , M≈N , N' , N'≈M' , sq) = ⟦ m ⟧C⊑
      ρd = ⟦ d ⟧ty⊑ .snd .fst
      e  = embV ⟦ tyL d ⟧ty ⟦ tyR d ⟧ty (rel d) ρd
      δl = δleV ⟦ tyL d ⟧ty ⟦ tyR d ⟧ty (rel d) ρd
      iδl = interpV ⟦ tyL d ⟧ty .fst δl
      p₁ = interpV ⟦ tyL c ⟧ty .fst (pullV (⟦ c ⟧ty⊑ .fst) .fst δl)
      |Γ|  = ValType→Predomain ⟦ ctxL C ⟧ctx
      |Γ'| = ValType→Predomain ⟦ ctxR C ⟧ctx
      UFS = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyL c ⟧ty))
      UFT = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyL d ⟧ty))
      UFU = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyR d ⟧ty))
  in U-mor (F-mor (p₁ .fst)) ∘p N ,
     ≈mon-comp {X = |Γ|} {Y = UFS} {Z = UFS}
       {f = ⟦ M ⟧C} {g = N} {f' = Id} {g' = U-mor (F-mor (p₁ .fst))}
       M≈N (≈mon-sym {X = UFS} {Y = UFS} (U-mor (F-mor (p₁ .fst))) Id
              (F-SemPtb {A = ValType→Predomain ⟦ tyL c ⟧ty} p₁ .snd)) ,
     U-mor (F-mor e) ∘p N' ,
     subst (λ h → _≈mon_ {X = |Γ'|} {Y = UFU} (U-mor (F-mor e) ∘p N') h) (sym (upC-eq d M'))
       (≈mon-comp {X = |Γ'|} {Y = UFT} {Z = UFU}
         {f = N'} {g = ⟦ M' ⟧C} {f' = U-mor (F-mor e)} {g' = U-mor (F-mor e)}
         N'≈M' (≈mon-refl (U-mor (F-mor e)))) ,
     CompSqV {c₁ = ctx C} {c₂ = U-rel (F-rel (rel c))} {c₃ = U-rel (F-rel (rel c ⊙ rel d))}
       sq (UF-sq (rel c) (rel c ⊙ rel d) (p₁ .fst) e
            (UpR-sq (rel c) (rel d) {δ₁ = p₁ .fst} {δ₂ = iδl .fst} {e = e}
              (pullVSq (⟦ c ⟧ty⊑ .fst) δl) (UpRV ⟦ tyL d ⟧ty ⟦ tyR d ⟧ty (rel d) ρd)))

-- DnL: the projection p of F c, against its perturbation δr pushed
-- along F d, then lax functoriality of F.
⟦ DnL {C = C} {d = d} {M = M} {M' = M'} {c = c} m ⟧C⊑ =
  let (N , M≈N , N' , N'≈M' , sq) = ⟦ m ⟧C⊑
      ρc = ⟦ c ⟧ty⊑ .snd .snd
      p  = projC (SemTypes.F ⟦ tyL c ⟧ty) (SemTypes.F ⟦ tyR c ⟧ty) (F-rel (rel c)) ρc
      δr = δrpC (SemTypes.F ⟦ tyL c ⟧ty) (SemTypes.F ⟦ tyR c ⟧ty) (F-rel (rel c)) ρc
      iδr = interpC (SemTypes.F ⟦ tyR c ⟧ty) .fst δr
      p' = interpC (SemTypes.F ⟦ tyR d ⟧ty) .fst (pushC (Rel.F ⟦ d ⟧ty⊑ .fst) .fst δr)
      |Γ|  = ValType→Predomain ⟦ ctxL C ⟧ctx
      |Γ'| = ValType→Predomain ⟦ ctxR C ⟧ctx
      UFS = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyL c ⟧ty))
      UFT = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyR c ⟧ty))
      UFU = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyR d ⟧ty))
  in U-mor p ∘p N ,
     ≈mon-comp {X = |Γ|} {Y = UFT} {Z = UFS}
       {f = ⟦ M ⟧C} {g = N} {f' = U-mor p} {g' = U-mor p} M≈N (≈mon-refl (U-mor p)) ,
     U-mor (p' .fst) ∘p N' ,
     ≈mon-comp {X = |Γ'|} {Y = UFU} {Z = UFU}
       {f = N'} {g = ⟦ M' ⟧C} {f' = U-mor (p' .fst)} {g' = Id} N'≈M' (p' .snd) ,
     CompSqV {c₁ = ctx C} {c₂ = U-rel (F-rel (rel d))} {c₃ = U-rel (F-rel (rel c ⊙ rel d))}
       sq (U-sq (F-rel (rel d)) (F-rel (rel c ⊙ rel d)) p (p' .fst)
            (DnL-sq (rel c) (rel d) {p = p} {δ = iδr .fst} {δ' = p' .fst}
              (DnLC (SemTypes.F ⟦ tyL c ⟧ty) (SemTypes.F ⟦ tyR c ⟧ty) (F-rel (rel c)) ρc)
              (pushCSq (Rel.F ⟦ d ⟧ty⊑ .fst) δr)))

-- DnR: the quasi-equivalence F(c ⊙ d) ≈ F c ⊙ F d, the perturbation δl
-- of F d pulled along F c, and the projection of F d.
⟦ DnR {C = C} {c = c} {d = d} {M = M} {M' = M'} m ⟧C⊑ =
  let (N , M≈N , N' , N'≈M' , sq) = ⟦ m ⟧C⊑
      ρd = ⟦ d ⟧ty⊑ .snd .snd
      p  = projC (SemTypes.F ⟦ tyL d ⟧ty) (SemTypes.F ⟦ tyR d ⟧ty) (F-rel (rel d)) ρd
      δl = δlpC (SemTypes.F ⟦ tyL d ⟧ty) (SemTypes.F ⟦ tyR d ⟧ty) (F-rel (rel d)) ρd
      iδl = interpC (SemTypes.F ⟦ tyL d ⟧ty) .fst δl
      p₁ = interpC (SemTypes.F ⟦ tyL c ⟧ty) .fst (pullC (Rel.F ⟦ c ⟧ty⊑ .fst) .fst δl)
      eq = Fcc'≈FcFc' (⟦ c ⟧ty⊑ .fst) (⟦ d ⟧ty⊑ .fst) (⟦ c ⟧ty⊑ .snd .fst) (⟦ d ⟧ty⊑ .snd .fst)
      ε₁  = interpC (SemTypes.F ⟦ tyL c ⟧ty) .fst (QuasiOrderEquivC.δ₁ eq)
      ε₁' = interpC (SemTypes.F ⟦ tyR d ⟧ty) .fst (QuasiOrderEquivC.δ₁' eq)
      -- the predomains involved, in canonical form
      |Γ|  = ValType→Predomain ⟦ ctxL C ⟧ctx
      |Γ'| = ValType→Predomain ⟦ ctxR C ⟧ctx
      UFS = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyL c ⟧ty))
      UFT = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyL d ⟧ty))
      UFU = U-ob (CompType→ErrorDomain (SemTypes.F ⟦ tyR d ⟧ty))
      -- the two perturbations on the left compose to something ≈ id
      ptb≈ : (U-mor (p₁ .fst) ∘p U-mor (ε₁ .fst)) ≈mon (Id ∘p Id)
      ptb≈ = ≈mon-comp {X = UFS} {Y = UFS} {Z = UFS}
        {f = U-mor (ε₁ .fst)} {g = Id} {f' = U-mor (p₁ .fst)} {g' = Id} (ε₁ .snd) (p₁ .snd)
  in U-mor (p₁ .fst ∘ed ε₁ .fst) ∘p N ,
     ≈mon-comp {X = |Γ|} {Y = UFS} {Z = UFS}
       {f = ⟦ M ⟧C} {g = N} {f' = Id ∘p Id} {g' = U-mor (p₁ .fst) ∘p U-mor (ε₁ .fst)}
       M≈N (≈mon-sym {X = UFS} {Y = UFS} (U-mor (p₁ .fst) ∘p U-mor (ε₁ .fst)) (Id ∘p Id) ptb≈) ,
     U-mor (p ∘ed ε₁' .fst) ∘p N' ,
     ≈mon-comp {X = |Γ'|} {Y = UFU} {Z = UFT}
       {f = U-mor (ε₁' .fst) ∘p N'} {g = Id ∘p ⟦ M' ⟧C} {f' = U-mor p} {g' = U-mor p}
       (≈mon-comp {X = |Γ'|} {Y = UFU} {Z = UFU}
         {f = N'} {g = ⟦ M' ⟧C} {f' = U-mor (ε₁' .fst)} {g' = Id} N'≈M' (ε₁' .snd))
       (≈mon-refl (U-mor p)) ,
     CompSqV {c₁ = ctx C} {c₂ = U-rel (F-rel (rel c ⊙ rel d))} {c₃ = U-rel (F-rel (rel c))}
       sq (U-sq (F-rel (rel c ⊙ rel d)) (F-rel (rel c)) (p₁ .fst ∘ed ε₁ .fst) (p ∘ed ε₁' .fst)
            (DnR-sq (rel c) (rel d) {ε₁ = ε₁ .fst} {ε₁' = ε₁' .fst} {δ₁ = p₁ .fst} {δ₂ = iδl .fst} {p = p}
              (QuasiOrderEquivC.sq-d-d' eq) (pullCSq (Rel.F ⟦ c ⟧ty⊑ .fst) δl)
              (DnRC (SemTypes.F ⟦ tyL d ⟧ty) (SemTypes.F ⟦ tyR d ⟧ty) (F-rel (rel d)) ρd)))
