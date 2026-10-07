# Plan: interpreting terms and term precision (`⟦_⟧C`, `⟦_⟧C⊑`)

Hole-by-hole plan for the two unfilled definitions that `Results.agda`
rests on:

- `Syntax/FineGrained/Denotation/Terms.agda`:
  `⟦_⟧C : Comp Γ S → ObliqueMor ⟦ Γ ⟧ctx (F ⟦ S ⟧ty)`, body `{!!}`.
- `Syntax/FineGrained/Denotation/TermPrecision.agda`:
  `⟦_⟧C⊑ : Comp⊑ C c M M' → ObliqueExtSq ⟦ C ⟧ctx⊑ (F ⟦ c ⟧ty⊑) ⟦ M ⟧C ⟦ M' ⟧C`,
  body `{!!}`.

Both modules hide the holes with `--allow-unsolved-metas`. The signatures
date from June and July 2024 and the bodies have never been filled. They
correspond to the paper's Section 5.3 (term semantics, Figure
"Semantics of casts") and Section 6.4.3 ("Interpreting Term Precision:
Extensional Squares") of arXiv 2411.12822; the LaTeX source is at
`<scratchpad>/gtt-src/concrete-term-model.tex` and
`concrete-relational-model.tex` for this session only.

Written 2026-10-06 against `main` at `e1fcdc2`.

**Status (2026-10-06): implemented.** Decisions taken: P1 by dropping
`matchDyn` in favour of the downcasts (option two) and adding
`injectTimes`; P2 by replacing `up-L` and `retraction` with UpL, UpR, DnL,
DnR and EquivTyPrec. The combinators are in
`Syntax/FineGrained/Denotation/Combinators.agda` and the square lemmas in
`Syntax/FineGrained/Denotation/Squares.agda`; `⟦_⟧C` and `⟦_⟧C⊑` are
complete and `Results.agda` builds with the unsolved-metas pragma removed
from the whole `Denotation/` tree, `ExtensionalModel.agda` and
`Relations/Base.agda`. Two deviations from the plan below: the square for
`app` is stated inline rather than through a lemma, and every bisimilarity
lemma application gives its predomain and morphism arguments explicitly
(inferring them makes Agda η-expand record metavariables and conversion
checking then does not terminate in practice). The H2 `dynCase`
combinator was not needed since `matchDyn` was dropped.

---

## 0. Summary

**Shape of the work.** Four mutually recursive interpretation functions
over the quotiented fine-grained syntax (`Subst`, `Val`, `Comp`, `EvCtx`:
about 45 point constructors and 30 path constructors), then four
mutually recursive functions over the precision judgments (`Subst⊑`,
`Val⊑`, `EvCtx⊑`, `Comp⊑`: about 25 rules) producing extensional
squares. Almost every path constructor is discharged by a definitional
unfolding or by an existing monad or category law; the real content is
in a handful of semantic combinators that do not exist yet (Section 3)
and in the cast rules (Section 5).

**Two blockers in the syntax, to decide before coding** (Section 1):

1. The path constructor `matchDynβf` in `Terms.agda` is not validated by
   the intended model: eliminating the function case of `Dyn` must insert
   a delay `θ ∘ next`, which is only *bisimilar* to the identity, not
   equal. It has to become a term-precision or bisimilarity rule.
2. `Order.agda` does not contain the paper's cast rules UpL, UpR, DnL,
   DnR and EquivTyPrec; it has a weaker `up-L` and a `retraction` axiom
   stating `M ⊑ up c (dn c M)`, which appears unsound in the model
   (`up (dn y)` errors when `y` is outside the image, and `y ⊑ ℧` fails).
   The paper removed retraction for exactly this reason.

**Effort.** Combinators S to M (the `Dyn` case analysis is the only hard
one); `⟦_⟧` functions L; `⟦_⟧⊑` functions L. In total about the size of
the quasi-representability layer, 2,000 to 3,000 lines, plus the syntax
edits.

**Gate.** `Results.agda` builds with `--allow-unsolved-metas` removed from
`Denotation/Terms.agda`, `Denotation/TermPrecision.agda` and
`Semantics/Concrete/ExtensionalModel.agda`, so that `Graduality` is
certified end to end.

---

## 1. Syntax decisions (do first)

**P1. `matchDynβf`.** `Terms.agda` has
`matchDynβf : matchDyn Kn Kf [ ids ,s injectArr [ !s ,s V ]v ]c ≡ Kf [ ids ,s V ]c`.
Semantically `⟦injectArr⟧ = e_{Inj→} ∘ next` lands in the `▹ U(D ⟶ F D)`
summand of `D`, so `⟦matchDyn Kn Kf⟧` on that summand can only produce
`θ (λ t. ⟦Kf⟧ (γ, f̃ t))`, and the left side denotes `δ (⟦Kf⟧ (γ, ⟦V⟧ γ))`.
That equals the right side only up to `≈`. The header comment of
`Terms.agda` already states the design rule ("we do not quotient by
order equivalence, because this maps only to bisimilarity"); `matchDynβf`
violates it. Options:

- (recommended) remove `matchDynβf` from `Comp` and add two `Comp⊑`
  axioms `matchDynβf-l` / `matchDynβf-r` relating the two sides in both
  directions at `refl-⊑`; these are validated by extensional squares with
  `N = δ ∘ ⟦Kf…⟧ ≈ ⟦Kf…⟧` and an identity square;
- or drop `matchDyn` altogether and express dynamic-type elimination
  through `dn inj-nat` and `dn inj-arr` plus `matchNat`, as the paper's
  syntax does (it has no `matchDyn`). This loses nothing the paper
  proves but changes `Terms.agda` more.

`matchDynβn` and `matchDynSubst` are fine (strict in the model).

**P2. Term precision rules.** Replace, in `Order.agda`:

- `up-L : Val⊑ (c ∷ []) refl-⊑ (up (mkTyPrec c)) var` by the paper's
  four rules in composite form, so that no transitivity is needed:
  ```
  UpL : Comp⊑ C (trans-⊑ c c_r) M M'  → Comp⊑ C c_r (upE c [ M ]∙) M'
  UpR : Comp⊑ C c_l M M'              → Comp⊑ C (trans-⊑ c_l c) M (upE c [ M' ]∙)
  DnL : Comp⊑ C c_r M M'              → Comp⊑ C (trans-⊑ c c_r) (dn c [ M ]∙) M'
  DnR : Comp⊑ C (trans-⊑ c_l c) M M'  → Comp⊑ C c_l M (dn c [ M' ]∙)
  ```
  (value-level variants for `up` as a `Val` are derivable through
  `ret'`; keep `up-L` only if something downstream uses it; nothing in
  the closure does). The present `up-L` cannot derive UpL because moving
  from relation `c` to `c c_r` needs heterogeneous transitivity, which
  the judgment deliberately lacks.
- `retraction` by nothing: `up c (dn c M) ⊑ M` is derivable from DnL and
  UpL, and `dn c (up c M) ≈ M` is a bisimilarity fact, not a precision
  fact. If a retraction rule is wanted, it must be `Comp⊑` in both
  directions between `M` and `dn c (upE c [M])`, modeled by an extensional
  square using `δ ≈ id`.
- add `EquivTyPrec : Comp⊑ C c M M' → c ≈ c' → Comp⊑ C c' M M'` (the
  `≈` on derivations now has all eight cases interpreted).
- add the congruences the paper elides and the judgment lacks:
  `matchDyn`, `up`, `dn`, `injectN`, `injectArr` at a fixed derivation,
  and `_,s_`/`!s` already present. `reflexive` covers the rest.

**P3. Products at the term level** (pairs, `split`) are out of scope
here; they are item E2 of `Effects-Paper-Worklist.md`. The type-level
product cases added on 2026-10-06 do not affect `⟦_⟧C`.

---

## 2. Signatures and conventions

Contexts are right-nested products, newest variable on the right:
`⟦ S ∷ Γ ⟧ctx = ⟦ Γ ⟧ctx × ⟦ S ⟧ty`, `⟦ [] ⟧ctx = Unit`. So `var` is `π2`
and `wk` is `π1`.

```
⟦_⟧S : Subst Δ Γ    → ValMor ⟦ Δ ⟧ctx ⟦ Γ ⟧ctx
⟦_⟧V : Val Γ S      → ValMor ⟦ Γ ⟧ctx ⟦ S ⟧ty
⟦_⟧C : Comp Γ S     → ObliqueMor ⟦ Γ ⟧ctx (F ⟦ S ⟧ty)          -- = PMor ⟦Γ⟧ (U F ⟦S⟧)
⟦_⟧E : EvCtx Γ S T  → CompMor (F ⟦ S ⟧ty) (⟦ Γ ⟧ctx ⟶ F ⟦ T ⟧ty)
```
These are the types in the commented skeleton of `Denotation/Terms.agda`
(with `ObliqueMor` for computations, as `Results.agda` expects). An
evaluation context is a homomorphism out of `F S` into the arrow domain,
so strength is handled by `_⟶ob_` and no separate strength lemma is
needed.

Precision:
```
⟦_⟧S⊑ : Subst⊑ C D γ γ'  → ValExtSq  ⟦C⟧ctx⊑ ⟦D⟧ctx⊑ ⟦γ⟧S ⟦γ'⟧S
⟦_⟧V⊑ : Val⊑ C c V V'    → ValExtSq  ⟦C⟧ctx⊑ ⟦c⟧ty⊑ ⟦V⟧V ⟦V'⟧V
⟦_⟧E⊑ : EvCtx⊑ C c d E E' → CompExtSq (F ⟦c⟧ty⊑) (⟦C⟧ctx⊑ ⟶ F ⟦d⟧ty⊑) ⟦E⟧E ⟦E'⟧E
⟦_⟧C⊑ : Comp⊑ C c M M'   → ObliqueExtSq ⟦C⟧ctx⊑ (F ⟦c⟧ty⊑) ⟦M⟧C ⟦M'⟧C
```
`ValExtSq` and `CompExtSq` are `ValTypeSq` and `CompTypeSq` in
`Semantics/Concrete/ExtensionalModel.agda` (a pair of morphisms
bisimilar to the given ones plus a strict square between them);
`ObliqueExtSq` is in `Relations/Base.agda`. Note `≈mon` is reflexive and
symmetric but not transitive (`Predomain/Morphism.agda:257-261`), and
the extensional-square definitions are designed so that no transitivity
is ever needed: every rule produces fresh `N ≈ M`, `N' ≈ M'` by
`≈mon-comp` (`Morphism.agda:315`) and composes the strict squares.

---

## 3. Semantic combinators to add first

Put these in a new module `Syntax/FineGrained/Denotation/Combinators.agda`
(parameterized by the clock) unless noted, so that the library modules
are not rebuilt.

**H1. Natural-number case analysis.**
`natCase : PMor Γ B → PMor (Γ ×dp ℕ) B → PMor (Γ ×dp ℕ) B` with
`natCase z s (γ, 0) = z γ`, `natCase z s (γ, n+1) = s (γ, n)`.
`ℕ` is `flat`, so monotonicity and `≈`-preservation reduce to `cong`
along an equality of numbers (as in `flatRec`,
`Predomain/Constructions.agda:81`). Both computation rules are `refl`.
No such combinator exists. Effort S.

**H2. Case analysis on the dynamic type.** A predomain morphism
```
dynCase : PMor (Γ ×dp ℕ) B → PMor (Γ ×dp (D ×dp D)) B
        → PMor (Γ ×dp P▹ (U-ob (D ⟶ob F-ob D))) B → PMor (Γ ×dp D) B
```
with computation rules on the three embeddings `embV injNat`,
`embV injTimes`, `embV injArr` (the latter precomposed with `next`).
`DynInstantiated.agda` builds `D` as `Σ` over a discrete index of `Π`
types plus the later summand (`DynV≅DynV'`, `Iso-DynP-SumP` in
`ParameterizedDyn.agda:354`, `isoSum-Sigma`, and the two `ΣΠ` isos used
by `rel-Nat-Sigma`, `rel-D×D-Sigma`), so `dynCase` is assembled from
`Case'`/`_⊎-mor_` (`Predomain/Combinators.agda:124-135`) and the `Σ`/`Π`
eliminators behind those isos. The computation rules follow by
unfolding the same isos that define the three injections. This is the
only combinator with real technical risk; budget M. It is needed only
for `matchDyn`; if option two of P1 is taken (drop `matchDyn`), H2 is
not needed at all, because `dn inj-nat`/`dn inj-arr` are already
interpreted by the projections `projC` built in `DynInstantiated.agda`.

**H3. Kleisli composition of evaluation contexts.** For
`E : CompMor (F S) (Γ ⟶ F T)` and `E' : CompMor (F T) (Γ ⟶ F U)`,
`E' ∘E E : CompMor (F S) (Γ ⟶ F U)` with underlying function
`λ s γ → E' (E s γ) γ`. Construct the `ErrorDomMor` directly: `f℧` from
`E .f℧` (giving the constantly-`℧` arrow) then `E' .f℧`; `fθ` from
`E .fθ` pointwise in `γ` then `E' .fθ`. Identity `∙E` is
`λ s γ → s`, i.e. the constant arrow `K-arrow : ErrorDomMor B (Γ ⟶ob B)`
(also needed by H7). Laws `∘IdL`, `∘IdR`, `∘Assoc` are `eqEDMor _ _ refl`.
Effort S.

**H4. Plugging.** `plug : CompMor (F S) (Γ ⟶ F T) → ObliqueMor Γ (F S) → ObliqueMor Γ (F T)`,
`plug E M = App ∘p PairFun (U-mor E ∘p M) Id` (`App`, `PairFun` in
`Predomain/Combinators.agda:106-214`; `U-ob (Γ ⟶ob B)` is definitionally
`Γ ==> U-ob B`). `plugId`, `plugAssoc`, `substPlugDist` become `refl`.
Effort S.

**H5. Bind.** For `M : Comp (S ∷ Γ) T`, i.e. `⟦M⟧ : PMor (Γ ×dp S) (U F T)`:
`⟦ bind M ⟧E = ExtAsEDMorphism.Ext (Curry (⟦M⟧ ∘p SwapPair))` with
`Ext : PMor A (U-ob B) → ErrorDomMor (F-ob A) B` at `B = Γ ⟶ob F T`
(`FreeErrorDomain.agda:352`). `ret-β` and `ret-η` are then the two unit
laws `Equations.Ext-η` and `F-extensionality`
(`FreeErrorDomain.agda:363, 626`). Effort S.

**H6. Substitution into evaluation contexts.**
`⟦ E [ γ ]e ⟧E = (⟦γ⟧S ⟶mor IdE) ∘ed ⟦E⟧E` using the contravariant
action `_⟶mor_` of `ErrorDomain.agda`. The four substitution laws for
`EvCtx` are `eqEDMor _ _ refl` after `∘ed` associativity. Effort S.

**H7. Casts.** `⟦ up c ⟧V = embV _ _ _ (⟦c⟧ty⊑ .snd .fst) ∘p π2` and
`⟦ dn c ⟧E = K-arrow ∘ed projC _ _ _ (⟦c⟧ty⊑ .snd .snd)` where
`projC … : CompMor (F ⟦T⟧) (F ⟦S⟧)` is the projection of the right
representation of `F ⟦c⟧` (accessors in
`Perturbation/QuasiRepresentation.agda`). `injectN` and `injectArr` are
the same with `⟦ inj-nat ⟧ty⊑` and `⟦ inj-arr ⟧ty⊑` (the latter's
embedding is `e_{injArr} ∘ next` because `⟦inj-arr⟧ = Next ⊙ injArr`).
Note the paper's Section 6 observation: the projection of a composite
`c c'` obtained from `repFcFc'→repFcc'` contains a perturbation, so
`⟦dn (c c')⟧ ≠ ⟦dn c⟧ ∘ ⟦dn c'⟧` strictly; this is fine because
`Terms.agda` has no cast-composition equations (they were removed from
the paper's syntax for exactly this reason). Effort S.

**H8. Unit.** `⟦ !s ⟧S = UnitP!` (`Predomain/Constructions.agda:113`);
`[]η` is `eqPMor _ _ refl` by the η rule for `Unit`.

**H9. `F` preserves quasi-order-equivalence.** `F-quasiEquiv`, the
analogue of `U-quasiEquiv` in `Relations/Constructions.agda:375`, built
with `F-sq`. Needed by EquivTyPrec (Section 5). Effort S.

---

## 4. `⟦_⟧`: clause by clause

Because every target (`PMor`, `ErrorDomMor`) is a set, each path
constructor needs a single equality between the denotations of its two
endpoints, written `⟦ p i ⟧ = lemma i`; the endpoints are definitionally
the denotations of the two sides by the point clauses. `Terms.agda` has
no set-truncation constructor, so there are no 2-dimensional cases.
"refl" below means `eqPMor _ _ refl` or `eqEDMor _ _ refl`.

### `⟦_⟧S` (substitutions)

| constructor | denotation | path discharged by |
|---|---|---|
| `ids` | `Id` | |
| `γ ∘s δ` | `⟦γ⟧ ∘p ⟦δ⟧` | |
| `∘IdL`, `∘IdR`, `∘Assoc` | | `CompPD-IdL/IdR/Assoc` (`Predomain/Morphism.agda`) |
| `!s` | `UnitP!` | |
| `[]η` | | refl (Unit η) |
| `γ ,s V` | `PairFun ⟦γ⟧ ⟦V⟧` | |
| `wk` | `π1` | |
| `wkβ` | | refl |
| `,sη` | | refl (Σ η) |

### `⟦_⟧V` (values)

| constructor | denotation | path discharged by |
|---|---|---|
| `V [ γ ]v` | `⟦V⟧ ∘p ⟦γ⟧` | |
| `substId`, `substAssoc` | | `CompPD-IdR`, `CompPD-Assoc` |
| `var` | `π2` | |
| `varβ` | | refl |
| `zro` | `K _ 0` | |
| `suc` | `mSuc ∘p π2` (`Combinators.agda:153`) | |
| `lda M` | `Curry ⟦M⟧` | |
| `fun-η` | | refl after `funExt`; uses `PMor` record η |
| `injectN` | `embV ⟦inj-nat⟧ty⊑ ∘p π2` | |
| `injectArr` | `embV ⟦inj-arr⟧ty⊑ ∘p π2` | |
| `up c` | `embV (⟦c⟧ty⊑ .snd .fst) ∘p π2` (H7) | |

### `⟦_⟧E` (evaluation contexts)

| constructor | denotation | path discharged by |
|---|---|---|
| `∙E` | `K-arrow` (H3) | |
| `E ∘E F` | H3 composition | |
| `∘IdL`, `∘IdR`, `∘Assoc` | | refl |
| `E [ γ ]e` | H6 | |
| `substId`, `substAssoc`, `∙substDist`, `∘substDist` | | refl |
| `bind M` | H5 | |
| `ret-η` | | `F-extensionality` + `Ext-η` |
| `dn c` | H7 | |

### `⟦_⟧C` (computations)

| constructor | denotation | path discharged by |
|---|---|---|
| `E [ M ]∙` | `plug ⟦E⟧ ⟦M⟧` (H4) | |
| `plugId`, `plugAssoc` | | refl |
| `M [ γ ]c` | `⟦M⟧ ∘p ⟦γ⟧` | |
| `substId`, `substAssoc`, `substPlugDist` | | refl / `CompPD-*` |
| `err` | `℧-mor` (`FreeErrorDomain.agda:273`) | |
| `strictness` | | `funExt λ γ → cong (apply γ) (⟦E⟧ .f℧)` |
| `ret` | `η-mor ∘p π2` | |
| `ret-β` | | `Ext-η` |
| `app` | `App ∘p (π2 ×mor Id)` modulo reassociation of `(Unit × U(S⟶FT)) × S` | |
| `fun-β` | | refl |
| `matchNat Kz Ks` | `natCase ⟦Kz⟧ ⟦Ks⟧` (H1) | |
| `matchNatβz`, `matchNatβs`, `matchNatη` | | refl, refl, `funExt` with a case split on the number |
| `matchDyn Kn Kf` | `dynCase ⟦Kn⟧ (℧ on pairs) (θ-case of ⟦Kf⟧)` (H2) | |
| `matchDynβn` | | computation rule of H2 on `embV injNat` |
| `matchDynβf` | **not provable**; see P1 | |
| `matchDynSubst` | | naturality of `dynCase` in `Γ`, refl |

The `θ`-case of `matchDyn` is `λ (γ, f̃) → θ (λ t → ⟦Kf⟧ (γ, f̃ t))`, a
predomain morphism because `θ` of the error domain `F ⟦S⟧` is monotone
and `≈`-preserving and `P▹` carries the pointwise-later structure.

---

## 5. `⟦_⟧⊑`: rule by rule

Common tools: `CompSqV`, `CompSqH`, `_×-Sq_`, `Predom-IdSqV/H`
(`Predomain/Square.agda`), `η-sq`, `Ext-sq`, `StrongExt-Sq`
(`FreeErrorDomain.agda:566-580`, `MonadCombinators.agda:259`), `U-sq`,
`F-sq`, `_⟶sq_`, the unit squares `sq-c-idA⊙c` and friends
(`ErrorDomain.agda`), and `≈mon-comp` for the bisimilarity components.
Two small lemmas are needed first:

- `ctx-refl-sq : (f : ValMor ⟦Δ⟧ ⟦Γ⟧) → PSq ⟦refl-⊑ctx Δ⟧ ⟦refl-⊑ctx Γ⟧ f f`,
  by induction on contexts, since `⟦refl-⊑ctx Γ⟧ctx⊑` is a product of
  identity relations and `PSq` on a product is componentwise; similarly
  for oblique and computation morphisms. Discharges every `reflexive`
  rule.
- `ptb≈id : ∀ δ → interpV A .fst δ .fst ≈mon Id` is just the second
  component of a semantic perturbation; used in every cast rule.

| rule | strict square | `≈` sides |
|---|---|---|
| `Subst⊑.!s`, `_ids_` | trivial / `Predom-IdSqV` | identities |
| `_,s_` | pairing of squares (`PairFun` square) | `≈mon-comp` on pairs |
| `_∘s_`, `Val⊑._[_]v`, `Comp⊑._[_]c`, `EvCtx⊑._[_]e` | `CompSqV` | `≈mon-comp` |
| `wk` | `π1` square (projection from `×pbmonrel`) | |
| `var` | `π2` square | |
| `zro`, `suc` | `flat` relations are equalities | |
| `lda` | `Sq-Curry` (private in `Predomain/Kleisli.agda`; make it public) | `Curry` preserves `≈mon` |
| `bind` | `Ext-sq` on `Curry (… ∘ SwapPair)` with `Sq-Curry`, `Sq-SwapPair` | `Ext` preserves `≈mon` (`strong-ext-pres≈`) |
| `∙E`, `_∘E_` | identity / composition of arrow-domain squares (H3 square lemma) | |
| `_[_]∙` | plugging preserves squares (H4 square lemma: `App` and `PairFun` squares) | |
| `err` | `℧` related to `℧` by `F-rel c` | |
| `err⊥` | `℧⊥` of the lock-step ordering | |
| `ret` | `η-sq` | |
| `app` | `App` square (U of the arrow relation is `c ==>pbmonrel U-rel d`) | |
| `matchNat` | `natCase` preserves squares (H1 square lemma) | |
| `matchDyn` | `dynCase` preserves squares (H2) with `θ`-congruence of `F-rel` | |
| `matchDynβf-l/r` (if P1 option one) | identity square | `δ* ≈ id` (`MonadCombinators.δ*≈id`) |
| `EquivTyPrec` | square between `i(δ₁) ∘ ⟦M⟧` and `i(δ₁') ∘ ⟦M'⟧` from `U-quasiEquiv (F-quasiEquiv ⟦c≈c'⟧)` (H9) composed with the given square | `ptb≈id` |
| `UpL` | see below | `N' = i(push_{c_r} δr_c) ∘ ⟦M'⟧ ≈ ⟦M'⟧` |
| `UpR` | `UpRV` of `⟦c⟧` pushed along `c_l` by `pullV` | `N = i(pull δl) ∘ ⟦M⟧` |
| `DnL` | `DnLC` of `F ⟦c⟧` pulled along `F ⟦c_r⟧` | `N' = i(…) ∘ ⟦M'⟧` |
| `DnR` | `DnRC` of `F ⟦c⟧` pushed along `F ⟦c_l⟧` | `N = i(…) ∘ ⟦M⟧` |

**The UpL square in detail** (paper, Section 6.4.3). Given the
extensional square for `M ⊑ M' : c c_r`, with fresh `N ≈ ⟦M⟧`,
`N' ≈ ⟦M'⟧` and strict `N ⊑[⟦C⟧ ; U F (c ⊙ c_r)] N'`: the output
relation of `⊙V` is relational composition, so for related inputs there
is a middle `y` with `x c y` and `y c_r z` (under `F`, through the free
composition `⊙ed`; use the fact that `F-rel (c ⊙ c_r)` is left-represented
by `e_{c_r} ∘ e_c`, i.e. the squares of `LeftRepV-Comp`). Then
`UpLV : PSq c r e_c (i δr_c)` gives `e_c x ⊑ i(δr_c) y`, and the push-pull
square of `c_r` (`pushV`, `VRelPtbSq` in `Perturbation/Relation/Base.agda:96,165`)
gives `i(δr_c) y c_r i(push δr_c) z`; downward closure of `c_r` yields
`e_c x c_r i(push δr_c) z`. Lift through `F`/`U` with `F-sq`, `U-sq` and
compose with the given square by `CompSqV`. The right morphism is
`i_{F}(push δr_c) ∘ N'`, which is `≈ ⟦M'⟧` by `ptb≈id` and `≈mon-comp`.
UpR, DnL, DnR are the same pattern with `UpRV`/`pullV` and
`DnLC`/`DnRC` with `pushC`/`pullC` on the computation relation
`F ⟦c⟧` (its push-pull structure comes from `RelPP.F`).

---

## 6. Order of work and gates

```
W0  Decide P1 and P2; edit Terms.agda and Order.agda accordingly.
    Gate: Results.agda still builds (nothing downstream matches on the
    removed constructors; Results uses only Comp⊑ at refl-⊑).
W1  Combinators H1, H3-H9 (new module); H2 only if matchDyn stays.
    Gate: the new module checks without the unsolved-metas pragma.
W2  ⟦_⟧S, ⟦_⟧V, ⟦_⟧E, ⟦_⟧C with all path cases.
    Gate: Denotation/Terms.agda checks with the pragma removed.
W3  ctx-refl-sq, ptb≈id, square lemmas for natCase/dynCase/plug/∘E.
W4  ⟦_⟧S⊑, ⟦_⟧V⊑, ⟦_⟧E⊑, ⟦_⟧C⊑: congruences first, then err⊥, ret,
    app, bind, then EquivTyPrec, then the four cast rules.
    Gate: TermPrecision.agda and ExtensionalModel.agda check with the
    pragma removed; Results.agda builds; Graduality has no hole below it.
W5  Update Remaining-Perturbation-Work.md (it does not list these holes)
    and the worklist.
```

Risks: H2 if `matchDyn` is kept; type-checking time of the mutually
recursive `⟦_⟧` with `--lossy-unification` (the 2024 commit message
reports "insanely slow type checking" for the signatures alone, so give
implicits explicitly as was done for the perturbation lemmas); and
universe levels, since `⟦c⟧ty⊑ : ValRel _ _ ℓ-zero` while the `Dyn`
relations are at a parameter `ℓ` instantiated to `ℓ-zero`.

---

## 7. Decisions needed from the user

1. P1: demote `matchDynβf` to a `Comp⊑` pair (recommended), or remove
   `matchDyn` in favour of the two downcasts.
2. P2: replace `up-L` and `retraction` by UpL/UpR/DnL/DnR and
   EquivTyPrec as in the paper (recommended), or keep them and accept
   that `retraction` cannot be interpreted.
