# Remaining perturbation-related work

Status of the perturbation-related definitions and lemmas of the paper
*Denotational Semantics of Gradual Typing using Synthetic Guarded Domain
Theory* (arXiv:2411.12822v2, extended version with appendix) in this
formalization.

- Generated on 2026-10-02 from the working tree at commit `8b33ef3`
  (Agda 2.8.0, cubical-0.9). Updated 2026-10-04 after completing the
  Definition B.3 laws in `Semantics/Concrete/Predomain/Kleisli.agda` and
  Definitions D.5 and D.6 in `Semantics/Concrete/Perturbation/Kleisli.agda`
  and `Semantics/Concrete/Perturbation/Semantic.agda`, Lemmas D.14 and
  D.15 in `Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda`,
  and Definition D.17 in `Semantics/Concrete/Relations/Constructions.agda`.
- Paths are relative to `formalizations/guarded-cubical`.
- "Hole" means an interaction hole `{! !}` in live (non-commented) code.
  Agda prints no warning for these when `--allow-unsolved-metas` is on, so a
  clean build of `Results.agda` does not imply completeness.
- Numbering follows the arXiv version. Section 6.3 of the paper lists
  item (1) below, "showing that the functors × and → preserve
  quasi-representability", as remaining work; most entries here are pieces of
  that item.

## Summary

| Paper result | Topic | Status | Location |
|---|---|---|---|
| App. D.1/D.2 (unnumbered) | `Σ-SemPtb-eq`, `Σ-SemPtb-ind` | 4 holes, unused | `Semantics/Concrete/Perturbation/Semantic.agda:762,782,788,790` |
| Lemma D.7 | Same embedding (values) / same projection (computations) cases | not started, unused | `Semantics/Concrete/Perturbation/QuasiRepresentation/QuasiEquivalence.agda` |
| Lemma D.9 | Computation half; identity computation relation | not started | `Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda`, `Semantics/Concrete/Relations/Constructions.agda` |
| Lemma D.18 | Quasi-order-equivalence of functors with composition | not started | `Semantics/Concrete/Relations/Base.agda:91,103` |
| Def. D.16 | Composition of computation relations | not started, ingredients exist | `Semantics/Concrete/Relations/Constructions.agda` |
| (outside paper) | `π1` as a value morphism with perturbation action | 2 holes, unused | `Semantics/Concrete/Types/Morphism.agda:227-228` |

## Appendix B: Kleisli actions

### Definition B.3, Kleisli action of products (done 2026-10-04)

The identity, composition and square-preservation laws of `_×Kᴸ_` and
`_×Kᴿ_` (`KlProdMorphismᴸ-Id/-Comp/-Sq`, `KlProdMorphismᴿ-Id/-Comp/-Sq`) are
now proved in `Semantics/Concrete/Predomain/Kleisli.agda`, which no longer
needs `--allow-unsolved-metas`. The proofs use two private helpers in that
file: squares for `SwapPair`/`Curry`/`Uncurry`, and `StrongExt-ED`, the
fibre of the strong extension at a fixed parameter packaged as an error
domain morphism. Lemma D.14 part 2 is therefore no longer blocked on this.

- A parallel attempt in `Semantics/Concrete/Predomain/KleisliOpaque.agda`
  (loaded by nothing) still has 12 holes, including the three ᴿ product laws
  at lines 461, 469 and 492, and lemmas `EDMor∘δ*`, `EDMor∘δ*⊑`, `KlProd∘δ*`
  (lines 554 to 586) stating that error domain morphisms commute with `δ`.
  That commutation is the fact the appendix cites in prose for the coherence
  results of Definition D.5.

Definitions B.1, B.2 and B.3 are thus complete, including identity,
composition and square laws, in `Semantics/Concrete/Predomain/Kleisli.agda`.

## Appendix D.2: lemmas about perturbations

### Definition D.5, Kleisli arrow action on syntactic perturbations (done 2026-10-04)

The two monoid homomorphisms `Kl-Arrow-Ptb-L` and `Kl-Arrow-Ptb-R`
(`Semantics/Concrete/Perturbation/Kleisli.agda`) and the coherence property
stated in prose after Definition D.6 (interpreting `id ⟶k m` equals the
Kleisli action applied to the interpretation of `m`) are complete in both
directions: `⟶Kᴸ-lemma` and `⟶Kᴿ-lemma` in the same file. The semantic
arrow actions `⟶KB-SemPtb` and `A⟶K-SemPtb`
(`Semantics/Concrete/Perturbation/Semantic.agda`) are both complete semantic
perturbations in the sense of Definition 5.5. The module
`Semantics/Concrete/Perturbation/Kleisli.agda` no longer needs
`--allow-unsolved-metas`.

### Definition D.6, Kleisli product action on syntactic perturbations (done 2026-10-04)

`Kl-Prod-Ptb-L` and `Kl-Prod-Ptb-R`
(`Semantics/Concrete/Perturbation/Kleisli.agda`) are the homomorphisms of the
definition, and `×Kᴸ-lemma` and `×Kᴿ-lemma` are the corresponding coherence
properties with the semantic product actions `×KA-SemPtb` and `A×K-SemPtb`
(`Semantics/Concrete/Perturbation/Semantic.agda`). The semantic actions are
monoid homomorphisms by the laws of Definition B.3; the coherence proofs use
`KlProdᴸ-δ*`/`KlProdᴿ-δ*` (the product actions commute with `δ*`) and
`KlProdᴸ-F`/`KlProdᴿ-F` (they turn `F-mor f` into `F-mor (f × id)` resp.
`F-mor (id × f)`), all in `Semantics/Concrete/Predomain/Kleisli.agda`.

### Unnumbered auxiliary lemmas on sigma-type perturbations (Appendix D.1, D.2)

`Σ-SemPtb-eq` and `Σ-SemPtb-ind` in
`Semantics/Concrete/Perturbation/Semantic.agda` have holes at lines 762, 782,
788 and 790; they are the only remaining holes in that module. Nothing uses
them; the dynamic type goes through `Σ-SemPtb` itself, which is complete.

### Complete in this section

Lemmas D.1 to D.4 (push-pull structures for composition, F and U, products,
arrows) are complete in
`Semantics/Concrete/Perturbation/Relation/Constructions.agda`. Two abandoned
attempts remain there as block comments and contain holes: a push-pull
structure for indexed sums (lines 428 to 505) and a generic injection-relation
construction (lines 741 to 801). Push-pull structures for Π and Σ types are
complete in `Relation/Constructions/Pi.agda` and `Sigma.agda` (not loaded by
`Results.agda`).

## Appendix D.3 and D.4: quasi-representability and relations

### Lemma D.7, relations represented by the same morphism are quasi-equivalent

Two of four cases are done in
`Semantics/Concrete/Perturbation/QuasiRepresentation/QuasiEquivalence.agda`:
computation relations with the same embedding (`eqEmb→quasiEquivC`, line 249)
and value relations with the same projection (`eqEmb→quasiEquivV`, line 358;
the name is misleading, the hypothesis is equality of projections). The two
remaining cases, value relations with the same embedding and computation
relations with the same projection, are absent. Nothing currently needs them.

### Lemma D.9, reflexive relations are quasi-representable

The value half is done (`LeftRepV-Id`, `RightRepV-Id` at
`Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda:90`
and `:94`). The computation half has no counterpart, and there is no identity
computation relation in `Semantics/Concrete/Relations/Constructions.agda`
(only `IdV`, line 98). The push-pull part `IdRelC` exists in
`Semantics/Concrete/Perturbation/Relation/Constructions.agda:105`.

### Lemma D.14, products preserve quasi-representability (done 2026-10-04)

Both parts are complete in
`Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda`:
`×-leftRep` (part 1, `c₁ × c₂` is quasi-left-representable) and
`×-F-rightRep` (part 2, `F (c₁ × c₂)` is quasi-right-representable). Part 2
follows the paper: the projection is the composite of the Kleisli product
actions of the two projections, the perturbations are the images of the
given ones under the Definition D.6 actions, and the squares are vertical
composites of the actions of `×Kᴸ` and `×Kᴿ` on squares (Definition B.3),
with the Definition D.6 coherence lemmas identifying the interpretation of
the composite syntactic perturbation.

### Lemma D.15, the arrow preserves quasi-representability (done 2026-10-04)

Both parts are complete in
`Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda`,
which no longer needs `--allow-unsolved-metas`: `RightRepArrow` (part 1,
`c ⟶ d` is quasi-right-representable) and `LeftRepUArrow` (part 2,
`U(c ⟶ d)` is quasi-left-representable). The squares are the functorial
actions of `⟶` and of the Kleisli arrow actions on squares; part 2 uses the
Definition D.5 coherence lemmas to identify the interpretation of the
composite syntactic perturbation with the composite of the Kleisli actions.
In both parts the squares come out stated for `r(A) ⟶ r(B)` rather than the
identity relation on the arrow type (the pointwise ordering); the two agree up
to reflexivity and transitivity of the ordering, and small conversions bridge
the gap.

### Lemma D.18, quasi-order-equivalence of functors with composition

Not formalized. `ValRel≈` and `CompRel≈`
(`Semantics/Concrete/Relations/Base.agda:91` and `:103`) define
quasi-equivalence of value and computation relations only as equality of
embeddings. The semantic validation of the type-precision equations
(`⟦_⟧ty⊑-≈` in `Syntax/FineGrained/Denotation/TypePrecision.agda`,
remaining-work item (2) of Section 6.3) is proved for five of the six
equations (symmetry, the two unit laws, associativity, and `⇀-refl`, the
last one via `U⟶F-Id-emb` in `Semantics/Concrete/Relations/Constructions.agda`).
The remaining equation `⇀-trans` cannot hold as an equality of embeddings:
the projection representing `F (c ⊙ c')` (`repFcFc'→repFcc'` in
`CompositionLemmaF.agda`) is the composite of the two projections conjugated
by perturbations, so the embeddings of `(c ⊙ c') ⇀ (d ⊙ d')` and
`(c ⇀ d) ⊙ (c' ⇀ d')` differ by perturbations. Proving it requires weakening
`ValRel≈` to the paper's quasi-order-equivalence (`QuasiOrderEquivV`), the
missing same-embedding case of Lemma D.7 for value relations, and this
lemma's cases for `U`, `F`, `⟶` and composition.

### Definition D.16, composition of computation relations

Value-relation composition `⊙V` is done
(`Semantics/Concrete/Relations/Constructions.agda:145`). The computation
version has no definition, although all three ingredients exist: the push-pull
structure `⊙C` (`Perturbation/Relation/Constructions.agda:161`),
`RightRepC-Comp` from Lemma D.10
(`Perturbation/QuasiRepresentation/Composition.agda:380`), and
`repUdUd'→repUdd'` from Lemma D.13
(`Perturbation/QuasiRepresentation/CompositionLemmaU.agda:122`).

### Definition D.17, functorial actions on value and computation relations (done 2026-10-04)

All four actions are defined in `Semantics/Concrete/Relations/Constructions.agda`,
which no longer needs `--allow-unsolved-metas`: `F` and `U` (already present),
and the new `_×_` on value relations and `_⟶_` from a value and a computation
relation to a computation relation. The product action combines the push-pull
structure of Lemma D.3 with `×-leftRep` and `×-F-rightRep` (Lemma D.14); the
arrow action combines the push-pull structure of Lemma D.4 with
`RightRepArrow` and `LeftRepUArrow` (Lemma D.15). These are the semantic
ingredients for `⟦ c ⇀ d ⟧ty⊑` and the context case `⟦ c ∷ C ⟧ctx⊑`
(`Syntax/FineGrained/Denotation/TypePrecision.agda`), which are now
defined; the interpretation of type precision derivations `⟦_⟧ty⊑` and of
context precision `⟦_⟧ctx⊑` is complete.

### Complete in this section

- Lemma D.8 (F and U preserve representability): `F-leftRep`, `F-rightRep`,
  `U-leftRep`, `U-rightRep` in
  `Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda`
  (lines 380 to 492).
- Lemma D.10 (composition preserves representability):
  `Semantics/Concrete/Perturbation/QuasiRepresentation/Composition.agda`.
- Lemma D.13 (composition for F and U):
  `Semantics/Concrete/Perturbation/QuasiRepresentation/CompositionLemmaF.agda`
  and `CompositionLemmaU.agda`.
- Lemmas D.11 and D.12 are not stated separately; they are discharged inside
  the two composition-lemma files through the same-embedding case of D.7.
- The three dynamic-type relations of Section 5.3.1 (`injNat`, `injTimes`,
  `injArr`) are complete as full value relations, including push-pull
  structure and both representabilities, in
  `Semantics/Concrete/Dyn/DynInstantiated.agda`.
- The perturbation monoids and their interpretations for all type constructors
  (Definition 5.5 instances) are complete in
  `Semantics/Concrete/Types/Constructions.agda`.

## Outside the paper

`Semantics/Concrete/Types/Morphism.agda` is an experimental notion of value
morphism carrying a perturbation action, not part of the paper's final
definitions. Its projection `π1` leaves two holes at lines 227 and 228. Nothing
loads this module.

## Dependency sketch

```
Def. B.3 laws (×Kᴸ/×Kᴿ functoriality, squares)  [done]
  └─> Lemma D.14 (2) [done] ──> Def. D.17 (× on relations) [done] ──> ⟦ c ∷ C ⟧ctx⊑ [done]

Def. D.5 coherence (⟶Kᴸ-lemma, ⟶Kᴿ-lemma) + ⟶KB-SemPtb bisimilarity  [done]
  └─> Lemma D.15 (2)  ─┐  [done]
Lemma D.15 (1) [done] ─┴─> Def. D.17 (⟶ on relations) [done] ──> ⟦ c ⇀ d ⟧ty⊑ [done]

Lemma D.18 + quasi-equivalence as ValRel≈ ──> ⟦ ⇀-trans ⟧ty⊑-≈ (the one remaining type precision equation)
```
