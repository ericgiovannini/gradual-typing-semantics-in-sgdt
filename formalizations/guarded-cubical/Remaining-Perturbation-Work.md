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
  Updated again on 2026-10-04 after completing Lemma D.7 and Lemma D.18 and
  redefining `ValRel≈`/`CompRel≈` as quasi-order-equivalence, which closes
  the last hole in `Syntax/FineGrained/Denotation/TypePrecision.agda`, and
  after completing the computation half of Lemma D.9 and Definition D.16.
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
| Lemma D.7 | Same embedding (values) / same projection (computations) cases | done 2026-10-04 | `Semantics/Concrete/Perturbation/QuasiRepresentation/QuasiEquivalence.agda:572,657` |
| Lemma D.9 | Computation half; identity computation relation | done 2026-10-04 | `Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda:120,124`, `Semantics/Concrete/Relations/Constructions.agda:114` |
| Lemma D.18 | Quasi-order-equivalence of functors with composition | done 2026-10-04 | `Semantics/Concrete/Relations/Constructions.agda:375-504` |
| Def. D.16 | Composition of computation relations | done 2026-10-04 | `Semantics/Concrete/Relations/Constructions.agda:182` |
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

### Lemma D.7, relations represented by the same morphism are quasi-equivalent (done 2026-10-04)

All four cases are in
`Semantics/Concrete/Perturbation/QuasiRepresentation/QuasiEquivalence.agda`:

- computation relations with the same embedding: `eqEmb→quasiEquivC` (line 248);
- value relations with the same projection: `eqEmb→quasiEquivV` (line 357;
  the name is historical, the hypothesis is equality of projections);
- computation relations with the same projection: `eqProj→quasiEquivC`
  (line 572), used by Lemma D.18;
- value relations with the same embedding: `eqEmbV→quasiEquivV` (line 657),
  used by the unit, associativity and `⇀-refl` cases of `⟦_⟧ty⊑-≈`.

The same file now also shows that quasi-order-equivalence is an equivalence
relation: `quasiEquivV-refl/sym/trans` (lines 391 to 425) and
`quasiEquivC-refl/sym/trans` (lines 450 to 484), with the perturbations of a
composite being the monoid products of the component perturbations. The
file no longer uses `--allow-unsolved-metas`.

### Lemma D.9, reflexive relations are quasi-representable (done 2026-10-04)

Both halves are in
`Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda`:
the value half (`LeftRepV-Id`, `RightRepV-Id`, lines 89 and 93) and the
computation half (`LeftRepC-Id`, `RightRepC-Id`, lines 120 and 124). In
each case the embedding and projection are the identity morphism, the
perturbations are the monoid unit, and the squares are identity squares
transported along the fact that the interpretation homomorphism preserves
the unit. The identity computation relation `IdC` (push-pull structure
`IdRelC`, right representation `RightRepC-Id`, left representation of
`U Id` via `U-leftRep`) is in `Semantics/Concrete/Relations/Constructions.agda`
at line 114, next to `IdV` (line 101).

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

### Lemma D.18, quasi-order-equivalence of functors with composition (done 2026-10-04)

`ValRel≈` and `CompRel≈` (`Semantics/Concrete/Relations/Base.agda:96` and
`:108`) are now the paper's quasi-order-equivalence of the underlying
relations (`QuasiOrderEquivV`, `QuasiOrderEquivC`) rather than equality of
embeddings. The lemma itself is in
`Semantics/Concrete/Relations/Constructions.agda`:

- `U-quasiEquiv` (line 375) and `⟶-quasiEquiv` (line 409): `U` and `⟶`
  preserve quasi-order-equivalence (the latter contravariantly in the value
  argument, with the perturbation of an arrow equivalence being the product of
  the two injected component perturbations).
- `Udd'≈UdUd'` (line 440) and `Fcc'≈FcFc'` (line 455): Lemmas D.12 and D.11
  as standalone statements, extracted from the two composition-lemma files.
- `⟶⊙≈⊙⟶` (line 476): `(c ⊙ c') ⟶ (d ⊙ d')` and `(c ⟶ d) ⊙ (c' ⟶ d')` are
  both right-represented by the projection `(e_c' ∘ e_c) ⟶ (p_d ∘ p_d')`, so
  they are quasi-order-equivalent by the same-projection case of Lemma D.7
  (the equality of projections is `refl` up to extensionality).
- `U⟶F-comp-equiv` (line 504): the chain
  `U(c ⟶ Fd) ⊙ U(c' ⟶ Fd') ≈ U((c ⟶ Fd) ⊙ (c' ⟶ Fd')) ≈ U((c ⊙ c') ⟶ (Fd ⊙ Fd')) ≈ U((c ⊙ c') ⟶ F(d ⊙ d'))`,
  assembled with `quasiEquivV-trans`.

With this, all six type-precision equations are validated in
`Syntax/FineGrained/Denotation/TypePrecision.agda` (`⟦_⟧ty⊑-≈`; `⇀-trans`
is `U⟶F-comp-equiv`), and that file no longer uses `--allow-unsolved-metas`.
The earlier obstacle, that the two sides of `⇀-trans` have different
embeddings (the projection representing `F (c ⊙ c')` is the composite of the
two projections conjugated by perturbations), is exactly why equality of
embeddings had to be weakened.

### Definition D.16, composition of computation relations (done 2026-10-04)

Both halves are in `Semantics/Concrete/Relations/Constructions.agda`:
value-relation composition `⊙V` (line 162) and computation-relation
composition `⊙C` (line 182). The latter assembles the push-pull structure
`RelPP.⊙C` (`Perturbation/Relation/Constructions.agda:161`, Lemma D.1),
`RightRepC-Comp` from Lemma D.10
(`Perturbation/QuasiRepresentation/Composition.agda:380`), and
`repUdUd'→repUdd'` from Lemma D.13
(`Perturbation/QuasiRepresentation/CompositionLemmaU.agda:122`), mirroring
`⊙V`. Together with `IdC` (line 115) the computation relations now have
identities and composition, matching the value relations.

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
- Lemmas D.11 and D.12 are stated as `Fcc'≈FcFc'` and `Udd'≈UdUd'` in
  `Semantics/Concrete/Relations/Constructions.agda` (also discharged inline in
  the two composition-lemma files through the same-embedding case of D.7).
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

Lemma D.7 (all cases) [done] ──> Lemma D.18 + quasi-equivalence as ValRel≈ [done] ──> ⟦ ⇀-trans ⟧ty⊑-≈ [done]
```
