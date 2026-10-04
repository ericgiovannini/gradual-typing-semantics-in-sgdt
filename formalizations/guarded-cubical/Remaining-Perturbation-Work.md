# Remaining perturbation-related work

Status of the perturbation-related definitions and lemmas of the paper
*Denotational Semantics of Gradual Typing using Synthetic Guarded Domain
Theory* (arXiv:2411.12822v2, extended version with appendix) in this
formalization.

- Generated on 2026-10-02 from the working tree at commit `8b33ef3`
  (Agda 2.8.0, cubical-0.9). Updated 2026-10-04 after completing the
  Definition B.3 laws in `Semantics/Concrete/Predomain/Kleisli.agda`.
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
| Def. D.5 (+ prose after D.6) | Coherence of syntactic and semantic Kleisli arrow actions, left side | 4 holes | `Semantics/Concrete/Perturbation/Kleisli.agda:113-130` |
| Def. D.5 (+ prose after D.6) | Same, right side | commented out | `Semantics/Concrete/Perturbation/Kleisli.agda:146-159` |
| Def. 5.5 / Def. B.1 | `⟶KB-SemPtb` is bisimilar to the identity | 1 hole | `Semantics/Concrete/Perturbation/Semantic.agda:264` |
| Def. D.6 | Kleisli product action on syntactic perturbations | not started | `Semantics/Concrete/Perturbation/Kleisli.agda` (end of file) |
| App. D.1/D.2 (unnumbered) | `Σ-SemPtb-eq`, `Σ-SemPtb-ind` | 4 holes, unused | `Semantics/Concrete/Perturbation/Semantic.agda:729,749,755,757` |
| Lemma D.7 | Same embedding (values) / same projection (computations) cases | not started, unused | `Semantics/Concrete/Perturbation/QuasiRepresentation/QuasiEquivalence.agda` |
| Lemma D.9 | Computation half; identity computation relation | not started | `Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda`, `Semantics/Concrete/Relations/Constructions.agda` |
| Lemma D.14 (2) | `F(c₁ × c₂)` quasi-right-representable | not started (no longer blocked) | `Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda` |
| Lemma D.15 (1) | `c ⟶ d` quasi-right-representable | 2 holes, squares built | `Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda:655-700` |
| Lemma D.15 (2) | `U(c ⟶ d)` quasi-left-representable | 4 holes, partial | `Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda:767-825` |
| Lemma D.18 | Quasi-order-equivalence of functors with composition | not started | `Semantics/Concrete/Relations/Base.agda:91,103` |
| Def. D.16 | Composition of computation relations | not started, ingredients exist | `Semantics/Concrete/Relations/Constructions.agda` |
| Def. D.17 | Product and arrow actions on value/computation relations | not started, blocked | `Semantics/Concrete/Relations/Constructions.agda` |
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

### Definition D.5, Kleisli arrow action on syntactic perturbations

The two monoid homomorphisms exist: `Kl-Arrow-Ptb-L`
(`Semantics/Concrete/Perturbation/Kleisli.agda:74`) and `Kl-Arrow-Ptb-R`
(line 81). The coherence property stated in prose after Definition D.6
(interpreting `id ⟶k m` equals the Kleisli action applied to the
interpretation of `m`) is unproved in both directions:

- Left side: `⟶Kᴸ-lemma` (line 113) has four holes in lines 121 to 130. The
  natural-number case is an equational chain with three missing steps; the
  monoid case is a bare hole.
- Right side: `⟶Kᴿ-lemma` exists only inside a block comment, lines 146 to 159.
- The semantic action the left side refers to, `⟶KB-SemPtb`
  (`Semantics/Concrete/Perturbation/Semantic.agda:261`), is itself incomplete:
  line 264 leaves the proof that the result is bisimilar to the identity, so it
  is not yet a semantic perturbation in the sense of Definition 5.5. The other
  semantic arrow action `A⟶K-SemPtb` (line 276) is complete.

### Definition D.6, Kleisli product action on syntactic perturbations

Not formalized. There is no product analogue of the two homomorphisms in
`Semantics/Concrete/Perturbation/Kleisli.agda` (the file ends with the comment
"Actions of Kleisli product on perturbations" and nothing after it), and no
semantic product action in `Semantics/Concrete/Perturbation/Semantic.agda`.

### Unnumbered auxiliary lemmas on sigma-type perturbations (Appendix D.1, D.2)

`Σ-SemPtb-eq` and `Σ-SemPtb-ind` in
`Semantics/Concrete/Perturbation/Semantic.agda` have holes at lines 729, 749,
755 and 757. Nothing uses them; the dynamic type goes through `Σ-SemPtb`
itself, which is complete.

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

### Lemma D.14 part 2, F preserves right-representability of products

Not started. Part 1 (`×-leftRep`,
`Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda:558`)
is complete. Part 2 is blocked on the square lemmas for Definition B.3.

### Lemma D.15 part 1, `c ⟶ d` is quasi-right-representable

`RightRepArrow`
(`Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda:655`).
The projection `p-arrow`, both perturbations `δl-arrow` and `δr-arrow`, and
both squares `DnR-arrow` and `DnL-arrow` are written in the `where` clause,
but the two square slots in the `mkRightRepC` call at line 660 are holes. What
is missing is the identification of the interpretation of the composite
perturbation with the composite of the two interpretations, so that the
constructed squares have the required type.

### Lemma D.15 part 2, `U(c ⟶ d)` is quasi-left-representable

`LeftRepUArrow`
(`Semantics/Concrete/Perturbation/QuasiRepresentation/Constructions.agda:767`).
The embedding `e-UArrow` and the left perturbation `δl-UArrow` are defined.
The three remaining fields at line 772 are holes: the right perturbation and
the two squares. `UpR-UArrow` (line 798) has its two component squares and
their composite built; the comment there identifies the missing fact as the
left-side coherence lemma `⟶Kᴸ-lemma` of Definition D.5. The right-side square
`UpL` has not been started.

### Lemma D.18, quasi-order-equivalence of functors with composition

Not formalized. `ValRel≈` and `CompRel≈`
(`Semantics/Concrete/Relations/Base.agda:91` and `:103`) define
quasi-equivalence of value and computation relations only as equality of
embeddings. This lemma is what the semantic validation of the type-precision
equations (`⟦_⟧ty⊑-≈` in `Syntax/FineGrained/Denotation/TypePrecision.agda:31`,
remaining-work item (2) of Section 6.3) would need.

### Definition D.16, composition of computation relations

Value-relation composition `⊙V` is done
(`Semantics/Concrete/Relations/Constructions.agda:145`). The computation
version has no definition, although all three ingredients exist: the push-pull
structure `⊙C` (`Perturbation/Relation/Constructions.agda:161`),
`RightRepC-Comp` from Lemma D.10
(`Perturbation/QuasiRepresentation/Composition.agda:380`), and
`repUdUd'→repUdd'` from Lemma D.13
(`Perturbation/QuasiRepresentation/CompositionLemmaU.agda:122`).

### Definition D.17, functorial actions on value and computation relations

F and U are done (`Semantics/Concrete/Relations/Constructions.agda:278` and
`:290`). The product and arrow actions have no definition, blocked on Lemma
D.14 part 2 and Lemma D.15 respectively. These two actions are what
`⟦ c ⇀ d ⟧ty⊑` and the context case `⟦ c ∷ C ⟧ctx⊑`
(`Syntax/FineGrained/Denotation/TypePrecision.agda:22` and `:28`) need.

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
  └─> Lemma D.14 (2)  ──> Def. D.17 (× on relations) ──> ⟦ c ∷ C ⟧ctx⊑

Def. D.5 coherence (⟶Kᴸ-lemma, ⟶Kᴿ-lemma) + ⟶KB-SemPtb bisimilarity
  └─> Lemma D.15 (2)  ─┐
Lemma D.15 (1)        ─┴─> Def. D.17 (⟶ on relations) ──> ⟦ c ⇀ d ⟧ty⊑

Lemma D.18 ──> ⟦_⟧ty⊑-≈ (equations on type precision derivations)
```
