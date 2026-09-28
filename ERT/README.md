# ERT — Equivalence of Russell and Tarski universes

A formalisation of §4.2–4.3 of the paper `sterbac1.pdf` on cumulative
universes à la Russell and à la Tarski (levels `0, 1, 2, …`), by the domain
technique of this repository. Check everything with

```sh
agda --safe --without-K --exact-split ERT/All.agda
```

about 15 s from scratch. There are no postulates and no pragmas. There is one
harmless `CoverageNoExactSplit` warning in `UniquenessTermPartial`, explained
in the notes.

The notes are [`sec43.tex`](sec43.tex) (built: [`sec43.pdf`](sec43.pdf)).
They cover the systems, the differences with the paper, and a gap in the
paper's proof of Lemma 4.17.

## §4.2 — Tarski `T_T` ⇔ Russell `T_R`

| Result | Module | Name |
|---|---|---|
| Lemma 4.6 (erasure preserves judgements) | [`EraseDeriv`](EraseDeriv.agda) | `erase-*` |
| U-injectivity, U/Π no-confusion (from the model) | [`Injectivity`](Injectivity.agda) | `U-inj-Ty-T`, … |
| Lemma 4.10 (uniqueness up to conversion / common lift) | [`UniquenessTermPartial`](UniquenessTermPartial.agda) | `type-uniq`, `term-uniq`, `uniq-El` |
| Theorem 4.13 (section of erasure) | [`Equivalence`](Equivalence.agda) | `lift-*`, `equivalence` |

## §4.3 — annotated `T_R` ⇔ unannotated `T_P`

| Result | Module | Name |
|---|---|---|
| Π-injectivity of `T_R` (adequacy of the domain model) | [`PiInjectivityR`](PiInjectivityR.agda) | `PiInj-R` |
| Theorem 4.15 (strip preserves judgements) | [`StripDeriv`](StripDeriv.agda) | `strip-*` |
| The gap in the proof of Lemma 4.17 | [`Gap417`](Gap417.agda) | |
| **Lemma 4.18 without normalisation** | [`StripUniqNF`](StripUniqNF.agda) | `term-uniq-NF`, `type-uniq-NF` |
| Theorem 4.19 (section of strip) | [`SectionR`](SectionR.agda) | `lift-*`, `section-*` |

Lemma 4.18 is proved by a structural induction with η-coercions and type
joins. It uses only Π-injectivity, injectivity of universes and Π/U
no-confusion, all proved from the domain model. An earlier proof under weak
normalisation of `T_P` is kept in [`StripUniq`](StripUniq.agda).

The type-in-type version is in [`ERTUU/`](../ERTUU/), and the version with
internal universe levels (bcde.pdf) is in [`BCDE4/`](../BCDE4/).
