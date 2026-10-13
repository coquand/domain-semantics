# MAHLORT: Russell ⇔ Tarski for the Mahlo universe

This directory proves that two presentations of the internal Mahlo universe
are equivalent. In the style of [`ERT/`](../ERT/README.md), the two sides are:

- **Russell:** the annotated theory [`MAHLO/Typing`](../MAHLO/Typing.agda),
  which has subsumption U_{f,g} ≤ V, the rule (R') and δ in V.
- **Tarski:** Setzer's internal Mahlo universe with recursive subuniverses and
  full decoding (setzer1, Def. 3.5(a)), together with the reflection rule.
  It is in [`TarskiSyntax`](TarskiSyntax.agda) and
  [`TarskiTyping`](TarskiTyping.agda).

Everything is `--safe --without-K --exact-split`, with no postulates and no
pragmas. To check everything:

```sh
agda MAHLORT/EquivalenceFinal.agda
```

## Results

| Result | Module | Name | Hypotheses |
|---|---|---|---|
| Erasure preserves judgements (Lemma 4.6) | [`EraseDeriv`](EraseDeriv.agda) | `erW`, `erI`, `erH`, `erT`, `erC` | none |
| Tarski metatheory (weakening, substitution, functionality, context conversion, presupposition, inversion) | [`Syntax/`](Syntax/All.agda) | MAHLOINJ names | none |
| No-confusion, Russell side: `TyEq G V X → X = V` (syntactic), V ≢ U_{f,g}, N ≢ Π, N ≢ Σ | [`RNoConf`](RNoConf.agda) | `V-only`, `V-U`, `Nat-Pi`, `Nat-Sig` | none |
| No-confusion of the Tarski type formers V, U_{f,g}, Π, Σ, N (10 cases) | [`TNoConf`](TNoConf.agda) | `tV-U`, …, `tNat-Sig` | none |
| **Π- and Σ-injectivity for Tarski type equality** | [`TFinal`](TFinal.agda) | `tInj : TInj`, `Pi-inj`, `Sig-inj` | **none** |
| Coherence of terms with equal erasure (ERT 4.10 merged with 4.18) | [`Coh`](Coh.agda), [`Uniq`](Uniq.agda) | `term-uniq`, `type-uniq` | `TInj`; instantiate at `TFinal.tInj` |
| Section of erasure (Theorem 4.13): every Russell judgement lifts, in any Tarski context erasing to its context | [`Section`](Section.agda), [`SectionLemmas`](SectionLemmas.agda) | `lift-Ty`, `lift-Tm`, `lift-TE`, `lift-Cv` | `TInj` |
| Equivalence: soundness + section + retraction (types up to TyEq, terms up to Coh) + contexts (`ctx-uniq`) | [`Equivalence`](Equivalence.agda) | `equivalence` | `TInj` |
| **Equivalence, hypothesis-free** | [`EquivalenceFinal`](EquivalenceFinal.agda) | `equivalence` at `tInj` | **none** |

`TInj` ([`Hyp`](Hyp.agda)) is the only hypothesis that uniqueness and the
section use, and `TFinal.tInj` discharges it. The final equivalence is
therefore hypothesis-free: it does not depend on PFix.

## Two departures from ERT

1. **Uniqueness has to allow coercions.** In MAHLO Russell, `App` and `Pair`
   are unannotated and `Lam` carries no codomain, so ERT's Lemma 4.10 is false
   here. For example, `λx:A. N̂_U(f,g)` and `λx:A. N̂_V` have the same
   erasure, but their types are neither equal nor universes. Uniqueness is
   therefore stated as coherence: up to T̂ at universes, and up to η at Π and Σ.
   Decomposing coherence at Π and Σ needs Tarski Π/Σ-injectivity. That has to
   come from a model argument on the Tarski side: pulling Russell injectivity
   back through erasure would assume faithfulness, which is circular.
2. **T̂ is unannotated.** If T̂ carried (f,g), the univ/univ extraction would
   need injectivity of U_{f,g} on the Tarski side, and no route to it is known.
   With T̂ unannotated, an element a : U_{f,g} and T̂ a : V have the same
   decoding El_V(T̂ a), and reflection closes the extraction.

## The Tarski adequacy (`Model`, `Valid/`, `Adq/`)

The Tarski adequacy is a port of [`MAHLOINJ`](../MAHLOINJ)'s logical relation
and fundamental lemma.

- **Model, through erasure.** A Tarski expression denotes what its erasure
  denotes in MAHLOINJ's finite-element model. Soundness is soundness of the
  erased judgements, by `EraseDeriv`, so the 11k lines of Domain and Model are
  reused unchanged.
- **Head reduction** ([`Valid/HeadRed`](Valid/HeadRed.agda)) has three kinds
  of steps:
  - β, π and ι;
  - the T̂-equations, which take the place of Russell's δ: T̂ commutes with the
    codes of U_{f,g}, and T̂ f̂ / T̂ ĝ unfold to f / g;
  - the decodings: El_V(code) → type, and El_U a → El_V(T̂ a).

  It ignores annotations.
- **Elements of a universe** are related through their decoding: El_V M at V,
  and El_V(T̂ M) at U_{f,g}. The universe clause records the kind of universe
  (V or U_{f,g}). The model cannot tell the two kinds apart, but V ≢ U_{f,g}
  makes recording it consistent.
- **Application and projection fields** quantify over all convertible
  annotations, one per side. This is what the annotation-changing congruences
  `conv-Lam`, `conv-App`, `conv-Pair`, `conv-Fst` and `conv-Snd` make sound.
- **Annotation irrelevance.** The head-expansion lemmas accept AR: an
  annotation change along the head spine, then reduction, then another
  annotation change. A simulation lemma (`hrSim`: reduction commutes with
  annotation change) and the rigidity of canonical forms justify this. It is
  used for funext, for the projections, and for the T̂ ĝ step, whose
  annotations contain weakenings of f.
- **Context retyping** (`Adq/El.envElU`): El_U f g a and El_V(T̂ a) are one
  head step apart and have the same erasure. So related substitutions over a
  context ending in one of them are related over the context ending in the
  other.

| Layer | Files |
|---|---|
| Model | `Model` |
| Relation | `Valid/HeadRed`, `Stage`, `Stab`, `Ann`, `Props`, `Step`, `Public` |
| Case lemmas | `Adq/View`, `Base`, `Env`, `App`, `Lam`, `Code`, `Cod`, `Form`, `LamApp`, `AnnRel`, `Small`, `Sig`, `Syn`, `RecSyn`, `Rec`, `Delta`, `Cases`, `El`, `Codes`, `FG` |
| Fundamental lemma | `Adq/Fund` |
| Injectivity | `Adq/Inj`, `TFinal` |
