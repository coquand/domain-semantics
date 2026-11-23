# PLAN-ANNOT: context annotations of T_GAT (sterbac4 §2.1) for the formalised T_E

Handoff, 2026-11-23. Read this whole file before touching code.

## 1. Goal

sterbac4.pdf (`~/DOMAIN/sterbac4.pdf`, §2.1, Definitions 2, 4, 7 and 11)
annotates exactly six leaf constants of T_GAT with contexts:

    (U_l)_Γ    (U^m_l)_Γ    id_Γ    ()_Γ    p_{Γ,A}    q_{Γ,A}

Composition σδ, the action Aσ / aσ, and the formers Π, λ, app, T_n, t^m_l,
Π_n carry no context annotation.

The formalised Ehrhard GAT T_E (`UNIT/GAT.seg`) deliberately leaves these
six leaves bare: `guu n`, `guc m n`, `gid`, `geps`, `gp`, `gq`. The context
of the judgement plays the role of the annotation (see the header of
`GAT.seg` and the remark in §3 of `UNIT/gat-ehrhard.tex`). A colleague
pointed out that this means the step T_Tarski -> T_GAT never has to
reconstruct the annotations.

Goal: define the annotated theory T_E^a, which is T_E with the six leaves
annotated as in the paper, and prove it equivalent to T_E, without
touching T_E or its proofs. Composed with the existing results (`RGAT.seg`)
this gives T_Tarski <-> T_E^a <-> T_Russell for the annotated theory.

Out of scope: Ehrhard's generators (lift_A(σ), sec_A(a)) versus the paper's
pairing (σ, a). Keep Ehrhard's generators. That difference is already
discussed in `gat-ehrhard.tex`.

## 2. Coordination: another session is working in the same directory

Another LLM session is executing `UNIT/PLAN-RSEM.md`: a semantics of
T_Russell through T_E, with steps S2-S4, using the model files
`IterativeSets.seg`, `IterativeSetLift.seg`, `IterativeUniverse.seg` and
more. That work is independent of this one, but both run in the same
working tree. Therefore:

- **Do not edit any existing `.seg` file.** In particular, leave `GAT.seg`,
  `Ev.seg`, `L18*.seg`, `L19*.seg`, `Thm20.seg`, `GPresup.seg`,
  `GLean.seg` and `RGAT.seg` alone. Only create new files (suggested
  prefix `A`: `AGAT.seg`, `AForget.seg`, `AAnnot.seg`, `AUniq.seg`,
  `ARGAT.seg`).
- **The only shared edits** are one import line in `GATCheck.seg` and one
  in `All.seg`.
  - Put your imports on their own new line, inside the
    `module BoundedSyntax (N : Base.Nat) { ... }` block, after
    `import RGAT ;`.
  - Do not reorder or reformat anything else in those files.
  - Re-read the file just before editing, since the other session may have
    changed it.
- **Do not edit `PLAN-RSEM.md`.** Your status file is this one,
  `PLAN-ANNOT.md`.
- If you ever need a change in an existing file, stop and ask the user.

## 3. Ground rules (from the user)

- **Git.** Never `git add -u` or `git add -A` in DOMAIN; the user keeps
  uncommitted tex/pdf work. Stage explicit paths only. Commit or push only
  when the user asks.
- **Wording.** Say "U : U", never "Type:Type".
- **Status.** Report status plainly: proved, open, stuck on X. Do not
  over-claim. Flag a mathematical or design obstruction as soon as you see it.
- **Proof checks are fast.** A file should check in seconds. A slow check
  usually means the formalisation is set up wrong.
- **Check that a new file is really checked.** After a first green check,
  plant a deliberate error, see it rejected, then restore the file.

## 4. Tools and current state

Checker (indexed families are needed):

    SEG=/Users/coquand/CANONICITY/unit-indexed/dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg
    cd ~/DOMAIN/UNIT && $SEG GATCheck.seg      # ~1900 declarations, 0 failed, < 1 s
    cd ~/DOMAIN && python3 UNIT/check.py        # everything (~25 s)

`check.py` checks sha256 snapshots of `UNIT/vendor/*.seg`; do not edit
those.

Since commit a0c9c5c, all syntax is inside `module BoundedSyntax (N : Nat)`.
Every level is ≤ N, and the rules introducing a level carry a premise `nb`
(see `GAT.seg`). Your files live inside that module too and simply use
`N`.

Read first:
- `UNIT/gat-ehrhard.pdf`: §§3, 4 and 12;
- `UNIT/GAT.seg`: raw `GE`, `GJ`, `GDer` (104 constructors), erasure `et/es/ec`;
- `UNIT/RGAT.seg`: `cx-sym`, `cx-trans` show how to do inductions over
  `GDer` with a motive that is `Top` off the index of interest, and the
  composite theorems `r2g-*`, `g2r-*`, `gu-*`, `gu-cx1`;
- `UNIT/TSection.seg`: the technique used below for existence.

Relevant T_E rules (`GAT.seg`):
- the rules whose conclusion is a leaf: `gt-uu`, `gm-uc`, `gs-id`,
  `gs-eps`, `gs-p`, `gm-q`;
- the equations mentioning a leaf: `ge-uu-sb`, `gm-uc-sb`, `ge-el-uc`,
  `gm-lf-uc`, `gq-idl`, `gq-idr`, `gq-eps`, `gq-p-lift`, `gq-p-sec`,
  `gq-lift-id`, `gq-lift-p-sec-q`, `gm-q-sec`, `gq-lift`, `gq-sec`, ... .
  Grep for `guu`, `guc`, `gid`, `geps`, `gp`, `gq` to get the full list.
- context conversion: `gt-cx`, `gm-cx`, `ge-cx`, `gm-ecx`, `gs-cx`.

## 5. Plan

### A0. Design note (write it here, then report to the user before coding A3)

Fill in section 7 below with the exact T_E^a rules for the six leaves,
with the annotation fixed by the contexts of each rule:
- `gs-id G : G -> id_G -> G`;
- `gs-p G A : G.A -> p_{G,A} -> G`;
- `gm-q G A : q_{G,A} : A p_{G,A}` in `G.A`;
- `ge-uu-sb D G n s : (U_n)_G s = (U_n)_D`;
- and so on for every rule listed in section 4.

Also fix the congruence rules for annotations. A GAT has congruence in its
sort arguments, so add, e.g.:

    Γ = Γ'                       |-  (U_n)_Γ = (U_n)_Γ'      in context Γ
    Γ = Γ'                       |-  id_Γ = id_Γ'  : Γ -> Γ
    Γ = Γ',  Γ |- A = A'         |-  p_{Γ,A} = p_{Γ',A'}  : Γ.A -> Γ
    Γ = Γ',  Γ |- A = A'         |-  q_{Γ,A} = q_{Γ',A'}  : A p
    likewise for (U^m_l)_Γ and ()_Γ.

The rule shapes must be chosen so that the presuppositions still hold. In
T_E, `gs-cx` exists for exactly that reason.

### A1. `AGAT.seg`: raw syntax and rules of T_E^a

- `GA` is a copy of `GE` with the six leaves annotated: `auu n G`,
  `auc m n G`, `aid G`, `aeps G`, `ap G A`, `aq G A`.
- `GAJ`, `GADer`: a copy of the 104 rules with the leaf annotations of A0,
  plus the congruence rules.
- Generate the copy mechanically with a script, as `UNIT/gen_tuniq.py`
  does for TUniq. Commit the script with the files.
- Also prove the presuppositions of T_E^a (copy `GPresup.seg`'s structure)
  if A2-A4 need them.

### A2. `AForget.seg`: forget the annotations, T_E^a -> T_E

- `fg : GA -> GE`, `fgJ : GAJ -> GJ`.
- Soundness: `GADer J -> GDer (fgJ J)` by induction. Each rule maps to the
  T_E rule; each congruence rule maps to a reflexivity rule. This is easy.

### A3. `AAnnot.seg`: existence, T_E -> T_E^a

Use the technique of `TSection.seg`, which avoids moving derivations
between contexts: induction on T_E derivations, quantifying over the target
annotated context.

- **Contexts.** A T_E derivation of `|- G` gives an annotated `G^a` with
  `fg G^a = G` and `|- G^a`.
- **Types, terms, equations.** For every annotated well-formed `D^a` with
  `fg D^a = G`, give the annotated judgement over `D^a`. Its forgetful
  image is the given one.
- **Substitutions `s : D -> G`.** Given an annotated domain `D^a`,
  produce some annotated codomain `G^a` with `fg G^a = G` (or
  convertible) and `s^a : D^a -> G^a`. For `gsb t s` and `gcomp s d`, the
  codomain produced for s (resp. the domain produced for d) is the
  context in which t (resp. s) is then annotated. No codomain-uniqueness
  lemma is needed for existence.
- **Leaves.** The annotation is the current annotated context, or its
  prefix and last type for p and q.

### A4. `AUniq.seg`: uniqueness (the real work; design first, then report)

Statement: two T_E^a judgements over the same annotated context with the
same forgetful image are T_E^a-convertible. Compare `unique-ty`,
`unique-tm` in `Thm20.seg` and `gu-*` in `RGAT.seg`. Also: two annotated
contexts with the same image are T_E^a-equal.

Expected obstacle: annotations depend on the derivation. They differ after
`gt-cx`/`gs-cx`, and inside `A σ` they depend on which codomain the
derivation gave σ. Two candidate strategies; evaluate both in the design
note before coding:

- **(U1) Codomain uniqueness plus induction on the raw term.** First prove
  that the codomain is unique up to context equality: from
  `s : D -> G`, `s : D' -> G'` and `D = D'`, conclude `G = G'`. Prove it
  in T_E, then transfer it to T_E^a, or prove it in T_E^a directly. The
  induction is over id, (), p, lift, sec, ∘, using inversion of context
  equality for p, as `tr-inv` in RGAT does. Then prove uniqueness by
  induction on the raw annotated term with generation lemmas for T_E^a.
  Those generation lemmas must see through `gt-cx`/`gm-conv`/`gs-cx`;
  `TGen.seg` does the same for T_Tarski. This could be the expensive part.
- **(U2) Through T_Tarski, as Theorem 20 does.**
  - Define `ceil^a`: for a Tarski judgement and an annotated context,
    annotate the T_E lift `section-*` (from `Thm20.seg`) with A3.
  - Prove an analogue of Lemma 19, `a^a = ceil^a |fg a^a|`, by induction on
    `GADer`. Then two annotated terms with the same image are both
    convertible to the same `ceil^a`.
  - Check whether that induction needs anything beyond A3 and the
    congruence rules. Lemma 19 for T_E used Lemma 18 (`L18*.seg`), and
    redoing L18 for T_E^a would be expensive: avoid that if possible.

Report the choice and its expected cost to the user before writing A4.

### A5. `ARGAT.seg`: compose

With `RGAT.seg` (T_Russell <-> T_E) and A2-A4, prove T_Russell <-> T_E^a.
That is existence, the converse, and uniqueness over a fixed annotated
context. Use the same statement shapes as `r2g-*`, `g2r-*`, `gu-*`,
`gu-cx1`.

### A6. Documentation

Add a section to `UNIT/gat-ehrhard.tex` and a file-table row. Recompile
with `pdflatex`, twice, and check for warnings. The other session may also
be editing this tex file; re-read it right before editing and keep your
change to one new section plus the table row.

## 6. Seg/Unit practicalities

- **Recursion.** Only `split` on data types. A constructor with recursive
  arguments gives extra variables after `|`, e.g.
  `gc-ext G D A B h1 h2 | r1 r2 -> ...`. There is no `let` and no
  self-reference.
- **Splitting an indexed family** at a fixed index still lists ALL
  constructors. Use a motive `M : GJ -> U l` that is `Top` elsewhere and
  return `tt`. Generate the case lists mechanically from the case patterns
  of `ext-inv` in `GLean.seg`. Every rule introducing a level now has an
  extra last argument `nb`, so check the current patterns in `RGAT.seg`.
- **Records** with manifest leading fields: `LTy[D, A]`,
  `new LTy[D, A, T := ...]`, `r.T` (see `TSection.seg`).
- `*` is right-associative: `.1`, `.2.1`, ...
- **Useful names.** `ap`, `trans`, `sym`, `subst`, `cong2`, `efq`, `LeN`;
  `gpresup` (`GPresup.seg`); `cx-sym`, `cx-trans` (`RGAT.seg`).
- **Error messages** print the expected and inferred type with de Bruijn
  `#k`.

## 7. Design note (to be written in A0)

(empty)

## 8. Checklist

- [ ] A0 design note: annotated rules + congruences; uniqueness strategy chosen and reported
- [ ] A1 `AGAT.seg` (+ generator script)
- [ ] A2 `AForget.seg`: T_E^a -> T_E
- [ ] A3 `AAnnot.seg`: T_E -> T_E^a, existence
- [ ] A4 `AUniq.seg`: uniqueness up to conversion
- [ ] A5 `ARGAT.seg`: T_Russell <-> T_E^a
- [ ] A6 tex section
