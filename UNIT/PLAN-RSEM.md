# PLAN-RSEM: a semantics of T_Russell through the Ehrhard GAT T_E

Handoff, 2026-11-23. Read this whole file before touching code.

## 1. Goal

Give a model of T_Russell, the type theory with Russell universes
U_0 : U_1 : ... and strict cumulativity, as in sterbac4.pdf Appendix A.3.
Do this without a direct interpretation of Russell derivations:

    T_Russell --(lift, Thm 28 + Thm 20, done)--> T_E --(interpretation, TODO)--> model

Why this route works:
- T_E is a GAT with Ehrhard's explicit substitutions, so it is easy to interpret.
- A Russell judgement is interpreted through any T_E lift of it.
- Two lifts are T_E-convertible, and that is proved (section 3). So the
  interpretation does not depend on the lift. This settles the Russell
  coherence problem once, syntactically, for every model.

Target model: set-theoretic semantics in Gylterud's iterative sets V, with
a hierarchy V_0 ⊂ V_1 ⊂ ... ⊂ V_N. Types are V-codes, so Ty is a set and the
interpretation has no higher coherence problems. In this model a lift is a
real operation on codes (`liftV`), not the identity. That is why the
Russell -> T_E step is needed here.

## 2. Ground rules (from the user; do not break them)

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
- **Status files.** Keep `UNIT/PLAN-RSEM.md` (this file) up to date with
  [x] marks and short DONE notes.

## 3. What already exists (all in `~/DOMAIN/UNIT`, checked)

Checker (indexed families are needed):

    SEG=/Users/coquand/CANONICITY/unit-indexed/dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg
    cd ~/DOMAIN/UNIT && $SEG GATCheck.seg     # 1748 declarations, 0 failed, 0.4 s
    cd ~/DOMAIN && python3 UNIT/check.py       # everything, incl. All.seg (~25 s)

`check.py` also verifies sha256 snapshots of `UNIT/vendor/*.seg`
(`vendor-manifest.json`). Do not edit vendored files. New files go
directly in `UNIT/`. Register each one in `GATCheck.seg` (last import line)
and in `All.seg` (line 92, after `import RGAT ;`).

Mathematical documentation: `UNIT/gat-ehrhard.tex` / `.pdf`, sections 1-12.
Read it first; section 12 is the composition this plan builds on.

### Syntax and judgements

All files are parametrised by `level l`.

| File | Contents |
|---|---|
| `TSyntax.seg` | raw de Bruijn `Tm`: `var, pi, uu n, el n a, lam, app, pic n a b, uc m n, lf m n a`; `Cx = cnil / csnoc` |
| `TTyping.seg` | T_Tarski: `data Der : Jf -> U l`, judgements `jwf, jty, jtm, jeqty, jeqtm`; `CxEq` |
| `GAT.seg` | T_E: raw `GE` (contexts gnil/gext, types, terms, substitutions `gid, gcomp, geps, gp, glift A s, gsec A a`, variable `gq`); `data GDer : GJ -> U l` (104 constructors); erasure `et, es, ec` to T_Tarski |
| `RTyping.seg` | T_Russell: `data RDer : Jf -> U l` (same raw `Tm`, `uu n` used as a term) |
| `ErR.seg` | Russell erasure `er, erC, erJ`; Lemma 21 `er-der : (J : Jf) -> Der J -> RDer (erJ J)` |

### Theorems used by this plan

| Name | File | Content |
|---|---|---|
| `sound` | `GSound.seg` | Theorem 16: `GDer J -> SoundJ J` (T_E -> T_Tarski) |
| `section-*` | `Thm20.seg` | Theorem 20, T_Tarski -> T_E via `ceil`/`ceilC` |
| `unique-*` | `Thm20.seg` | Theorem 20, uniqueness up to conversion |
| `lemma19` | `L19.seg` | `G = ceil |G|` and `A = ceil |A|` in T_E |
| `ty-uniq`, `tm-uniq`, `er-inj` | `TUniq.seg` | Lemma 25 / Corollary 27 |
| `sec`, `thm28`, `un-*`, `cxer` | `TSection.seg` | Theorem 28, T_Russell -> T_Tarski |
| `r2g-*`, `g2r-*`, `gu-*`, `cx-sym`, `cx-trans` | `RGAT.seg` | the composition, see below |

`RGAT.seg` in more detail (‖X‖ = Russell erasure of Tarski erasure,
`dC`/`dT`):
- `r2g-wf/ty/tm/eqty/eqtm`: an `RDer` judgement gives a T_E context X and
  judgement with `GDer`, `Id Cx (dC X) G` and `Id Tm (dT Y) A`. The
  context is `ceilC D` for the Tarski lift D.
- `g2r-*`: a `GDer` judgement gives an `RDer` judgement on its double erasure.
- `gu-ty`, `gu-tm`, `gu-eqty`, `gu-eqtm`: same T_E context and same double
  erasure imply T_E-convertible.
- `gu-cx1`: two T_E contexts with the same double erasure are T_E-equal.
- `cx-sym`, `cx-trans`: symmetry and transitivity of T_E context equality,
  by induction on `GDer`.

## 4. Plan

### S0. Environment check (small; do first)

The V library is in a different tree: `~/CANONICITY/unit/core/`. The files
are `V.seg` (Gylterud V, `isSetV`, `mkV`, `Ix`, `ev`), `VLift.seg`
(`liftM`, `liftV : V[k].V -> V[l].V`, `liftV-inj`, `PiS`) and `VCode.seg`.
They sit inside `module Model (fe) (univ)` in `core/All.seg`, and are
checked with `./segc` / `cabal list-bin exe:seg` in `~/CANONICITY/unit`,
not with the unit-indexed checker.

Decide how to use them from DOMAIN/UNIT, which needs the indexed checker:
- (preferred) copy `V.seg` and `VLift.seg`, plus what they import, into
  `DOMAIN/UNIT` under new names (e.g. `SV.seg`, `SVLift.seg`), adapted to
  DOMAIN/UNIT's `Base/Prelude/Lib/Axioms`, with fe and ua as parameters as
  in `UNIT/All.seg` line 15;
- or check whether `core/` passes the indexed checker unchanged.

Seg's universes are cumulative (`A : U k` is in `U l` for k <= l), and
`VLift.seg` relies on this.

Caveat noted in `VLift.seg`: `Ix (liftV x)` does not compute for a
variable x. So El(lift a) = El a will be a propositional equality in a
set, not a judgemental one. That is fine for a set model.

**DONE.** The local ports `IterativeSets.seg` and `IterativeSetLift.seg`
use the existing foundation and the enclosing `ua` and `fe`. Both entry
points import them. The full upstream `core/All.seg` stopped on a scope
error at `Model.CBase.CB.CExt2` with the indexed checker.
`GATCheck.seg` checked 1876 declarations in 0.41 s after each port
independently rejected a deliberate error and was restored.
`python3 UNIT/check.py` passed all checks and verified 40 vendor hashes.
A scratch check built the universe code for `k+ <= l` and verified that
it decodes to `V[k].V` by reflexivity. For a variable `x`, the equality
of the index types of `liftV x` and `x` checks by splitting on the
underlying multiset. Reflexivity alone is rejected.

### S1. Bound the levels by N (syntax)

T_E has `uu n` for every n : Nat. A V-model needs a meta-level above all of
them, so add a bound N, a parameter of the systems, with every level ≤ N.

- Add a side condition `LeN n N` (or `LeN p N`) to every rule that
  introduces a level not already in its premises:
  - T_Tarski (`TTyping.seg`): `ty-uu`, `tm-uc`, `tm-lf`, `eqty-el-lf`,
    `eqty-el-uc`, `eqtm-lf`, `eqtm-lf-pic`, `eqtm-lf-uc`, `eqtm-lf-lf`.
  - T_E (`GAT.seg`): `gt-uu`, `gm-uc`, `gm-lf`, `ge-el-lf`, `ge-el-uc`,
    `ge-uu-sb`, `gm-elf`, `gm-lf-pic`, `gm-lf-uc`, `gm-lf-lf`,
    `gm-uc-sb`, `gm-lf-sb`.
  - T_Russell (`RTyping.seg`): `rty-uu`, `rtm-uu`, `rtm-cum`, `reqtm-cum`.

  The lean Tarski and Ehrhard rules carry the same premises.

**DONE.** Both entry points use one `BoundedSyntax (N : Base.Nat)`
module for the syntactic development. Raw terms retain natural-number
annotations. The RGAT statements have the same form at the shared bound.
The files for the filter model and `TInv` were unchanged. The soundness
induction in `TSound` only accepts the additional constructor arguments.

- Tarski and Ehrhard recover the bound from a derivation of a universe
  type, and use the existing presupposition lemmas for terms. Ehrhard
  type inversion accounts for context conversion.
- Russell uses `RLevels.seg` to prove that all levels of a derivable
  judgement are bounded, using preservation under renaming and
  substitution. An application type can expose a universe after
  substitution. `cu-tm` and `cu-eqtm` recover their bounds by erasing
  their existing Tarski premises and using the Russell lemma.
- The Π-code proof in `TUniqComb` uses both component derivations to
  bound `max ka kb`. For the universe-code successor, the original
  typing premise gives `suc m <= n <= N`. The generic lift helpers
  accept a target bound when their inputs only constrain the source.
  No proof needs a universe above N.
- `GATCheck.seg` checked 1918 declarations in 0.60 s after rejecting a
  deliberate error in `RLevels.seg` and restoring it. `check.py` passed
  all checks and verified 40 vendor hashes. Scratch checks verified
  `U_0 : U_1` and its RGAT lift at `N = 1`, and rejected level 1 in
  each system at `N = 0`.

### S2. The model: a CwF on V with Π and the hierarchy (new file(s), e.g. `SModel.seg`)

Meta-level: a V-code at level t means `V[t].V`. Take the top level ≥ N+1.

- First turn the S0 scratch check into a checked file. Construct the
  universe code for `k+ <= l` and prove its decoding by reflexivity.
- **Structure.**
  - Ctx: a type, a set if needed; e.g. Ctx = V-codes or meta types.
  - Ty G = G -> V_top (a set by funext and `isSetV`).
  - El G A = (x : G) -> Ix (A x).
  - The Ehrhard operations (id, ∘, p, q, lift, sec): the standard model.
    All equations should be `refl` or funext. See the Agda precedent
    `DOMAIN/MODEL/VModel.agda` (every CwF equation is refl there).
  - Use the Ehrhard record from `~/CANONICITY/unit/core/CwF.seg`
    (`record CwF`) as interface, or state the needed fields directly.
- **Π.** Π-code over V (`mkV` / `PiS` from `VLift.seg`).
- **Universes.**
  - U_n as a type in context G: the constant family on the code of V[n]
    seen at level n+1, i.e. `mkV (V[n].V) liftV liftV-inj` (with
    `liftV : V[n] -> V[top]`).
  - El_n a = the lifted code: decode an element of U_n (a V[n] set) by
    lifting to V_top.
  - `pic n a b`: the Π-code at level n.
  - `uc m n`: the code of V[m] inside V[n] (m < n ≤ N).
  - `lf m n a` = `liftV a`.
- **Equations to prove** (as `Id` in sets):
  - El(lf a) = El a: lifts compose (`liftV ∘ liftV = liftV`, by W-induction
    and the extensionality `ext` of V);
  - El(pic a b) = Π(El a)(El b);
  - El(uc m n) = U_m;
  - lf(pic a b) = pic(lf a)(lf b);
  - lf(uc m n) = uc m p;
  - lf ∘ lf = lf;
  - naturality of all of these under substitution (should be refl when
    families are functions).

  Expect `VLift`-style lemmas: liftV preserves `mkV`, Π-codes and `Ix`.
- **η and β for Π.** Should hold judgementally (funext not needed for β).

Package everything as a record, say `TEModel`: the CwF fields and Π plus
`U n`, `El n`, `pic`, `uc`, `lf` and the equations above, each guarded by
`LeN _ N`. Then build the instance `vModel : TEModel`.

### S3. Interpret T_E^N in any `TEModel` (new file, e.g. `TEInterp.seg`)

This is the main engineering step. The conversion rules (`gt-cx`,
`gm-conv`, `gm-eqconv`, `ge-cx`, `gm-ecx`, `gs-cx`) transport along
equalities, so a naive interpretation of derivations needs coherence: two
derivations of the same judgement must give equal values. Options:

- (recommended) **Partial interpretation à la Streicher.** Define the
  meaning of raw `GE` by recursion (`split`) on raw syntax, relative to a
  semantic context, as a partial value (e.g. a predicate "denotes" with
  functionality). Then prove by induction on `GDer` that derivable
  judgements denote, and that equality judgements denote equal values.
  Functionality is by induction on raw syntax, so no coherence problem
  arises.
- Interpret derivations directly and prove coherence separately. Since Ty
  and El are sets in the V-model, the coherence lemma is "equal up to
  `Id`", with no higher paths. It still needs its own induction.

Ehrhard's explicit substitutions help here: every T_E rule matches a model
field, and no syntactic substitution lemma is needed.

Statement shape: for `GDer (gjty G A)`, a semantic context ⟦G⟧ and a type
⟦A⟧ in it; similarly for terms. For `gjeqty`/`gjeqtm`/`gjeqcx`, equal
values.

### S4. Semantics of T_Russell (small once S1-S3 are done, e.g. `RSem.seg`)

- For an `RDer` judgement J over G, take the lift from `r2g-*` and its
  T_E interpretation.
- **Independence.** Any two T_E lifts with the same double erasure are
  convertible by `gu-*` / `gu-cx1`; the contexts are first aligned by
  `gu-cx1` and the `gt-cx`-style rules. So by S3 they have equal
  interpretations.
- **Soundness for Russell equality.** `r2g-eqty` / `r2g-eqtm` lift a
  Russell equality to a T_E equality, which S3 interprets as an equality.
- Final theorem, to state cleanly:
  1. every T_Russell judgement has a meaning in any `TEModel`;
  2. the meaning is independent of the lift;
  3. Russell-convertible terms have equal meanings.

  Instantiate at `vModel`.
- Then add a section to `gat-ehrhard.tex` (the semantics of T_Russell)
  and a row to its file table.

## 5. Seg/Unit practicalities (learned the hard way)

- **Recursion.** Only `split` on data types. A constructor with recursive
  arguments gives extra variables after `|`, e.g.
  `gc-ext G D A B h1 h2 | r1 r2 -> ...`. There is no `let` and no
  self-reference.
- **Splitting an indexed family** (`GDer`, `Der`, `RDer`) at a fixed index
  still lists ALL constructors. Use a motive `M : GJ -> U l` that is `Top`
  off the index of interest, and return `tt` there. Generate the 104-case
  list mechanically; copy the case patterns of `ext-inv` in `GLean.seg`.
  See `cx-sym-J`, `tr-inv` and `cx-trans-J` in `RGAT.seg`.
- **Records** with manifest leading fields: `LTy[D, A]`,
  `new LTy[D, A, T := ...]`, projections `r.T` (see `TSection.seg`).
- `*` is right-associative: `a * (b * c)`, projections `.1`, `.2.1`, ...
- **Useful names.**
  - Paths: `ap A B f x y p`, `trans A x y z p q`, `sym`, `subst A P x y p u`,
    `cong2`, `efq` (Lib).
  - Order: `LeN` (Lib).
  - T_E presuppositions: `gpresup : (J : GJ) -> GDer J -> GPJ J`
    (`GPresup.seg`).
  - T_Tarski presuppositions: `presup-tm`, ...
- **Error messages** print the expected and inferred type with de Bruijn
  `#k`. The first parse error stops the file (e.g. "';' expected").

## 6. Risks / open points (report, do not hide)

- S1: a proof in TUniq/TSection might create a level above the inputs
  (e.g. a max or a suc not bounded by an existing level). If so, report
  where it happens before working around it.
- S2: El(lf a) = El a and lf ∘ lf = lf need W-induction and V's
  extensionality. This is the only real mathematics on the model side. If
  `liftV` turns out not to commute with the Π-code on the nose up to `Id`,
  report it.
- S3: the size of the partial interpretation. Keep files small (seconds to
  check); split by rule groups as `L18*.seg` does.
- Alternative model, lower priority: the univalent model in
  `~/CANONICITY/unit/sag-model/` has an Ehrhard CwF (`CwF.seg`), Π,
  one universe (`CwFU.seg` `UnivStr`, instance `FibUniv.seg`) and
  univalence. It lacks Π-codes with strict decoding (`M1.md` line 403:
  "not yet"). It fits only N = 0; strict cumulativity there is open.

## 7. Checklist

- [x] S0 environment: V and VLift usable under the indexed checker
- [x] S1 level bound N threaded through T_Tarski, T_E, T_Russell, all proofs
- [ ] S2 `TEModel` record + `vModel` instance on V_0 ⊂ ... ⊂ V_N
- [ ] S3 interpretation of T_E^N in any `TEModel` (soundness for all judgement forms)
- [ ] S4 semantics of T_Russell (existence, independence of lift, soundness); tex section
