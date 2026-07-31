# FRESH SESSION — computability at the infinite point, and mutual recursion

Rules: `~/.cabal/bin/agda-2.9.0 --safe --without-K --exact-split` from `/Users/coquand/DOMAIN`;
no hole/postulate/pragma; **< 20 s per file**; **grep before writing any lemma** (§7 lists what
exists and the traps); proceed autonomously; stop only for a genuine MATH issue, and when a
clause resists **state the SIMPLEST CONCRETE INSTANCE where it fails** rather than grinding.

Everything below is committed on branch `hide-old-archives`, all EXIT 0, no
postulate/hole/pragma.

---

## 1. WHAT IS PROVED

### 1a. Single PR terms — CLOSED

```agda
PRInf.prVal      : (q : PR) (n : Nat) -> Wf q n -> D
PRInf.prVal-lub  : prVal q n wf IS the least upper bound of
                   evalF q (S^m bot, ..., S^m bot)
```

So `f(S^w(bot),...,S^w(bot))` is **computable** for every PR term: a total function produces
an explicit element of `D`, and it is the value. Write-up: `OBSTINATION/prinf.tex`.
`PRInfTest` checks by `refl` that it RUNS (`prec zerf zerf` gives `cpl 0` — Case 1 firing at
an infinite point). Depends only on the Proposition-1 cone; the trace is NOT needed.

### 1b. The trace, and MP1 for every PR term — CLOSED

```agda
TrTerm.traceOf-ok    : MonoTr n (traceOf q n wf) * Den n (traceOf q n wf) (evalF q)
TrTermIv.traceOf-MP1 : MP1T n (traceOf q n wf)
```

by induction on the PR term. The value half of MP1 is Proposition 1 (`TrMP1Red`), the index
half is `TrSelStab.compTr-ivAll-full` for composition and `TrPrecIvAll.precTr-ivAll` for the
recursion. `precTr`'s parameter direction, both regimes, is `TrPrecIvP.precTr-ivP`
(no hypotheses); see `NEXT_SESSION_TRACE.md` for that line.

### 1c. Mutual blocks, r = 2 — the verdict from `PhiOK`

```agda
BlkVerdict2.BLK.vd2-blk
  : ((j : Nat) -> Sigma Nat (\ k -> PhiOK k (kv j)))
  -> (j : Nat) -> LeN (suc j) two -> Vd2 (\ m -> HGT m j)

Unb h = (K : Nat) -> Sigma Nat (\ s -> h s > K)
Vd2 h = Or (EvBndN h) (Unb h)
```

`Vd2` is exactly what naming the value at the all-infinite point needs: `EvBndN` gives
`S^(h M)(bot)`, `Unb` gives `S^w(bot)`.

Engines: `PhiIter.iter-gv` (the one-coordinate iteration `h(m+1) = phi(h m)`, decided by
`k+2` steps and ONE comparison) and `PhiIter.phiok-comp` (`PhiOK` closed under composition,
for the cross-cycle). `BlkPass2.shape` is reused verbatim — its own hypothesis
`HPass (kv j)` follows from `PhiOK` + monotonicity (`BlkVerdict2.phiok-gv`, `MPGrow.gv-pass`).

---

## 2. THE NEGATIVE RESULTS — READ THESE BEFORE PROPOSING ANYTHING

| refuted | file | what it does NOT say |
|---|---|---|
| (I)+(G) for step **traces** ⇒ (I)+(G) for the block | `BlkGrowFail.blk-grow-lpo` | nothing about REAL PR step terms — its `kv0 n = b n + n` is not the `kv` of any PR term (`BlkGrowPR.phiok-lpo`) |
| the (lag,increment,threshold) widening of `PhiOK` | `MPGrowFail2.mpg-not-closed` | that class IS `MPGrow.GV`; widening `PhiOK` to a lag is exactly what lets `BlkGrowFail` in |
| `PhiOK` for step terms ⇒ `PhiOK` for the block | `MutUOFail.uo-fails` | nothing about `Vd2`: its `floor(m/2)` is UNBOUNDED, so the block still has `Vd2` |
| `Property.UO` for mutual blocks | `MutUOFail` | the corrected form is `MutUOWeak.BlkUOw` |

**Do not target `GV` for the block.** `Vd2` is the right conclusion, and strictly easier:
`Unb` transports along a subsequence with no rescaling, whereas `GrowN`'s period would have
to be multiplied by the subsequence's stride — and the cross-cycle runs along `g k = 2k+T`.

**Do not cite `BlkGrowFail` as showing a real block is uncomputable.** It does not.

---

## 3. THE CURRENT FRONT: DISCHARGE `vd2-blk`'s HYPOTHESIS FOR REAL STEP TERMS

`BlkVerdict2.BLK` wants `(j : Nat) -> Sigma Nat (\ k -> PhiOK k (kv j))`, where `kv j n` is
the height component `j`'s step term offers at replay depth `n`.

**The first step is FREE and already committed** (`OBSTINATION/BlkBridge.agda`):

```agda
verdict-phiok : Verdict ov -> Or (EvTot ov) (Sigma Nat (\ k -> PhiOK k (hgt o ov)))
```

`TrMP1.Verdict`'s second branch IS `Sigma k. Property.PhiOK k (hgt o ov)` — the two `PhiOK`s
(`MP1.PhiOK`, `Property.PhiOK`) unfold to the same thing, checked. And
`TrTermIv.traceOf-MP1` gives `MP1T` for the trace of EVERY PR term, so `Verdict ov_j` is
available for real step terms.

### THE OBSTACLE IS THE `EvTot` BRANCH, AND IT IS A MODEL PROBLEM

`Verdict` splits: either the step term's value goes COMPLETE (`EvTot`) or it never does and
its height is `PhiOK`. Only the second branch feeds `vd2-blk`. And `BlkTraceR`'s block trace
is **height-only** — `hv : Nat -> Nat -> Nat` — so it cannot express "this component's value
became a numeral". That is exactly what `MP1BridgeFail` refuted: a height cannot tell
`fbot k` from `fcpl k`, and `prec zerf zerf` is the witness (`TrTest.E-cpl-1`).

Two routes, and **route (i) is the one to try**:

**(i) Handle `EvTot` at the block level without changing the model.** If a step term's value
is complete from `n0` on, then past the point where the block's replay reaches `n0` that
component's contribution is a NUMERAL, so its height is eventually constant — `EvBndN`
outright, hence `Vd2` — and the OTHER component then sees a settled argument. Concretely:
add to `BlkVerdict2.BLK` a variant hypothesis

```agda
pverd' : (j : Nat) -> Or (Sigma Nat (\ n0 -> ... j's value complete from n0 ...))
                         (Sigma Nat (\ k -> PhiOK k (kv j)))
```

and check whether the `EvTot` side collapses each of `BlkPass2.shape`'s three cases to
`EvBndN`. **Check this on `prec zerf zerf` first** (its trace is `TrTest.ETr`, and
`E-cpl-1 : sem ETr (S^1 bot) = fcpl 0`) — if the collapse is not true there, say so and stop.

**(ii) Rebuild the block trace on `Tr`/`ov : Nat -> FEl`**, as `TrComp`/`TrPrec` already do
for composition and single recursion. Correct but a large rewrite of `BlkTraceR`, `MainBlk2`,
`BlkPass2`; only worth it if (i) genuinely fails.

### THE OTHER ROUTE TO `PhiOK`, AND WHY IT STALLS

Apply `Prop1.prop1` to `g_j` directly at `(inf, inf, ..., inf)`. Case 2 is impossible there
(`PRInf.valOK`'s Lemma), Case 1 is `EvTot`-like, Case 3 hands over `phi_j` with `PhiOK` at a
computable threshold. **The stall**: Case 3's side condition `X[c] >= A_0[c]` needs the
coordinates OTHER than the pinned one to have passed the approximant, and if the other
component stalls below it the clause never applies. `MainBlk2.comp-verdict` ("frozen from D
on, or replay past its own threshold at D") is the tool for that, and it is where a
counterexample would have to live.

---

## 4. SECONDARY FRONTS

* **(I) for the component WITH parameters, r = 2** — `BlkFunPar` ports the whole MP1
  parameter-direction machinery (`q-source`, `par-small`, `stretch`, `BUD`,
  `PAR.RUN.Ivb-EvConstN`) and reduces it to ONE `bsplit` interface. **The obvious `bsplit`
  is FALSE**; the file gives the concrete two-component scenario. A correct terminal clause
  must constrain BOTH components at once (`MainBlk2.comp-verdict` again), at the cost of the
  cheap half.
* **general `r`** — `BlkTraceR.main` has the index at general `r` given `st`; `MainBlk2` and
  `BlkPass2` are r = 2 only.
* **`TrSelStab.go` generalised** to an arbitrary monotone family (the `Feed` interface in
  `NEXT_SESSION_TRACE.md` §5) — still the right refactor, still not on the critical path.

---

## 5. THE FILES OF THIS LINE

| file | lines | what |
|---|---|---|
| `PRInf` / `PRInfTest` | 408 / 79 | **`prVal`, `prVal-lub`** — computability for single PR terms, with `refl` tests |
| `prinf.tex` | 355 | the write-up, incl. the mutual-recursion analysis |
| `PhiIter` | 333 | **`iter-gv`** (the self-iteration), **`phiok-comp`** (composition) |
| `BlkVerdict2` | 530 | **`BLK.vd2-blk`** + the `Vd2` toolkit (`vd2-sub`, `vd2-tail`, `vd2-comp`, `phiok-shift`, `phiok-gv`) |
| `BlkBridge` | 44 | **`verdict-phiok`** — the first step of §3, free |
| `BlkGrowPR` | 219 | **`phiok-lpo`** — `BlkGrowFail`'s block is not realised by PR step terms |
| `MPGrowFail2` | 94 | **`mpg-not-closed`** — the lag widening is refuted at r = 2 |
| `BlkFunPar` | 630 | the r = 2 WITH parameters port, reduced to `bsplit` |

Pre-existing and load-bearing: `Prop1` (Proposition 1), `Property` (`UO`, `PhiOK`, `uoValue`),
`MPGrow` (`EvBndN`, `GrowN`, `GV`, `grow-unb`, `gv-pass`), `MPPass` (`HPass`, `IterF`),
`MainBlk2` (`comp-verdict`, `MPblock`, `hgt`), `BlkPass2` (`shape`, `Stab`/`Self`/`Cross`,
`phi`, the affine law, `hpass-blk`), `BlkTraceR` (the block trace), `PhiProps`/`PhiComp`
(`phi-escape`, `sinc-mono-le/lt`).

---

## 6. TRAPS THAT COST COMPILES

* **`Vd2`, not `GV`.** See §2.
* `BlkPass2`'s big module is ANONYMOUS (`module _ (...) where`), so its members take the
  whole parameter list as explicit arguments and cannot be `open`ed — alias them
  (`BlkVerdict2.BLK` shows how: `SH = shape a iv ivr kv kv-mono Y N I iv-stab hverd`).
  The `hverd` you pass must be the SAME term everywhere or the types will not match.
* `plus` (from `BlkReplay`) recurses on its FIRST argument: `plus (suc t) K` reduces,
  `plus t (suc K)` does not (`plus-suc-r` is a lemma). `PhiProps.addN` recurses on the
  SECOND. Pick the one that makes your induction reduce.
* `Property.PhiOK` takes the threshold as an argument; `MP1.PhiOK` existentially quantifies
  it. They compose (`BlkBridge`), but watch which one a signature wants.
* `LeN` is `Top`/`Empty`-valued, so proofs of the same bound are equal — `TrScan.LeN-uniq`
  is what identifies continuations across a walk.
* Pin implicit arguments on `LeN-trans` and `Eq-transport` motives; inference stalls through
  the non-injective `plus`/`nOf`/`hgt`.

---

## COMMAND TO RUN AFTER `/clear`

```
Read OBSTINATION/NEXT_SESSION_BLKVERDICT.md first — it is the state of play, the negative
results (do NOT re-propose them), and the front.

GOAL: discharge `BlkVerdict2.BLK`'s hypothesis for REAL step terms, i.e. get from
`TrTermIv.traceOf-MP1` to `(j) -> Sigma k. PhiOK k (kv j)` and hence to
`f_i(S^w(bot), S^w(bot))` computable for a mutual block at r = 2.  `OBSTINATION/BlkBridge.agda`
is the first step and is already green: `Verdict ov` gives `EvTot ov` or exactly the PhiOK
that is wanted.  The whole difficulty is the `EvTot` branch — the step term's value goes
COMPLETE, and `BlkTraceR`'s block trace is HEIGHT-ONLY, so it cannot express that
(`MP1BridgeFail`, and `prec zerf zerf` is the witness).  Try route (i) of section 3 —
handle `EvTot` at the block level as "that component's height is eventually constant, hence
`EvBndN` outright" — and CHECK IT ON `prec zerf zerf` (`TrTest.ETr`, `E-cpl-1`) BEFORE
proving anything about it.  If the collapse is false there, say so and give the instance
rather than grinding; route (ii), rebuilding the block trace on `ov : Nat -> FEl`, is the
fallback and is a large rewrite.

Rules: `~/.cabal/bin/agda-2.9.0 --safe --without-K --exact-split` from /Users/coquand/DOMAIN;
no hole/postulate/pragma; <20 s per file; GREP `BlkPass2`, `MainBlk2`, `BlkVerdict2`,
`PhiIter` before writing any lemma (section 6 lists the traps).  Proceed autonomously; stop
only for a genuine MATH issue, and when a clause resists state the SIMPLEST CONCRETE INSTANCE
where it fails.  Everything on this line is committed on `hide-old-archives`.
```
