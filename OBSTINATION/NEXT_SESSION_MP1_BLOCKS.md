# DOES THE PROP-1-FREE ARGUMENT GENERALISE TO MUTUAL RECURSION?

Rules: `~/.cabal/bin/agda-2.9.0 --safe --without-K --exact-split` from `/Users/coquand/DOMAIN`;
no hole/postulate/pragma; **< 20 s per file**; **grep before writing any lemma** (§6 lists what
exists, §7 the traps); proceed autonomously; stop only for a genuine MATH issue, and when a
clause resists **state the SIMPLEST CONCRETE INSTANCE where it fails** rather than grinding.

Everything below is on branch `hide-old-archives`, all EXIT 0, no postulate/hole/pragma.

---

## 1. THE STARTING POINT (all Prop-1-free)

```
TrTermMP1.traceOf-MP1np : MP1T n (traceOf q n wf)          -- for every PR term
PRInfMP1.prValMP        : (q : PR) (n : Nat) -> Wf q n -> D
PRInfMP1.prValMP-lub    : prValMP q n wf IS the lub of  evalF q (S^m bot, ..., S^m bot)
```

Verified mechanically: `TrTermMP1`'s 126-module cone contains no `TrUOfrz`, `TrMP1Red`,
`TrPrecIvAll` or `TrTermIv` — the modules that APPLY `prop1` — and the only thing taken from
`Prop1` is the well-formedness PREDICATE `Wf`. Write-up: `prinf.tex` (§2 is the trace and MP1,
informal). Detail of the construction: `NEXT_SESSION_MP1_NOPROP1.md`.

Two things to keep in mind:

* **MP1 does NOT imply Proposition 1** (`TrUOFail.uo-fails`): `stop (fbot 0)` has full MP1 and
  denotes a constant `bot`, whose `UO` fails at an all-complete point. The missing ingredient
  is totality, `PRTot.evalF-tot`. So do not try to route anything through `UO`.
* **`Property.UO` is FALSE for blocks** (`MutUOFail.uo-fails`, height `floor(m/2)`). That used
  to block the whole enterprise; it no longer does, because `PRInfMP1` never goes through `UO`.

---

## 2. THE QUESTION

For a block of `r` functions

```
f_j(S x, y) = g_j(x, f_1(x,y), ..., f_r(x,y), y),      1 <= j <= r
```

with each `g_j` a PR term (so each has a trace with full MP1, by §1): is the value
`f_j(S^w(bot), ..., S^w(bot))` computable, by the same argument?

**The target is MP1 with `PhiOK` weakened to `Vd2`.** `MutUOFail` rules out `PhiOK` for the
block components (`floor(m/2)` is neither constant nor strictly increasing), but `Vd2` — the
bare bounded-or-unbounded verdict — is all that `PRInfMP1`'s Theorem consumes:

```
Vd2 h = EvBndN h + Unb h                                  (BlkVerdict2)
blockVerdict j : Or (EvTot (V j)) (Pair (Never (V j)) (Vd2 (hgt o V j)))
```

where `V j` is component `j`'s chain of Kleene approximants. `EvBndN` names `S^h(bot)`, `Unb`
names `S^w(bot)`, exactly as in `PRInfMP1`'s three-way reading.

---

## 3. WHAT PORTS VERBATIM — DO NOT REDO IT

The engine of the Prop-1-free proof is stated for **a trace fed a monotone family of argument
tuples** and never mentions how the function was defined. A block's components ARE such a
family. In particular:

| already proved, generic | file |
|---|---|
| the collapse: while nothing is complete, `sem T X = ov (stick X)` | `TrSat.sem-bot`, used via `TrPrecChain.CH.step` |
| the three-way case analysis of `sem` at a node | `TrCompVal.SEMf` (`sem-inl`/`sem-fbot`/`sem-descend`) |
| a descent FREEZES the replay, so the continuation is fixed | `TrCompNG.NG-freeze`, `TrCompVal.CT-freeze` |
| stuck-coordinate dichotomy + bounded search + descent recursion | `TrCompVerdict.fedV`, `TrFeedR.fedR` |
| `EvConstN` for each step term's walk | `TrTermMP1.traceOf-MP1np` |

So the block work is **not** to reprove any of this. It is to put a block's components into
the shape these lemmas already accept.

---

## 4. WHAT DOES *NOT* PORT — THE ONE REAL DIFFERENCE

The `prec` proof (`TrPrecStall`) rests on two facts about a stall of the step term's replay:

1. **a stall is never on the recursion argument** — that coordinate grows by one per depth all
   by itself, while `find-below` caps the level consumed at the depth one lower;
2. **a stall on anything else is permanent** — a parameter never moves again, and a stall pins
   the recursive value (`V(j+2) = ov(N(j+1)) = ov(N j) = V(j+1)`), so the coordinate it waits
   on does not move either.

**Fact 1 ports verbatim.** The block's unfolding depth is still a coordinate that grows by one
per depth on its own, and `find-below` is generic. This is the first thing to check, and it
should be a transcription of `TrPrecStall.stall-not-zero`.

**Fact 2 does NOT port**, and this is exactly the mutual dependence: `g_1` may stall on the
value of component 2, which keeps moving because it is driven by `g_2`. A stall of component
`i` is permanent when it is on a parameter, or on `i`'s own value; when it is on ANOTHER
component's value it lasts only until that component grows.

That three-way split — stall on a parameter / on itself / on the other component — is
precisely `BlkPass2`'s `Stab` / `Self` / `Cross`, and the whole r = 2 analysis on top of it
already exists **at the height level**:

```
BlkVerdict2.BLK.vd2-blk : ((j) -> Sigma k. PhiOK k (kv j)) -> (j) -> Vd2 (\ m -> HGT m j)
BlkReal.BLOCK.vd2 / .val  -- instantiated at real PR step terms, with `pverd` discharged
                          -- by BlkPhiOK.pr-phiok (the EvTot branch collapses)
```

So at r = 2 the combinatorics is done. What is missing is that it is done on HEIGHTS.

---

## 5. THE OBSTACLE, AND IT IS MACHINE-CHECKED

`BlkTraceR`'s block trace records `hv : Nat -> Nat -> Nat` — a height per component per
unfolding — not a value. That is faithful while no component answers:

```
BlkRealDen.FAITH.faithful : NC -> Eq (hgt (Ap m j)) (HGT m j)
```

(`Ap` = the real Kleene approximants from `PR.evalF` alone; `NC` = no component's value is ever
complete). It is **wrong** as soon as one answers, and there is a two-line instance:

```
BlkRealGap :  f0 = 0 ,  f1 = plus(f0, S f1)
   real:  f1 = bot 0, bot 0, bot 1, bot 2, ...   (ap1-step, by refl)  ==>  value inf
   trace: f1 frozen at bot 0                     (gap-val1, by refl)
```

The cause is the third clause of `sem`: a coordinate that has gone complete makes the
computation **descend into a continuation**, and a height cannot see that.

---

## 6. THE PLAN

**Rebuild the block trace on values and continuations**, as the single-term traces already are.
Concretely:

1. **`stall-not-zero` for a block** — transcribe `TrPrecStall.stall-not-zero`. Cheap, and it
   is the load-bearing half of §4. Do this first; if it fails, say where.
2. **The block chain as a lookup** — the analogue of `TrPrecChain.CH.step`: while no component
   is complete, component `j`'s value at unfolding `m+1` is `ov_{g_j}` at `g_j`'s replay depth
   against `(m, hgt(V^1_m), ..., hgt(V^r_m), L)`. This is `sem-bot` again and should be short.
3. **The value-level block trace** — replace `hv : Nat -> Nat -> Nat` by `Nat -> Nat -> FEl`,
   with the descent at a component that answers. `TrCompVal.SEMf` + `CT-freeze` is the model:
   a descent freezes that component's replay, so the continuation is FIXED and the block
   recurses at strictly smaller arity, at most `r + (number of parameters)` times.
4. **The r = 2 verdict on values** — redo `BlkVerdict2`'s `Stab`/`Self`/`Cross` assembly with
   `ov` in place of `kv`. The `Vd2` toolkit (`vd2-sub`, `vd2-tail`, `vd2-comp`, `phiok-shift`,
   `PhiIter.iter-gv`, `phiok-comp`) is height-only and survives unchanged; what changes is the
   step law that feeds it.
5. **The value at the infinite point** — then `PRInfMP1`'s Theorem applies with `Vd2` in place
   of the verdict: at `Delta_infty` nothing is complete and nothing is finite, so the block
   never descends and never blocks, and the chain is cofinal in the same way.

**Note on step 4:** do NOT target `PhiOK` for the block (`MutUOFail`), and do NOT target the
global growth verdict `GV` (`BlkGrowFail`). `Vd2` is the right conclusion and is strictly
easier — `Unb` transports along a subsequence with no rescaling.

---

## 7. NEGATIVE RESULTS — READ BEFORE PROPOSING ANYTHING

| refuted | file | what it does NOT say |
|---|---|---|
| `Property.UO` for mutual blocks | `MutUOFail.uo-fails` | nothing about `Vd2`: `floor(m/2)` is unbounded, so the block still has `Vd2` |
| (I)+(G) for step traces ⇒ (I)+(G) for the block | `BlkGrowFail.blk-grow-lpo` | nothing about REAL PR step terms — its `kv0 n = b n + n` is not the `kv` of any PR term (`BlkGrowPR.phiok-lpo`) |
| the (lag,increment,threshold) widening of `PhiOK` | `MPGrowFail2.mpg-not-closed` | that class IS `MPGrow.GV`; widening `PhiOK` to a lag is what lets `BlkGrowFail` in |
| the height-only block trace, off the obstinate cone | `BlkRealGap` | it IS faithful on that cone (`BlkRealDen`) |
| MP1 ⇒ Prop 1 | `TrUOFail.uo-fails` | nothing about MP1 itself, which is proved |

Also refuted and **not to be reopened**: `Property.UO` as the route (it is false for blocks);
the (lag,increment,threshold) invariant; `rN` for mutual generalisation.

---

## 8. TRAPS

* `BlkPass2`, `MainBlk2`, `BlkTraceR` are ANONYMOUS modules (`module _ (...) where`), so their
  members take the whole parameter list explicitly and cannot be `open`ed — alias them
  (`BlkVerdict2.BLK` and `BlkRealDen` show how). The `hverd` you pass must be the SAME term
  everywhere.
* `BlkReal.sel` makes the block's data TOTAL in the component index (everything from `1` on is
  component 1). Prove things about it by matching `zero` / `suc zero` / `suc (suc _) ()`.
* `plus` (from `BlkReplay`) recurses on its FIRST argument; `TrPrecDecMP.pl` and
  `PhiProps.addN` on the SECOND. Pick the one that makes your induction reduce.
* `Property.PhiOK` takes the threshold as an argument; `MP1.PhiOK` existentially quantifies it.
  They compose, but watch which one a signature wants.
* `TraceDef.nOfOf` is `zero` at a `stop`, while `nOf a (ivOf T) (ivrOf T)` is not —
  `TrPrecStall.nOf-below` and `TrCompVerdict`'s `sem-bot-acc` pattern exist for exactly that.
* `LeN` is `Top`/`Empty`-valued, so proofs of the same bound are equal (`TrScan.LeN-uniq`).
* Pin implicit arguments on `LeN-trans` and `Eq-transport` motives.

---

## 9. THE FILES

**The Prop-1-free single-term line** (input to everything above):
`TrPrecChain`, `TrPrecStall`, `TrPrecDecMP`, `TrPrecPhi`, `TrPrecIvPMP`, `TrPrecParPhi`,
`TrPrecOvP` (recursion); `TrCompVal`, `TrCompVerdict`, `TrCompMP1` (composition); `TrFeed`,
`TrFeedR` (the generic fed-trace lemmas); `TrTermMP1` (the theorem); `PRInfMP1`,
`PRInfMP1Test` (the value at the infinite point); `TrUOFail`, `PRTot` (what MP1 does not give).

**The block line as it stands**: `BlkTraceR` (the height-only block trace), `MainBlk2`,
`BlkPass2`, `BlkVerdict2` (the r = 2 `Vd2` assembly), `BlkPhiOK`, `BlkReal`, `BlkRealDen`,
`BlkRealTest`, `BlkRealGap`. Handoff for that line: `NEXT_SESSION_BLKVERDICT.md`.

---

## COMMAND TO RUN AFTER `/clear`

```
Read OBSTINATION/NEXT_SESSION_MP1_BLOCKS.md first — it is the state of play, the negative
results (do NOT re-propose them), and the plan.

CONTEXT: MP1 is now proved for every PR term WITHOUT Proposition 1
(`TrTermMP1.traceOf-MP1np`), and with it the value at the all-infinite point
(`PRInfMP1.prValMP` / `prValMP-lub`).  Proposition 1 is not used and is not needed; it is also
FALSE for mutual blocks, so this is the only route that can port.

QUESTION: does the Prop-1-free argument generalise to a block
`f_j(S x, y) = g_j(x, f_1(x,y), ..., f_r(x,y), y)`?  Target = MP1 with `PhiOK` weakened to
`Vd2` for the block components (section 2), which is all `PRInfMP1`'s theorem consumes.

START WITH SECTION 6 STEP 1: transcribe `TrPrecStall.stall-not-zero` to a block — a stall of a
step term's replay is never on the unfolding depth, because that coordinate grows by one per
unfolding all by itself while `find-below` caps the level consumed one depth lower.  That is
the load-bearing half; its companion (`stall-perm`) is exactly what does NOT port, because
`g_1` may stall on component 2's value, which keeps moving (section 4).  If step 1 fails,
state the SIMPLEST CONCRETE INSTANCE rather than grinding.

Then steps 2-3: the block chain as a lookup (`sem-bot`, the analogue of `TrPrecChain.CH.step`),
and the value-level block trace with descents (`TrCompVal.SEMf` + `CT-freeze` is the model).
The height-level r = 2 combinatorics already exists (`BlkVerdict2.vd2-blk`, `BlkReal`); what is
missing is doing it on values, and `BlkRealGap` is the machine-checked instance showing why
heights are not enough.

Rules: `~/.cabal/bin/agda-2.9.0 --safe --without-K --exact-split` from /Users/coquand/DOMAIN;
no hole/postulate/pragma; <20 s per file; GREP `BlkVerdict2`, `BlkPass2`, `MainBlk2`,
`TrCompVerdict`, `TrFeedR` before writing any lemma (section 8 lists the traps).  Proceed
autonomously; stop only for a genuine MATH issue.
```
