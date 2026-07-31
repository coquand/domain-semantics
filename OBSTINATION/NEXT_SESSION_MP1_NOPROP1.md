# MP1 WITHOUT PROPOSITION 1 — **DONE**, and with it the value at the all-infinite point

Goal: prove **Prop 1 from MP1**, so MP1's closure properties must not use Prop 1.
Rules as usual: `~/.cabal/bin/agda-2.9.0 --safe --without-K --exact-split` from
`/Users/coquand/DOMAIN`; no hole/postulate/pragma; < 20 s per file.

---

## 0. THE SITUATION, ESTABLISHED MECHANICALLY

There is **no circularity**: `Prop1`'s transitive import cone is 64 modules and contains no
`Tr*`, `MP1*`, `Blk*`. `Prop1.prop1` is proved by induction on PR terms, independently.

But every use of Prop 1 inside MP1 is **self-referential** — it consumes `UO` of the very
term being analysed, not of its parts. So the trace line *presupposes* Prop 1 and cannot
yield it, and cannot port to mutual blocks (where `UO` is false, `MutUOFail`).

Prop 1 entered `prec` at exactly **two** points:

| where | what it wanted | status |
|---|---|---|
| `TrPrecIvP.precTr-ivP` → `TrPrecDec.Vd-tot-or-never` | `UO (precFun g h)`, to decide whether the recursion chain ever becomes a numeral | **REMOVED** (§1) |
| `TrMP1Red.mp1T-from-iv` → `TrVerdict.verdict-of` / `TrUOfrz.uofrz-PR` | `UO` of the term and its frozen restrictions, to supply `Verdict ov` | **OPEN** (§3) |

`Vd-mono` and `Vd-mono-L` never used Prop 1 (they are `Den` + monotonicity).

---

## 1. DONE — THE INDEX HALF FOR `prec` IS NOW PROP-1-FREE

```agda
TrPrecIvPMP.precTr-ivP-mp
  : (p : Nat) (Th : Tr (suc (suc p))) (g h : FTup -> FEl)
  -> MonoTr (suc (suc p)) Th -> MP1T (suc (suc p)) Th -> Den (suc (suc p)) Th h
  -> MonoF p g -> MonoF (suc (suc p)) h
  -> EvConstN (P.ivP p Th)
```

— `TrPrecIvP.precTr-ivP`'s extra hypothesis `(A : Tup) -> Eq (length A) (suc p) -> UO (precFun g h) A`
is **gone**. It was spent only on `Vd-tot-or-never`, and

```agda
TrPrecDecMP.DEC.decide
  : Or (Sigma Nat (\ j0 -> IsCpl (V j0))) ((j : Nat) -> Not (IsCpl (V j)))
```

proves that from **`TrMP1.Verdict ovh` alone** — the induction hypothesis, already in
`precTr-ivP`'s scope as `fst (snd m1th)`.

### The two lemmas it rests on

**`TrPrecChain.CH.step`** — while `V j` is incomplete, every coordinate of `g`'s argument
tuple `(S^j bot, V j, params)` is a `fbot`, so the tuple is a `botTup` and `TrSat.sem-bot`
collapses `g`'s semantics to one lookup:

```agda
step : (j : Nat) -> Bt (V j) -> Eq (V (suc j)) (ovh (NJ j))
```

No continuation is ever entered — a continuation is entered only at a coordinate that has
gone complete (`TraceDef.brf`), and none has.

**The decision** then splits on `Verdict ovh`:

* `Never ovh` → the chain never completes, by induction. Immediate.
* `EvTot ovh` at `n0` → `ovh n` is complete for every `n >= n0` (`cpl-max` + `MonoTr`), so
  scan `V 0 … V B` for `B = 2*n0+1`. If one is complete, done. If none is, then `NJ i < n0`
  for every `i < B`, `NJ` is monotone, so a **repeat** `NJ (i+1) = NJ i` occurs with
  `n0 <= i` (else `NJ` would have climbed `n0+1` times), and `ReplayLv.nOf-sat` turns it into
  a permanent freeze: past it the two height vectors differ only in coordinate 0, both are
  already `>= n0` there, and the replay sticks strictly below `n0`.

---

## 2. DONE — THE STALL DICHOTOMY (the tool the value half needs)

```agda
TrPrecStall.ST.stall-not-zero : Eq (NJ (suc j)) (NJ j) -> Not (Eq (ivh (NJ j)) zero)
TrPrecStall.ST.stall-perm     : Bt (V j) -> Bt (V (suc j))
                              -> Eq (NJ (suc j)) (NJ j)
                              -> Eq (NJ (suc (suc j))) (NJ (suc j))
```

**The replay can never stall on the recursion argument.** At depth `j` the walk reached step
`NJ j`, so `lv 0 (NJ j) <= AV j 0 = j` (`ReplayLv.find-below`, exported here as `nOf-below`);
being still stuck at that same step one depth later would need `lv 0 (NJ j) >= j+1`. The
recursion argument is the one coordinate that grows by one per depth **all by itself**.

So a stall is on the recursive value or on a parameter, and both are permanent — a parameter
never moves, and a stall pins the recursive value (`step` twice). Hence:

> **either `NJ` strictly increases at every depth, or it is frozen from the first stall on.**

---

## 2b. DONE — **phi FOR THE RECURSION, FROM MP1 OF THE STEP TERM ALONE**

```agda
TrPrecPhi.PHI.chain-phiok : PhiOK (\ j -> hgt (V j))
```

i.e. **the number of successors of `f(S^j bot, Y)` is eventually constant or strictly
increasing in `j`** — from `Verdict ovh`, `EvConstN ivh`, monotonicity, and "the chain never
answers". **This is IMG_0270's theorem.** With `g`'s sequence `(n_p, x_p, y_p, z_p)`,
Thierry's criterion

> `f` boucle dans son premier argument ssi il existe `p` tel que `y(p+1) = y(p)+1` et `n_p <= y_p`

is exactly a STALL: `y(p+1) = y(p)+1` is `ivh p = 1`, and `n_p <= y_p` is
`hgt (ovh (NJ j)) <= lv 1 (NJ j)`, the replay being blocked on the recursive value. §2 says
such a stall is permanent, and then `f`'s sequence is ultimately `(n_p, x, z), (n_p, x+1, z), …`
— `ConstFrom`. Otherwise `NJ` strictly increases at every depth and `g`'s own `PhiOK`
transfers verbatim ("en gros comme la suite `h`").

**The search is BOUNDED**, which is what was missing, and both halves of MP1 for `g` pay for
it. A stall is never on the recursion argument (§2), so past `EvConstN ivh`'s threshold `Nh`
the stalled coordinate is the eventual demand `Ih`:

* `Ih = 0` — impossible, so any stall is below depth `Nh`;
* `Ih >= 2` — a parameter: `lv Ih` grows by one per step past `Nh` (`lv-pump`) while
  `find-below` caps it at that parameter's own level, so any stall is below `Nh + AV 0 Ih + 1`;
* `Ih = 1` — the recursive value: a stall needs `hgt (ovh (NJ j)) <= lv 1 (NJ j) <= hgt (V j)`,
  while `StrictIncFrom k0` forces `hgt (V (j+1)) > hgt (V j)` once the replay is past `k0`,
  so any stall is below `k0 + 1`.

One search of length `max (Nh + AV 0 Ih) k0 + 1` decides it (`SI.no-stall-suc`, `SI.run`).
The `EvTot ovh` case cannot avoid stalling at all (`TOT.tot-phiok`), and the `ConstFrom k0`
case needs no stall analysis (`CF.cf-phiok`).

---

## 2c. DONE — **THE GENERAL FEED LEMMA**

```agda
TrFeed.FEED.feed-verdict : Verdict (\ t -> sem q T (Y t))
```

`T` a trace with MP1 (`Verdict ov`, `EvConstN iv` — the IH); `Y t` a family of argument
tuples, monotone, **never complete**, every coordinate with `PhiOK` heights. No Prop 1.

Same engine as §2b, one level up. `sem-bot` collapses it to `sem q T (Y t) = ov (M t)` with
`M t = nOf q iv ivr (heights of Y t)`, and at each `t` the replay is stuck on `d = iv (M t)`
with `lv d (M t) = ` the height coordinate `d` offers (`stuck` + `find-below`). So past `d`'s
threshold there is no third possibility — `d` constant ⟹ **frozen for ever** (`frozen`);
`d` strictly increasing ⟹ it grows by the exact level the replay wanted ⟹ **advance**
(`advance`). Deciding is bounded: if `M` has not frozen by `K + Ng` then `M ≥ Ng`, so the
stuck coordinate is the single eventual demand `I`, whose regime `regP I` already names.

---

## 2d. DONE — **MP1 IS PRESERVED BY `comp`, WITHOUT PROP 1**

```agda
TrCompMP1.compTr-verdict : Verdict (W.ovf p Tg a Ths)
TrCompMP1.compTr-MP1     : Verdict (W.ovf …) * IvAll (suc a) (compTr p Tg (suc a) Ths)
```

from `MonoTr`/`MP1T` of the outer trace and of every argument, and nothing else.

**The index clause was ALREADY Prop-1-free** — checked mechanically: the whole `comp` cone
(`TrComp`, `TrCompDen`, `TrCompIv`, `TrCompNG`, `TrCompSel`, `TrSelStab`) never mentions
`Prop1`/`Property`/`UOfrz`, and `TrSelStab.compTr-ivAll-full` takes exactly the IHs. So only
the VALUE clause was missing, and it is now proved:

* **`TrCompVal.SEMf`** — `sem-inl` / `sem-fbot` / `sem-descend`, the value-side twins of
  `TrCompNG`'s `blk-inl` / `blk-fbot` / `blk-descend`, plus **`CT-freeze`**: after a descent
  `NG-freeze` pins the replay, hence `cg`, hence the frozen level, so the continuation
  descended into is the SAME trace for ever.
* **`TrCompVerdict.fedV`** — the general theorem, by **structural recursion on the outer
  trace**: a trace fed a monotone family whose demand `blockOn p T (V k)` is eventually the
  constant `inr J` has a `Verdict`, given `J`'s own `OvSettles`/`OvGrows`.
  - *settles* → `sem-sat` needs agreement only at the coordinate the trace waits on, so the
    value is CONSTANT — no case analysis at all;
  - *grows, and the demanded coordinate goes complete* → descend, and recurse on a trace of
    strictly smaller arity with that coordinate deleted;
  - *grows, no descent* → decided by a **bounded search of length `Ng`** (the threshold of
    `EvConstN ivg`): without a descent the replay strictly increases (`NG-grow`), so after
    `Ng` steps it is past `Ng`, the demanded coordinate is the eventual index `J` for ever,
    and `J`'s value is never complete — so `sem = ovg ∘ NG` with `NG` strictly increasing and
    the outer trace's own `PhiOK` transfers verbatim.
  Also `fedV-inl` (waiting for nothing ⟹ constant) and `verdictFrom-verdict`.
* **`TrCompMP1`** — the instantiation. `TrSelStab.SS.selStab` gives stability of `sel` **as an
  `Or Top Nat`**, not merely of its index, so one case split suffices; and argument `J`'s own
  `Verdict`, split by `TrCompSel.verdict-split`, transports from `J`'s private replay depth to
  the composite's clock by the DRIVE (`TrCompIv.CI.Sel.dep-step` / `dep-drive`): while `J` is
  selected the composite raises exactly the level `J` is stuck on. **That is the only place
  the sharing of variables between `f1,f2,f3` matters, and it is where `TrComp`'s design — one
  shared level function, each argument replayed against it — pays.**

---

## 2e. DONE — **THE FED VERDICT WITHOUT DEMAND-STABILITY, AND `prec`'s PARAMETER DIRECTION**

```agda
TrFeedR.fedR       : MonoTr p T -> MP1T p T -> (V) -> monotone
                   -> ((c : Nat) -> Sigma kc. FixC V kc c + GroC V kc c)
                   -> VerdictFrom K (\ k -> sem p T (V k))

TrPrecParPhi.PAR.unroll : (c : Nat) -> VerdictFrom zero (\ t -> R.Vd p Th (Lt t) c)
```

`fedV` needs the demand `blockOn p T (V k)` to be eventually `inr J`; for a COMPOSITE that
comes free from `selStab`, for the RECURSION nothing supplies it. `fedR` removes the
hypothesis, replacing it by a REGIME per coordinate —

* `FixC V kc c` : the coordinate's VALUE never moves again past `kc`;
* `GroC V kc c` : it is never complete and its height grows by ≥1 at EVERY step past `kc`,

which is what the recursion does supply. The engine is the same dichotomy: `ReplayLv.stuck`
says the level the replay needs IS the height the stuck coordinate offers, so `FixC` ⟹ stuck
for ever, `GroC` ⟹ advance; hence `NG` strictly increases until it freezes, and a bounded
search of length `Ng` decides which. Then the demand IS eventually constant and `fedV`
finishes — except when the settled coordinate is a numeral, where `fedR` descends and recurses
at a strictly smaller arity.

**`TrPrecParPhi`** is the payoff: for `f(S x,y) = g(x, f(x,y), y)` with `f`'s walk raising a
parameter, the recursion depth is frozen at some `c` and layer `c+1` is `g` applied to
`(S^c(bot), layer c, S^(Lt t 1)(bot), …)`. Every coordinate has one of the two regimes — the
recursion argument and the frozen parameters are `FixC`, a growing parameter is `GroC`, and
the middle coordinate is whichever its own verdict says (`vf-reg`, which unpacks a
`VerdictFrom` into a regime). Induction on `c`, each layer one `fedR`.

---

## 2f. DONE — **MP1's VALUE CLAUSE FOR `prec`, WITHOUT PROP 1**

```agda
TrPrecOvP.ovP-verdict : Verdict (P.ovP p Th)
```

from `MonoTr`/`MP1T` of the step term, `Den`/`MonoF`, and `EvConstN (P.ivP p Th)` — the index
clause, Prop-1-free since §1.

`ovP k = Vd (Lv k) (Lv k 0)` is `f`'s value along `f`'s OWN walk, and past `EvConstN ivP`'s
threshold `N` that walk raises ONE coordinate `I`. Reading off `Lv (k+1) = bump (ivP k) (Lv k)`:
every coordinate other than `I` is frozen at `Lv N` (`Lv-ne`), and `I` grows by exactly one per
step (`Lv-I`). So there are two shapes and each already had its theorem:

* **`I = 0`** — parameters frozen, recursion argument growing, so
  `ovP (N+t) = Vd (Lv N) (c+t)` (by `Vd-cong-L`): this is the CHAIN. `chainV` packages
  `TrPrecDecMP.DEC.decide` (does it ever answer?) with `TrPrecPhi.PHI.chain-phiok` (IMG_0270's
  `PhiOK` if it does not), handling a `stop` step term separately; then a shift by `c`
  (`phiok-shift-r` + `phiok-cong-from`).
* **`I >= 1`** — recursion depth frozen at `c`, one parameter growing, so
  `ovP (N+t) = Vd (Lt t) c` with `Lt t = Lv (N+t)`: this is the UNROLLING, and `Lv-ne`/`Lv-I`
  are *exactly* `PAR`'s `Lt-reg`, so `TrPrecParPhi.PAR.unroll` applies verbatim.

`shiftVF` turns a verdict on the tail `t |-> ovP (N+t)` into one on `ovP`, using only that
`ovP` is monotone (`Vd-mono` + `Vd-mono-L`, both Prop-1-free).

---

## 2g. **DONE — MP1 FOR THE TRACE OF EVERY PR TERM, WITHOUT PROPOSITION 1**

```agda
TrTermMP1.traceOf-MP1np : (q : PR) (n : Nat) (wf : Wf q n) -> MP1T n (traceOf q n wf)
```

**The goal of this line is reached.** The same induction as `TrTermIv.traceOf-MP1`, but
carrying `MP1T` directly instead of `IvAll` plus `TrMP1Red.mp1T-from-iv` — which is exactly
where Proposition 1 entered, through `TrUOfrz.uofrz-PR`.

| clause | `comp` | `prec` |
|---|---|---|
| index | `TrSelStab.compTr-ivAll-full` (always was) | `TrPrecIvPMP.precTr-ivP-mp` (§1) |
| value | `TrCompMP1.compTr-verdict` (§2d) | `TrPrecOvP.ovP-verdict` (§2f) |

and two structural recursions thread them: `compTr-MP1T` on the outer arity, and
`precTr-MP1` on the arity of the recursion with `atNum-MP1` for the numeral continuations.
**`UOfrz` has disappeared** — `atNum-MP1` recurses on itself exactly where `atNum-ivAll`
called `mp1T-from-iv`.

### VERIFIED MECHANICALLY

* the import cone of `TrTermMP1` (125 modules) does **not** contain `TrUOfrz`, `TrMP1Red`,
  `TrPrecIvAll` or `TrTermIv` — the modules that APPLY `prop1`;
* the only thing any file of this line takes from `Prop1` is `Wf` / `AllWf`, the
  well-formedness PREDICATE (`TrTermMP1` line 35), not the theorem;
* no file mentions `prop1`, `UO`, `uofrz` or `Property.*` outside comments.

---

## 2h. **MP1 ALONE DOES NOT IMPLY PROP 1 — and what is missing**

```agda
TrUOFail.uo-fails : UO (\ _ -> fbot zero) (cons (cpl zero) nil) -> Empty
```

with `T = stop (fbot zero) : Tr 1`, which has **everything MP1 asks for** —
`MonoTr 1 T = Top`, `MP1T 1 T = Top`, `Den 1 T (\ _ -> fbot zero)` — and whose denotation
violates `Property.UO` at the ALL-COMPLETE point `A = (0)`.

**Why.** At an all-complete `A` the three cases leave no room: Case 2 wants a coordinate of
`A` that is incomplete and finite, Case 3 wants one that is `S^omega(bot)`, and `A` has
neither — so Case 1 must hold and the value must be a NUMERAL. A constant `S^m(bot)` is not.

So `Prop 1 from MP1` is **not** a repackaging of `verdict-of`: it needs TOTALITY, which a
trace does not know. That is now available:

```agda
PRTot.evalF-tot : (q : PR) (X : FTup) -> Wf q (length X) -> AllCpl X -> IsCpl (evalF q X)
```

— a PR term applied to numerals returns a numeral, by the same induction that defines `evalF`
(the recursion clause unrolls exactly `j` times, `precF-cpl`).

This costs `TrTermMP1.traceOf-MP1np` nothing: that direction is proved and uses no Prop 1.

---

## 2i. **DONE — `f(S^w(bot), …, S^w(bot))` IS COMPUTABLE, FROM MP1, NO PROP 1**

```agda
PRInfMP1.prValMP     : (q : PR) (n : Nat) -> Wf q n -> D
PRInfMP1.prValMP-lub : IsLub (Chain q n) (prValMP q n wf)
```

`PRInf` proves the same thing by reading `Property.uoValue` off `Prop1.prop1`. This proves it
from `TrTermMP1.traceOf-MP1np`, so the whole cone is Prop-1-free — **and that is the point**:
it is the form that ports to mutual blocks, where `Property.UO` is FALSE (`MutUOFail`) but the
trace-level statement survives.

**It is short because the all-infinite point is the easy point.** Nothing is complete and
nothing is finite, so the trace never descends and never blocks, and `TrSat.sem-bot` collapses
the whole chain to a single lookup:

```
evalF q (S^m bot, …, S^m bot)  =  ov (NN m) ,   NN m = nOf n iv ivr (m,…,m)  >=  m
```

— the walk spends at most one level per step (`ReplayLv.lv-le`), so `NN` is cofinal and the
lub of the chain IS the lub of `ov`. Then `Verdict ov` names it outright, exactly as
`uoValue` does but with no `UO` anywhere:

| `Verdict ov` | lub |
|---|---|
| `EvTot` at `n0` | `embed (ov n0)` — a numeral |
| `Never` + `ConstFrom k` | `bot (hgt (ov k))` — `S^h(bot)` |
| `Never` + `StrictIncFrom k` | `inf` — `S^w(bot)` |

Only the third needs work, and only for the LEAST part: `PhiProps.phi-escape` makes the
heights unbounded, so neither `bot K` nor `cpl K` can bound the chain.

`PRInfMP1Test` checks by `refl` that it RUNS and agrees with `PRInf`: `prec zerf zerf` gives
`cpl 0`, `proj 0` and `succ o proj 0` give `inf`, `zerf` gives `cpl 0`. Verified to
discriminate. The cone (126 modules) contains no `PRInf`, `TrUOfrz`, `TrMP1Red`, `TrTermIv`
or `TrPrecIvAll`.

---

## 3. THE FRONT

**The two things asked for are done, both Prop-1-free:**

1. the sequentiality index is eventually constant — that is MP1's index clause,
   `TrTermMP1.traceOf-MP1np`;
2. `f(S^w(bot), …, S^w(bot))` is computable — `PRInfMP1.prValMP` / `prValMP-lub`.

What is left is to carry this to MUTUAL BLOCKS, which was the point of making it Prop-1-free:
`Property.UO` is false there (`MutUOFail`) so `PRInf`'s route cannot be ported, but the trace
route can. The obstacle is on the block side, not here: see
`NEXT_SESSION_BLKVERDICT.md` §3 — `BlkTraceR`'s block trace is HEIGHT-ONLY, and `BlkRealGap`
is the machine-checked instance where that is wrong. The fix (route (ii) there) is to rebuild
the block trace on `ov : Nat -> FEl` with continuations, which is exactly the shape
`TrCompVal.SEMf` / `TrCompVerdict.fedV` / `TrFeedR.fedR` now provide for single terms.

Full `Prop 1 from MP1` is NOT needed for that, and in any case cannot follow from MP1 alone
(§2h) without `PRTot.evalF-tot`.

---

## 4. FILES

| file | lines | what |
|---|---|---|
| `TrPrecChain` | 167 | `CH.step` — the chain is a lookup in `g`'s trace while incomplete; `tup-cong-le`, `Bt` |
| `TrPrecDecMP` | 420 | `DEC.decide` — chain completion decided from `Verdict ovh`, **no Prop 1** |
| `TrPrecIvPMP` | 74 | `precTr-ivP-mp` — MP1's index clause for `precTr`, **no Prop 1** |
| `TrPrecStall` | 202 | `nOf-below`, `stall-not-zero`, `stall-perm` — the stall dichotomy |
| `TrPrecPhi` | 500 | **`PHI.chain-phiok`** — phi for the recursion, IMG_0270's theorem, **no Prop 1** |
| `TrFeed` | 569 | `FEED.feed-verdict` — the never-complete feed lemma (subsumed by `fedV` for descents) |
| **`TrCompVal`** | **138** | `sem-inl`/`sem-fbot`/`sem-descend` + **`CT-freeze`** |
| **`TrCompVerdict`** | **649** | **`fedV`** — the fed-trace Verdict, structural recursion incl. descents |
| **`TrCompMP1`** | **222** | **`compTr-verdict`, `compTr-MP1`** — MP1 preserved by `comp`, **no Prop 1** |
| **`TrFeedR`** | **468** | **`fedR`** — the fed Verdict with no demand-stability hypothesis |
| **`TrPrecParPhi`** | **317** | **`PAR.unroll`** + `vf-reg` — `prec`'s parameter direction |
| **`TrPrecOvP`** | **444** | **`ovP-verdict`** — MP1's value clause for `prec`, **no Prop 1** |
| **`TrTermMP1`** | **288** | **`traceOf-MP1np`** — MP1 for every PR term, **no Prop 1** |
| **`TrUOFail`** | **114** | **`uo-fails`** — MP1 alone does NOT give Prop 1 |
| **`PRTot`** | **131** | **`evalF-tot`** — totality on numerals (needed only for full Prop 1) |
| **`PRInfMP1`** | **314** | **`prValMP`, `prValMP-lub`** — the value at `S^w(bot)`, **no Prop 1** |
| **`PRInfMP1Test`** | **43** | `refl` checks that it runs and agrees with `PRInf` |

All EXIT 0, no postulate/hole/pragma, < 0.5 s each. None of them mentions `Prop1`,
`Property`, `UO` or `uofrz` outside comments.

The originals (`TrPrecIvP`, `TrPrecDec`) are untouched and still green, so nothing downstream
has moved yet; switching `TrPrecIvAll` over to `precTr-ivP-mp` is a one-line change once the
value half is settled (it still needs `UOfrz` for `atNum-ivAll` in any case).
