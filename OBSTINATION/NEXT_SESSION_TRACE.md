# FRESH SESSION — the TRACE (`iv`, `ov`) and min1.pdf, via a walk

New line of work. It **supersedes** `NEXT_SESSION_MP1.md`'s `MP1Comp` / `MP1Prec`: those are
theorems about abstract `iv`/`kv` walks, but the walk they build for a composition is WRONG
(see §6), and nothing there was ever checked against `PR.evalF`. Everything below is checked
against `evalF`.

Rules unchanged: `~/.cabal/bin/agda-2.9.0 --safe --without-K --exact-split` from
`/Users/coquand/DOMAIN`, no hole/postulate/pragma, <20 s per file, grep before writing any
lemma, find the SIMPLEST PROBLEM INSTANCE rather than grinding.

**CORRECTNESS IS DONE, AND MP1 IS REDUCED TO ITS INDEX HALF.**

```agda
traceOf     : (q : PR) (n : Nat) -> Wf q n -> Tr n
traceOf-ok  : Pair (MonoTr n (traceOf q n wf)) (Den n (traceOf q n wf) (evalF q))
traceOf-sem : Eq (length X) n -> Eq (sem n (traceOf q n wf) X) (evalF q X)
traceOf-mp1 : IvAll n (traceOf q n wf) -> MP1T n (traceOf q n wf)
```

The first three are the whole-term correctness theorem, by induction on the PR term.
The fourth says the VALUE half of MP1 -- min1.pdf's three cases -- is not an independent
obligation at all: it is Proposition 1 (`Prop1.prop1`, already proved) read along the walk's
own level chain. What was left of MP1 was `IvAll`, the sequentiality index -- and that is now done too.

**MP1 IS PRESERVED BY COMPOSITION** (`TrSelStab.compTr-ivAll-full`): from `MonoTr` and
`MP1T` of `Tg` and of every argument, `IvAll (compTr p Tg a Ths)` -- and the value clause is
free, so that is MP1 for a composition.

**MP1 IS PROVED, FOR THE TRACE OF EVERY PR TERM.**

```agda
TrTermIv.traceOf-ivAll : (q : PR) (n : Nat) (wf : Wf q n) -> IvAll n (traceOf q n wf)
TrTermIv.traceOf-MP1   : (q : PR) (n : Nat) (wf : Wf q n) -> MP1T  n (traceOf q n wf)
```

by induction on the PR term.  Nothing is left open on this line: correctness (`traceOf-ok`),
the value half (`traceOf-mp1`, = Proposition 1), the index half for composition
(`compTr-ivAll-full`) and for the recursion (`precTr-ivAll`) are all discharged.

The three steps that closed it, in order:

```agda
TrPrecIvP.precTr-ivP    : EvConstN (P.ivP p Th)          -- the top node of precTr
TrPrecIvAll.precTr-ivAll: IvAll (suc p) (precTr p Tg Th) -- + every continuation
TrTermIv.traceOf-ivAll  : IvAll n (traceOf q n wf)       -- the term induction
```

`precTr-ivP` covers BOTH regimes -- the recursive value never a numeral, and the descent
regime; `TrPrecIv.LOOP`'s hypotheses `nevV` and `nevo` are gone.  See "HOW THE DESCENT REGIME
WAS CLOSED" in section 5.  `precTr-ivAll` adds the continuations: `atNum` recurses on the
NUMERAL (via `compTr-ivAll-full`, its `MP1T` obligation discharged by the GENERAL
`TrMP1Red.mp1T-from-iv`), the parameter continuations recurse on the ARITY at the frozen base
and step (`TrPrecFun.precFun-ins` + `UOfrz-ext`).  Carrying `UOfrz` rather than bare `UO` is
what makes both recursions go through with one hypothesis.

Twenty-nine modules, **all EXIT 0** under `--safe --without-K --exact-split`, no
postulate/hole/pragma; a `--ignore-interfaces` rebuild of the whole cone is 6.3 s.

| file | lines | what it is |
|---|---|---|
| `TraceDef` | 350 | the trace `Tr a`, its semantics `sem`, `blockOn`, the base cases |
| `TrComp` | 108 | the composite trace `compTr` |
| `TrPrec` | 212 | the recursion trace `precTr` / `precCont` (+ `blockOn-range`, `argPr`) |
| `TrSat` | 572 | **saturation**: `nOf-stick`, `sem-sat`, `blockOn-sat`, `sem-bot`, `MonoF` |
| `TrDen` | 197 | `ins`/`del` laws, **`Den`**, `Den-ext` / `Den-extL`, base cases |
| `TrWalk` | 78 | `den-sem`/`den-cont`, **`lv-L`** (a walk's levels ARE its state) |
| `TrCompDen` | 484 | **`compTr-den`: the composite trace denotes the composite** |
| `TrPrecFrz` | 194 | **IMG_0270's looping criterion, proved** |
| `TrPrecFun` | 179 | **`precFun`** — primitive recursion as an operator on FUNCTIONS |
| `TrMono` | 168 | **`MonoTr`** for the constructed traces (`lev-mono`, `compTr-mono`) |
| `TrPrecDen` | 602 | **`prec-sat`, `precTr-den`, `precTr-mono`** |
| `TrTerm` | 259 | **`traceOf` / `traceOf-ok` — the whole-term theorem** |
| `TrMP1` | 145 | MP1's STATEMENT for `ov`-valued traces + the three base cases |
| `TrVerdict` | 460 | **`verdict-of`: min1.pdf's three cases ARE Proposition 1** |
| `TrUOfrz` | 275 | Proposition 1 closed under freezing a coordinate to a numeral |
| `TrMP1Red` | 75 | **`traceOf-mp1`: MP1 reduces to the index half `IvAll`** |
| `TrCompIv` | 300 | the composite's index clause reduces to `SelStab`; the DRIVE |
| `TrCompSel` | 210 | `sel` freezes when the selected argument settles; `verdict-split` |
| `TrCompNG` | 345 | `Tg`'s run along a family: `NG-freeze`, `cg-or-small`, **`scan-const`** |
| `TrScan` | 125 | `orMap`, decidable demands, the bounded search, `del-tup`, `LeN-uniq` |
| `TrSelStab` | 785 | **the bounded climb: `SelStab`, and `IvAll` for `compTr`** |
| `TrPrecIv` | 1830 | the recursion: depth direction, `BUD`, **`LOOP.ivP-EvConstN`**, `Dm-not-one` |
| `TrPrecDec` | 465 | **`Qd-stab-of` — the depth direction UNCONDITIONALLY, via Prop 1**; `Vd-mono-L`, `Vd-cpl-fixed` |
| `TrPrecPar` | 1144 | **the parameter direction, BOTH regimes**: `node-split`, `termA`/`cheapA`, `SUB.termB`/`cheapB`, `NG-frz`, `w-fixed`, `PAR.RUN`, `PAR.ivP-EvConstN` |
| `TrPrecIvP` | 78 | **`precTr-ivP` — the same, with NO hypotheses left** |
| `TrPrecIvAll` | 196 | **`precTr-ivAll` — `IvAll` for the WHOLE recursion trace** (`atNum` on the numeral, parameters on the arity) |
| `TrTermIv` | 154 | **`traceOf-ivAll` / `traceOf-MP1` — MP1 FOR EVERY PR TERM** |
| `TrTest` | 97 | `prec zerf zerf` and `plus`, values by `refl` |
| `TrShare` | 79 | `f x = g (x , x)`: the sharing regression test |
| `TrTermTest` | 145 | the same three terms through `traceOf`, values by `refl` |

---

## 1. READ THESE FIRST — the operational intuition

**`IMG_0269.jpeg`, `IMG_0270.jpeg`** (in `/Users/coquand/DOMAIN`). They are the source of
the whole design; read them before touching anything.

`IMG_0269` says what the trace IS. For an almost-closed non-constant term `t(x1..xk)`, the
normal form is `S^n(u)` with `u` a *needed variable*. Associate to `t` the sequence obtained
by repeatedly substituting `x_i := S(x_i)` for the CURRENTLY NEEDED variable:

* the first entry is `S^{n0}(u0)` with index `i0`;
* the second is the normal form of `t[x_{i0}/S(x_{i0})]`, `S^{n1}(u1)`, index `i1`; ...

so the trace is `(n_p , i_p)`, and in the "deep" reading `(n_p , a_{1p} .. a_{kp})` with
`p = a_{1p} + ... + a_{kp}`, where `a_{ip}` is how far one has gone in variable `i`.
**That is exactly `ReplayLv`'s `lv` and `sumLv`**: `a_{ip} = lv i p`, `n_p = kv p`,
`i_p = iv p`. Substituting `S(x)` feeds ALL occurrences of `x` at once — which is the whole
content of §6 below.

`IMG_0270` states the goal for `prec` — see §4, it is PROVED.

---

## 2. THE TRACE (`TraceDef`)

```agda
data Tr : Nat -> Set where            -- indexed by arity
  stop : FEl -> Tr a
  node : (iv : Nat -> Nat) -> (ivr : (n) -> iv n < a)
       -> (ov : Nat -> FEl)
       -> (cont : (c : Nat) -> c < a -> (v : Nat) -> Tr (a-1))
       -> Tr (suc a)

sem (node iv ivr ov cont) X          -- n = nOf a iv ivr (heights X)
  | ov n = fcpl w      = fcpl w                          -- already total
  | X (iv n) = fbot _  = ov n                            -- blocked
  | X (iv n) = fcpl v  = sem (cont (iv n) _ v) (del (iv n) X)
```

Two departures from the old `(iv , kv)`, both forced:

* **`ov : Nat -> FEl`, not `kv : Nat -> Nat`.** The old shape can only output `fbot _`, and
  `prec zerf zerf` — `bot` at `bot`, the COMPLETE `0` above — refutes it with no `comp` in
  sight. Recording the VALUE pointwise (rather than a height plus a halting threshold) is
  also what keeps the trace definable by induction on the term alone: a threshold would have
  to be SEARCHED for, and only MP1 could produce it.
* **`cont c _ v` — the term with coordinate `c` frozen to the numeral `v`.** `fbot v` and
  `fcpl v` both supply `v` levels, so the walk is identical until it needs level `v` there;
  `fbot v` blocks, `fcpl v` answers "0" and the computation goes on with that coordinate now
  a fixed numeral. The arity strictly drops, so `Tr` is an ORDINARY inductive family and
  `sem` is structurally recursive — no coinduction.

Companion `blockOn : Tr a -> FTup -> Or Top Nat` — `inl tt` = waiting for nothing (total, or
stuck for good), `inr c` = blocked on coordinate `c` OF THE ORIGINAL TUPLE (the index is
un-shifted through every freeze by `su`).

Base cases, each proved against `evalF`: `zerfTr-sem`, `projTr-sem`, `succTr-sem`.

---

## 3. WHAT IS PROVED

### `TrSat` — saturation, the core everything rests on

```
nOf-stick   : av <= av' , equal at the stuck coordinate  ->  same nOf
sem-sat     : X <= X' , agreeing at `blockOn T X`  ->  sem T X = sem T X'
blockOn-sat : ... same, and it stays blocked on the SAME coordinate
sem-bot     : sem T (botTup a av) = ovOf T (nOfOf a T av)
```
`sem-sat` is min1.pdf's Case 2 at trace level. Two facts carry it: `nOf-stick` (it gets at
least as far by `nOf-ge`+`Adv-mono`, and no further since the step it is stuck on needs a
level of a coordinate that has not grown), and `cpl-max` (total values are MAXIMAL, so if the
stuck coordinate of `X` is a numeral then `X'` has the same numeral there; both sides freeze
and the induction descends, `Agr` transporting along `nth-del`). `MonoTr` is needed only for
the already-total branch. `sem-bot` is the bridge between the two views of a trace — as a
function, and as a walk plus a value sequence.

### `MonoF` IS ARITY-INDEXED — do not "simplify" it away

```agda
MonoF a f = (X X' : FTup) -> length X = a -> length X' = a -> LeX X X' -> LeF (f X) (f X')
```
`LeX` compares coordinate by coordinate with `fbot zero` out of range, so
`LeX (cons (fbot 0) nil) nil` HOLDS — and `evalF succ` sends those to `fbot 1` and `fbot 0`.
The length-free `MonoF` is therefore FALSE of `evalF succ`, and the whole-term theorem cannot
be stated with it. Every use compares two tuples of the term's own arity anyway
(`TrTerm.evalF-MonoF` derives it from `Mono.evalF-mono` through `LeX-LeFTup`).

### `TrDen` — what correctness means

```agda
Den a (stop v)  f = v is f everywhere
Den (suc a) (node ..) f =
    (X) -> length X = suc a -> sem (node ..) X = f X
  , (c , v) -> Den a (cont c _ v) (\ Y -> f (ins c (fcpl v) Y))
```
`sem T X = f X` alone is NOT enough: `sem` reaches `cont c _ v` only when the walk happens to
stick on `c` at level `v`, yet `compTr` freezes an ARBITRARY coordinate in every argument. So
each continuation must denote the FROZEN function. `ins` is the inverse of `del` (`ins-del`).
`Den` is closed under pointwise equality of `f` (`Den-ext`) and, more usefully, under equality
**on tuples of the right length** (`Den-extL`) — that weaker form is what `tup-eta` and the
`succ` clause need.

### `TrCompDen` — **COMPOSITION IS CORRECT**

```agda
compTr-den : MonoTr p Tg -> Den p Tg g
           -> ((i) -> MonoTr a (Ths i)) -> ((i) -> MonoF a (h i))
           -> ((i) -> Den a (Ths i) (h i))
           -> Den a (compTr p Tg a Ths) (\ X -> g (tup p (\ i -> h i X)))
```
* FREEZE branch is free: the composite's continuation is the composite of the arguments'
  continuations, so the arity induction applies and `ins-del` restores the tuple.
* BLOCKED branch is the theorem: `sem-bot` reads each argument's value as what it denotes at
  the levels obtained so far, `botTup (suc a) LK`; `lv-L` identifies `LK` with the walk's own
  `lv`, so `levels-below` gives `LK <= hts X` and `vals K <= V` by monotonicity of the `h i`;
  and at the coordinate `g` waits on the two AGREE, because the composite sticks exactly where
  the selected argument sticks (`blkBot-shape` + `stuck-level`). `sem-sat` finishes.
* `sem-total` (a total value means `blockOn = inl tt`) discharges the case where `g` has
  already answered.

### `TrPrecFun` — primitive recursion AS AN OPERATOR ON FUNCTIONS

`PR.precF` recurses on TERMS, and that is not enough: the continuation of `precTr` at a frozen
PARAMETER is the recursion built from the FROZEN base and step, and freezing is an operation
on functions. So

```agda
precA g h (fbot 0)     Y = fbot 0
precA g h (fbot (j+1)) Y = h (fbot j , precA g h (fbot j) Y , Y)
precA g h (fcpl 0)     Y = g Y
precA g h (fcpl (v+1)) Y = h (fcpl v , precA g h (fcpl v) Y , Y)
precFun g h nil = fbot 0 ,  precFun g h (cons x Y) = precA g h x Y
```
with `precFun-eval` (it is `evalF (prec g h)` on the denotations of terms), `precFun-mono`,
`precFun-ins` (freezing parameter `1+i` = the recursion of the frozen base and step — the
clause that makes the induction on the arity go through), and `pre` / `precA-unf` / `pre-le`
(unfolding ONE successor without caring whether the argument is `fbot` or `fcpl`).

### `TrMono` — `MonoTr` FOR THE CONSTRUCTIONS

`lev-step` / `lev-mono` (a `bump` state never goes down, stated once for both `W.L` and
`P.Lv`), `ovOf-mono`, `nOfOf-mono`, `zerfTr-mono` / `projTr-mono` / `succTr-mono`, and

```agda
compTr-mono : Den p Tg g -> MonoF p g -> ((i) -> MonoTr a (Ths i))
            -> MonoTr a (compTr p Tg a Ths)
```
Note it wants `Den`+`MonoF` of the OUTER trace and never `MonoTr Tg`: `ovf k` is `g` applied
to the arguments replayed at the levels obtained after `k` steps, so its monotonicity is `g`'s
composed with `lev-mono` + `nOf-mono` + `MonoTr (Ths i)`.

### `TrPrecDen` — **PRIMITIVE RECURSION IS CORRECT**

```agda
prec-sat    : Den Th h -> MonoTr Th -> MonoF p g -> MonoF (2+p) h
            -> LeX (avP p L j) X -> Agr (inr (Qd L j)) (avP p L j) X
            -> Vd L j = precFun g h X
precTr-den  : MonoTr p Tg -> MonoTr (2+p) Th -> MonoF p g -> MonoF (2+p) h
            -> Den p Tg g -> Den (2+p) Th h
            -> Den (suc p) (precTr p Tg Th) (precFun g h)
precTr-mono : ... -> MonoTr (suc p) (precTr p Tg Th)
```

`prec-sat` is the heart and it is NOT an instance of `sem-sat`. `sem-sat` compares `sem` with
`sem`; here what is wanted is a statement about the FUNCTION the trace is supposed to denote,
and using `sem-sat` on `precTr` itself gives a tautology. So it is proved directly, by
induction on the recursion depth, with `sem-sat` used at the STEP term only. The case split is
on `blockOn Th (avT L j)`, read through `qsel`:

| `blockOn Th` | `Qd L (j+1)` | what discharges the agreement |
|---|---|---|
| `inl tt` | 0 | nothing to agree on |
| `inr 0` (the recursion argument) | 0 | `Eq-cong pre` of the hypothesis |
| `inr 1` (the recursive value) | `Qd L j` | **the induction hypothesis**, at `cons (pre x) Y` |
| `inr (2+i)` (a parameter) | `1+i` | the hypothesis, unchanged |

Only the `inr 1` row uses the IH, and there the agreement has to be pushed down through `pre`
(a further split on `Qd L j` being 0 or not). Everything else is monotonicity.

`Vd-den` is the bridge: `Vd L j = precFun g h (avP p L j)`, i.e. the chain
`Vd L 0 , Vd L 1 , ...` IS `f(bot,Y) , f(S bot,Y) , ...` with the parameters frozen at the
levels `L`. Note `avP p LK (LK 0)` is `botTup (suc p) LK` *definitionally* — that is why the
main walk's `ovP K` is `precFun g h BT` on the nose.

`atNum-den` handles the tower `f (S^(v+1) 0 , Y) = h (S^v 0 , f (S^v 0 , Y) , Y)`: it is
`compTr-den` applied `v` times, with `tup-eta` closing `tup p (\ i -> nth _ i Y) = Y`.

### `TrTerm` — **THE WHOLE-TERM THEOREM**

`traceOf` / `traceOf-ok` by induction on the PR term, threading `Prop1.Wf`. Three points
where the statement is not the naive one:

* `MonoTr` and `Den` are proved TOGETHER — `compTr-den` wants `MonoTr` of every argument,
  `compTr-mono` wants `Den` of the outer one, and neither follows from the other afterwards.
* `succ` at arity `n` is the trace of `succ o proj 0` (`succTr` itself has arity exactly 1).
* the arguments of a composition are indexed by `Nat`, not by the list, so the recursion goes
  through a mutual `traceList`: `nth zerf i hs` is not a structural sub-term of `comp g hs`.
* `prec` needs `n = suc m` from `Wf`; `precTr-at` matches that equation with `refl` instead of
  transporting, so nothing gets stuck behind an `Eq-transport`.

`TrTermTest` re-runs `E = prec zerf zerf`, `plus` and the sharing term `f x = g (x , x)`
through `traceOf` and checks the values against `evalF` by `refl`.

---

## 4. `TrPrecFrz` — IMG_0270's CRITERION, PROVED

IMG_0270: with `h`'s sequence `(n_p , x_p , y_p , z_p)`, `f = rec(x,_,(u,v)h(u,v,z))` loops in
its first argument **iff `exists p . y(p+1) = y(p)+1 and n_p <= y_p`**, and then `f`'s sequence
is ultimately `(n_p , x , z) , (n_p , x+1 , z) , ...`; otherwise it is essentially `h`'s.

Read on the walk this collapses: `y(p+1) = y(p)+1` says `h` is stuck on the RECURSIVE VALUE,
and `stuck-level` says `y_p` is exactly the height available there, `hgt (Vd L j)`, while
`n_p = hgt (Vd L (suc j))`. So the criterion is

> **`h` is blocked on the recursive value, and the value did not grow.**

and that state REPRODUCES ITSELF — the tuples at depths `j` and `j+1` differ only at the
recursion coordinate, which `h` is not waiting on, so `sem-sat`/`blockOn-sat` carry both the
value and the block one depth up:

```
F.frz-step , F.frz , F.Vd-frozen , F.Qd-frozen , F.ultimate
```
`Qd` freezes because a block on the recursive value makes `qsel` DESCEND
(`qsel prev (inr 1) = prev`). `F.ultimate` is exactly "la suite associee a f aura ultimement
la forme (n_p , x , z) , (n_p , x+1 , z) , ...".

---

## 5. MP1 — WHAT IS PROVED, AND WHAT IS LEFT

```agda
EvTot   ov = Sigma Nat (\ n -> IsCpl (ov n))                        -- Case 1
Never   ov = (n : Nat) -> ov n = fbot (hgt (ov n))
Verdict ov = Or (EvTot ov) (Pair (Never ov) (PhiOK (hgt o ov)))     -- + Cases 2, 3
MP1T  (node iv ivr ov cont) = EvConstN iv , Verdict ov , (every continuation)
IvAll (node iv ivr ov cont) = EvConstN iv ,              (every continuation)
```
Cases 2 and 3 are `MP1.PhiOK` verbatim, so everything already proved about it applies.
Case 1 must be separate: `hgt` cannot tell `fbot k` from `fcpl k`, which is what refuted the
old height-only trace (`MP1BridgeFail`). `Never` is not decoration — a monotone `ov` that
ever goes complete stays complete, so "incomplete at arbitrarily large depths" is "incomplete
everywhere", and that is what lets a caller know a coordinate will NEVER become a numeral.

### THE VALUE HALF IS PROPOSITION 1 (`TrVerdict`, `TrUOfrz`, `TrMP1Red`) — DONE

The bridge is `ov-bot`: for any `node iv ivr ov cont`,

```
ov k = sem (node ..) (botTup (suc a) (lv . k))      -- = F (botTup (suc a) (lv . k))
```

the value at replay depth `k` is the trace at ITS OWN levels after `k` steps. (`sem-bot`
gives the value as `ov` at the replay depth; `nOf-own` says the walk replayed against its own
levels gets exactly `k` steps -- every earlier step advances because the level it needed was
raised, and step `k` cannot because it was not.) So with `N` the threshold of `EvConstN iv`
and `I = iv N`, past `N` the walk raises ONLY coordinate `I`, and

```
ov (N + t) = F ( levels l_c(N) , with coordinate I at S^(l_I(N)+t)(bot) )
```

**which is exactly the family `Property.UO` speaks about**, at the point `A` with `A(I) = inf`
and `A(c) = S^(l_c(N))(bot)`. UO's Case 1 gives `EvTot`; its Case 2 is pinned at a coordinate
with `A(i)` incomplete FINITE, hence `i /= I`, and gives `ov` constant; its Case 3 is at the
infinite coordinate, which must be `I`, and hands over its own `phi` with
`hgt (ov (N+t)) = phi (l_I(N) + t)`. This is the formal content of IMG_0269.

`TrUOfrz` supplies UO for the FROZEN functions too (a continuation denotes
`\ Y -> F (ins c (fcpl v) Y)`), by exhibiting freezing as a PR operation: `comp q` with the
identity substitution, the numeral `num v` spliced in at `c`, the rest re-indexed by
`TraceDef.sd` -- the same re-indexing `nth-ins-ne` uses. The recursion is on the ARITY, not
the term (the term grows). `UO F A` only mentions `F` at tuples of length `length A`, so it
transports along agreement at that length (`UO-ext`).

Result: `TrMP1Red.traceOf-mp1 : IvAll n (traceOf q n wf) -> MP1T n (traceOf q n wf)`.

### THE INDEX HALF — COMPOSITION IS DONE, `prec` IS NOT

Base cases (`TrMP1`): `zerfTr-mp1`, `projTr-mp1`, `succTr-mp1`.

**COMPOSITION (`TrSelStab.compTr-ivAll-full`) — DONE.**

```agda
compTr-ivAll-full : MonoTr p Tg -> MP1T p Tg
                  -> ((i) -> MonoTr a (Ths i)) -> ((i) -> MP1T a (Ths i))
                  -> IvAll a (compTr p Tg a Ths)
```

It goes in four steps, and each is worth remembering because `prec` will need the analogues.

1. **The DRIVE** (`TrCompIv.CI.Sel.dep-drive-b`). While `selC k = j`, the composite's next
   demand IS the level argument `j`'s replay is stuck on, so raising it advances that replay
   (`nOf-step`, from `stuck-level` + `bump-eq`): `dep (s+K) j >= s + dep K j`. Hence
   `compTr-ivAll`: `selC` eventually constant ==> `ivf` eventually constant, via
   `EvConstN (ivOf (Ths j))`.
2. **The FREEZING half** (`TrCompSel`). `blockOn-sat` needs agreement only at the coordinate
   `Tg` waits on, so `inl tt` is stable outright (`sel-inl-stable`) and `inr j` is stable as
   soon as `vals . j` stops moving (`sel-frozen`, `settles-frozen`). `verdict-split` turns
   `Verdict` into `OvSettles` / `OvGrows`, both with COMPUTABLE thresholds -- that is what
   makes the searches bounded.
3. **The BOUND on `Tg`'s progress** (`TrCompNG`). The demand `inr (cg k)` is a function of
   the replay depth `NG k` alone (`blk-stuck`); `NG-ge-hts` (`stuck-level` + `lv-le`) says
   `NG k >= hts (V k) (cg k)`, so a coordinate whose height grows drags `NG` up with it; and
   `NG-freeze` says a DESCENT freezes `NG`, `cg` and the continuation FOR EVER.
4. **The CLIMB** (`TrSelStab`). One round at a stage waiting on `j`: if `Ths j` settles,
   drive `n1` steps and freeze; if it grows, drive `M + n1` steps and `sinc-grow` +
   `NG-ge-hts` put `NG` past ANY target in one shot; if the scan fails, that stage is
   `inl tt`, or a descent, or the demand moved -- and then `cg` changed, so `NG` strictly
   grew. `reach` iterates with fuel; `phase2` (past `EvConstN ivg`'s threshold, where `cg` is
   constant) rules the third outcome out and finishes on `Verdict ovg` and
   `ovTot-or-never`. `go` recurses structurally on `Tg` at a descent.

**PRIMITIVE RECURSION — OPEN, and the generalisation check has been DONE.**  The index is

```
ivP k = R.Qd (P.Lv k) (P.Lv k zero)      -- Qd folds `qsel` DOWN the recursion chain
```

The fact the definitions hide, and everything turns on: **`avT L j` does NOT mention `L 0`**.
The chain depends on `L` only through the PARAMETER levels.  So the walk is two-dimensional
and the two dimensions do not interfere:

* `ivP k = 0`   ==> the depth `D k = Lv k 0` grows by one, the parameter levels are UNCHANGED,
  so the chain is the old one with ONE MORE FOLD STEP;
* `ivP k = 1+i` ==> the depth is unchanged, parameter `i` grows, the chain is RECOMPUTED.

**THE DEPTH DIRECTION is done modulo the generalisation.**  Two lemmas, both proved:

* `TrPrecIv.QD.Qd-evconst` -- `blockOn Th (avT L .)` eventually constant ==> `Qd L .`
  eventually constant, one step later, because `qsel _ R` is idempotent in `R`
  (`qsel-idem`);
* `TrPrecIv.PZ.stretch` -- and then a BOUNDED CHECK decides a stretch of the walk: if
  `Qd (Lv K) .` is constant from `J+1` on, then `ivP` being `0` for the first `J+2` steps
  forces it to be `0` FOR EVER.  So a `0`-stretch either settles the index outright, or ends
  within `J+2` steps at a stage demanding a PARAMETER.  (`PZ.Vd-cong` / `PZ.Qd-cong` carry
  it: the chain does not see `L 0`.)

`avT L .` IS a monotone family in `j` (coordinate 0 grows by exactly one per step, coordinate
1 is `Vd`, the parameters are fixed), with the drive automatic, so `Qd-evconst`'s hypothesis
is exactly what `TrSelStab`'s climb proves -- once the climb is GENERALISED from the
composite's own family `Vs` to an arbitrary monotone family.  That generalisation looks clean and would
probably be shorter than the current file: drop `sh` and `orMap` (a descent gives
`Dem k = shiftOr c (Dem' k)`, and `shiftOr` reflects eventual constancy), and replace the two
uses of the composite's own data by one hypothesis --

```
Feed = (c : Nat) -> c < q -> (M K : Nat) -> Sigma Nat (\ s ->
         <demand is `inr c` throughout [K , K+s]>
         -> Or <`V . c` constant from `K+s` on> (LeN M (hts (V (plus s K)) c)))
```

-- which is precisely what `verdict-split` + `dep-drive-b` deliver for the composite
(`OvSettles` gives `s = n1+1` and the left branch, `OvGrows` gives `s = M+n1` and the right).

**THE PARAMETER DIRECTION.**  The composite's freezing half does NOT transfer, and it is
worth knowing why before trying: a composite argument may SETTLE, and
`TrCompSel.settles-frozen` freezes the selection when it does, but a PARAMETER never settles
-- it is `fbot (L (1+i))` and the walk grows exactly the coordinate it demands.  Growing it
also perturbs the WHOLE chain (any lower depth blocked on the same parameter moves, and every
value above it is recomputed), so there is no `Qd`-analogue of `blockOn-sat` either.  The
simplest instance is `h (x,r,z) = z`, i.e. `Th = proj 2`: every depth is blocked on the same
parameter.  That instance still settles, so the difficulty was always finding a MEASURE, not
a counterexample (and `p = 0` is outright trivial -- `R.Qd-range` forces `Qd L m = 0`).

**THE MEASURE, AND IT COMES STRAIGHT FROM min1.pdf.**  The note's `prec` case turns on the
FINITENESS of the approximant `A_0` that ultimate obstination hands back for `h` at
`(S^w(bot), S^w(bot), Y)`: above `A_0`, `h` no longer looks at the parameters at all.  Read
on the trace, that finiteness is

```agda
TrCompNG.NGf.cg-or-small :   -- `Nh` , `stab` = the threshold of `EvConstN ivh`
    Or (Eq (cg k) (ivg Nh))                       -- the demand IS the eventual one
       (LeN (suc (hts (V k) (cg k))) Nh)          -- or the demanded height is BELOW `Nh`
```

-- proved from `NG-ge-hts` (`stuck-level` + `lv-le`: the demanded coordinate's height is
below the replay depth) plus `nle-lt`.  **A coordinate that is always incomplete and only
grows when demanded can therefore be demanded at most `Nh` times before the demand has
settled**, so the parameters give a fuel of `p * Nh`.  That is exactly what was missing.

**AND THE DESCENT TOWER COLLAPSES.**  `TrPrecIv.PZ.avT-incpl`: in `avT L j` coordinate 0 is
`fbot j` and coordinate `2+i` is `fbot (L (1+i))`, so ONLY coordinate 1 -- the recursive
value -- can ever be complete.  Hence `blockOn Th (avT L j)` descends at most ONCE, at
coordinate 1, into an all-incomplete tuple that cannot descend again; and once it does
descend the numeral is maximal, so the continuation is fixed for ever (as in `NG-freeze`).
The recursion has none of the composite's descent tower.

**SO THE PROOF PLAN IS NOW COMPLETE -- AND CHEAPER THAN GENERALISING THE CLIMB.**  The depth
direction does NOT need `TrSelStab` generalised at all: along the depth the family `avT L .`
is so constrained that a BOUNDED SCAN settles it.  Of the four demands, two freeze outright
(both proved):

```agda
TrPrecIv.PZ.Dm-inl-frozen  -- waiting on NOTHING is for ever
TrPrecIv.PZ.Dm-par-frozen  -- waiting on a PARAMETER is for ever
```

-- because along the depth only coordinates 0 and 1 move, the parameters being constant in
`j`, so `blockOn-sat` applies with no further argument (`PZ.avT-mono` supplies the
monotonicity, from monotonicity of `Vd`).  The other two are "waits on `x`" and "waits on the
recursive value", and the second is IMG_0270's criterion, i.e. `TrPrecFrz` -- a ONE-STEP,
DECIDABLE check (`Vd L (j+1) = Vd L j`).  So:

**The general engine for all of this is now proved** (`TrCompNG.NGf`):

```agda
tail-const : past the threshold, with nothing going complete, the demand IS the
             eventual index -- for ever
scan-const : if nothing ever goes complete, ONE coordinate `dom` has height at least
             the stage number, and every OTHER coordinate is constant, then AT MOST TWO
             DECISIONS settle the demand -- no climb at all
```

`scan-const` is exactly the shape of the recursion's POST-DESCENT family, and

```agda
TrPrecIv.post-stab : MonoTr (suc p) T -> MP1T (suc p) T
                   -> `blockOn (suc p) T (parV p L .)` eventually constant
```

is proved: once the recursive value is a numeral, `blockOn Th` descends at coordinate 1, and
by `PZ.avT-incpl` it cannot descend again, so what it descends into is
`(S^j(bot), S^(L 1)(bot), ..., S^(L p)(bot))` -- only the depth moves, and `scan-const`
settles it.

Left, then:

**And the accounting for the pre-descent scan is proved** (`TrPrecIv`): `leF-ne-hgt` -- an
incomplete value that changes has a STRICTLY GREATER height -- and `run-up` -- a sequence
that strictly increases over a stretch grows at least as fast as the stretch.  So `Nh` steps
of "waits on the recursive value, criterion has not fired" push `hgt (Vd L .)` past `Nh`, and
`NG-ge-hts` + `cg-or-small` then say the demand has settled.

**THE DEPTH DIRECTION IS DONE, UNCONDITIONALLY:**

```agda
TrPrecDec.Qd-stab-of : MonoTr Th -> MP1T Th -> Den Th h -> MonoF g -> MonoF h
                     -> ((A) -> length A = suc p -> UO (precFun g h) A)
                     -> `R.Qd p Th L .` eventually constant
```

The decision `Dm-stab` needed -- does the recursive value ever become a numeral? -- is
answered by `TrPrecDec.decide`, i.e. by PROPOSITION 1 applied to the chain: `Vd-den` says
`Vd L j = precFun g h (avP p L j)`, and `avP p L .` is EXACTLY the family `UO` speaks about
at the point whose coordinate 0 is `S^w(bot)`.  Case 1 gives the numeral; Cases 2 and 3 give
"never" (incomplete at arbitrarily large `j`, hence -- monotone plus `cpl-max` -- incomplete
everywhere).  Same move as `TrVerdict.verdict-of`, at a simpler family.

Underneath:

```agda
Dm-stab      : ... -> Or (Vd ever a numeral) (Vd never a numeral)
             -> `blockOn Th (avT L .)` eventually constant
Qd-stab-full : ... same hypothesis ...  -> `Qd L .` eventually constant
```

built from two scans, each bounded by `Th`'s own threshold `Nh`:

* `pre-stab` (the recursive value is NEVER a numeral, so nothing ever descends): the three
  ways out are `Dm-inl-frozen`, `Dm-par-frozen` and IMG_0270's criterion (`TrPrecFrz.F.frz`,
  a one-step decidable test), and otherwise the demanded coordinate's height GREW -- the
  depth in the `x` case, the value's height in the other (`leF-ne-hgt`) -- so `NG-grow` makes
  the replay depth strictly increase.  **Every continuing step costs one unit of replay
  depth**, so the two moving coordinates may interleave freely and no separate accounting is
  needed: the scan is bounded by `Nh` outright, and `tail-const` finishes.
* `post-desc` (it IS a numeral from `j0` on, hence maximal, hence fixed): the same three-way
  scan, except that "waits on the recursive value" now DESCENDS -- and `NG-freeze` pins the
  continuation for ever while `delEq` identifies the family with `parV`, which `post-stab`
  settles.

Left, then:

1. ~~the PRE-descent scan~~ -- DONE (`pre-stab`), as is the descent case (`post-desc`).  At each `j` decide
   `blockOn Th (avT L j)`: `inl tt` or a parameter ==> frozen, done; the recursive value with
   `Vd L (j+1) = Vd L j` ==> `TrPrecFrz`, done; otherwise continue.  If the scan runs to the
   end, then `NG-ge-hts` gives `NH j >= Nh` -- from `hts = j` in the `x` case, and from
   `hgt (Vd L j)` in the recursive-value case (`leF-ne-hgt` + `run-up`) -- so `cg-or-small`
   says the demand IS `Th`'s eventual index, constant for ever.  Mind the accounting: the two
   cases INTERLEAVE, so scan to `2*Nh` and argue that either some `x`-step at or above `Nh`
   occurs (then `NG >= Nh` at once) or every step in `[Nh , 2*Nh]` is a recursive-value step
   (then `run-up` gives `hgt (Vd L (2*Nh)) >= Nh`).  `NG` is monotone, so the maximum over
   earlier steps is available at the end.  Then `QD.Qd-evconst` turns that into `Qd L .` eventually
   constant, and `PZ.stretch` into: every `0`-stretch of the walk either settles the index or
   ends within a computable number of steps at a stage demanding a PARAMETER.
2. ~~THE DECISION~~ -- DONE (`TrPrecDec.decide`).  For the record, it was:: does `Vd L .` ever become a numeral?
   Answer it with PROPOSITION 1 applied to the chain -- `TrPrecDen.Vd-den` says
   `Vd L j = precFun g h (avP p L j)`, and `avP p L .` is EXACTLY the family `Property.UO`
   speaks about at the point whose coordinate 0 is `S^w(bot)` and whose parameters sit at `L`.
   Case 1 gives the numeral (at a computable stage), Cases 2 and 3 give "never" (via
   monotonicity and `cpl-max`, as in `TrVerdict`).  This is the same move `TrVerdict.verdict-of`
   makes, at a different family -- most of `TrVerdict`'s `dtup`/`ptD`/`Approx` machinery is
   reusable, and the family here is simpler (coordinate 0 grows by exactly one per step).
3. **THE PARAMETER DIRECTION -- THE ONLY THING LEFT.  The alternation worry is RESOLVED.**

   The link is `TrPrecIv.PZ.Qd-source` and its dual `PZ.Qd-zero-source` (both PROVED): `Qd`
   is a fold, so `Qd L D = 1+i` forces `h` to demand coordinate `2+i` at some depth
   `j* < D`, and `Qd L D = 0` forces `h` to demand `x` or NOTHING at some depth below `D` --
   unless EVERY depth descends (waits on the recursive value).

   I worried that the fuel bounds only how many DIFFERENT parameters can be demanded, not an
   ALTERNATION between `0` and the surviving one.  It does not happen, and the reason is
   `PZ.Qd-indep-par` / `PZ.Qd-indep-zero` (PROVED):

   > `qsel _ (inr (2+i)) = 1+i` and `qsel _ (inl tt) = qsel _ (inr 0) = 0` do not look at the
   > accumulator, so once the depth demand has settled on anything BUT the recursive value,
   > **the parameter levels drop out** and `Qd L D` is a constant read off `Th`'s settled
   > demand alone.

   So an `ivP = 0` step needs a depth where `h` waits on `x` or on nothing, and by
   `cg-or-small` such a depth has `NH < Nh`, i.e. is SHALLOW -- while an `ivP = 1+i` step past
   the fuel has `NH >= Nh`.  The two cannot alternate for ever: `h` needs at most `Nh` levels
   of `x`, so once the depth passes `Nh` no deep depth waits on `x` again, and each parameter
   bump exhausts one unit of the shallow budget.

   **The terminal half of the fuel is PROVED**: `TrPrecIv.Qd-par-const` says that if at some
   depth `J` the step term's replay is already past `Nh` and its eventual demand `ivh Nh` is a
   PARAMETER `2+i`, then `cg-past` gives that demand at EVERY depth above `J`, nothing
   descends there (a parameter is never a numeral), and so `Qd L D = 1+i` for every `D > J`.
   And the hypothesis SURVIVES A BUMP -- raising a parameter only raises the tuple, so `NG`
   only grows -- so a bump whose parameter is already at level `Nh` fixes the index FOR EVER.

   So the dichotomy is complete: by `cg-or-small`, a parameter bump either costs one unit of
   a budget of `p * Nh` (its level was below `Nh`) or is terminal (`Qd-par-const`).

   **The budget itself is PROVED too** (`TrPrecIv.BUD`):

```agda
   Mof k  = sum over the parameters of (min (level) Nh)
   M-bound : Mof k <= p * Nh
   M-step  : a CHEAP bump raises `Mof` by exactly one
   M-max   : at the bound, every bump must be the TERMINAL kind
```

   and the terminal hypothesis SURVIVES a bump, because the chain is monotone in the
   parameter levels: `TrPrecDec.Vd-mono-L` (from `Vd-den` + `precFun-mono`), hence
   `avT-mono-L`, hence `NG` monotone in `L` by `nOf-mono`.

   **AND THE ASSEMBLY IS DONE, IN BOTH REGIMES** (`TrPrecPar`, `TrPrecIvP`):

```agda
   TrPrecPar.PAR.ivP-EvConstN : EvConstN (P.ivP p Th)          -- 3 chain hypotheses
   TrPrecIvP.precTr-ivP       : EvConstN (P.ivP p Th)          -- NO hypotheses
```

   `precTr-ivP` takes only what an actual PR trace has -- `MonoTr`, `MP1T`, `Den`, the two
   `MonoF`s, and `Prop1`'s `UO (precFun g h)` -- and discharges the three chain facts from
   `TrPrecDec` (`Vd-mono`, `Vd-mono-L`, `Vd-tot-or-never`).  `LOOP`'s two hypotheses `nevV`
   (the recursive value is never a numeral) and `nevo` (the outer value never total) are
   BOTH GONE.  `TrPrecIv.LOOP` is now history: it is the main-phase special case.

### HOW THE DESCENT REGIME WAS CLOSED (`TrPrecPar`, 1144 lines, EXIT 0)

   At the source depth `j` that `PZ.Qd-source` names, decide `IsCpl (NN.at L j)` -- is the
   coordinate `h` is stuck on COMPLETE?

   * **(A) no** -- the demand is the top-level one, `ivh (NG L j) = 2+i0`, and the analysis is
     `LOOP`'s: `termA` (past the threshold, the demand persists at every later stage AND every
     greater depth) or `cheapA` (the parameter's level is below the threshold);

   * **(B) yes** -- then `PZ.avT-incpl` forces that coordinate to be 1, the recursive value, so
     `blockOn` DESCENDS.  `descEq` rewrites the demand as

     ```
     Dmj L j = shiftOr 1 (blockOn (suc p) (Tw w) (parV p L j))     w = hgt (Vd L j)
     ```

     and `shiftOr-inv` turns `f`'s demand `2+i0` into `Tw w`'s demand `1+i0`.  The SAME
     dichotomy then applies one level down (`SUB.termB` / `SUB.cheapB`).

   **Three facts make (B) a two-level analysis and not a regress**, all of them the
   "propriete remarquable" of IMG_0269 read on the trace:

   1. `parV` has NO complete coordinate (`parV-incpl`), so `Tw w` cannot descend again;
   2. a descent FREEZES the top level in BOTH directions (`NG-frz`, by `ReplayLv.nOf-freeze`):
      the replay is stuck on coordinate 1, whose value is complete hence MAXIMAL, so `NG` is
      pinned at every greater depth and every greater parameter setting.  Hence `cg`, the
      continuation, and `ovh (NG)` are all fixed -- `liftUp` is exactly this;
   3. `Tw w` itself is fixed once and for all (`w-fixed`): two stages at which the recursive
      value is complete give the SAME numeral, by `cpl-max` at the pointwise maximum of the
      two depths.  **So the walk changes regime AT MOST ONCE**, and `Q1` is a single number.

   This is the point the manuscript's "cette suite a des proprietes remarquables" settles:
   bumping a parameter does not RECOMPUTE the ladder `f(bot,y), f(S bot,y), ...`, it moves
   further along the SAME sequence.  The formal content is `blockOn-sat` / `nOf-freeze` /
   `nOf-sat`: a demand past its threshold never moves again.  That is why the descent level
   does not have to be re-established stage by stage -- the worry that had blocked this.

   **`ov` GOING TOTAL is handled uniformly at both levels** by `node-split`: it returns ONE
   threshold `Q` past which the index is the eventual one AND `ov` is either never complete or
   complete throughout.  In the second case the demand past `Q` is `inl tt`, which CONTRADICTS
   the parameter demand we started from -- so the terminal branch is vacuous and every bump is
   cheap.  That is how `nevo` disappeared.

   **The loop is parametric** (`PAR.RUN`): a bound `B`, a start stage `k0`, and a `bsplit`
   returning `Persist | cheap | an answer outright`.  `RUN` is instantiated TWICE --
   `bsplitA` with `B = Q0` from stage 0, escaping into `goB` on the first descent; `bsplitB`
   with `B = maxN Q0 Q1` from the descent stage.  The escape happens at most once (fact 3), so
   there is no recursion between them.

   ONE IMPLEMENTATION WRINKLE: `blockOn` descends into `conth c lc v` where `lc` is
   `ivhr (NG k)` -- and across the walk `NG` GROWS, so those continuations are the same trace
   only up to the proof argument.  `TrScan.LeN-uniq` is what identifies them (`conth-cong`).

   Mind also the third alternative of `Qd-zero-source` -- EVERY depth descending -- which is
   `qsel _ (inr 1) = prev`, the one clause that keeps a dependence on the chain below; there
   IMG_0270's criterion (`TrPrecFrz`) is the tool and `Dm-stab` already handles it.

### THE CONTINUATIONS OF `precTr`, AND THE TERM INDUCTION — BOTH DONE

   `IvAll (suc p) (precTr p Tg Th) = Pair (EvConstN ivP) (every continuation)`.  The first
   component is `precTr-ivP`; the second is `TrPrecIvAll.precTr-ivAll`:

```agda
   precCont p Tg Th zero    lc v = N.atNum p Tg Th v
   precCont (suc p) Tg Th (suc i) lc v =
     precTr p (contOf Tg i lc v) (contOf Th (suc (suc i)) lc v)
```

   * `c = 0`: `atNum 0 = Tg`, `atNum (v+1) = compTr (suc (suc p)) Th p (argsA v)` -- an
     induction on `v` using `TrSelStab.compTr-ivAll-full`, whose `MP1T` obligations for the
     arguments come from `TrMP1Red.mp1T-from-iv` (GENERAL: `Den`, `MonoTr`, `UOfrz`, `IvAll`
     give `MP1T`).  `TrPrecDen.atNum-mono`/`atNum-den` supply the rest.  NOTHING about
     `precTr` is used, so the two recursions do not interleave.
   * `c = 1+i`: a recursion on the ARITY `p`, at the FROZEN base and step, where
     `TrPrecFun.precFun-ins` (freezing a parameter of a recursion IS the recursion of the
     frozen base and step) plus `UOfrz-ext` reproduce the hypothesis one arity down.

   **THE HYPOTHESIS MUST BE `UOfrz (suc p) (precFun g h)`, NOT BARE `UO`** -- that is what
   makes both recursions go through with one assumption.  Freezing coordinate 0 to `fcpl v`
   turns `precFun g h` into `\ Y -> precA g h (fcpl v) Y`, which is exactly what `atNum v`
   denotes, so the `c = 0` component of `UOfrz` serves the numeral recursion and the
   `c = 1+i` component serves the arity recursion.  `TrUOfrz.uofrz-PR` supplies it.

   And then `TrTermIv.traceOf-ivAll`: the whole-term `IvAll n (traceOf q n wf)` by induction on
   the PR term (base cases `TrMP1.zerfTr-mp1` etc., `succ` and `comp` by `compTr-ivAll-full`,
   `prec` by `precTr-ivAll`), with `TrMP1Red.traceOf-mp1` turning each sub-result into the
   `MP1T` the next construction needs.  `TrTermIv.traceOf-MP1` is MP1 for every PR term.

Generalising `TrSelStab.go` to an arbitrary monotone family (the `Feed` interface above) is
still the right refactor eventually, but it is NOT on the critical path.


---

## 6. THE BUG THAT WAS FOUND, AND WHY THE STATE IS WHAT IT IS

`TrShare` is the regression test. With

```
g (0 , v) = 0 ,  g (S u , v) = v          -- one level of u, then v
f (x)     = g (x , x)                     -- so f is the identity
```

the FIRST `compTr` (and the old `MP1Comp`, which has the same
`ivf k = ivs (sel k) (st k (sel k))`) drove the arguments ONE STEP AT A TIME. The second copy
of `x` then re-demanded level 0, the `lv`-counting replay charged it a SECOND time, and the
composite answered `S^1 bot` at `S^2 bot`. The information a computation needs from a
coordinate is the MAX over the arguments, not the SUM — substituting `S(x)` feeds every
occurrence at once (IMG_0269).

**The fix, and it made the construction simpler.** The state is the composite's OWN LEVELS,
and each argument is REPLAYED against them:

```agda
L 0 = 0~ ,  L (k+1) = bump (ivf k) (L k)
dep  k i = nOfOf (Ths i) (L k)
vals k   = ( ovOf (Ths i) (dep k i) )_i
ovf k = sem Tg (vals k)     sel k = blockOn Tg (vals k)
ivf k = ivOf (Ths (sel k)) (dep k (sel k))
```
Raising a level advances EVERY argument waiting for it, and the demanded cell is always fresh
(the selected argument is stuck at `ivf k`, so by `stuck-level` it needs exactly level
`L k (ivf k)`). No per-argument step counter, no `bumpS`.

**Moral: check every construction against `evalF` before proving anything about it.** The bug
survived a full MP1 development because nothing was ever evaluated.

---

## 7. TOOLING NOTES / PITFALLS

* `OBSTINATION/TraceComp.agda`, `Trace*.agda` are DAVID's traces (`rdavid.pdf`, tokens
  `xtok`), a different development. The new files are `TraceDef` + `Tr*`. Do not overwrite.
* `where`-bound helpers are lifted with the module telescope and are then UNREACHABLE from a
  proof. Every function a proof must reason about (`hlt`, `brf`, `hb`, `bb`, `pick`,
  `projPick`, `semAt`, `blockAt`, `argPr`, `precCont`) is TOP-LEVEL for that reason. Keep it
  that way — `argPr` and `precCont` were pulled out of `where` blocks precisely to prove §3.
* **`precTr` builds its `node` uniformly in `p`**, with the case analysis in the separate
  top-level `precCont`. Without that, `precTr p Tg Th` does not reduce to a `node` for a
  variable `p`, and no statement about `sem (precTr p Tg Th)` can be proved at an abstract
  arity. Do not fold `precCont` back in.
* Pattern matching on a defined term gets a `SplitError`: abstract as
  `go : (e : Nat) -> Shape e -> Eq e d -> ...` and call `go d (shape d) refl`. The same trick
  is `go (ov n) refl` / `br (nth _ (iv n) X) refl` throughout `TrSat`/`TrCompDen`, and
  `ago (blockOn ...) refl` / `down (Qd L j) refl` in `prec-sat`.
* `nOf av = find av zero (suc (sumTo a av))`: the FUEL depends on `av`, so Agda cannot infer
  it; and `nOf-cong` needs agreement at EVERY coordinate — that is why `L-out`
  ("`L k c = 0` outside the arity") has to be proved before `sem-bot` can be used.
  (`precTr-main` needs no `sem-bot`, hence no `L-out`: `Vd-den` connects `ovP` to `precFun`
  directly.)
* `refl` will not compute a walk at a SYMBOLIC height: tests must use concrete numerals
  (`TrTest`, `TrTermTest`).
* `ReplayLv` is richer than it looks: `nOf-ge`, `nOf-le`, `nOf-cong`, `nOf-mono`,
  `nOf-below-adv`, `nOf-sat`, `nOf-freeze`, `lv-le`, `levels-below`, `sumLv`, `Adv-mono`, and
  **`Round2.result`**. GREP IT FIRST. `WalkAffine.stuck-level` and `affine` are the two most
  useful lemmas in the repo.
* `MonoF` is arity-indexed and `Verdict`'s second branch carries `Never` — both are
  load-bearing, see §3 and §5. Do not "simplify" either away.
* `MP1BridgeFail.agda` records why the OLD trace was wrong (`prec zerf zerf`, and
  `comp (prec (proj 0) (proj 0)) [zerf, proj 0]`). Keep it; it is the reason `ov` is
  `FEl`-valued.

---

## COMMAND TO RUN AFTER `/clear`

Read OBSTINATION/NEXT_SESSION_TRACE.md, and look at IMG_0269.jpeg and IMG_0270.jpeg in
/Users/coquand/DOMAIN.

DONE: correctness (`TrTerm.traceOf-ok`); the reduction of MP1 to its INDEX half
(`TrMP1Red.traceOf-mp1` — min1.pdf's three cases are Proposition 1 read along the walk's own
level chain, §5); and MP1 for COMPOSITION (`TrSelStab.compTr-ivAll-full`). Twenty-four
modules, all EXIT 0, pragma/postulate/hole-free, 5.1 s for the whole cone from scratch.

THE GOAL IS `IvAll (precTr p Tg Th)`, and then the whole-term `IvAll` by induction on the PR
term. **§5 now carries a complete proof plan in three steps**, with both missing ingredients
found and verified: `TrCompNG.cg-or-small` (min1.pdf's finiteness of `A_0`, read on the trace
— a demanded coordinate is either the eventual one or has height below the walk's threshold,
which is the MEASURE bounding parameter bumps) and `TrPrecIv.PZ.avT-incpl` (only the
recursive value can be a numeral, so the descent tower collapses to at most one step). The plan does NOT need
`TrSelStab` generalised: along the depth a BOUNDED SCAN suffices (two of the four demands
freeze outright — `PZ.Dm-inl-frozen`, `PZ.Dm-par-frozen`, both proved — and the third is
IMG_0270's one-step criterion). Start at step 1. §7 lists the tooling traps.

READ min1.pdf ITSELF, not just the repo's formalisation of it: its `prec` case is where the
measure comes from.

`~/.cabal/bin/agda-2.9.0 --safe --without-K --exact-split` from /Users/coquand/DOMAIN; no
hole/postulate/pragma; <20 s per file; GREP `ReplayLv`, `TrSat`, `TrDen`, `TrMono`,
`TrCompNG`, `TrScan` and `WalkAffine` before writing any lemma. Proceed autonomously; stop
only for a genuine MATH issue, and when a clause resists state the SIMPLEST CONCRETE INSTANCE
where it fails rather than grinding.
