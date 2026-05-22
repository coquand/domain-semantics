# NEXT SESSION — finish the kernel TYPING (eliminate `PaperTyping`'s 3 `TERMINATING` pragmas)

## THE GOAL (one sentence)
Make **`MIN/PaperTyping.agda` have zero `TERMINATING` pragmas** (currently **3**, lines 34 / 73 / 147)
by stage-stratifying the membership predicate `FinMem` exactly the way the kernel ORDER was done
last session, then re-found `PaperTyping` as a thin re-export shim — and `~/.cabal/bin/agda-2.9.0
--without-K MIN/PiInjectivity.agda` still exits 0.

After this, the whole `PiInjectivity` cone is **TERMINATING-pragma-free** (the order is already done).

## WHY THIS IS STRICTLY EASIER THAN THE ORDER (read this first)
Last session's hard part was the **`EvalFun ↔ order` cycle**. **Typing has no cycle.** `FinMem`
depends on the order and on `EvalFun`, and *both are already pragma-free* in the `MIN/LeqStage*`
layer (see `project-leqstage-progress`). So `FinMem`'s only source of non-termination is that it
**recurses at a strictly smaller iterative-stage RANK** — it is a pure RANK-stratification of a
**Set-valued** predicate. Stratifying a Set predicate is *invisible* (like `Val2`, like the order's
`LeCode`): you keep the public `FinMem` STRUCTURAL so it still unfolds definitionally, stratify a
parallel `FinMem_n`, prove closure + stability, and bridge. **No value-function needs re-founding.**

## THE METHOD THAT WORKED FOR THE ORDER (replicate it — it is validated)
The 6 `MIN/LeqStage*` files are your template. The moves that made it work, in order of importance:

1. **Keep the public types STRUCTURAL.** `LeCode`/`LeFunCode` were kept as the *original structural
   definitions* (NOT `:= LeqC`), so `LeCode (PiCode a f)(PiCode b g) = Pair (LeCode a b)(LeFunCode f g)`
   etc. still hold **definitionally** ⇒ the 24-file cone was **untouched**. Do the same: keep
   `FinMem`/`FinMemFun`/`FinMemAllU` structural; get the *properties* from the bridge.

2. **Free-standing mutual `(n : Nat) -> ...` block, NOT a record pack.** Agda accepts the
   `lex (stage n, structure)` measure (proven by the existing `lei-sound` and by all of
   `LeqStageProps2`). The stage `n` is the primary measure; same-stage recursion is structural on
   the FinEl/FinFun argument; the recursion that descends RANK drops `suc m → m`.

3. **RANK side-conditions** `Le (RANK u) n` / `Le (RANK a) n` on every stage lemma. At stage 0 they
   force atoms (`Le (suc _) 0 = Empty`), so compound cases are discharged with `()` on the bound.
   Thresholds are mechanical — copy the shapes from `goodStab` / `LeqStageProps2`.

4. **n-split.** `FinMem_n u a` (like `OB.leq n`) is *stuck for abstract n*; case-split `n` into
   `zero`/`suc m` wherever a clause needs the bundle to reduce or an input to reduce to `Empty` for
   a `()`. Use a `mem-Bot-any`-style helper for the always-true clauses (cf. `leq-Bot-any`).

5. **The bridge.** Prove `FinMem u a ↔ FinMem_n u a` (for `n` above the ranks) by structural
   recursion on the first/type argument, with a **stage-shift at the leaves** (you will need a
   `mem-shift` mirroring `leq-shift`/`lei-shift` in `LeqStageStable`). EvalFun-results sit only in a
   non-measure position, so the bridge is structural ⇒ pragma-free (this is exactly how
   `toLeq/fromLeq/toLeqf/fromLeqf` and `ev-bridge` work in `MIN/LeqStageBridge.agda`).

6. **Re-found `PaperTyping` as a re-export shim** (`MIN/PaperOrder.agda` is the model — 38 lines).

## THE 3 PRAGMAS AND THEIR TRIAGE
Source for all of this is the current `MIN/PaperTyping.agda`.

### Block 1 — `FinMem` / `FinMemFun` / `FinMemAllU` (line 34): the definition
```
FinMem Bot          a            = FinMem a UCode                       -- SWAP: type a -> UCode
FinMem UCode        UCode        = Top
FinMem (FunEl g)    (PiCode a f) = FinMemFun g a f × CoherentFun g × FinMem (PiCode a f) UCode
FinMem (PiCode a f) UCode        = FinMem a UCode × FinMemAllU f a × CoherentFunTail f
...(all other (u,a) combinations = Empty)
FinMemFun  (cons p ps) a f = (FinMem (fst p) a × FinMem (snd p) (EvalFun f (fst p))) × FinMemFun ps a f
FinMemAllU (cons p ps) a   = (FinMem (fst p) a × FinMem (snd p) UCode)              × FinMemAllU ps a
```
**Why non-structural** (the intended measure is the iterative-stage RANK, primarily of the **type**
argument, NOT syntactic `rk`):
- the **swap** `FinMem Bot a = FinMem a UCode` puts `a` in the type-position then drops the type to
  `UCode` (RANK `a` → 0);
- `FinMem (FunEl g)(PiCode a f)` recurses `FinMem (PiCode a f) UCode` (type `PiCode a f` → `UCode`);
- `FinMemFun (cons p ps) a f` recurses `FinMem (snd p) (EvalFun f (fst p))` — **through an
  EvalFun-RESULT** (RANK ≤ `RANKFun f` < `RANK (PiCode a f)`). This is the genuinely non-structural
  one, mirroring the order.
**Stage version** (mirror `buildOrderStage`): `FinMem_{suc m}` reduces each of these recursions to
`FinMem_m` (predecessor). EvalFun is the **finished** structural function from `MIN/LeqStageBridge`
(import it; do NOT re-define it). Carry `Le (RANK u) n`, `Le (RANK a) n` bounds; the EvalFun-result
bound is `RANK (EvalFun f x) ≤ RANKFun f` via `RANK-ev` (already proved, exported from `LeqStage`).

### Block 2 — `FinMem-coh-u` / `FinMem-a-in-U` / `FinMem-coh-a` (line 73): projections
These recurse on sub-terms / project the `FinMem` value (e.g. `FinMem-coh-u (PiCode a f) UCode =
mkSigma (FinMem-coh-u a UCode (fst mem)) ...`). **Likely pragma-free once `FinMem` is structural**
(analogous to the order's `leFinEl-sound`). **DELETE-PRAGMA TEST** after refounding; only
stage-index if Agda still complains.

### Block 3 — closure / monotonicity (line 147): the bulk
`finMemUCode-Sup`, `FinMemAllU-append-Sup`, `FinMemAllU-Sup-right`, `finMem-Sup-right`,
`finMem-Sup-left`, `finMemFun-Sup-right`, `finMemFun-Sup-left`, `FinMem-Sup-element`,
`finMem-upward`, `finMemFun-upward`, `FinMemFun-append`, `EvalFun-in-UCode`, `finMem-EvalFun-append`.
Triage exactly like the order:
- **structural-on-first-arg / on-list ⇒ pragma-free after refounding** (delete-pragma test):
  `finMemUCode-Sup` (recurses on `a`), `FinMemAllU-append-Sup`/`-Sup-right` (recurse on the list),
  `FinMem-Sup-element`, `FinMemFun-append`. `EvalFun-in-UCode` already fires on `leiC`/`EvalFun-step`
  (it was adjusted last session) and is structural on its list.
- **GENUINELY needs stage-indexing** (recurses through `EvalFun`-results in a cycle):
  `finMem-Sup-left` / `finMem-Sup-right` and their `finMemFun-Sup-left` / `finMemFun-Sup-right`
  partners — see `finMem-Sup-left (EvalFun k (fst p)) (EvalFun h (fst p)) (snd p) ...` (≈ line 421);
  and `finMem-upward` / `finMemFun-upward`. These are the analogue of the order's block 905 / 705 and
  are what you port stage-indexed. They are CONDITIONAL on `Coherent`/`Comp` and on the now-stable
  order (`LeCode`, `Comp-down`, `LeCode-Sup-left/right`, `Coherent-EvalFun`, `comp-EvalFun`,
  `EvalFun-append-eq` — all imported pragma-free from the `LeqStage*` layer).

The math closure property being proved (kernel-stratification-method, instance 1): "compatible
members of a type have a sup that is also a member" — `finMemUCode-Sup` / `finMem-Sup-left/right`,
and `finMem-upward` is the monotonicity `LeCode a b → FinMem v a → FinMem v b` that drives stability.

## THE PUBLIC `FinMem` INTERFACE (must be preserved name-for-name; counts = cone files using it)
Types (keep STRUCTURAL): `FinMem` (24), `FinMemFun` (14), `FinMemAllU` (16).
Projections: `FinMem-coh-u` (20), `FinMem-a-in-U` (15), `FinMem-coh-a` (1), `coh-from-aU` (16).
Closure/mono: `finMemUCode-Sup` (12), `FinMemAllU-append-Sup` (3), `finMem-Sup-right` (6),
`finMem-Sup-left` (6), `FinMem-Sup-element` (7), `finMem-upward` (16), `finMemFun-upward` (1),
`FinMemFun-append` (1), `EvalFun-in-UCode` (9).
PaperTyping-INTERNAL (0 external uses — may stay private or be dropped): `FinMemAllU-Sup-right/left`,
`finMem-Sup-both`, `finMemFun-Sup-right/left`, `finMem-EvalFun-append`, `finMem-Sup-right-PiCode/FunEl`.

## SUGGESTED FILE LAYOUT (mirror the order's 6-file split; likely fewer files since no cycle)
- `MIN/FinMemStage.agda`     — `FinMem_n`/`FinMemFun_n`/`FinMemAllU_n` bundle (`buildMemStage`,
  `MemStage n`, public `FinMemC`), RANK bounds. Imports `MIN.LeqStage` (RANK toolkit) and
  `MIN.LeqStageBridge` (the finished `EvalFun`). NO pragma.
- `MIN/FinMemStageProps.agda`— stage-indexed closure/mono pack (`finMem-Sup-left/right-n`,
  `finMemFun-Sup-*-n`, `finMem-upward-n`, `finMemFun-upward-n`), free-standing mutual on `(n,struct)`.
- `MIN/FinMemStageStable.agda`— `mem-shift` (mirror `leq-shift`) + collapse to public `FinMemC` props.
- `MIN/FinMemStageBridge.agda`— STRUCTURAL `FinMem`/`FinMemFun`/`FinMemAllU` (original defs) +
  `FinMem↔FinMemC` bridges (structural-on-type-arg, EvalFun-result in non-measure position).
- `MIN/FinMemStageInterface.agda`— the public lemmas on structural `FinMem` via bridge∘stage; also
  the projections (`FinMem-coh-u` etc.) and the structural closure lemmas (`finMemUCode-Sup`,
  `FinMemAllU-append-Sup`, `FinMem-Sup-element`, `EvalFun-in-UCode`) — re-prove pragma-free here.
- `MIN/PaperTyping.agda`      — re-export shim over the above (+ `open import MIN.PaperOrder public`
  so the order names still flow through). Keep `coh-from-aU` (one-liner) and any thin wrappers.

You may be able to fold several of these together (typing is simpler). Start by validating the
hardest unknown in isolation (as last session validated the core + bridge before touching the cone):
**(a)** the `FinMem_n` bundle compiles 0-pragma, and **(b)** the `FinMem↔FinMemC` bridge compiles —
those are the only real risks.

## CONE-COMPATIBILITY CHECK (the thing that bit us last session — pre-empt it)
The order refounding broke because `Selection`/`PaperTyping` mirrored `EvalFun`'s *reduction*
(`EvalFun-step` + `leFinEl`-firing). For typing, before swapping `PaperTyping`, grep the cone for
any file that pattern-matches `FinMem`'s recursion shape (a helper that fires on the membership
unfolding the way `EvalFun-in-UCode` mirrored `EvalFun`):
```
grep -rln "FinMem-step\|FinMemAllU (cons\|FinMemFun (cons" MIN/*.agda   # outside PaperTyping
```
Because you KEEP `FinMem` structural (definitional unfolding preserved), there should be **nothing
to change in the cone**. **CONFIRMED (this session):** the grep above returns **NONE** — no cone file
mirrors `FinMem`'s recursion shape; the cone uses `FinMem` only via definitional unfolding
(`FinMem (PiCode a f) UCode = triple` etc.) + the public lemmas. So, unlike the order (where
`Selection`/`PaperTyping` mirrored `EvalFun-step`), **typing needs NO cone edits** as long as you
keep `FinMem`/`FinMemFun`/`FinMemAllU` structural.

## TOOLING & VERIFICATION
- Binary: `~/.cabal/bin/agda-2.9.0 --without-K` (NOT plain `agda`). Timeout wrapper:
  `perl -e 'alarm 250; exec @ARGV' ~/.cabal/bin/agda-2.9.0 --without-K MIN/<F>.agda`.
- `--without-K --exact-split` (enumerate clauses; split `n` so clauses stay definitional — watch for
  `CoverageNoExactSplit` warnings, fix by splitting `n` like `LeqStageBridge`'s `fromLeq UCode UCode`).
- `.agdai` caches live in `_build/` (auto-managed).
- Backup `PaperTyping` first: `cp MIN/PaperTyping.agda /tmp/PaperTyping.agda.bak`.
- **DONE when:** `grep -c "{-# TERMINATING" MIN/PaperTyping.agda` → **0**, and
  `~/.cabal/bin/agda-2.9.0 --without-K MIN/PiInjectivity.agda` exits 0 (clean, 0 holes).

## ORIENTATION / REFERENCES
- Template: the 6 `MIN/LeqStage{,Comp,Props2,Order,Stable,Bridge,Interface,Eval2}.agda` files + the
  `MIN/PaperOrder.agda` shim. The order's `LeqStageBridge.toLeq/fromLeq` + `ev-bridge` are the exact
  pattern for the `FinMem` bridge.
- Memory: `project-leqstage-progress` (full record of the order session, incl. the convention and the
  "keep-structural + bridge" win), `kernel-stratification-method` (the user's stage-n+stability recipe;
  instance 1 = typing), `feedback-indexfree-architecture`.
- Don't relitigate: the order is settled & pragma-free; build typing ON TOP of it (import, don't copy).
- `RANK`/`RANKFun`/`RANK-ev`/`RANK-Sup`/`RANK-append`/`Le-max-lub`/`max-mono` are exported from
  `MIN.LeqStage` — reuse them.
