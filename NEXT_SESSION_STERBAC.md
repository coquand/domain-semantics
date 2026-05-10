# Next session: Sterbac Tarski⇔Russell equivalence

## Goal

Agda formalization of Sterbac's TYPES 2026 result (joint with Coquand):
syntactic equivalence of Tarski-style and Russell-style presentations of
MLTT with cumulative universes `Uₙ` and βη judgemental conversion.
Reference: `sterbac.pdf` in repo root. Rocq formalization at
https://github.com/raphael-sterbac/Russell-Tarski-Equivalence.

All work lives in `Sterbac/` subdirectory. Independent of the rest of
DOMAIN (no `--type-in-type`).

## Type-checking

Use `~/.cabal/bin/agda-2.9.0` (faster than the default agda binary):

```
~/.cabal/bin/agda-2.9.0 --no-libraries -i . Sterbac/<File>.agda
```

## Constraint

> No `postulate` outside `Sterbac/Postulates.agda`. No holes.

`Sterbac/Postulates.agda` contains the agreed assumed lemmas:
Π-injectivity, U-injectivity, U/Π no-confusion (for both Tarski T_T
and Russell T_R), plus their term-level analogues for codes
(`UCode-inj-T`, `PiCode-inj-T`, `UCode-PiCode-noconf-T`). These are
admissible by normalisation, deferred for later.

## File status

| File | Lines | Status | Postulates | Notes |
|---|---|---|---|---|
| `Basic.agda` | ~160 | ✅ done | 0 | Nat, Fin, Eq, Sigma, Either, Le/Lt, max, Ren/liftRen/wkRen |
| `RussellSyntax.agda` | ~280 | ✅ done | 0 | Russell raw terms + ren/subst stack |
| `RussellTyping.agda` | ~200 | ✅ done | 0 | WfCtx, IsType, HasType, ConvTy, ConvTm with cumulativity, βη. Lam/App congruences split into -body/-Ty and -fun/-arg/-Ty respectively. |
| `TarskiSyntax.agda` | ~370 | ✅ done | 0 | Tarski raw terms (9 constructors) + ren/subst stack |
| `TarskiTyping.agda` | ~320 | ✅ done | 0 | WfCtx, IsType, HasType, ConvTy, ConvTm with the 6 Tarski equations + βη. Lam/App congruences split. |
| `Erasure.agda` | ~160 | ✅ done | 0 | erase : T.Expr n → R.Expr n + commutation with ren and parallel subst |
| `Postulates.agda` | ~110 | ✅ done | 8 (allowed) | Pi-inj, U-inj, U-Π no-conf for T_T and T_R; UCode/PiCode injectivity + no-conf for T_T |
| `TarskiMeta.agda` | ~900 | ✅ done | 0 | Full Tarski meta-theory mutual block: ren, wk, presup-l/r for ConvTy and ConvTm, subst, ctx-conv. Uses `{-# TERMINATING #-}`. |
| `TarskiMetaCong.agda` | ~200 | ✅ done | 0 | Cross-substitution congruence. Mutual `subst-cong-{IsType,HasType}` block parameterised by `ConvTmSub`. Wrapper `subst1-cong-Ty : ConvTm G a a' A → IsType G A → IsType (extend G A) B → ConvTy G (subst1 B a) (subst1 B a')`. Uses `{-# TERMINATING #-}`. |
| `Uniqueness.agda` | ~560 | ⚠ type-uniq DONE, term-uniq postulated | 1 (need to discharge) | Defines `size`, `CommonLift` (with `LiftStep` wrapper for trivial lifts), 6 inversion lemmas (`inv-Var`, `inv-Lam`, `inv-App`, `inv-PiCode`, `inv-UCode`, `inv-Lift`), Russell-syntax injectivity helpers, and **`type-uniq` is now fully proved**. `term-uniq` remains the postulate to discharge. |
| `Equivalence.agda` | ~370 | ⚠ erase done, lift postulated | 4 (need to discharge) | `eraseCtx`, `erase-WfCtx/IsType/HasType/ConvTy/ConvTm` all proved. Records `LiftIsType`/`LiftHasType`/`LiftConvTy`/`LiftConvTm` defined. `lift-*` POSTULATED. |
| `UniquenessTermPartial.agda` | ~270 | ⚠ structural cases done, Lift cases postulated | 1 (need to discharge) | Partial `term-uniq`: ty-conv peeling, (Var, Var), (Lam, Lam), (App, App) via `subst1-cong-Ty`, (PiCode, PiCode), cross-shape impossible cases — all proven.  Lift-related cases factored into a single auxiliary postulate `term-uniq-Lift-cases`. |

Total: ~3870 lines of Agda. 8 allowed postulates + 5 (lift-*) + 1 (term-uniq-Lift-cases) to discharge.

## Progress in this session (2026-05-10)

* **`type-uniq` proven** (~200 lines) — all 9 cases of `(IsType, IsType)`
  combinations: (U,U), (U,Pi)-impossible, (U,El a)-cases on a's shape,
  (Pi,Pi), (Pi,El a), (El a, *)-symmetric, (El a1, El a2)-uses term-uniq.
* **6 inversion lemmas** for HasType: `inv-Var`, `inv-Lam`, `inv-App`,
  `inv-PiCode`, `inv-UCode`, `inv-Lift`. Each peels ty-conv chains.
* **3 absurdity lemmas**: T.Pi/U/El cannot occur as terms (no HasType
  producer except ty-conv, which recurses).
* **Russell-syntax injectivity / no-confusion helpers** added: needed
  for the cases where `eq : Eq (erase A) (erase B)` must be split.
* **`CommonLift` refactored** with a new `LiftStep` data type wrapping
  `u₀≡` and `u₁≡` fields. This handles the "trivial lift" case (e.g.,
  Var x : U_n vs Lift_m_n x : U_m) without needing to relax Tarski's
  strict `Lift` constructor. The Rocq formalisation uses a unified
  `cLift` with `Le` and `cLift l l u = u`; our `LiftStep` is the
  meta-level equivalent.

## Progress in second session (2026-05-10)

* **`Sterbac/TarskiMetaCong.agda` added** (~200 lines, 0 postulates).
  Cross-substitution congruence proven via parametric `ConvTmSub`,
  with public wrapper:

  ```agda
  subst1-cong-Ty : ConvTm G a a' A
                -> IsType G A
                -> IsType (extend G A) B
                -> ConvTy G (subst1 B a) (subst1 B a')
  ```

  Uses `{-# TERMINATING #-}` (recursion is on the IsType/HasType
  derivation but Agda can't see it through the mutual block).
  Unblocks the (App, App) case of `term-uniq`.

* **`Sterbac/UniquenessTermPartial.agda` added** (~270 lines).  A
  partial proof of `term-uniq`: the structural cases — ty-conv
  peeling on either side, (Var, Var), (Lam, Lam), (App, App) using
  `subst1-cong-Ty`, (PiCode, PiCode), and the cross-shape impossible
  cases — are fully discharged.  The Lift-related cases (UCode-UCode,
  Lift on either side, etc.) are deferred to a single auxiliary
  postulate `term-uniq-Lift-cases`.

  This file is independent of `Uniqueness.agda` (which still
  postulates `term-uniq` directly).  Once `term-uniq-Lift-cases` is
  proven, `Uniqueness.term-uniq` can be re-defined to call this
  partial implementation.

  Compile: ✅ (with `--exact-split` warnings about ty-conv overlap
  and the `_` patterns; warnings only, no errors).

## Quick verification

```bash
for f in Sterbac/Basic Sterbac/RussellSyntax Sterbac/RussellTyping \
         Sterbac/TarskiSyntax Sterbac/TarskiTyping Sterbac/Erasure \
         Sterbac/Postulates Sterbac/TarskiMeta Sterbac/Uniqueness \
         Sterbac/Equivalence; do
  echo -n "$f: "
  ~/.cabal/bin/agda-2.9.0 --no-libraries -i . $f.agda 2>&1 \
    | grep -c error
done
```

All should show 0.

## Design decisions for the remaining work (DO NOT re-litigate)

These were settled at the end of the previous session.  Override only
with explicit user input.

* **Trivial-lift handling: keep `LiftStep` (the current design).**  Do
  not relax Tarski's `Lift` constructor to `Le` and add `Lift l l a =
  a`.  The `LiftStep` data type wraps `CommonLift`'s `u₀≡` / `u₁≡`
  fields with two constructors `trivial` (when `m ≡ k`) and `proper`
  (when `Lt k m`).  This is already in use in `type-uniq`'s `(El,El)`
  case (`step-from-LiftStep` helper).  The Rocq formalisation goes the
  other way (unified `cLift` with `Le` + `cLift l l u = u`), but
  changing here would require touching `TarskiTyping`, `TarskiMeta`,
  and `Equivalence` and would invalidate the existing `type-uniq`
  proof.

* **Cross-subst location: new file `Sterbac/TarskiMetaCong.agda`.**
  Do not reopen `TarskiMeta.agda`'s `{-# TERMINATING #-}` mutual
  block.  Put the `subst-cong-{IsType,HasType,ConvTy,ConvTm}` mutual
  block (parameterised by a `ConvTmSub`) in a new file that imports
  `TarskiMeta` and re-exports / specialises only what's needed.  The
  specialised `subst1-cong-Ty` is the public name used by
  `Uniqueness.agda`.

## Key design decisions (don't undo without thought)

1. **`Sterbac.Basic` is shared** by both syntaxes. Hosts Nat, Fin, Eq,
   Sigma, Either, Le/Lt, max, and `Ren / liftRen / wkRen`. Russell and
   Tarski must use the same `Ren` so `Erasure` can commute.

2. **`ConvTy` is a separate primitive judgement** (not a sigma over
   `ConvTm` at U). Has its own equivalence rules + `conv-Ty-Pi` +
   `conv-Ty-from-U`. This was a Coquand request.

3. **`Lam` and `App` congruences split**:
   - `conv-cong-Lam-body` (changes only `b`) and `conv-cong-Lam-Ty`
     (changes `A`, `B`).
   - `conv-cong-App-fun` (changes `c`), `conv-cong-App-arg` (changes
     `a`), `conv-cong-App-Ty` (changes `A`, `B`).
   - `conv-cong-App-arg` carries an explicit `ConvTy G (subst1 B a)
     (subst1 B a')` premise. This sidesteps cross-substitution
     metatheory (which would otherwise need ~300 extra lines).
   - The "strong" 4-arg `conv-cong-App` and `conv-cong-Lam` are
     derivable as lemmas via transitivity (not yet written; do if
     needed by Uniqueness or `lift-*`).

4. **`Lift` uses strict `Lt`** (not `Le`). So `Lift n n a` is not a
   well-formed Tarski term. The `CommonLift` in `Uniqueness.agda` may
   need revisiting if the proof needs trivial lifts; one option is to
   relax `Lift` to `Le` and add the equation `Lift n n a = a`. Flag if
   it comes up.

5. **`is-Ty-El`'s level** is the OUTER universe: `is-Ty-El {l = m}
   (a : U m)` gives `IsType (El m a)`. The Tarski equations like
   `conv-Ty-El-UCode` use the outer level too (`El m (UCode m l) = U
   l`). When constructing IsType for `El m (UCode m l)` use
   `is-Ty-El {l = m}` not `{l = l}` (this caught me once).

6. **`TarskiMeta` uses `{-# TERMINATING #-}`** because Agda's
   structural-recursion checker can't see the termination through the
   web of mutual functions. Same situation as `SubstitutionLemmaSigma`
   in DOMAIN. Recursion is genuinely on subderivations though, so
   it's safe.

7. **`Equivalence.cum-up` and `cum-by`** lift Russell `HasType` /
   `ConvTm` at U through cumulativity. Live in `Equivalence.agda`
   (because erase-soundness uses them). If Russell metatheory becomes
   needed, consider promoting to a `Sterbac.RussellMeta` module.

## What's left, in priority order

### Step 1 — Prove `Uniqueness.term-uniq`

`type-uniq` is **done**.  `term-uniq` remains postulated; the
statement is unchanged.

**Proof structure (Sterbac slide 17):** mutual induction on size of
`u₀`. Use `{-# TERMINATING #-}`.

The skeleton has been worked out; see the comment block in
`Sterbac/Uniqueness.agda` just above the `term-uniq` postulate, plus
the `LiftStep` wrapper definition.  The previous draft (deleted from
the WIP file) is in the git history if needed.

For `term-uniq dM₀ dM₁ eq`, case-analyse on the typing derivations
after peeling ty-conv chains (use the inversion lemmas already in the
file).  Use the postulates from `Sterbac.Postulates`:
- `UCode-inj-T` to identify code levels.
- `PiCode-inj-T` to project through Pi-codes.
- `UCode-PiCode-noconf-T` to rule out absurd cases.
- `Pi-inj-Ty-T`, `U-inj-Ty-T`, `U-Pi-noconf-Ty-T` for type-side reasoning.

**Subtask: cross-substitution congruence.**  The (App, App) case
needs

```agda
subst1-cong-Ty : ConvTm G a a' A
              -> IsType G A
              -> IsType (extend G A) B
              -> ConvTy G (subst1 B a) (subst1 B a')
```

This is *not* in `Sterbac.TarskiMeta`.  To prove it, add a mutual
block (`subst-cong-IsType`, `subst-cong-HasType`, `subst-cong-ConvTy`,
`subst-cong-ConvTm`) parameterised by a `ConvTmSub H G s s'` that
asserts `s` and `s'` are pointwise convertible at each variable's
type.  Then specialise to `subst1Sub a` vs `subst1Sub a'` for the
cross-subst.  Estimated 200-300 lines for the mutual block.

The `LiftStep` wrapper lets `CommonLift` express "u₀ is convertible
to v₀ directly (when n₀ = k)" or "u₀ is convertible to Lift n₀ k v₀
(when k < n₀)".  This handles trivial-lift cases like
(`Var x : U_n`, `Lift m n (Var x) : U_m`), which would otherwise be
unprovable because Tarski's strict `Lift` rules out `Lift n n a`.

Key cases for `term-uniq`:
- (Var, Var): erasure forces `i = i'`; emit 1st case.
- (Var/Lam/App/PiCode/UCode, Lift): recurse into the Lift's inner; the
  result is wrapped via `lift-r` (helper) to add a `proper` LiftStep
  on the right side.
- (Lift, *): symmetric, `lift-l` helper.
- (Lam, Lam) / (App, App) / (PiCode, PiCode): use congruences. App
  needs the cross-subst lemma above.
- (UCode m₁ j, UCode m₂ j): emit 2nd case with `k = suc j`,
  `v₀ = v₁ = UCode (suc j) j`. Dispatch on whether `m_i = suc j`
  (`trivial`) or `m_i > suc j` (`proper` via `conv-Lift-UCode`).
- (UCode, Lift) / (Lift, UCode): recurse on the Lift's inner.

Estimated remaining: ~500-700 lines.

### Step 2 — Discharge `lift-*` in `Equivalence.agda`

Postulated at `Sterbac/Equivalence.agda:307-322`. Each is structural
recursion on the Russell derivation, choosing Tarski terms whose
erasure recovers the Russell ones.

Key insight: most of the work is reconciling that recursive lift
results from independent calls produce *convertible* Tarski
derivations. Each reconciliation is exactly an instance of
`type-uniq` or `term-uniq` from Step 1.

For each Russell rule, write the Tarski lifted form:

| Russell | Tarski |
|---|---|
| `ty-var` | `ty-var` |
| `ty-conv M A=B` | `ty-conv M' A=B'` (after lift + uniqueness reconciliation) |
| `ty-U {l}` | `ty-UCode (l+1) l` |
| `ty-cum HasType A (U l) → HasType A (U (suc l))` | `Lift (l+1) l` of the lifted term |
| `ty-Pi` | `ty-PiCode` |
| `ty-Lam` | `ty-Lam` |
| `ty-App` | `ty-App` (uniqueness needed to identify `Pi A B` shape of c's type) |

For `ty-cum`: if the lifted term `M'` has Tarski type `T'` (with
`erase T' = R.U l`), and we want type `R.U (l+1)`, take
`Lift (l+1) l (Eq-transport ty-conv to U l)`. The `ty-conv` step uses
`type-uniq` to identify `T'` with `T.U l`.

Estimated size: ~300-500 lines.

### Step 3 — Optional: derive the strong `conv-cong-App` and `conv-cong-Lam`

```agda
strong-conv-cong-App :
  ConvTy G A A' -> ConvTy (extend G A) B B'
  -> ConvTm G c c' (Pi A B) -> ConvTm G a a' A
  -> ConvTy G (subst1 B a) (subst1 B a')   -- the cross-subst
  -> ConvTm G (App A B c a) (App A' B' c' a') (subst1 B a)
strong-conv-cong-App dA dB dc da Bsubst =
  conv-trans
    (conv-cong-App-fun (presup-l-ConvTy dA) (presup-l-ConvTy dB)
                       dc (presup-l-ConvTm da))
    (conv-trans
      (conv-cong-App-arg ... ... ... da Bsubst)
      (conv-cong-App-Ty dA dB
                        (presup-r-ConvTm dc) (presup-r-ConvTm da)))
```

Only do this if `Uniqueness` or `lift-*` actually needs it.

## Useful pointers

- DOMAIN's `SubstitutionLemmaSigma.agda` (1297 lines) is the template
  for `TarskiMeta.agda`. Look at how it splits cases, names implicit
  arguments explicitly in `Eq-transport` lambdas, etc.
- DOMAIN's `Validity*` files have analogous uniqueness-style proofs
  (in a different setting — domain-theoretic, not syntactic), which
  may be useful for case structure inspiration.
- The Sterbac slides themselves (`sterbac.pdf`) have the proof
  outline on slide 17.

## Anti-patterns to avoid (lessons from this session)

- **Don't write `\T → HasType _ _ T` in `Eq-transport`** — Agda can't
  always infer the `_`s. Pattern-bind context and term explicitly.
- **`presup-r` of a binder rule needs context conversion** — don't
  try to fake it by returning the left side. `presup-r-ConvTy` of
  `conv-Ty-Pi` calls `ctx-conv-IsType`, which calls `subst-IsType`,
  hence the giant mutual block.
- **`Lift` is strict (`Lt`)** — `↑^n_n a` isn't well-formed. If
  Uniqueness's `CommonLift` requires a trivial lift, that's a sign
  to revisit the formulation (e.g., relax `Lift` to `Le` and add
  `↑^n_n a = a` rule).
- **Erasure direction** — `erase-subst1 B a : Eq (E.erase (T.subst1 B
  a)) (R.subst1 (E.erase B) (E.erase a))` (forward, NOT `Eq-sym`).
  Get the orientation right when transporting.
