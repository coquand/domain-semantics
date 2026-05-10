# Next session: Finish `term-uniq`, following sterbac1.pdf §4.2

## Goal

Discharge the single remaining `term-uniq-Lift-cases` postulate in
`Sterbac/UniquenessTermPartial.agda` and unify the partial proof
back into `Sterbac/Uniqueness.agda` so that `term-uniq` is no
longer postulated anywhere.

This corresponds to finishing **Lemma 4.10** of `sterbac1.pdf`
(Coquand & Sterbac, "From Tarski to Russell").

## Reference

- **Paper**: `sterbac1.pdf` (in repo root). Read §4.2, especially
  Lemma 4.10 (the "catch-up" lemma) and its proof.
- **Rocq formalisation**: <https://github.com/raphael-sterbac/Russell-Tarski-Equivalence>
  — citation [16] in the paper; consult if our proof gets stuck on
  a case the paper doesn't spell out (the paper details
  λ-abstraction and U-code; PiCode and the App cases are left
  implicit).
- **Status doc**: `NEXT_SESSION_STERBAC.md` (long-form context).

## Constraints

- **No new `postulate`s.** The 8 admissible postulates in
  `Sterbac/Postulates.agda` (U/Π injectivity, no-confusion, code
  injectivity) are the only ones permitted. If you need a stepping
  stone, prove it as a lemma — do not introduce new postulates.
- `--without-K --exact-split` everywhere; `{-# TERMINATING #-}` is
  permitted (already used in `TarskiMeta.agda`,
  `TarskiMetaCong.agda`, and `UniquenessTermPartial.agda`).
- Type-check command:
  ```
  ~/.cabal/bin/agda-2.9.0 --no-libraries -i . Sterbac/<File>.agda
  ```

## Current state (start of session)

`UniquenessTermPartial.agda` already discharges:

- ty-conv peeling on either side
- (Var, Var), (Lam, Lam), (App, App), (PiCode, PiCode) — structural
  cases via `extract-conv-same`
- All cross-shape impossibles (Var-vs-Lam, etc.)
- (UCode, UCode) — direct CommonLift via canonical witness
  `UCode (suc l) l : U (suc l)`
- (Lift, *) and (*, Lift) — recurse on inner of the Lift, build
  CommonLift via `conv-cong-Lift` and `conv-Lift-Lift`

Helpers already in place:
- `Lt-trans-Lt`, `Lt-not-self`
- `commonLift-same-A : CommonLift G u₀ u₁ A A → ConvTm G u₀ u₁ A`
  — paper Lemma 4.11
- `extract-conv-same : TermUniqResult G u₀ u₁ A A → ConvTm G u₀ u₁ A`
  — paper Cor. 4.12
- `subst1-cong-Ty` (in `Sterbac/TarskiMetaCong.agda`)

## The single remaining case

`UniquenessTermPartial.agda:275`:

```agda
case-PiCode-a eqB (inr _) =
  term-uniq-Lift-cases (TT.ty-PiCode da1 db1)
                        (TT.ty-PiCode da2 db2) eq
```

**Setup.** Both sides are PiCodes:

```
da1 : HasType G a₁ (U l₁)        db1 : HasType (G.El l₁ a₁) b₁ (U l₁)
da2 : HasType G a₂ (U l₂)        db2 : HasType (G.El l₂ a₂) b₂ (U l₂)
eq  : Pi (erase a₁) (erase b₁) ≡ Pi (erase a₂) (erase b₂)
```

The outer levels `l₁` and `l₂` may differ, since
`erase (PiCode l a b) = R.Pi (erase a) (erase b)` discards `l`.
Recursion on `a₁, a₂` returns

```
cl_a : CommonLift G a₁ a₂ (U l₁) (U l₂)
```

So:
- `cl_a.A₀≡U : ConvTy G (U l₁) (U cl_a.n₀)`, hence `l₁ ≡ cl_a.n₀`
- `cl_a.A₁≡U : ConvTy G (U l₂) (U cl_a.n₁)`, hence `l₂ ≡ cl_a.n₁`
- `cl_a.u₀≡ : LiftStep G a₁ cl_a.n₀ cl_a.k cl_a.v₀ (U l₁)`
- `cl_a.u₁≡ : LiftStep G a₂ cl_a.n₁ cl_a.k cl_a.v₁ (U l₂)`
- `cl_a.v₀≡v₁ : ConvTm G cl_a.v₀ cl_a.v₁ (U cl_a.k)`

**Goal.** Produce
`TermUniqResult G (PiCode l₁ a₁ b₁) (PiCode l₂ a₂ b₂) (U l₁) (U l₂)`
— a `CommonLift` on the outer PiCodes.

## Strategy (paper-flavoured)

This is the analogue of the paper's "Code for a universe" case
(end of §4.2 proof of Lemma 4.10), which handles `(U^{n₀}_m, U^{n₁}_m)`
by taking `k := min(n₀, n₁)` and producing the canonical witness
`UCode k m : U_k`.

For PiCode, the canonical witness at the common base level should be
`PiCode k_a v_a v_b'` where:

- `k_a := cl_a.k` (the common base level from the `a`-recursion)
- `v_a := cl_a.v₀` (the common base code for the domain)
- `v_b'` is the common base code for the body, *also* at level
  `k_a`

The body is the genuinely new ingredient: we need `v_b'` at
universe level `k_a`. Recurse on the body:

1. **Bring bodies into a common context.** `db1` lives in
   `G.El l₁ a₁` and `db2` in `G.El l₂ a₂`. Use the Tarski equation
   `El l_i (Lift l_i k a) ≡ El k a` (constructor
   `conv-Ty-El-Lift`) plus `cl_a.u_i≡` to obtain
   ```
   ConvTy G (El l₁ a₁) (El k_a v_a)
   ConvTy G (El l₂ a₂) (El k_a v_a)   -- via cl_a.v₀≡v₁
   ```
   (Two `LiftStep` cases each: `trivial` collapses, `proper` uses
   `conv-Ty-El-Lift`.) Then `ctx-conv-HasType` to bring both bodies
   into the common context `G.El k_a v_a`:
   ```
   db1' : HasType (G.El k_a v_a) b₁ (U l₁)
   db2' : HasType (G.El k_a v_a) b₂ (U l₂)
   ```

2. **Recurse on the bodies.** Erase agrees by `eqB`:
   ```
   cl_b-or-conv := term-uniq db1' db2' eqB
                : TermUniqResult (G.El k_a v_a) b₁ b₂ (U l₁) (U l₂)
   ```

3. **Two sub-subcases** on the body result.

   - **`inl (cTy_b, cb)`**: `cTy_b : ConvTy (G.El k_a v_a) (U l₁) (U l₂)`,
     so `l₁ ≡ l₂` by `U-inj-Ty-T`. With `l₁ ≡ l₂`, the situation
     collapses to the same-level case: `cl_a` becomes a same-type
     CommonLift after Eq-transport, so `commonLift-same-A` produces
     `ConvTm G a₁ a₂ (U l₁)`, and we proceed as the existing
     same-level (PiCode, PiCode) case (build `conv-cong-PiCode`,
     return `inl`).

   - **`inr cl_b`**: now `cl_b : CommonLift (G.El k_a v_a) b₁ b₂ (U l₁) (U l₂)`
     with its own `cl_b.k`, `cl_b.v₀`, `cl_b.v₁`, etc. By
     `cl_b.A₀≡U` and `cl_b.A₁≡U`: `l₁ ≡ cl_b.n₀` and
     `l₂ ≡ cl_b.n₁`.

     **Construct the outer CommonLift.** Take:
     - `n₀ := l₁`, `n₁ := l₂`
     - `k := k_a` (the body's `k_b` may be smaller; if so, lift
       `v_a` up to `k_b` first — see below)
     - `v₀ := PiCode k_a v_a (lift-up cl_b.v₀ from k_b to k_a in body context)`
     - `v₁ := PiCode k_a v_a (lift-up cl_b.v₁ from k_b to k_a)`

     **The level-mismatch sub-issue.** If `cl_b.k ≠ cl_a.k`, lift
     the smaller-level body code up using `Lift cl_a.k cl_b.k`
     (when `cl_b.k < cl_a.k`) or symmetrically. Use
     `conv-Lift-Lift` and `conv-cong-Lift` to massage the
     `LiftStep`s into shape.

     **The big LiftSteps.** Build the two `LiftStep`s for
     `PiCode l_i a_i b_i` relating to `PiCode k_a v_a (lifted body)`
     at level `k_a`. Use:
     - `conv-Ty-El-PiCode` (Tarski equation
       `El l (PiCode l a b) ≡ Π (El l a) (El l b)`)
     - `conv-cong-PiCode` for the congruence on the inner pieces
     - `conv-Lift-PiCode` (Tarski equation
       `Lift m l (PiCode l a b) ≡ PiCode m (Lift m l a) (Lift m l b)`)
       — this is the key equation that lets a lifted PiCode be
       written as a PiCode of lifted components.

## Concrete subtasks

1. **Verify the contextual equality of `(G.El l₁ a₁)` and
   `(G.El k_a v_a)`** via `cl_a.u₀≡`. Two cases on the `LiftStep`:
   - `trivial`: `l₁ ≡ k_a` and `a₁ ≡ v_a` at `U l₁`. Then
     `conv-Ty-El` on the ConvTm gives the type equality.
   - `proper`: `a₁ ≡ Lift l₁ k_a v_a` at `U l₁`. Then
     `conv-Ty-El` + `conv-Ty-El-Lift` chains to
     `El l₁ a₁ ≡ El k_a v_a`.

   Same for `(G.El l₂ a₂) ≡ (G.El k_a v_a)`, using `cl_a.v₀≡v₁` to
   bridge `v_a` and `v₁`.

2. **Implement step 2 (recurse on bodies).** Trivial once step 1
   is done.

3. **Implement step 3a (inl branch).** Use `Eq-transport` on
   `Eq l₁ l₂` to coerce `cl_a` from
   `CommonLift G a₁ a₂ (U l₁) (U l₂)` to
   `CommonLift G a₁ a₂ (U l₁) (U l₁)`, then `commonLift-same-A`,
   then standard PiCode-cong.

4. **Implement step 3b (inr branch).** This is the hard part:
   - Decide the relationship between `cl_a.k` and `cl_b.k` (they
     may differ). If `cl_a.k ≠ cl_b.k`, lift the smaller one up to
     match.
   - Construct `v₀_outer := PiCode (chosen k) v_a (adjusted body code)`
     and `v₁_outer` similarly.
   - Build the two outer `LiftStep`s, each of which expresses
     `PiCode l_i a_i b_i ≡ Lift l_i k v_outer` at `U l_i` using
     `conv-Lift-PiCode` and `conv-cong-PiCode`.
   - Build `v₀_outer ≡ v₁_outer` at `U k` via PiCode-cong on the
     `cl_a.v₀≡v₁` and `cl_b.v₀≡v₁`.

## Estimated size

~150–250 lines once the algebra is worked out.

The level-mismatch subcase (step 4 first bullet) is the trickiest;
concentrate the time budget there. If stuck, factor it into a
named auxiliary `align-k-levels` lemma and tackle separately.

## After finishing

1. Replace the postulate `term-uniq-Lift-cases` with an actual
   definition (or just inline the case directly in `term-uniq`).
2. In `Sterbac/Uniqueness.agda`, replace the
   `postulate term-uniq` block with
   ```agda
   open import Sterbac.UniquenessTermPartial public using (term-uniq)
   ```
   or move the partial proof into `Uniqueness.agda` and delete
   `UniquenessTermPartial.agda`.
3. Verify all 12 (now 11) Sterbac files still compile:
   ```
   for f in Sterbac/Basic Sterbac/RussellSyntax Sterbac/RussellTyping \
            Sterbac/TarskiSyntax Sterbac/TarskiTyping Sterbac/Erasure \
            Sterbac/Postulates Sterbac/TarskiMeta Sterbac/TarskiMetaCong \
            Sterbac/Uniqueness Sterbac/Equivalence; do
     echo -n "$f: "
     ~/.cabal/bin/agda-2.9.0 --no-libraries -i . $f.agda 2>&1 | grep -c error
   done
   ```
   All should show 0.
4. Update `NEXT_SESSION_STERBAC.md` to reflect that Lemma 4.10 is
   fully formalised; only Theorem 4.13 (`lift-*` in
   `Equivalence.agda`) remains.

## Anti-patterns to avoid

- **Don't introduce new postulates.** The "common base" PiCode
  construction is intricate but provable from the existing Tarski
  equations (`conv-Lift-PiCode`, `conv-Ty-El-PiCode`,
  `conv-Lift-Lift`, etc.).
- **Don't try to re-litigate the strict-`Lift` vs `Le`-`Lift`
  design.** The `LiftStep` wrapper is established. Work within it.
- **Don't reopen `TarskiMeta.agda`'s `{-# TERMINATING #-}` mutual
  block.** If you need a new meta-lemma, put it in
  `TarskiMetaCong.agda` (or a new file) — `TarskiMeta` is closed.
- **Don't assume the body recursion at `(G.El k_a v_a)` is the
  same as at `(G.El l_i a_i)` without a context-conversion step.**
  Tarski's typing is intensional; conversions of the context type
  must be explicit via `ctx-conv-HasType`.
- **Watch the orientation of Eq-transports.** `cl_a.A₀≡U` is
  `ConvTy G (U l₁) (U cl_a.n₀)` (which way? — the convention is
  that the LHS is the original `A₀ = U l₁`). When you apply
  `U-inj-Ty-T`, you get `Eq l₁ cl_a.n₀`. Use this to substitute
  `cl_a.n₀ ↦ l₁`, not the other way.

## When the proof is done

The `term-uniq-Lift-cases` postulate disappears, the partial proof
becomes total, and `term-uniq` is fully discharged in
`Sterbac.Uniqueness`. This completes paper §4.2 Lemma 4.10 (and
Lemma 4.11, Cor. 4.12 are already done).

The next milestone after that is **Theorem 4.13** (Section of
erasure, `lift-*` in `Sterbac/Equivalence.agda`) — see
`NEXT_SESSION_STERBAC.md` Step 2 for the roadmap.
