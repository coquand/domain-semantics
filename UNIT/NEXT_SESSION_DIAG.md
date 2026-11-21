# STATUS 2026-11-21: DONE (commits 50e52cb, 37e5b28)

`BetaIDS4Diag.Fin.diagId` proves the finish line below; see PLAN-ID1.md,
"Diagonal identity law for S4 homogeneity DONE". Hypothesis added: the
pointwise km identity law only. Finding: the recursion is not diagonal
definitionally (J on relE0 at the dispatcher; target steps at beta nu,
c c0, f y), so the node law is a heterogeneous (transport / total-space)
statement, with UIP for rules, Bool, O3 and LO carriers.

Still open: composition across three certificates, inverse laws,
certificate independence up to a specified isomorphism, the trace-range
laws; minimality of the km hypothesis.

---

# Next session: diagonal identity law for S4 homogeneity

Start point: b0d2ed3 (branch hide-old-archives). Read first: PLAN-ID1.md, the
section "Homogeneity of S4 DONE"; BetaIDS4HomFin.seg; BetaIDS4HomThm.seg
(Goal, HomOut, IHR, NodeT, Ind).

## Finish line

Prove, in Unit, that the FIRST PROJECTION of the existing
`BetaIDS4HomFin.Hom.hom` fixes every element of the computed extension in
the diagonal case:

- the same o on both sides;
- the same certificate ac and the same well-foundedness witness wY on both
  sides, so both computed extensions are definitionally the same E;
- c, every tau_Z and f are POINTWISE identities;
- quantify over an arbitrary supplied rl : RelIn o o c tau, because the
  recursive calls construct their own witnesses (ShiftRel, PShRel).

Conclusion: for all x : E, `(hom o o c tau rl ac ac Y Y wY wY f).1 .1 x = x`.

The deliverable is this law for the map that `hom` actually computes, not
for a re-implementation.

## Hypothesis to add (to the coherence theorem only)

Pointwise km identity law: `(Z : LO) (p : (o.k Z).car) ->
Id ((o.km Z Z (idMap Z)).1 p) p`.
- Add it as a hypothesis of the new theorem. Do NOT change IObj, Thm.thm
  or hom.
- Call it a clean sufficient hypothesis; leave minimality open.
- Why it is needed:
  - At kept rules, e = DSumMap along lmap, which is induced by
    beta = tau_Y' . km f (TrCSquare.CombRel). Caveat: RegAsm puts the
    empty order on invalid branches and on stage labels >= top, and natS
    controls the action below top. So necessity is not established on
    every label.
  - The sharp reason: in the variable xl case the upper-tail summand
    occurs in the output extension, and its computed map is read from the
    child base map.
  - Kind III uses t (tail of beta) in f1 = f + ((1 + t) + e1).

## Inheritance under shifts (no extensionality hypothesis needed)

- `LOCat.map-eq` turns pointwise equality into equality in DP.Map.
- For a shift by D, prove id_D + id_Z = id_{D+Z} pointwise (two summand
  cases) and apply map-eq.
- The shifted km is the original km applied to this sum map
  (BetaIDS4.seg, around lines 339-422), so congruence gives the law for
  shifted families.

## Order of work

1. TEST THE ACCESSIBILITY WRAPPER EARLY (Stmt.Ind / goalT).
   - In the diagonal case, eliminate the shared Good root equation ONCE,
     with both occurrences varying together (path induction on a
     generalised statement).
   - Do this before assuming that any root equation computes to refl.
   - If this fails, stop and report the exact obligation.
2. Milestone lemmas: beta, lmap (labels) and the tail map t are pointwise
   identities under the hypotheses.
3. The motive: the pointwise-identity statement above, over all
   (o, ac, c, tau, rl, Y, wY, f) satisfying the pointwise hypotheses.
4. The node cases:
   - kept rules: DSumMap with lmap = id pointwise and e_a = id by the IH;
     check the label-selection transports;
   - xl constant and variable stages: ShiftRel data
     (c + id, tau . k(id + id));
   - r-bar: e1 + id_1;
   - kind III: t = id, so f1 = id pointwise; the IH at (V1, V1, f1); then
     e3 = e1 + ((1 + t1) + e2).
5. Known risk: e is the first component of terms through relC, subst and
   idJ transports (relC touches only the RelF component; check the
   others). Each non-refl transport needs a lemma about its action on the
   first component.

## Rules

- Spartan seg; checker: see PLAN-ID1 / memory.
- Full check: from DOMAIN run `python3 UNIT/check.py` (All.seg must stay
  green).
- Make focused local commits at green milestones, ending with
  "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>".
- Leave unrelated working-tree changes alone (di-domains.*,
  scott-domains.*, OBSTINATION/*).
- If an essential extra hypothesis appears, stop with the exact failed
  obligation, why the current data do not supply it, and the weakest
  repair.
- Report at the end:
  - the exact theorem and its hypotheses;
  - the check result and the commits;
  - what remains: composition across three certificates, inverse laws,
    certificate independence up to a specified isomorphism, and the
    trace-range laws.
