# MAHLO — Lemma 14 (the fixed point): feasibility study, step 1

The setting: after P2 and the concrete model, Theorem 16 and (T2a) depend only on
`Fixpoint concreteTM`, a candidate V with `V << Γ V` (unfold) and `Γ V << V` (fold).

## Verdict

**There is no known way to prove Lemma 14 in `--safe --without-K` Agda. I expect it is not provable there without an extra principle.**
- The constructive parts (successor stages, unions of chains, the unfold half at a limit) are fine; they are proved in the spike below.
- What fails is *closure/termination*: a stage θ with `Γ X_θ << X_θ`.
  - Every constructive route to closure needs **impredicativity** (route b), or **a universe principle of at least Mahlo strength in the metatheory** (route d).
  - Plain stages hit a size wall (route a). Induction-recursion does not apply (route c).
- **Recommendation:** keep `Fixpoint` as the single, clearly stated hypothesis. It is already minimal (soundness uses both halves). Optionally, isolate the residue further (see "Next steps").

Status vocabulary: **proved** = machine-checked here; **known** = literature or standard; **open** = neither.

## Constructive parts — proved (`MAHLO/FixpointSpike.agda`, `--safe`, 202 lines)
- `<<` (end-extension) is reflexive and transitive (`<<-refl`, `<<-trans`).
- Union of an ω-chain `X n << X (n+1)` (`Chain.Uw`): it is a candidate, with all fields, including the setoid closure fields.
  - It end-extends every stage (`upper`).
  - It is the **least** upper bound: if every `X n << Z` then `Uw << Z` (`least`).
- Iterating Γ from a seed `X0 << Γ X0` (`Iter`): the successor step is P1's `mono` (Lemma 13), and `unfold-omega : X_ω << Γ X_ω`.
- **Not proved, and false at ω in general:** `Γ X_ω << X_ω`. A Π-code whose family members first appear at stages 1, 2, 3, … is in Γ(X_ω) but in no X_n.

## (a) Stages over an ordinal notation
- **Successor:** fine (P1 `mono`). **ω-limits:** fine (spike).
- **General limits — open constructively.**
  - The closure of Γ needs sups over families indexed by D, by the proof-relevant interpretations `I A v v'`, and by `Pre`-derivations (infinitely branching).
  - So the ordinals must branch over arbitrary small types: `data Ord : Set1` with `sup : (I : Set) → (I → Ord) → Ord`.
  - The union `⋃_{i:I} X_{f i}` is a PER only if the family is **directed** (a common upper bound for any two stages, for transitivity).
  - Classically this comes from the linearity of the ordinals. For Brouwer-style trees, linearity, and hence comparability of the stages, is not available constructively.
- **Termination — classical as stated.**
  - The plan's argument (strictly increasing stages inject |D×D|⁺ into D×D) uses LEM, to decide whether a stage grows, and Hartogs.
  - With the concrete D (countable terms) it stabilises at a countable ordinal, but that is still a classical existence claim.
- **"Union over ALL ordinals" instead of termination — fails on size in `--safe` Agda.**
  - `R_V a b := Σ (α : Ord). R_{X α} a b` lives in **Set1**, but a candidate's `R : D → D → Set`. Resizing is unavailable.
  - Putting the ordinals in Set (branching over a universe `U : Set`) forces U to be closed under sups indexed by the stages' own relations, which mention `Ord_U`. That needs a universe containing (codes for) its own ordinal type: impossible (Burali–Forti), or else a Mahlo-type reflection principle.

## (b) Impredicative: least fixed point
- Knaster–Tarski does not apply: ⊑ is not a complete lattice (plan, Issue 3).
- **Pataraia's theorem** (constructive in any topos): a monotone map on a dcpo with ⊥ has a least fixed point. It does fit:
  - candidates above the seed, ordered by ⊑, have directed unions (the spike's ω-proof generalises to directed families);
  - Γ is ⊑-monotone (P1 Lemma 13).
- But the proof quantifies over all monotone inflationary maps on that dcpo, and the resulting sups must stay **Set-valued**. That needs impredicativity: **known** to work in an impredicative setting.
- **Minimal extension:** make the PERs proof-irrelevant (R, I valued in Prop) and take an **impredicative Prop** (topos-style / CIC Prop), or an impredicative Set with resizing. Agda `--safe` has neither (its Prop is predicative; `--type-in-type` is inconsistent).
- Strength is far more than needed (higher-order-arithmetic level).

## (c) Induction-recursion
- **Does not apply — known.**
  - Γ is not strictly positive: X occurs negatively via `Indep`, which quantifies over `Pre(f,g,X)`, and via `FamResp`/`I_X` inside `Pre`. Monotonicity holds only by a lemma (extended predicativity).
  - Setzer (setzer1 §3.3) shows the Mahlo universe is not an inductive-recursive definition. A reformulation of Γ as IR would yield an IR definition of (a model of) the Mahlo universe.
- So Agda's IR (Dybjer–Setzer) does not reach this Γ.

## (d) Extra principles
- **The current `Fixpoint` record is already the minimal hypothesis.** Soundness uses *both* halves:
  - unfold `V << Γ V` for inversion: `invU` (the key observation that a code carries Indep/Op), `piSmall2`, `Vnotin`, `invPi`;
  - fold `Γ V << V` for introduction: `piIn`, `mahlo-code`, `mahlo-int`.
  - A "Γ-closed candidate" (fold only) or a "Γ-consistent candidate" (unfold only) would not suffice.
  - Anything general, e.g. "every ⊑-monotone operator with directed unions has a fixed point", is *stronger* than `Fixpoint`.
- **Principled replacements**, each a clearly stated module parameter:
  - **(d1) A type-theoretic Mahlo universe** in the metatheory (Setzer's MLM rules as a record). Then run route (a) with ordinals branching over the Mahlo universe, and get the closure stage from a subuniverse closed under the stage operator.
    - **Open** whether a plain Mahlo universe suffices.
    - Kahle–Setzer place the extended predicative Mahlo universe in KPM + one recursively inaccessible above it, so one more universe above the Mahlo universe is probably needed.
  - **(d2) Impredicative Prop**, giving route (b) via Pataraia.
  - **(d3) Classical set theory:** the plan's proof is a valid ZF(C) proof. It is not available in Agda.
- **Strength:** by Gödel (plan, Metatheory §), any such principle must exceed the strength of the object theory.
  - Kahle–Setzer: extended predicative Mahlo is roughly KPM + an inaccessible.
  - The exact proof-theoretic strength of Agda `--safe` (IR plus a universe hierarchy) is, to my knowledge, not established. It is therefore **open**, not refuted, whether some unknown construction in pure `--safe` Agda exists.
  - No route in (a)–(c) yields one.

## Next steps (only if the user wants them; none started)
1. *Cheap (about 1 session):* generalise the spike's union from ω-chains to **directed** families of candidates.
   - This isolates the residue as a single "closure" statement about the tower.
   - It is also the dcpo half of route (b).
2. *Research:* route (d1). State a Mahlo-universe record and attempt the closure stage. First check whether Kahle–Setzer's "one inaccessible above" is needed in the PER setting.
3. Otherwise: leave `Fixpoint` as the documented hypothesis. The plan's status table already says this.

## Step 2 (user decision: keep Fixpoint; justify it by fix.pdf) — DONE

`fix.pdf` (Coquand 1995): a monotone map on a conditional sup-semilattice with ⊥ and sups of all directed subsets has a fixed point. The proof is constructive but impredicative.

### Hypotheses of the theorem for P = (Cand, <<) — `MAHLO/FixHyp.agda`, `--safe`, proved
| hypothesis | status |
|---|---|
| (1) preorder | `<<-refl`, `<<-trans` (FixpointSpike) |
| (2) least element | `Seed.seed` is a candidate, and `seed-least : seed << X` for **every** candidate X (so P can be taken to be all of Cand) |
| (3) f = Γ maps P to P, monotone | `seed-Gam`. `Gam-mono : X << Y → Γ X << Γ Y` holds **with no side condition** (P1's `EndExt.mono` assumes only `X << Y`); the restricted monotonicity on {x ≤ f x} is not needed |
| (5) conditional binary sups | `Join`: if X, Y << Z then X ∨ Y (union of the relations) is a candidate and the lub. Transitivity goes through Z and comes back by end-extension (a X b, b Y c ⇒ a Z c ⇒ a X c, since a ∈ \|X\|). A common upper bound suffices |
| (4) directed sups, Set-indexed | `DirSup`: for I : Set, the union of a directed family is a candidate and the lub |

(4) and (5) are **one construction**, `Union`: the union of a Set-indexed family whose members are pairwise bounded by *some* candidate. It keeps all setoid closure fields.

### The size issue (flagged, machine-checked)
- If the theorem only asks for sups of **Set-indexed** families on a carrier in Set1, it is **refutable** (`MAHLO/FixCounter.agda`, `refute : FixThmSmall → Empty`).
  - The carrier is W-ordinals branching over Set. It has ⊥, binary joins and lubs of all Set-indexed families.
  - The successor is monotone and has no fixed point (well-foundedness).
  - This also answers fix.pdf's closing question ("use Brouwer's ordinals … Is this possible?") negatively, in the naive form.
- So the faithful statement is `FixThm`: sups of directed families **of the carrier's own size** (Set1-indexed for Car : Set1). It is classically valid.
- Candidates have such sups only impredicatively. A union of Set1-many candidates has Set1-valued relations. That one-level gap is exactly the impredicativity. Coquand's proof also takes ⋁A over its inductive A ⊆ D, which is one more level up.

### The derivation
- `FixThm` is stated with large sups, as a record and **not provable** here. `LargeSups` gives lubs of Set1-indexed directed families of candidates.
- `candDCPO : LargeSups → LargeDCPO` (Cand, <<, seed, LargeSups, Join).
- `pfix-of : FixThm → LargeSups → PFix`.
- `fixpoint-of-pfix : PFix → Fixpoint` (Γ is unconditionally monotone).
- `fixpoint : FixThm → LargeSups → Fixpoint`.
- At the concrete model: `Concrete/Sound.normalise-fix : FixThm → LargeSups → (T2a)` and `normalise-pfix : PFix → (T2a)`.

### (a) What exactly LargeSups is
- Classically: R_U a b := ∥Σ i. R_i a b∥, and likewise for I. Strong (untruncated) large Σ in Set is not an option (impredicative strong sums are inconsistent).
- So it is **propositional resizing of truncated large sums**: ∥Σ (i : I : Set1). R_i a b∥ must land in Set.
- **But that is not the whole story with our proof-relevant relations.** The candidate fields `ne-int`, `ne-only`, `nat-int`, `nat-only`, `R-safe` and `I-hi` map the union INTO the base relations N, S, NatR and ~~. Eliminating the truncation into them requires either
  - N, S, NatR and ~~ to be propositions (true after truncating them, e.g. truncate SR, NR and Conv; the development only uses them up to logical equivalence), or
  - a large unique choice.
- The interpretations need no extra choice: any witness gives an equivalent I, by end-extension.
- **Precise form:** LargeSups = propositional resizing + truncation, for a development in which all relations are proposition-valued.

### (b) One clean statement
- **`PFix`: every <<-monotone endomap of Cand has a <<-fixed point.**
- PFix ⇒ Fixpoint immediately. PFix ⇐ FixThm + LargeSups (proved). PFix is classically valid.
- Suggested plan text: "Theorem 16 and (T2a) hold relative to PFix, the impredicative fixed-point principle for candidates (Coquand 1995 + propositional resizing); every concrete hypothesis of the fixed point theorem is machine-checked."
