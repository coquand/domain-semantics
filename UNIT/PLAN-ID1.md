# Constructive cut elimination for ID1 in beta-logic — plan

Sources:
- `~/CANONICITY/GHerbrand.pdf` (Girard 1982), §1: the problem. Omega-logic
  cut elimination for ID1 (Pohlers, Buchholz, Sieg) only works when the
  inductive predicate occurs positively in the conclusion. Pi^1_2-logic
  gives full cut elimination and a subformula property.
- `~/DOMAIN/girard1.pdf` (Synthese 1985) §§6–8: sketch.
- `~/COLL/GIRARD/ptlc2.pdf` ch. 11: the full proof. The references below are
  to it.
  - 11.3.1: inductive logic T^{alpha beta}.
  - 11.4.1: the theorem.
  - 11.4.3: cuts of kinds I/II/III and the degree d0, with
    d0(I^lambda(n)) = omega . lambda.
  - 11.4.4: the main construction (pi, F) |-> (pi~, F + F'').
  - Lemmas 11.4.5–11.4.7.
  - 11.4.4 is proved "by induction on pi (10.2.9)".
- `~/DOMAIN/extomega.pdf` (Akiyoshi–Mints 2016): for contrast.
  - They get complete cut elimination for arbitrary sequents in omega-logic
    (extended Omega-rule, ID1 strength), with an inductive metalogic.
  - They have NO subformula property: the rule for "not forall X" takes an
    arbitrary instance T.
  - They have no completeness: cut-free provability is Pi^1_1, and
    "t notin I" is Sigma^1_1-complete.

## Target

Fix a positive operator Phi(X, x): a formula in NNF in which X occurs only
positively. The data are:
- a homogeneous F-proof pi of a sequent of L[Phi-bar, I^t];
- correctness of pi: its trees are well-founded at every well-order.

The construction should give, constructively (no LEM, no choice):
- a functor F~ with F <= F~ that preserves well-orders;
- a cut-free homogeneous F~-proof of the same sequent. Atoms are decidable
  (ev), so all cuts go, including the cuts of kind I.

Every formula of a cut-free proof is then a subformula of the end sequent,
up to the stage formulas I^mu(t) and Phi(I^mu, t). This subformula property
is syntactic, hence constructive.

NOT goals (both classical, see the memory note on Girard's ID1 cut
elimination):
- completeness (girard1 7.1, ptlc2 11.3.6): every true sequent has a
  beta-proof. Its proof uses the search tree plus "no countermodel ⇒
  well-founded", i.e. bar induction. It also cannot be inductive: provability
  by a first-level inductive definition is Pi^1_1.
- the reversal 11.6.4 (Cut-E ⇒ Pi^1_1-CA), which goes through completeness.

## Representation (reuse)

- **F-proofs = BetaPred.Obj.** k : LO -> LO, with km on embeddings and a
  family of trees over the labels of k X, natural in X. For an F-proof,
  pi_alpha has ordinal parameters in F(alpha). Homogeneity is
  F(f)^-1(pi_beta) = pi_alpha.
- **Extra structure on F (record `Pref`).** Girard's form is
  F = a + Id + 1 + F':
  - a natural embedding eta_X : X -> k X, the "Id" part;
  - a natural point top_X in k X above eta_X(X), the "+1" part;
  - preservation of well-foundedness.

  The constant prefix a matters only for 11.4.4(i)1, so start with a = 0.
- **Formulas as in BetaProof.** Closures (p, e), with e a list of labels.
  New atoms:
  - Ibar(n) / not-Ibar(n), standing for Phi-bar;
  - I(s, n) / not-I(s, n), where s is a stage given as an environment index
    whose value is a point of k X.
- **Rules** (one-sided Tait form, principal formula kept, as in BetaProof):
  - omega-rule for number quantifiers;
  - (rI) I(lambda, n): one premise Phi(I^mu, n), for a chosen mu < lambda;
  - (lI) not-I(lambda, n): a premise not-Phi(I^mu, n) for every
    mu < lambda in k X;
  - (r-bar) Ibar(n): one premise Phi(I^mu, n), for a chosen mu in k X;
  - (l-bar) not-Ibar(n): a premise not-Phi(I^nu, n) for every nu in X,
    labelled by eta(nu). This is the asymmetry: it has premises only for
    nu < alpha, not for all of k(alpha).
- **Composition** of the k's is ordinary function composition. F o G is
  needed for 11.4.4.

## Steps

**S0 (syntax, soundness) — DONE 2026-11-20 (core).** `BetaID.seg`: formulas, rules, pre-proofs and
F-proofs over Pref.
- Soundness at every well-order alpha, with the standard interpretation:
  I^mu = the mu-th stage, Phi-bar between I^alpha and I^{k alpha}.
- Use the Goedel–Gentzen refutation semantics as in BetaProof.
- Consistency.

Sanity check: the asymmetric rules make each T^{alpha, F(alpha)} inconsistent
on its own (11.3.2). Exhibit a small pre-proof that is correct at one alpha
only, to see why homogeneity is essential.

**S1 (kind II cuts, 11.4.3).** Pointwise and homogeneous elimination of cuts
whose cut formula contains I^lambda but not Phi-bar. Reuse the pattern of
BetaCut/BetaHom: generic double induction `Ind` and branching on decEq.
- The measure is d0(I^lambda(n)) = omega . lambda (11.4.3):
  Phi(I^mu, n) with mu < lambda has smaller degree.
- Constructively this is a lexicographic induction: Acc of lambda in k X,
  then the size of the formula.
- Homogeneity holds because d0 is functorial.

**S2 = MILESTONE 1 (the Phi-bar cut; ptlc2 pp. 300–310) — DONE pointwise 2026-11-20.** Girard does
NOT reduce a Phi-bar cut by recursion. Revised after reading the proof of
11.4.4:
- **Input.** Two families: L proves G, Phi-bar(t) and R proves
  G, not Phi-bar(t). Here G is parameter-free and the cut formula sits at
  index p.
- **11.4.5.** In L, rename the positive Phi-bar(t) at index p to I^c(t).
  - Every (r-bar) choice mu on p becomes an (rI^c) choice, valid when
    mu < c.
  - With principal formulas kept (Tait), the only "ancestor" of the occurrence
    is the same closure, so renaming touches only index p.
- **11.4.7.** In R, rename the negative Phi-bar(t) to I^c(t) with c = top:
  (l-bar) and (lI^top) have the same premises.
- **Evaluate R at k(X), with c = top_{kX}.** Map L along
  eta_{kX} : kX -> k(kX). This is an initial segment, so transport is
  trivial, and its choices are < top_{kX}.
- **Chop R** to top~ = eta_{kX}(top_X). Since the l-bar bound is read from
  top in br, this only lowers top: the tree shrinks, so LocOK and the
  Brouwer bound are inherited. The renamed rule (now lI^c) is not chopped.
- **Output.** At (k(kX), eta_{kX}(top_X)), a pre-proof of G whose root is a
  cut on the stage atom I^{top_{kX}}(t) (kind II, left to S1).
- **Correctness at X** needs L correct at X and R correct at kX, hence
  k preserves WF. This is where "the proof as a whole" is used.
- **Homogeneity** of the output (S2b) comes after.

Design decisions made in S0 for this:
- (xl i o) names its predicate o; the bound of l-bar is top, read in br.
- Number quantifiers range over N (labels (n, inl tt)), so ordinal
  parameters enter only through stages.
- Pref: eta_X : X -> kX is an initial segment with image {< top_X}
  (Girard's F = Id + 1 + F', prefix a = 0).

Building blocks:
- (T) transport of pre-proofs along initial-segment embeddings.
- (C) chop.
- (N) renaming at an index.
- (A) cut assembly.

**S3 (Lemmas 11.4.5, 11.4.6, 11.4.7 with functoriality).** The bookkeeping
around S2:
- ancestors of an occurrence of Phi-bar;
- the transfer T(pi) along T in I^1(F, G);
- naturality in T.

**S4 (11.4.4: the global construction; THE CRUX).** Girard proves 11.4.4 by
induction on pi along the predecessor relation of 10.2.9, and F~ is built
during that recursion.

Constructive status (BetaPred.seg):
- Classically, 10.2.9 holds via LEM2/DC2 (`Cl.main`).
- Constructively (`Cons`), induction along predecessors holds when their
  shifts D are absorbed by one well-order Z (D + Z -> Z). The proof is by
  induction on the Brouwer bound at Z.
- The full constructive 10.2.9 is OPEN. It needs a large absorbing
  well-order, i.e. lifting homogeneous trees to level l+.

Plan for S4:
- (a) Check which predecessors 11.4.4 actually uses:
  - immediate premises (D empty);
  - (l-bar)/(lI) premises (shift D = beta + 1);
  - the re-evaluation at k(alpha) in the Phi-bar case. Does it still go to a
    predecessor in the 10.2.9 sense? Find out.
- (b) If (a) shows that every shift is absorbed by a fixed Z, then S4
  follows from `Cons`, possibly evaluated at Z = k^omega-type orders.
- (c) Otherwise this is exactly where the Pi^1_1-CA strength of 11.6.4
  should enter. Try a nested inductive definition, as in the Lambda plan
  (`~/CANONICITY/unit/dilators/PLAN-LAMBDA.md`, open step "every IsDil is
  accessible"), and record precisely what is assumed.

**S5.** Kind I cuts: atoms are decidable, so ordinary propositional cut
elimination via BetaCut. Then the subformula property, as a theorem by
induction on the cut-free trees.

**S6 (optional).** girard1 §8: a cut-free proof of
forall x in Phi-bar exists y in Phi-bar A gives bounds by the dilator F~.


## S4(a) analysis (2026-11-20, on paper, NOT formalised)

**What Girard uses.**
- 11.4.4 is proved by induction along the predecessors of 10.2.8/10.2.24.
- Premises of unary and binary rules, cuts, and the omega-rule have shift
  D = 0.
- Premises of ordinal-branching rules (lI^lambda, l-bar) are
  chi^beta_alpha = pi_{c_beta + alpha} at (z; x; c_beta + alpha). The shift
  D = c_beta is the initial segment up to the support of beta, an
  ARBITRARY well-order. That is why 10.2.9 needs omega^a (classically), or
  a large absorbing order (constructively: BetaPred, OPEN).

**Claim.** Finite shifts suffice.
- Homogeneous proofs are determined by their restrictions to finite
  suborders (as in BetaPre: the rule at an address is computed in the
  finite suborder spanned by its points).
- For a finite suborder S containing the support x of nu, write S = S1 + S2
  with S1 = points <= max x. Then nu is a natural label in k(S1 + Y), so
  it gives a predecessor with FINITE shift D = S1.
- Finite D is absorbed by Z = omega (n + omega -> omega). BetaPred.Cons at
  Z = omega therefore gives the induction constructively, by induction on
  the Brouwer bound of the tree of pi at omega (a countably branching
  tree).

**Consequence (if the claim holds).**
- The termination of 11.4.4 needs no large ordinal.
- The Pi^1_1-CA strength (11.6.4) sits in the MOTIVE: the cut-free
  F~-proof is correct at ALL well-orders, i.e. F~ is a dilator. This is an
  elimination of the tree at omega into U l+, quantifying over all
  well-orders.

**Formalised (2026-11-20, `BetaIDPred.seg`, in All.seg, green).**
- (a) Homogeneous ID F-proofs are BetaPred objects (FObj; naturality via
  BetaIDTr.Mp.treeMap).
- (b) Finite D is absorbed by omega (absF). FinInd: induction along
  finite-shift predecessors for every data-valued Q and every correct
  object, with no LEM or choice (Cons at Z = omega).
- (c) The premises of a root l-bar rule are finite-shift predecessors
  (LBar.stepL). The label eta_{D+X}(inl d) is natural and below top, and
  the shifted object is the premise family.

**Test 1 (2026-11-20, on paper): the claim FAILS for correctness.**
- Data is fine: rules at addresses are computed in finite suborders
  (BetaPre-style), so finite shifts and Z = omega suffice for the
  construction and its homogeneity.
- Correctness, i.e. well-foundedness at INFINITE well-orders, is not
  carried by finite-shift predecessors.
  - At X = omega+1, the l-bar premise at x = omega lives over the initial
    segment X_{<=omega}, which is infinite.
  - No finite-shift object covers it: mutilation goes from bigger to
    smaller orders, and well-foundedness at X is not determined by finite
    suborders.
- Counterexample to FinInd carrying CorrO (k = id). Take the tree of
  sequences  x0, then strictly increasing points below x0.
  - It is natural.
  - Every finite-shift predecessor is correct at all well-orders (below
    inl d there are finitely many points).
  - The object itself is not correct: at omega+1 with x0 = omega the branch
    omega, 0, 1, 2, ... is infinite.
  - It is correct at omega, so Cons at omega cannot prove "correct at all
    well-orders".
- Consequence.
  - Correctness of the output (and "F~ is a dilator") needs the induction
    along predecessors with ARBITRARY shifts c_beta: the full 10.2.9.
    Constructively this needs a large absorbing well-order, as in
    BetaPred, which is OPEN.
  - This is where the Pi^1_1-CA strength of 11.6.4 shows up. The original
    crux of S4 stands.
  - Alternative (also open): a simulation of the output tree at X into the
    input tree at F~(X). That still needs F~ to be a dilator, which is the
    same obstruction.

**To check (superseded by Test 1).**
- The 11.4.4 construction (with its F~) must be compatible with the
  finite-support presentation: does F~ itself come from finite data?
- Rebuilding the premise at X from the IH on finite-shift predecessors
  needs the BetaPre-style extension for the OUTPUT families.


## Option 1: full constructive 10.2.9 (2026-11-20, analysis, STUCK)

Routes examined:
- **Large absorbing Z** (BetaPred's plan). Cons needs a DECIDABLE linear
  order Z, well-founded, with embeddings D + Z -> Z for every small
  well-order D.
  - Candidates fail. A sum over all small well-orders needs a decidable
    linear order on the index (well-orders lack decidable equality).
  - E*omega with E universal for small well-orders has the same problem
    for E.
  - Brouwer ordinals are well-founded but not decidably comparable.
  - I see no construction, and suspect none exists, but have NO proof of
    impossibility.
- **Z relative to the target order Y** (Z = Lab(Y), with D in copy 0
  absorbed by shifting copies). This works for the l-bar premises.
  It breaks at the Phi-bar case: the composition F~'' o (Id+1+F~') needs
  F~'' correct at F~'(Y), which escapes any Z fixed in advance. Choosing
  Z after F~ is circular, because "F~ is a dilator" is itself the
  correctness at stake.
- **Bar induction.** What is constructive today: BetaPred.Chain (an
  infinite chain contradicts correctness) and Cons (absorbed shifts). Going
  from "no infinite chain" to "accessible" is bar induction over
  predecessor chains, a spread over a LARGE type. This is not available in
  type theory.

Option (a) result (`BetaIDAbs.seg`, formalised, in All.seg).
- The conditional "absorbing Z => full predecessor induction" IS
  BetaPred.Cons.
- noAbsorb: no well-founded Z of level l absorbs every well-founded D of
  level l. Take D = Z + 1: a strictly increasing self-map bounded by a
  point is impossible (Burali-Forti).
- So the absorbing order must live at level l+, and the level-l
  beta-proofs must be evaluated there. The precise open hypothesis is the
  LIFTING: a homogeneous family correct at all small well-orders is
  correct at a large absorbing well-order.
  - Classically this holds via "a branch is countable, hence bounded"
    (the large order has uncountable cofinality).
  - Constructively it meets the same "no infinite branch => Brouwer bound"
    gap.

Verdict: stuck on the step from "no infinite chain of predecessors" to
"accessible for predecessors". This is presumably where the Pi^1_1-CA
strength of 11.6.4 is spent: impredicativity, or BI over large spreads.


## Analysis of the lifting (2026-11-20, on paper)

**Statement.** A homogeneous family P that is correct (Brouwer-bounded) at
every small well-order is correct at a large well-order Omega that absorbs
all small ones.

**Two independent obstructions to the "large absorbing order" route.**
- (L1) Omega must be a DECIDABLE linear order (rules, labels and the
  bounds in br compare points). No construction is known, even at level l+:
  - sums over all small well-orders need a decidable order on the index;
  - a universal E needs the same;
  - Brouwer ordinals are not decidably comparable.
  Not refuted either: an absorbing Omega does not obviously decide
  comparisons of well-orders.
- (L2) Even given Omega, passing correctness from small orders to Omega is
  "no infinite branch => Brouwer bound". Classically a branch is countable,
  hence lies in a small suborder. Constructively nothing turns this into a
  bound.
- Level-polymorphic correctness (seg has [j] types) would remove (L2), but
  not (L1).

**Equivalences (classical, Girard).** The lifting, full 10.2.9, and
"every correct object is accessible for the predecessor relation" (the
analogue for beta-proofs of the 9.4 open step in PLAN-LAMBDA) are the same
content: a BAR THEOREM over a large spread (chains of predecessors indexed
by all small well-orders). This is where LEM + DC (Pi^1_1-CA, 11.6.4)
enter.

**Constructive reformulation (proposed).** Replace "correct beta-proof"
(semantic, Pi^1_2) by "ACCESSIBLE beta-proof": the inductive (large)
accessibility predicate along BetaPred predecessors, with all shifts D.
- accessible => correct at EVERY well-order (constructive, uniform in X).
  - A child a of the root at X is a predecessor: D = X_{<=x}, label
    (n, inr (inl x)), evaluated at X_{>x}, using X = D + X_{>x}
    (decidable split). Number labels give D = 0.
  - Recurse on the accessibility proof, building the Brouwer bound at all
    X at once. For general k this needs supports (k = a + Id is fine).
- correct => accessible is exactly the classical 10.2.9 (BetaPred.Cl with
  Q = accessibility, up to propositional truncation).
- Cut elimination (S4) by induction on ACCESSIBILITY needs no lifting. The
  induction hypothesis covers all shifts, and the S2 evaluation at kX is
  just application of the induction result. The output should again be
  accessible.

Formalised (`BetaAcc.seg`, in All.seg, green):
- AccO: large inductive accessibility along BetaPred predecessors.
- accCorr (CONSTRUCTIVE): accessible + k functorial (FC, FE) + trees
  prefix-closed (PC) => correct at every well-order.
  - Trick: no splitting of X is needed. A node a at X is the predecessor
    with shift D = X and label k(inl)(a); evaluated at the EMPTY order it
    is the subtree at a, read along k(inl).
  - FC/FE/PC pass to predecessors (Inh).
- Classical.corrAcc: with LEM2 + DC2 + AC2 (choice over predecessors),
  correct => merely accessible, via BetaPred.Cl.
- 2026-11-21: certificates are unique (AccR.accProp, funext; J on the
  root equation), so ClassicalAcc.corrAcc gives the DATA AccO from
  correctness with LEM2 + DC2 only (no AC2). Still classical.

Expected constructive theorem: cut elimination for ACCESSIBLE ID1
beta-proofs, output accessible, hence correct. Girard's version follows
classically via 10.2.9. The Pi^1_1-CA content is isolated as one bar
theorem: correct => accessible.


## S4 under accessibility (2026-11-20, on paper)

**Key point.** In Girard's 11.4.4 the induction hypothesis is used ONLY on
predecessors of the INPUT. The outputs are combined (e.g. pi~'' evaluated
at F~'(alpha)) but never recursed on.
- So induct on the accessibility of the input, with motive
  Q(o) := cut-free output family + output correct at every well-order
  + F~ a dilator.
- Outputs need not be accessible, which removes the composition problem
  (R o k has no predecessors of the BetaPred form).

**Cases.**
- Commuting rule at the root (e.g. l-bar).
  - Output at X: same root rule. The child at a is the induction output of
    the predecessor "shift by X, label k(inl)(a)" at the empty order,
    pulled back along k(inl).
  - The Brouwer bound comes as in accCorr.
- Phi-bar cut at the root: exactly S2 (BetaIDS2), fed with the induction
  outputs of the two premises (predecessors with D = 0).
  - Correctness at X needs the left output correct at X and the right
    output correct at kX. Both are given by the induction hypothesis
    (correct at all well-orders, kX well-founded).
  - The new cut is on I^c (kind II): S1 eliminates it at the order k(kX).
    That is a pointwise induction on the tree and the degree omega*c, with
    no recursion on predecessors.

**What remains.**
- S1: elimination of kind II cuts.
- Homogeneity / functoriality of the construction (11.4.4 (ii)-(iii)):
  outputs must form natural families, compatible across predecessors
  related by maps (10.2.25). This is bookkeeping, but large.
- Bookkeeping of F~ (sums and compositions of dilators; dilators are
  closed under these).
- I see no remaining conceptual obstruction. This is NOT yet checked
  formally beyond S2, BetaIDPred and BetaAcc.

## S1 DONE pointwise + S2+S1 combined (2026-11-20, in All.seg, green)
- `BetaIDCf.seg`: inductive derivations Cf with the x-rules (cXr, cXl),
  weakening, the generic double induction Ind (branching on membership
  proofs), and Mis.
- `BetaIDCfCut.seg`: StOK (kind II at stage lambda), cut cases CAt, CAnd,
  COr, CAll, CEx, and CX (stage atom: a cut on I^lambda'(t) becomes a cut
  on phi(I^mu, t) with mu < lambda'). cutAll: induction on the stage (A
  well-founded), then on the formula. Dv and elim.
  - Hypothesis wfPhi: phi(I^mu, t) is of kind II at stage mu.
- `BetaIDCfTr.seg`: translation from BetaID pre-proofs with a Brouwer
  bound to Dv. cutFree: pointwise elimination of kind II cuts (CutOK
  witnesses at in-tree cut nodes).
- `BetaIDS21.seg`: S21.Fin.cutFree. For L, R cut-free (NC), the S2
  output's only cut (I^topK, kind II) is eliminated, giving a CUT-FREE
  derivation of eta G at (k(kX), eta topX). This is a pointwise, end-to-end
  elimination of a Phi-bar cut between cut-free proofs.
- Still open: homogeneity (outputs as natural families, BetaHom-style with
  `decide`), F~ bookkeeping, and the global induction on accessibility (S4).

## Homogeneity of S1 and S2 DONE (2026-11-20, in All.seg, green)

- `BetaIDCf.Ind` now branches on DATA: `decide`, i.e. decidable equality
  of closures (`eqF` on formulas with X-atoms, `eqL` from BetaCut). It no
  longer branches on membership proofs. Downstream files are unchanged.
- `BetaIDHom.seg` (S1, port of BetaHom). Data: an embedding g : A -> B
  with g(topA) = topB and atoms invariant under g.
  - `RelF`: a cut-free derivation at B restricts to one at A.
  - `RInd`: the generic double induction preserves restriction. The other
    side is related by an arbitrary RO, and the sequents at A and B are
    NOT related, since the output trees never depend on them. This avoids
    the `nthMap` mismatch on the closures of the x-rules.
  - `numR`, `belR`: the dummy premises (off the numbers, off the bound)
    agree.
  - Cut cases CAtR, CAndR, COrR, CAllR, CExR, and CXR (the stage atom: the
    induction hypothesis at mu < la on A, g mu < laB on B).
  - Stage induction (`St.Step`, `indR`, `cutAllR`): recursion on the
    accessibility tree at A, with the tree at B split along it. A
    `W.subst` lemma handles `indT`.
  - `elimR`, `toDvR`.
  - `St.Fin.nat`: for pre-proofs whose rules and cut stages are natural AT
    THE ADDRESSES OF THE TREE at A, and whose end sequents are natural, the
    derivations from `BetaIDCfTr.CT.cutFree` are related along g.
- `BetaIDS2Hom.seg` (S2b). Data: two S2 instances, at X and at Y, and maps
  h1 : kX -> kY, h2 : k(kX) -> k(kY). Hypotheses:
  - h2 o eta = etaY o h1;
  - rhoY o etaY = id;
  - h1 topX = topY and h2 topK = topKY;
  - the data at Y are the images (G_Y := h1 G, e_Y := h1 e, literally);
  - the premises L, R are natural at the addresses of their trees.
  Then the S2 output is natural at the addresses of its tree (`Prem.nr`):
  - root: `envRoot`;
  - left: the addresses are images of eta (`pENat`), then `ruleNat`;
  - right: `fixNat`.
  `S2N.Hom.nat`: the cut-free derivations of S21 at k(kX) and k(kY) are
  related along h2.
- Caveats.
  - Naturality is relational (restriction), as in BetaHom. The outputs are
    not presented as one pre-proof on all linear orders.
  - In S2b the Y data are the images literally. A family that is natural
    only up to propositional equality needs one transport (not done).
- Next: the bookkeeping of F~, and S4 (cut elimination by induction on
  accessibility), combining BetaAcc, S2/S21 and the two homogeneity
  results.

## S4 design (2026-11-21): pointwise, Cf-native

Reading of ptlc2 11.4.4-11.4.7 (pp. 302-310):
- Lemma 11.4.6 (transfer along T = id + T' : F -> G) works because in a
  proof without cuts of kind II/III, every NEGATIVE stage is < a + alpha,
  i.e. below top.
- Outputs are F + F''-proofs: the extensions lie ABOVE top. Premise outputs
  are combined in F + F1 + F2 (sums of the extensions).
- Output sequents replace every I^t, t non-constant, by Phi-bar. With an
  F-term t, non-constant means t >= top.

Formal choices:
- **Outputs are Cf derivations** (inductive, cut-free), not pre-proofs.
  - The output for pi at a well-order Y lives on kY + E (E well-founded)
    and has top = inl top_Y.
  - It proves rep(G_Y): each stage label >= top_Y becomes Phi-bar (same
    number), and stages < top_Y are kept.
  - Pointwise first; homogeneity later, with BetaIDHom's RelF on Cf.
- **Motive:** Q(pi) = for all Y WF, Out(pi, Y), by induction on the
  ACCESSIBILITY of the input family (BetaAcc). Correctness of the input is
  not needed, since Cf derivations are well-founded by construction.
- **Input objects** carry the Pref structure explicitly: an order iso
  sigma_Y : kY = (Cst + Y) + (1 + F'Y), natural, with top_Y = the point 1.
  - Shifting by D gives Cst' = Cst + D and F'' = F'(D + -), and sigma is
    re-associated. No subtypes are needed.
  - The functor laws of k are needed for evaluating an ordinal premise at
    E0: k(Y + 0) -> kY.
- **Premises:**
  - natural labels (numbers, binary, constant stages) are plain steps
    (same k);
  - variable ordinal premises nu = sigma^-1(inl (inr y)) are shifts with
    D = Y, evaluated at E0, then pulled back along k(Y+0) -> kY.
- **Combination:** B = kY + DSum_{a in Lab(kY)} E_a, a dependent
  lexicographic sum. It is needed for ordinal-branching rules; this is
  Girard's integral of dilators.
  - The transfers kY + E_a -> B are initial only below top. The transport
    of Cf (TrC with the bound predicate Bd) uses the invariant "negative
    stages < top" of cut-free derivations. That is a subformula property,
    from the syntactic hypothesis "phi has only positive X-atoms, all
    reading the stage position".
- **Cases at the root of pi_Y:**
  - axioms and logical rules: the same rule with the premise outputs;
  - (xl) with bound < top: the same rule;
  - (xl) with bound >= top: (l-bar), keeping the premises nu < top;
  - (xr) with principal predicate kept: the same rule;
  - (xr) with principal predicate replaced, choice mu < top: (r-bar) with
    mu;
  - (xr) with principal predicate replaced, choice mu >= top: the premise
    output proves Phi(Phi-bar, t). Extend by one point c = top of
    kY + (E + 1), rename the marked Phi-bar inside Phi(Phi-bar, t) into I^c
    (11.4.5, compound case: the label at the end of the environments of
    the descendant closures), then (r-bar) with choice c;
  - kind I cut (no X-atom): combine, then the BetaIDCfCut cut;
  - kind III cut (Phi-bar(t)): L~ from Out(pi', Y) on A1 = kY + E1.
    - Set V1 = Y + ((1 + F'Y) + E1), so that A1 = Cst + V1 by
      re-association.
    - R~ = Out(pi'', V1) on A2 = k(V1) + E2. Its context is the image of
      L~'s context, by naturality of G and sigma.
    - S2C (DONE) gives a Cf derivation on (A2, iota top).
    - A2 = kY + E by an explicit iso.
  - kind II cuts in the input are excluded (Girard: 11.4.3 first).
- **Hypotheses on ev:** atoms depend only on the numbers of the labels.

**Done so far:** `BetaIDCfOps.seg` (dev loop `_devcf.seg`, 4 s; in
All.seg, green):
- TrC: transport of Cf along embeddings, with a bound predicate;
- ChopC;
- RenPC (11.4.5 for an atom) and RenNC (11.4.7);
- S2C: the Phi-bar cut between cut-free derivations on Cf, with the new
  cut on I^topK eliminated by BetaIDCfCut.

**Done since** (same files, green):
- `DSumLO.seg`: the dependent lexicographic sum over an LO, with laws via
  J and Hedberg, embeddings of the summands, and WF.
- `BetaIDCfOps.Inv`: the invariant "negative stages < top" for cut-free
  derivations, from posX phi 0 = true. posX says the X-atoms are positive,
  read the stage position, and never use it as an argument.
  - It also gives BetaIDCfCut's wfPhi at every order.
- `BetaIDCfOps.TrL`: transport along embeddings that are initial below top
  only (Lemma 11.4.6).
- `BetaIDCfOps.RenM`: the compound case of 11.4.5. Marked closures are
  (formula, prefix), with environment prefix ++ [t, xb]; the decision
  "marked?" is made on data.

**Refinements of the design:**
- With sigma, NO functor laws for k are needed.
  - The variable ordinal premise at nu = sigma^-1(inl(inr y)) is the
    shift by D = Y with label sigma^-1_{Y+Z}(inl(inr(inl y))). It is
    natural by the naturality of sigma below top.
  - It is evaluated at E0. Its output on k(Y+0) + E goes into
    kY + (F'(Y+0) + E): the part of k(Y+0) below top maps through
    Cst + (Y+0) = Cst + Y, top maps to top, and the part F'(Y+0) above top
    goes into the extension.
- Node conditions of premise steps at ALL orders Z come from the root rule
  at E0 (naturality along E0 -> Z).
- Kind III: iota : kY + E1 -> k(V1) is sigma^-1 o inl o (re-association).
  It is globally initial with image below top_{V1}, and
  A2 = k(V1) + E2 = kY + ((E1 + T1) + E2) by explicit sum isos.
- Naturality of sigma is needed only below top, plus k(f)(top) = top.

**`BetaIDS4.seg` part 1 (green):**
- Sm, wfSm, wfOpt, wfLab.
- `Rep` (rO/rL/rE/rC/rS, nthR, memR, getR).
- `OutM.Out G` = Sigma (E : LO) (WF E) * Res at (A + E, inl top) of rep G.
- `EnvOK`: labels below top or Phi-bar give the invariant for every
  formula.
- EvN: atoms depend only on the numbers of the labels; evMap.
- `Comb`: B = A + DSum[Lab A, Ex]; `move a G` transports an output on
  A + Ex a to B (TrL, with the invariant from EO).

**`BetaIDS4.seg` part 2 (green):**
- `Assoc`: the re-association isos of sums.
- `Obj`: `record IObj` with the fields listed below, plus noX, barAt,
  KindOK, topO.
- `Steps`: PStep and PSh.obj (plain predecessors).
- `SSteps`:
  - SStep and SSh.obj (shift by D: sigma re-associated, natS', sec',
    ret');
  - Step = plain + shifted; shiftO; AO = BetaAcc.AccR over IObj; AccI.
- `OutBack`: moves an output on A' + E for mS_h X to an output on
  A + (Ext + E) for X, along j : A' -> A + Ext.
**`BetaIDS4.seg` part 3 (green, in All.seg: 33299 declarations):**
- `Main`: Q o = for all Y WF, Out(kY, top_Y, G_Y); e0 : E0 -> Z; brMR.
- `Main.Node`: rZ (the root rule at Z is mR of the rule at E0), brNum,
  nodeNum, stNum. pNum gives the premise output at a number label, from
  the induction hypothesis.
- `Sig`: the sigma-decomposition of points (dec, belowW, ltTop, notTop).
- `Main2.Bnd`: images of a bound of E0 (constZ, and bigZ for bounds
  >= top).
- `XL` (with `XL.Cn`) and `XLV` (with `XLV.Vr`): the premise outputs of a
  root (xl) rule at stages nu < top below the bound (`XLV.pStage`).
  - Constant nu: a plain step.
  - Variable nu: a shift by D = Y, evaluated at E0, then OutBack along
    the sigma-map j : k(Y+0) -> kY + Fp(Y+0).

**Part 4 (green, dev loop):**
- `RepR`: rR, Reg, stepRep, applRep, brN, preX, noXSt.
- `CfDv`: cf2dv, okCD.
- `RegAsm.Fin.out`: the output at a node whose root rule is kept. This
  covers ax, and, or, all, ex, xr with choice < top, xl with any bound,
  and kind I cuts. Route: the providers pv (pNum, sp for stage labels),
  then Comb, then CT.okRule at B, then elim.
- `RBar.out` (DONE): the root rule is (xr) with choice mu >= top. The
  premise output is moved into kY + (E + 1), its Phi-bar is renamed into
  I^c (RenM, with c the last point), and (r-bar) is applied with choice c.
- `RepMap`, `subLast`, `pickF`, `fstAp`; `Iso` with isoComp, isoSum,
  isoAG, isoAF, isoHr (DONE).
- Still OPEN:
  - **kind III**, with this exact design:
    - Orientation first: barAt accepts Phi-bar(t) and not Phi-bar(t),
      and branch 0 carries the displayed cut formula, branch 1 its
      negation. Choose (labL, labR) by polarity BEFORE building E1 and
      V1: positive formula gives labL = lab0 and labR = lab1; negative
      gives labL = lab1 and labR = lab0. S2C.out needs the positive
      premise at Y and the negative one at V1. Swapping its arguments
      afterwards is too late, because V1 depends on E1.
    - L~ = pNum(labL) on A1 = kY + E1.
    - V1 = Y + ((one + Fp Y) + E1), f1 = inlS : Y -> V1.
    - R~ = ih (plain step labR) at V1; its sequent is
      mS_{km f1}(app G [not Phi-bar]) by ngGen.
    - g : A1 -> A2 = k V1 + E2 is
      inl o sgi_V1 o inl o alpha o (sg_Y + id), where
      alpha = Assoc[Cst,Y,..].g o Assoc[Cst+Y,T0,E1].g and beta is its
      inverse. rho uses sg_V1 and beta.
    - Lemma: rL2 (lm (km f1) l) = lm g (rL1 l), by natS and belowW.
      DONE as `K3Ctx.seqC` (with lC, envC, gBelow, ltK), together with
      V1, f1, alpha and g (dev loop, green, uncommitted).
    - DONE: theta : kV1 + E2 = A1 + (T1 + E2) as an Iso composite, with
      `thetaG` (theta (g a) = inl a on all of A1). Also `rho` (read off
      theta), `hr` (g is initial: from theta b < inl a, by map-inj) and
      `gTop` (g a < inl top_V1).
    - Next: the kind III node, which applies S2C.out with
      (g, rho, hr, gTop) and then transports along theta followed by
      re-association.
    - Then S2C.out.
    - theta : A2 = kY + ((E1 + T1) + E2) as an Iso composite:
      isoSum (sg_V1)^-1, then beta + id, then isoAG, then isoSum sgi_Y,
      then isoAG. theta (g (inl p)) = inl p; transport with TrC.
  - the **dispatcher** on the E0 rule r0 (rZ: R_Y nil = mR r0):
    - ax/and/or/all/ex: RegAsm with sp absurd;
    - xl: RegAsm with sp = XLV.pStage;
    - xr: inspect ltB mu top, then RegAsm or RBar;
    - cut: kd gives noX (RegAsm, kw = noXSt) or barAt (kind III).
  - `thm : AccI o -> Q o` by AO.ind.

**NEXT (rule assembly), planned route:**
- A rule map rR (rep on rules: choices mu < top become inl mu; the bounds
  through rO), and the lemmas:
  - stepRep: step (rS G) (rR r) (rL a) = rS (step G r a), for regular r;
  - applRep;
  - the preimage of the branch labels of B.
- Then use BetaIDCfTr.CT.ruleDR at B = kY + DSum (premises as Dv), and
  CT/KC.elim. This also eliminates the kind I cuts (StOK holds for noX).
- Special cases:
  - (xr) with choice mu >= top: RenM on kY + (E + 1), c = the last point;
  - kind III: S2C at V1, then the iso to kY + E.
- Finally `thm`: AccI o -> Q o by AO.ind.

**Remaining plan (d)-(f), concrete:**
- (d) `record IObj` inside a module (ev, phi, evN), with fields:
  - k, km, Cst, Fp;
  - sg : kY -> P Y and sgi : P Y -> kY, where
    P Y = (Cst + Y) + (one + Fp Y); with sec and ret;
  - natS: km f (sgi (inl w)) = sgi (inl (smapC f w)); ntop for
    top = sgi (inr (inl tt));
  - wC, wF;
  - G, R, ng, nr (via BT.Mp with evMap);
  - lo : LocOK at every Y;
  - kd: in-tree cuts are of kind I (no X-atom) or III (Phi-bar atom).
- Steps:
  - plain: a natural label family in kY plus node at all Y; the same k.
  - shift: D WF, a natural label family in k(D + Z) plus node; the object
    is k(D + -) with Cst' = Cst + D, Fp' = Fp(D + -), and
    sg' = re-association o sg_{D+Z}.
  - AccR (BetaAcc) over IObj.
- Branch labels at the root (rule r_Y = R_Y nil):
  - numbers: plain steps with constant labels;
  - stage nu < top with sg nu = inl (inl c): plain step, label
    sgi_Z (inl (inl c));
  - stage nu with sg nu = inl (inr y): shift by D = Y with label
    sgi_{Y+Z}(inl (inr (inl y))), evaluated at E0, then moved into
    kY + (Fp(Y+0) + E) by the sigma-map.
  - Node at every Z: r_Z = mR(r_{E0}), by naturality along E0 -> Z.
- (e) The rules: ax, and, or, all, ex, xr (3 subcases, 2a with RenM on
  kY + (E + 1) and c = the last point), xl (bound < top, or >= top giving
  l-bar), and kind I cut (Comb, then BetaIDCfCut cutAll).
- (f) Kind III: V1 = Y + ((one + Fp Y) + E1); iota by re-association and
  sgi_{V1}; R~ = IH(right premise, plain step) at V1; S2C; transport
  along the iso A2 = kY + ((E1 + T1) + E2).

## S4 pointwise THEOREM DONE (2026-11-21, All.seg 33683 declarations, green)

`BetaIDS4.Thm.thm`: every ACCESSIBLE input family o (homogeneous, locally
correct, with sigma : kY = (Cst+Y)+(1+F'Y), all cuts of kind I or III)
gives, at every well-order Y, a well-founded E and a CUT-FREE
derivation (Cf) of rep G_Y at (kY + E, inl top_Y). This is Girard's
Gamma~: stages >= top are replaced by Phi-bar.
- Proof: AccR induction (`Disp`) on the root rule, read off at E0:
  - RegAsm for ax/and/or/all/ex, xr with choice < top, xl, and kind I
    cuts;
  - RBar for xr with choice >= top;
  - K3Sel/K3Node for kind III: polarity choice, then L~ at Y, R~ at V1,
    seqC, S2C, and transport along theta + re-association (thetaG).
- Hypotheses: EvN (atoms see only the numbers of labels) and
  posX phi 0 = true. No LEM, no choice.
- Not covered:
  - homogeneity of the outputs: DONE afterwards (next section);
  - kind II cuts in the input (11.4.3 for families);
  - correct => accessible, which is classical (10.2.9; BetaAcc.Classical).

## S6 for Part 3's bar predicate (2026-11-21, BetaIDS4Bar, checked)

phi(X,s) = G(s) or forall t (not ch(s,t) or X(t)), G and ch decidable
(ev reads them from the environment numbers; EvN by ap; posX by refl).
- ORDINARY stages B^lambda(s) = Sigma mu<lambda. phi(B^mu)(s): CondR for the
  hereditary clause is the obligation `HerB mu la s`: not B^la(s) ->
  not not exists n (ch(s,n) & not B^mu(n)). `WithDNS.herB`: it follows
  from the double-negation shift over N; `herToShift`: with
  forall n not not (ch -> B^mu n) it gives not not B^la(s). So ordinary
  stage evidence works exactly up to the shift.
- STABLE stages J^lambda(s) = not not Sigma mu<lambda. phi(J^mu)(s), by
  recursion on accessibility trees (`Jn`, tree irrelevance `jIrr`,
  `jIn`/`jOut`, `jStab`). `Model.condR`, `Model.condL`: a split model on
  ANY well-order with top (J at stages, negative Phi-bar = J^top,
  positive Phi-bar = Jall = not not exists mu phi(J^mu)). No shift needed:
  J^mu(t) is not-not-stable.
- J vs B: `bToJ` (B^la -> J^la); `WithDNS.jToB` (J^la -> not not B^la,
  given the shift). So a bound on J is a CLASSICAL stage bound for bar
  evidence; it gives ordinary bar evidence only up to not not and the
  shift.
- `Bar.Cor.stageBound`: for an accessible family proving
  forall x (B(x) -> exists y (A(x,y) & B(y))), at every WF Y (E returned
  by normalisation): J^{top_Y}(n) -> not forall m not not (F A(n,m) or
  not Jall(m)), Jall = J after all of kY + E.
- Example `Ex` (G = nonempty, children nonempty, on omega): `enter1`
  (nonempty in J^1), `notEnter1` (empty not in J^1), `enter2` (empty in
  J^2); the stage-1 version of enter2 fails (indexing check).
- Next: the benchmark B(s) -> B(sw) for monotone G (direct proof keeps
  the stage) against the bound normalisation returns.

## S6 stage bound: first corollary (2026-11-21, BetaIDS4Stage)

- Obstruction found: BetaID.Snd needs ONE predicate M(Phi-bar) with
  U_{mu in A} phi(I^mu) <= M(Phi-bar) <= U_{nu < top} phi(I^nu). On the
  output order kY + E (top' = inl top_Y) this forces the hierarchy to be
  stationary from top_Y: the existing semantics cannot express the bound.
- Fix (Girard's reading): Phi-bar BY POLARITY. `PN` is the refutation
  semantics with F(xF b s k) = xsF b (M b label arg); `CondR` constrains
  M true (positive: contains the unfoldings at allowed stages), `CondL`
  constrains M false (negative: below the bound, stated with
  not F(neg phi), so no key lemma). `PN.Snd.soundCf`: cut-free (Cf)
  derivations are sound for such split models (induction on Cf).
- `Cor.bound`: for an accessible family o, at every WF Y, every split model
  on (kY + E, inl top_Y), E the order returned by Thm.thm, validates
  rep G_Y (Valid = Not AllF).
- `Cor.Mixed.Bd.stageBound`, for G_Y = forall x (B(x) -> exists y (A(x,y)
  & B(y))) with both B Phi-bar in the input:
      M-(n) -> not forall m. not not (F A(n,m) or not M+(m)),
  M- below the stages < top_Y, M+ containing the unfoldings at every stage
  of kY + E. Constructively a DOUBLE-NEGATED existential: no witness.
- CAVEAT: relative to split models; the trivial model (M+ = all, M- =
  nothing) satisfies the conditions. Teeth need the STANDARD model
  (I^lambda = U_{mu<lambda} phi(I^mu) by WF recursion on kY + E, with
  locality of F and wfPhi): not yet constructed.
- Next: the standard split model; witness extraction from the cut-free
  derivation (a separate theorem); the coded-tree example.

## Atomic cuts represented as Phi-bar DONE (2026-11-21)

`Obj.KindOK A top` cut case: `StLow` (below top) or `BarR` (an atom whose
label is RepBar: Phi-bar or a stage >= top). So every ATOMIC cut (any
polarity, any stage) and every compound cut below top is admissible;
pointwise theorem, homogeneity and diagonal law all hold.
- K3Node takes `RepBar` (only the represented occurrence must be Phi-bar;
  `repBar` gives hbar1). K3Sel.out takes BarR.
- Homogeneity: `NodeD.rbPres`/`rbRefl` (an embedding preserving top
  preserves and reflects RepBar on corresponding atoms) give the cross-case
  exclusions `lowBar`/`barLow` (with `Obj.lowRep`).
- Boundary test `BetaIDS4Bound.Ex`: a concrete accessible family, root cut
  on I^{top_Y}(t) beside a true arithmetic atom (k Y = (0+Y)+(1+0),
  sigma = id); kdK uses the BarR branch (`notLow`: not below top);
  `out`, `hom`, `diag` instantiate the three theorems.
- Remaining class: compound cuts with at least one occurrence represented
  as Phi-bar (I^mu(t) & I^nu(u), mu < top <= nu; Phibar(t) & Phibar(u)).

## Cuts below top DONE (2026-11-21, All.seg 35525 declarations, green)

The input kind condition is now `Obj.KindOK A top`: every cut is BELOW TOP
(`Obj.StLow`: every X-atom of the cut formula reads a stage mu < top, never
Phi-bar; compound formulas and number quantifiers allowed; kind I is the
case without X-atoms, `noxLow`) or of kind III (`barAt`). The pointwise
theorem (Thm.thm), homogeneity (Hom.hom) and the diagonal law (diagId)
all hold for these inputs.
- Pointwise: `Disp.cutC` sends a cut below top to the kept-rule node, with
  `RepR.stLow` (rep keeps it of kind II at inl top) as the CutOK witness
  for RegAsm.Fin (okRule, then KC.elim). Premises are input predecessors;
  no elimination of kind II cuts for families.
- Homogeneity: `NodeD.cutH`; the cross cases are excluded by `lowBar`,
  `barLow` (the target environment is the beta-image, `eEnv`).
- Not covered: atoms at stages >= top (rep makes them Phi-bar; these occur
  in unrestricted inputs, e.g. a cut on I^{top_Y}(0) beside a true
  arithmetic atom) and compound formulas mixing stage and Phi-bar atoms.
  Next test: the atomic high-stage case via the kind III construction
  with an interface asking only that the REPRESENTED occurrence be Phi-bar.
- Write-up: UNIT/id1-cut-elim.tex (6 pages).

## Diagonal identity law for S4 homogeneity DONE (2026-11-21, All.seg 35471 declarations, green)

**Theorem** (`BetaIDS4Diag.Fin[ev,phi,evN,hPos].diagId`). Same hypotheses as
`Hom.hom` (EvN ev, posX phi 0 = true). Let o be an input family with
certificate ac, Y a well-order with wY, c : Cst -> Cst, tau_Z : kZ -> kZ,
f : Y -> Y, and rl : RelIn o o c tau ARBITRARY. Assume pointwise
c w = w, tau_Z p = p, f y = y, and the pointwise km identity law
(km Z Z id) p = p. Then for every z in E = (Thm.thm o ac Y wY).1,
`(hom o o c tau rl ac ac Y Y wY wY f).1 .1 z = z`.
- The km law is a clean sufficient hypothesis; minimality is open (see
  the caveats in NEXT_SESSION_DIAG.md). No other extra hypothesis:
  funext enters only through LOCat.map-eq (km along a pointwise identity).
- The deliverable is about the map that hom computes; IObj, Thm.thm, hom
  are unchanged. No holes, no postulates.

Proof structure (files `BetaIDS4Diag*.seg`, about 960 lines):
- `BetaIDS4Diag.Wrap`: the accessibility wrapper. The shared Good root
  equation is eliminated ONCE (J on g.1 with both occurrences varying);
  the recursion on the tree gives the induction hypothesis IHD for the
  children (same step on both sides, any cs, taus, rs).
- `BetaIDS4DiagBase`: the hypotheses (DB.KmId/CId/TId/FId), kmF, betaId,
  IHD; UIP for LO carriers; UIP for rules (RuleSet: code into
  N x N x Form x LL x Lb x Opt, decidable equality, Hedberg); omId/lmId/mEId;
  based J at the endpoint (JE); PropFam (normalised transport over a
  proposition, fixing every point).
- The recursion is NOT diagonal definitionally: NodeD.Cases.out does J on
  relE0 : r0' = tau-image of r0, and the target steps carry other proofs
  or points (stage beta nu, constant c c0, variable f y). So the node law
  is heterogeneous:
  - `DiagNode` (dispatcher): the map at (rr, e) -> (MZ.mR rr, e') is the
    transport Tr2 along the singleton (z, Id r0 z); split rr, J on the
    mapped parameter (w = MZ.lm w, e0 = MZ.mE e0, mu0 = tau mu0,
    oo0 = MZ.om oo0), UIP for rules; then the homogeneous case.
  - `DiagReg` (kept rules): DSumMap(lmap, em) fixes every point; number
    labels by IHD (the same plain step on both sides); stage labels after
    the two Bool splits of pv reduce to the stage law SPRD (the summand
    point at nu equals the image point at beta nu, through the embeddings
    ib, i2 of the split providers).
  - `DiagRbK3`: (r-bar) e2 = e1 + id; kind III e3 = e1 + ((1 + t1) + e2)
    with f1 pointwise id and the tail maps t, t1 identities (DTail: from
    tlp and injectivity of sigma^-1, no decision computed).
  - `DiagXl`: SPRD for the (xl) stage relation. Points live in a total
    space TW over (v, hm, hlt, w, ew); pWH moves the point at nu to the
    point at beta nu: J on weq, split w, contract to the canonical stage
    sigma^-1(inl w) by JE, then J on c0 = c c0 (constant) or y = f y
    (variable) and UIP (O3, Bool), then IHD (the variable child at E0
    through the shift data c + f, tau . k(f + id), with the upper-tail map
    an identity). The bridge TW -> summands is PropFam over the
    proposition (hm, hlt, w, ew).
- Certificate independence (`BetaIDS4DiagIso.At`, 2026-11-21; argument
  supplied by the user): certificates are unique (BetaAcc.AccR.accProp),
  so `outputEq` gives equality of the computed outputs at two certificates
  (no km hypothesis). Under the km law, `Laws.round` shows that the maps
  e_ab computed by homSame (at id_Y) are mutually inverse: transport along
  a = b, then diagId twice. `Laws.iso` is the specified isomorphism.
- Remaining: composition along arbitrary parameter embeddings, the
  trace-range laws of 11.4.4(iii); minimality of the km hypothesis.

## Homogeneity of S4 DONE (2026-11-21, All.seg 35005 declarations, green)

**Theorem** (`BetaIDS4HomFin.Hom[ev,phi,evN,hPos].hom : Stmt.Goal`).
Hypotheses: EvN ev and posX phi 0 = true, the same as Thm.thm. Let o, o'
be input families related by (c, tau) (`RelIn`), with accessibility
certificates ac : AccI o and ac' : AccI o'. Let Y, Y' be well-orders and
f : Y -> Y'. Put (E, d) = thm o ac Y wY and (E', d') = thm o' ac' Y' wY'.
For each f, hom constructs an embedding e : E -> E' and a witness of RelF d d' along
beta + e : kY + E -> k'Y' + E', where beta = tau_Y' o k(f). The base map
preserves top (`baseTop`) and the tops are inl top_Y, inl top'_Y'.

- Same family (`homSame`): o' = o, c = id, tau = id, with `relId : RelIn
  o o id id` proved from mapL-id/omap-id. Any two certificates and any f
  give e with RelF along k(f) + e.
- No holes, no postulates, no classical assumptions. The pointwise
  theorem and its hypotheses are unchanged.
- Files:
  - BetaIDS4Hom (RelIn, ShiftRel, VrSq);
  - TrCSquare, AssemblyRel;
  - BetaIDS4HomThm (Goal, IHR, NodeT, Ind.thm by recursion on ac.1 with
    the target tree split);
  - BetaIDS4HomReg (kept rules: RegPrem/RegHom);
  - BetaIDS4HomNode (dispatcher NodeD.Cases);
  - BetaIDS4HomXl ((xl) stage premises, constant and variable);
  - BetaIDS4HomRen (RenMRel: compound renaming 11.4.5; RenPCRel, RenNCRel:
    atom renamings 11.4.5/11.4.7);
  - BetaIDS4HomRb (r-bar above top);
  - BetaIDS4HomK3 (tail map t from beta, SgNat: sg' beta = Phi sg; K3Sq:
    g' u1 = u2 g, theta naturality, rho' u2 = u1 rho, h' u2 = v3 h;
    S2CRel);
  - BetaIDS4HomK3N (K3NodeRel, K3SelRel);
  - BetaIDS4HomFin.
- Kind III: the positive premise gives e1 : E1 -> E1' by the IH at
  (Y, Y', f). Then f1 = f + ((1 + t) + e1) : V1 -> V1', and the negative
  premise gives e2 by the IH at (V1, V1', f1). The output map is
  e3 = e1 + ((1 + t1) + e2), with t1 the tail map of beta1 = tau_V1' o k(f1).
- r-bar: the IH (label 0) gives e1. Then e2 = e1 + id_1, and the target
  principal closure is the beta-image (G' = beta G).
- The identity and composition laws for the constructed embeddings and
  the trace-range laws of 11.4.4(iii) remain open.
  Kind II elimination for families and correct => accessible remain
  separate tasks.

## Homogeneity of S4: development notes (2026-11-21)

`BetaIDS4Hom.seg` and `TrCSquare.seg` (in All.seg, green):
- `Rel.RelIn o o' c tau`: related input families. tau_Z preserves top,
  the root sequent and the rules. Below top,
  tau_Z (sigma^-1 (inl w)) = sigma'^-1 (inl ((c + id) w)).
- `Rel.ShiftRel`: shifts of related families along f : Y -> Y' are
  related along (c + f, tau_{Y'+Z} o k(f + id)), given matching labels
  (`Lab.rel`). The variable-premise labels match (`varLab`).
- `BetaIDS4.SigMaps`: the sigma-maps of XLV, which XLV now aliases (so
  they are convertible).
- `VrSq`: the upper-tail map tl, read off the child base map, and the two
  squares v o J = J' o u (`sq1`) and u o rho = rho' o v (`sq2`).
- `TrCSquare.Square.alg` (written by the user): TrC.mD preserves RelF given
  the two squares. `Variable.Back.backRel`: the two OutBack.back
  derivations of a variable ordinal premise are related, given the child
  RelF witness.
- `TrCSquare.DSumMap` and `TrCSquare.CombRel.moveRel`: Comb.move preserves
  RelF along beta + (a, x) |-> (l a, e_a x).
- `AssemblyRel.seg` (written by the user): cf2dvR (RelF gives RelD of the
  cf2dv translations) and `assemble` (BetaIDHom ruleDR + elimR applied to
  RegAsm's one-rule assembly; needs CHR at valid source branches only).
  `selStage`: the target preX selects the image of the source stage.
- OPEN for RegAsm: the concrete CHR witness, i.e. the related pv
  providers, moveRel, cf2dvR, and the selection of target labels.
- `BetaIDS4HomThm.seg`: the TARGET `Stmt.Goal` (related accessible
  inputs, both certificates, arbitrary f : Y -> Y'; an embedding of the
  computed extensions and RelF along (tau_Y' o k(f)) + e), and `Ind.thm`:
  Goal from the node comparison NodeT (recursion on the source tree with
  Good, a split of the target tree, J on both Good equations). OPEN: NodeT.
- Note: in Fin.prem, ch reads only the first projection, so the stepRep
  transports of correctness proofs need no comparison.
- Next: the same for the other operations (Comb.move, RepR/CT.okRule plus
  elim via BetaIDHom, RBar/RenM, K3Node/S2C), then the induction on
  ac.1 with Good, with arbitrary f and the target certificate quantified.

## Expected outcome / what would be new

- A constructive, checked reconstruction of Girard's ID1 cut elimination,
  with a genuine subformula property. This is what Akiyoshi–Mints lack.
- The constructive principle that makes S4 terminate, set against
  11.6.4 (Pi^1_1-CA).
- If S4 needs more than `Cons`, that is itself the answer to "where does the
  strength go?".

## Status
- 2026-11-21 (night): homogeneity of the S4 outputs DONE (bf6ba47, see
  "Homogeneity of S4 DONE").
- 2026-11-21: homogeneity committed (a3374f0). S4 design fixed (section
  above). `DSumLO.seg` and `BetaIDCfOps.seg` (TrC/TrL, ChopC, RenPC/RenNC/
  RenM, Inv, S2C) are in All.seg, green. Not committed.
- 2026-11-21 (later): `BetaIDS4.seg` parts 1-3 (outputs, combination,
  input objects, steps, accessibility, premise outputs at number and stage
  labels) are in All.seg: 33299 declarations, green. The rule assembly,
  the r-bar case, kind III and the final theorem are OPEN (in progress).
- 2026-11-21 (end): Thm.thm DONE (see the "S4 pointwise THEOREM" section).
  Not committed past 84caca2.
- 2026-11-20: plan written.
- 2026-11-20: S1 (pointwise) and S2+S1 DONE (see section above).
- 2026-11-20: homogeneity of S1 (BetaIDHom) and of S2+S1 (BetaIDS2Hom) DONE;
  All.seg 32589 declarations, green. Not committed.
- 2026-11-20: S0 core and S2 (pointwise) DONE, in All.seg, check.py green
  (All.seg 31115 declarations). Not committed.
  - `BetaID.seg` (S0): syntax with X-atoms whose predicate is read from
    the environment (inl = Phi-bar, inr mu = I^mu), x-rules, pre-proofs at
    (A, top), refutation semantics relative to a model (CondR/CondL),
    LS, soundW.
  - `BetaIDTr.seg` (T): transport along initial-segment embeddings (trLo,
    trWf).
  - `BetaIDCut.seg`: (C) Chop (loChop, wfChop); (N) Ren (generic
    renaming at index p), RenP (11.4.5), RenN (11.4.7).
  - `BetaIDS2.seg` (S2): `S2.Out.lo` / `S2.Out.wf`. From L at (kX, top_X)
    and R at (k(kX), top_kX) we get a locally correct, Brouwer-bounded
    pre-proof of eta G at (k(kX), eta top_X) whose root is the cut on
    I^{top_kX}(t).
  - Dev loop: `_devid.seg` (3.7 s).
- Open next:
  - S1: kind II elimination, needed to remove the new I^c cut. A port of
    BetaCut with a measure (stage, formula).
  - S2b: homogeneity of the S2 output.
  - S3 / S4 as above.
- Assumption used in S2: the right premise at kX has end sequent
  eta G, not Phi-bar(t) (true for natural, parameter-free G).
