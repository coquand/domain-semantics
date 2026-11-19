# Girard's conjecture for n = 2: a type-3 "exponential" for Pi^1_2-CA

Source: Girard, "Herbrand's theorem and proof-theory" (Herbrand Symposium,
1981; ~/CANONICITY/GHerbrand.pdf), section 3:
  conjecture: Pi^1_n-CA <-> A_n in PT^{n+1}, for a canonical "exponential"
  A_n; known for n = 0 (2^Id in PT^1, ACA) and n = 1 (Lambda in PT^2,
  Pi^1_1-CA); n = 2 "would give the ordinal of Pi^1_2-CA".
Here: n = 0 is DilLO.twoD-dil, n = 1 is ThetaFun2.thetaP-ptyx (Freund's
theta in place of Girard's Lambda).  Forward (constructive) directions only.

## Candidate (2026-11-19, NOT established)
Theta : type-2 pre-ptykes -> pre-dilators, "theta one type up":
ThetaF(Y): atoms y in Y, and Theta(K, sigma, a) with K a code (finite
dilator, C2.Fin), sigma a normal trace point of F at Decode K, a the images
of K's generators in ThetaF (terms at finite stages) -- a finitary
presentation of an element of F(ThetaF): F applied to the dilator being
built (self-application, as theta applies D to theta D; stability rather
than admissibility).
Order: Freund's clauses; F-parts compared after amalgamating the codes
(C2.dir, StabAmal/StabJt) in F(Decode K'').
Statement: forall type-2 ptyx F, ThetaF is a dilator.  Conjecture: this
is (classically, over a weak base) equivalent to Pi^1_2-CA0.

## Steps
1. Literature check (Freund's thesis 2018 and later; any WOP for Pi^1_2).
2. Sanity: F = evaluation at omega gives the Pi^1_1 level; F = theta must
   go beyond the ordinal of Pi^1_1-CA0; Python mirror on finite fragments.
3. Terms/comparison (codes + amalgamation).  4. Laws by height (semantic
   lemma in F of the sub-DILATOR of lower terms).  5. Functoriality (C3).
6. Well-foundedness: accessible sub-dilator must be a dilator -- induction
   on dilators (Girard 9.4, ~ type-2 bar induction): the research risk.

## Step 1: literature (2026-11-19)
- No known well-ordering principle for Pi^1_2-CA0 (searched; Freund's
  thesis and later papers stop at Pi^1_1-CA0 and its iterations).
- Complexity bound (Freund-Rathjen 2021 intro, Rathjen 2021): "D(X) WF
  whenever X WF" is Pi^1_2; type-2 "F(D) WF for every dilator D" is Pi^1_3
  (enough for Pi^1_1-CA0, a Pi^1_3 theory).  Pi^1_2-CA0 is Pi^1_4, so its
  characterization needs a statement of the form forall F (F type-2 ptyx
  -> Phi(F) of complexity Pi^1_2/Pi^1_3): a type-3 principle.  The
  candidate "forall F type-2 ptyx, Theta F is a dilator" is
  forall F (Sigma^1_3 or Pi^1_2) = Pi^1_4: complexity is right.
- Closest results:
  * Freund, "Well ordering principles and Pi^1_4-statements: a pilot
    study" (arXiv 2006.12111): Pi^1_2-INDUCTION <-> fixed points for all
    normal 2-ptykes -- the first type-3-level characterization.
  * Aguilera-Freund-Weiermann, "Induction on dilators and Bachmann-Howard
    fixed points" (arXiv 2412.13051): Pi^1_1-CA <-> totality of
    Paeppinghaus's functor J (a streamlined Lambda); Girard's Lambda claim
    was never fully worked out.  Relevant to step 6 (induction on dilators).
  * Rathjen, "Well-ordering principles in proof theory and reverse
    mathematics" (arXiv 2010.12453), Thm 6.5 (beta-models of Pi^1_1-CA via
    OT_D(Omega_omega)) and Conjecture 6.6: ordinal systems of strong T give
    F_OT : DIL -> WO with "F_OT(D) WO for all dilators D" <-> every set in a
    countably coded beta-model of T.  Type 2, so it characterizes beta-model
    REFLECTION of T (Pi^1_3), not T itself (Pi^1_4 for Pi^1_2-CA0).
- Consequence for the design: two targets of different strength:
  (a) type 2 (Rathjen 6.6 style): F : DIL -> LO from a notation system for
      Pi^1_2-CA (stability), characterizing beta-models -- fits IsPtyx
      directly, like theta;
  (b) type 3 (Girard (*) for n = 2): Theta : PT^2 -> DIL, statement Pi^1_4,
      characterizing Pi^1_2-CA0 itself -- the conjecture proper.

## Step 2: sanity (2026-11-19, on paper)
Target (b) chosen.  Anchor: Freund's ladder (abstract of 2006.12111):
  type 1: normal dilator has a WF fixed point      <-> Pi^1_1-induction
          dilator has a WF Bachmann-Howard collapse <-> Pi^1_1-CA0 (theta)
  type 2: normal 2-ptyx has a WF fixed point       <-> Pi^1_2-induction
          2-ptyx has a WF BH collapse              <-> Pi^1_2-CA0 ?  (CONJECTURE)
Here a 2-ptyx is P : DIL -> DIL (curried: a binary stable functor
P(Delta)(Y)); the "BH collapse" of P is a dilator Delta with a collapse
theta : P(Delta) => Delta, i.e. theta applies P to the DILATOR being built,
as theta_D applies D to the ORDER being built.  This is the precise form
of the candidate Theta : PT^2 -> DIL (type 3, statement Pi^1_4).

2a. NEGATIVE (obstruction to the first candidate above).  If Delta(Y) has
  only atoms y and collapses theta(sigma) that are closed (no free y), then
  Delta = C + Id with C = Delta(0), hence P(Delta) = P(C + Id) and
  C = theta_{D_P} for the type-1 dilator D_P(X) = P(X + Id)(0) (up to a
  routine identification of supports).  Pi^1_1-CA0 proves "P 2-ptyx ->
  D_P dilator" (X WF -> X + Id dilator -> P(X+Id) dilator) and then
  "theta_{D_P} WF" (Freund).  So that variant is <= Pi^1_1-CA0: the
  hypothesis "P is a 2-ptyx" is only used on dilators X + Id, a Pi^1_2 use.
  Any candidate of Pi^1_2-CA strength needs collapses with free
  Y-variables, i.e. Delta(Y) genuinely non-trivial in Y.

2b. REDUCTION (positive).  For P(Delta)(Y) = D(Delta(Y)) (a dilator D
  lifted pointwise) the collapse at Y = 0 is a BH collapse of D, so
  Theta_P(0) = theta_D: the type-3 construction specializes to theta.

2c. DESIGN ISSUE (open; signalled now).  The Delta-support of
  sigma in P(Delta)(Y) consists of TRACE elements (m, t) of Delta
  (images of the generators of a code K -> Delta), not of elements of
  Delta(Y); e.g. P(Delta)(Y) = Delta(omega) + Y uses Delta at omega, not at
  Y.  The collapse conditions "supp(sigma) < theta sigma" and
  "sigma < tau, supp(sigma) < theta tau" need a comparison between trace
  elements and elements of Delta(Y).  Proposed resolution (Buchholz-style
  coefficient sets): read the m variables of a trace element (m, t) as
  cardinals above everything, and replace supp by K(sigma) = the closed
  (variable-free) components of the support terms; collapses theta_u
  indexed by u in {top} + Y (one collapsing function below each atom, as
  psi_{Omega_y}), so Delta(Y) has free Y-variables (needed by 2a).
  Not yet checked: linearity/decidability of this order, and strength:
  the check "P = (Delta |-> theta(Delta)) gives something beyond the
  Bachmann-Howard ordinal and beyond Pi^1_1-CA0" needs a Python mirror of
  this term system (next).

2d. MIRROR (UNIT/mirror/theta3.py, test_theta3.py, explore.py).  Design
  (L) made precise: Delta(A) = atoms a in A (below all collapses) |
  th(s), s in P(Delta)(A); th s < th t iff (s < t and K(s) < th t) or
  th s <= k for some k in K(t); K_A(s) = maximal components of s lying in
  Delta(A) (A-atoms, and Delta-subterms that pull back along the canonical
  embedding A -> B, B = A+1, 1+A, Delta(A), omega^A, composites).
  2-ptykes given by combinators Y | 1 | + | omega^ | Delta(-).
  Checked on random terms (6 functors P, bases 0,1,2, seeds 1-6, depth 6):
  antisymmetry, (cmp = 0 iff equal), transitivity, naturality along
  increasing maps 0..n-1 -> 0..n+1.  All pass: the order is a decidable
  linear order and Delta is functorial on the samples (not a proof).
  Observations:
  - P with no constants (e.g. Delta(Delta(Y))) gives Delta(0) empty;
    harmless (least fixed point), but instances should have constants.
  - In (L) a fresh variable (Delta(Y+1)) sits BELOW all collapses, so it is
    a small ordinal, not an Omega: instances like omega^Delta(Y+1) look
    weak.  The Omega role is played by self-application: in
    P(Delta)(Y) = omega^Delta(Delta(Y)) the atoms of the outer Delta are
    elements of Delta(Y), the collapse is a BH collapse D(X) -> X with
    D = omega^Delta, and unfolding Delta at Omega gives a tower
    Omega_1 < Omega_2 < ...  HEURISTIC (not checked): this instance is
    around psi_0(Omega_omega), the ordinal of Pi^1_1-CA0 -- exactly the
    threshold that 2a could not pass.
  - Enumeration by size shows only tiny initial segments; it cannot
    measure strength.  The real check is an order-embedding test: map
    Buchholz's psi_0-terms (Omega_n, +, omega^) into Delta(0) for
    P = omega^Delta(Delta(Y)) and test order preservation on samples.
2e. CORRECTION (2026-11-19, on paper, before coding the embedding).
  For P = omega^Delta(Delta(Y)) put A_n = Delta^n(0).  Delta(A_n) =
  atoms (the elements of A_n, "below Omega_n") + collapses th(s) with
  s in omega^{A_{n+2}}: so Delta(0) is a psi-system with Omega_n read as
  A_n and psi_n(omega^a_1 + ... + omega^a_k), a_i < Omega_{n+2}.  The
  argument of psi_n is bounded by Omega_{n+2}; in Buchholz's system
  psi_n takes arguments up to Omega_omega.  Hence the order type is at
  most about Buchholz's psi_0(Omega_2) (above Bachmann-Howard, below
  |ID_2|), NOT psi_0(Omega_omega): the heuristic of 2d is wrong.
  Lesson: as for theta (Pi^1_1-CA0 is reached by iterating theta on
  dilators built from theta, not by one natural D), the strength of
  "forall P, Theta_P is a dilator" cannot be read off one combinator
  instance; a single instance only gives a lower bound, and the
  threshold psi_0(Omega_omega) of Pi^1_1-CA0 needs P that use the type-2
  collapse itself.  The embedding test of Buchholz terms into a single
  combinator instance is therefore dropped.
  Next sanity target (paper first): add theta (type-2, ThetaFun2.thetaP)
  as a combinator, P(Delta)(Y) = theta(omega^Delta(Y + -)) or similar,
  and show that the resulting instances are cofinal in psi_0(Omega_omega)
  -- the minimal requirement for exceeding Pi^1_1-CA0.
2f. ITERATION INSTEAD OF theta (2026-11-19).  No theta combinator needed:
  iterate Delta along omega.  For an arbitrary dilator Delta put
  Delta+(Y) = Y + Delta(Y) (unit Y -> Delta+(Y), an initial segment) and
  Delta+^omega(Y) = colim_n Delta+^n(Y), a union of a chain of initial
  segments.  P_omega(Delta)(Y) = omega^{Delta+^omega(Y)} is a 2-ptyx,
  provably in ACA0 (each Delta+^n(Y) WF; union of a chain of initial
  segments of WF orders is WF; stability = direct limits).
  In Theta_{P_omega}: with B_0 = 0, B_{n+1} = Delta+(B_n), the collapses
  at level n have arguments omega^a_1 + ... with a_i in Delta+^omega(B_n),
  i.e. at ALL levels: psi_n with arguments below Omega_omega, as in
  Buchholz.  So Theta_{P_omega}(0) should have order type >=
  psi_0(Omega_omega) = |Pi^1_1-CA0|, and then
    ACA0 + "forall P, Theta_P dilator"  |-  WF(psi_0(Omega_omega)),
  i.e. the principle is strictly stronger than Pi^1_1-CA0 (it is at least
  Pi^1_1-CA0 by 2b).  OPEN step in this argument: the comparison of the
  Freund-style (non-monotone) theta-order with Buchholz's psi-order
  (cf. the known theta/psi comparisons at the Bachmann-Howard level).
  Mirror: combinator Dw = Delta^omega using Delta's own atoms (the unit
  of design (L); the official instance uses Delta+ for arbitrary Delta,
  same level structure).  Tests (8 functors incl. omega^Dw(Y), seeds 1-3)
  pass: linear, natural.

## Step 3 design (2026-11-19): generic P, before any seg code
Two obstacles found when moving from the mirror (syntactic P) to an
arbitrary 2-ptyx P; both have a proposed resolution.
3a. Coefficient sets.  The mirror's K walks P's syntax.  Generic
  replacement: compare SUPPORT TRACE POINTS in the canonical linear order
  of trace points Pt2 (LabTree2: (c,t) ordered by its image in Delta(omega),
  then c) -- already in the library, and well-founded when Delta is a
  dilator.  Collapse condition: Delta-support trace points of sigma
  <_{Pt2} the trace point of th(sigma); A-support < th(sigma) as before.
  Needs P to come with EXPLICIT support functions
  supp^Delta : P(E)(A) -> List (Pt2 E) (the covering theorem only gives a
  truncated Ex, which cannot feed a comparison).  Cf. AFW Def. 3.1:
  supports as data of a predilator.  The mirror must be re-run with this
  K (does the 2f strength argument survive?).
3b. Comparison of sigma, tau in P(Delta)(A) needs P applied to a LAWFUL
  dilator containing both supports; a code amalgamated from comparison
  data has no proofs (unlike theta, where merging finite LOs is a number).
  Resolution: height-stratified semantic construction instead of a raw
  term type: Delta_0 = Id (atoms only), Delta_{h+1} = Step(Delta_h) with
  Step(E)(A) = A + { th sigma : sigma in P(E)(A) } ordered by Freund's
  rule (P(E)(A).cmp, 3a for K), together with embeddings
  Delta_h -> Delta_{h+1}; Theta_P = colim_h Delta_h.  Proof obligations
  per step: Step(E) is a lawful pre-dilator (linearity = the theta
  argument, but at the semantic level), Step monotone, embeddings.
  AFW (arXiv 2412.13051) checked: J is defined by recursion ON dilators
  (types 0,1,omega,Omega), not by a collapse, so it does not answer 3a.
3c. RESOLUTION (2026-11-19, after reading StabJt/StabSum): both problems
  disappear with RAW TERMS in Girard normal form, as for theta.
  Theta_P(A) = A (atoms, low) + th(K, c, z, ys, ts) with
    K : C2.Fin (a code over LOCEF), z in (P(Decode K))(ord c),
    ys : c increasing elements of A (the A-support),
    ts : K.m TRACE TERMS, ts_i a term over ord (K.gen i) = the image of the
         i-th generator of K (the Delta-support, explicit: no support
         functions on P needed -- this answers 3a).
  Trace terms TmN = the same grammar with atoms in N; th is the only
  recursion, and ts are closed traces, so relabelling (along words) only
  touches atoms and ys (shallow).
  Comparison th s vs th t (Freund, with 3a's Pt2 rule): lt if tr(th s) <=
  some ts'_j (trace order = cmpN, then arity); gt if some ts_i >= tr(th t);
  else compare s, t in P(Delta)(A): choose the entry (p,(tb,ok),(u,v)) of
  the joint-type list JL[LOCEF,K,K'] (Diers's finite multicoproduct:
  restriction K'r p, valid table tb, SumCode cd, lawful u, v from homL)
  that matches the data -- generator images under u, v agree with ts, ts'
  (relabelled), table entries = recursive comparisons of relabelled
  generator images at the joint types -- and compare
  (P(Decode cd)).arr(word) ((Pm u) z) with the same for z' after merging
  ys, ys' into words (as ThetaTerm.mW).  No match: escape (eq), as cmpAt.
  All checks are finite and decidable (FL.DecAll, decO3, words); the
  recursion is on the first term with an inner recursion on the second
  (relabelling-parametric), as in ThetaTerm.R/cmpIn.  This answers 3b:
  the amalgam is SELECTED from a finite list of lawful cospans instead of
  being built from comparison data; no height stratification needed.
  P interface: PG : DL -> DL, Pm : O.Mor D D' -> O.Mor (PG D) (PG D')
  (laws later).
First seg file: ThetaP3Term.seg (interface, TmN, relabelling, JL entry
selection, cmp).

## Step 3 progress (2026-11-19)
ThetaP3Term.seg (in All.seg; check.py exit 0, All.seg 26,419 decls):
Th3[PG,Pm]: data Tm (at / th K c z ys ts / nl / cs), rn (shallow
relabelling), trT, Sel[K,ts,rts,K',ts'] (okU: u canonical on K's
generators; okV: v canonical on selected generators, else agreement of
relabelled images; okT: table entries = recursive comparisons at the
joint types; via: TT.Th[PG cd].cmpAt after Pm u, Pm v and mN ys ys';
selC/cmpP: first matching entry of SJ.JL[F3,K,K'].e1L, else eq), Freund
clauses with Pt2-style trace comparisons (anyLeI, anyGeI), cmpIn, R, cmp.
Tests (#conv): constant 2-ptyx idD with the empty code (lt/gt/eq, atoms
low) and P = identity with the one-generator code Gen1[idD] (K1.m, gen,
atom < collapse).  Comparisons of two K1-collapses exceed the checker's
10 s budget (JL[K1,K1] enumerates tables and homs by normalisation): not
evaluated.  Possible remedy if needed: a cheaper direct selection
(compute p and the table from the terms, then look up the entry) instead
of filtering the whole list.
Next: step 4 (laws: NF/normality, equality of normal terms, linearity by
height, as ThetaLO*), then terms over an arbitrary LO A and functoriality.

## Towsner (2026-11-19): ~/CANONICITY/towsner2.pdf, towsner3.pdf
- "Proofs that modify proofs 1/2" (arXiv 2506.16491): mu-calculus up to
  ~parameter-free Pi^1_2-CA; ordinal BOUNDS WITH FREE VARIABLES for
  functions on proofs that must preserve well-foundedness (= dilators,
  substitution lemma 4.18 = functoriality); FUNCTION-SORT variables for
  nested inductive definitions (= type-2 ptykes).  Collapses sit BELOW
  variables (theta alpha < v < Omega): design (H), not our (L).
- "Polymorphic ordinal notations" (arXiv 2504.02131, draft): polymorphic
  Omega with de Bruijn levels Omega^(J) (footnote 5: related to the
  dilator view of BH, citing Girard and Freund); WF "from below" via
  Acc_n built level by level with Pi^1_1-CA at each level (template for
  step 6).  Sec. 4 "Functions as cardinals": Xi of function sort, Xi^(J)(a);
  K of theta alpha may contain FUNCTIONS (terms with a variable, e.g.
  theta v), and the order instantiates them at the PARAMETERS of the other
  term:  theta a < theta b if a < b and gamma[v := b'] < theta b for every
  parameter b' of b and gamma in K a  ("theta b closed under gamma").
  This is our 3a problem (supports = trace points = functions) with a
  different, principled rule; our Pt2 rule instantiates at the bottom of
  omega instead.  Sec. 5: OT_{omega+Xi+omega}, a bit below parameter-free
  Pi^1_2-CA0.
- Consequences: (i) reconsider design (L) -> (H) and the 3a rule ->
  Towsner's parameter instantiation BEFORE step 4; (ii) test: is OT_Xi
  (or a fragment) Theta_P(0) for a specific combinator P?  That would give
  an independent strength calibration; (iii) Towsner's systems are
  specific notations below Pi^1_2-CA0; Theta for ALL 2-ptykes is the
  uniform (Girard (*)) version.

## Rework after Towsner (2026-11-19)
Mirror (mirror/theta3t.py, theta3tl.py; tests test_theta3t*.py, findbad.py):
- Towsner's parameter rule, made parameter-free by his own remark: theta b
  is CLOSED under a support function gamma (a trace term) iff
  gamma[vars := b^-] < b, the variables becoming points "just below b"
  (above everything below b).  Rule: th s < th t if th s is not closed
  under some support function of t; symmetrically gt; else compare in P.
  Symbolic points sy i b: compared semantically (sy < c iff b <= c) only
  with terms not mentioning points just below b; otherwise as atoms.
- Design (H) (atoms cardinal-like: y < th s iff y <= some A-argument of s)
  is INCONSISTENT with the closure rule: P = omega^Delta(Y), base 2,
  a = th(w^th(w^y0)), b = th(w^y1): a < y1 < b by (H), b < a since b is
  not closed under x |-> th(w^x), a support function of a.  Towsner avoids
  this because his variables are incomparable with collapses (his order on
  open terms is partial); a dilator needs a total natural order.
- Closure rule + atoms LOW (L): antisymmetry, transitivity, naturality pass
  for all 8 functors, seeds 1-4 (findbad: no violation).
Seg: ThetaP3Term.seg rewritten: Tm gains sy i b; ys is a term list; rn,
inst (variables -> sy i b), hasSym (shallow), notClosed, step (one level,
given the comparison one level down), cmpF by recursion on FUEL
(the closure test is not a subterm call), fuel = (1+|s|+|t|)^2, out of
fuel: eq.  Sel now takes the comparison cf as a parameter.  Tests (#conv)
as before pass; All.seg 26,428, check.py exit 0.
OPEN: fuel sufficiency (a measure that decreases: |s|+|t| with |sy i b|
counted as 1 fails in the sym-vs-collapse case, which compares the bound
b); the laws (step 4) must be stated for cmpF at sufficient fuel.

## Step 2 of the plan (WF of Theta_P, informal) -- OBSTRUCTION (2026-11-19)
Natural proof shape (type 2 analogue of Freund's accessible part W):
W := the subfunctor of GOOD trace points, gamma good iff for every
well-founded C and every instantiation of its variables in C the instance
is accessible in Theta_P(C); show W is a dilator, then P(W) is WF (P a
2-ptyx), then induction on P(W) as in ThetaWF.  "good" quantifies over
ALL well-orders: Pi^1_2-comprehension, as expected for Pi^1_2-CA0.
In the type theory: good : (trace point) -> U (l+1) (quantifies over LO
in U l), so W is not an object of Stab(LO) at level l: SIZE, i.e.
impredicativity.  This is not an accident: the seg type theory (universes,
inductive types incl. Acc; no resizing) is predicative, of strength
around Martin-Lof type theory with W-types and universes (KPi-like),
far below Pi^1_2-CA0.  If the conjecture holds, the theorem
"forall 2-ptyx P, Theta_P is a dilator" (classically implying
Pi^1_2-CA0 over ACA0) is NOT provable in it.  (For theta at type 2,
Pi^1_1-CA0 is below the type theory, consistent with ThetaWF.)
Options: (a) prove it from an explicit impredicative hypothesis (resizing
for the predicate good, or an axiom of induction on dilators) -- a
relative result; (b) prove Theta_P a dilator for specific P (as for
eps_X), which needs only the strength of that instance; (c) keep the
type-3 work at the level of definitions + laws (steps 3-5), leaving
step 6 as the conjecture.

## A statement beyond the type theory implying Pi^1_2-CA0 (2026-11-19)
User goal: a statement not provable in the type theory which implies
Pi^1_2-CA0.  Route: Girard's completeness one type up (not Theta).
DONE: NSumLO.seg (lexicographic N-sum of LOs, shifted recursion, WF);
LabTree3.seg (C3 = Stab(Stab(LO)); trace points (n, y in F(Decode code_n))
for a fixed code sequence with fd: each Decode code_n a dilator; empty
code K3, covering over dilLO, pointwise pull-backs; Tree: type-3
pre-ptyx, ptyx-wf/wf-ptyx); Girard3.seg (Agree2: Girard2 depends on its
matrix only through short words; Girard3[T4,dec,e,code,fd,e3]: Gp :
SF[C3]; ptyx-wf/wf-ptyx; ptyx-not3: F_f a 2-ptyx => Gp not a type-3
ptyx).  All.seg 26,650, check.py exit 0.
Classically: Gp type-3 ptyx => forall f, F_f not a 2-ptyx => S (Pi^1_4);
with S the axiom of Pi^1_2-CA0, Gp ptyx => Pi^1_2-CA0, hence unprovable
in the (predicative) type theory (Goedel; metatheorem).
Not formalised: the classical steps; coding the specific S.
fd DISCHARGED (2026-11-19) for MONOTONE codes (every code is false:
X^op): AlmostFull.seg (Coquand's direct proof of the intuitionistic Ramsey
theorem: trees, secures, p (x)_n q, Theorem 0.1 ram, afInter; afPull;
AFLe: <= on a WF linear order is almost full; AFWf: almost full and
contained in <= => WF); FinDilWF.seg (FD[K].Mono, monoDil : monotone code
=> dilator; Girard3M: Girard3 over monotone codes, fd derived).
All.seg 26,824, check.py exit 0.  Open: decidability of Mono (for an
enumeration of all monotone codes), a concrete monotone instance.

## Status
(2026-11-19) step 1 done; step 2 on paper: target (b) fixed as "BH
collapse of 2-ptykes"; first candidate shown too weak (2a); reduction to
theta (2b); open design issue = support comparison (2c).  Mirror of design (L)
built: linear + natural on random tests (2d).  Strength NOT checked; the single
instance omega^Delta(Delta(Y)) is only ~psi_0(Omega_2) (2e, heuristic of
2d withdrawn).  2f: iterating Delta along omega
gives psi_n with arguments up to Omega_omega, so design (L) should exceed
Pi^1_1-CA0 (open: theta/psi order comparison).  Minimal sanity passed
modulo that comparison.  Next: step 3 (terms + decidable order in seg,
generic P via codes) or the theta/psi comparison on paper.
(2026-11-19) step 3 design 3c (raw terms, amalgam selected from SJ.JL);
ThetaP3Term.seg: terms + decidable comparison, checked.  Next: step 4.
(2026-11-19) Reworked after Towsner: closure rule, atoms low; (H) refuted
for a total order; seg rewritten with fuel.
