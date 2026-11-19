# Freund's Bachmann-Howard collapse D |-> theta D as a type-2 ptyx

Goal (user, 2026-11-19): a type-2 pre-ptyx on Stab(LO) (LOWF.C2), proved to be
a ptyx (LOWF.IsPtyx) constructively.  Classically "theta D is a well-order
for every dilator D" is equivalent to Pi^1_1-CA0 (Freund).  Chosen over
Girard's Lambda (PLAN-LAMBDA.md in ~/CANONICITY/unit/dilators).

## Terms (D : SF.SF[LC.ce] any pre-dilator)
data Tm = th (n : N) (z : D([n])) (as : Tm) | nl | cs (t : Tm) (r : Tm)
th n z a = theta(sigma), sigma in D(theta D) given by its support list a
(n args, strictly increasing) and z in D([n]); nl/cs encode lists.
Normal: args sorted, |a| = n, args normal, z NORMAL in D: every map
j : A -> [n] whose D-image contains z is surjective (a proposition; kept by
morphisms of C2 since they are cartesian).

## Order (Freund): s = th n z a, t = th m z' b
  s < t  iff  s <= some b_j, or (no a_i >= t and sigma < tau);
decided as: if some cmp s b_j in {lt,eq} then lt; else if some cmp a_i t
in {gt,eq} then gt; else cmpAt: merge a and b (words u, u', using cmp
a_i b_j), compare D(u) z and D(u') z' in D([len u]).
Definition: R : Tm -> (Tm -> O3 * List O3) * List (Tm -> O3) by recursion
on s (the list of element comparisons cmp a_i .); inner recursion cmpIn on
t returning (cmp s t, list of cmp s b_j).  cmpAt decides ones u = n etc.
with decN (proof-irrelevant by HN.uip).

## Linear order (the hard part)
Induction: outer on max size k (gives an LO LO_k of normal terms of size
<= k, whose laws are the IH); D-parts of terms whose args lie in LO_k are
compared in D.G LO_k (semantic lemma: merge-based cmpAt = D(LO_k).cmp of
the images) -- laws for free; inner induction on the sum of sizes for the
mixed comparisons s vs b_j.  Equality: normality + stability (pull-back)
gives equal supports.

## Functor on C2, supports, pull-backs
Points of terms are trace points (n, z) in Pt2 D (LabTree2); S : D -> D'
acts by z |-> S_n z (Nat: order preserved; Cart: normality preserved).
Supports: LabTreeG[C2,Pt2,...] dummy instance suppL (cover theorem);
pull-backs: LabTree2.Pbp.

## Well-foundedness (IsDil D => WF (theta D))
W = accessible part of theta D (Sigma-type, an LO, WF by construction);
D(W) WF.  For sigma with args in W, its image y in D(W); Acc-induction on
y, inner structural induction on the predecessor's args: theta tau < theta
sigma is either <= some a_i (in W) or tau < sigma with args < theta sigma
(accessible by the inner induction, so in W, and the image of tau is below
y by the semantic lemma).

## Files (planned)
ThetaTerm.seg (terms, cmp), ThetaLO.seg (laws), ThetaFun.seg (C2 functor),
ThetaWF.seg (ptyx).

## Status
(2026-11-19) design written.
T1 DONE: ThetaTerm.seg (Th[D]: Tm, mW merge words mirroring LinOrd.merge,
cmpAt with decN decisions, cmpIn/R, cmp, unfolding cmpTh).
T2a DONE: ThetaLO.seg (ThL[D]): isTh/isList/lenT/srt/nfB, NZ (normality:
any other finite-stage support of an image covers it), NF = nfB * nfZ;
merge-word lemmas on1/on2/lnW, all-equal merge pwW; cAeval (cmpAt =
cmpAtP when the words fit, uip); leNZ (NZ => ones of u are ones of u');
ceq: cmp s t = eq => s = t for normal theta terms (ceqM, Main: wext on
the words, listOf for the arguments, zEq/thEq transports).
T2b DONE: ThetaLO2.seg (L2[D]: hgt, Good k, laws Lk k = TrK*FlK*RfK,
normal forms are props (nzProp via funext), LO k; SemK: liftL, srtLift,
mWL (mW = LinOrd.merge words), nthC/nthS, mapOf, Img (image of a term in
D(LO k)), SemL.result (semantic lemma)); ThetaLO3.seg (L3[D]: Any lemmas,
Step[k,lk]: Core (Freund's transitivity cases), nested structural
induction MS/MT/MR -> trK; FCore (consistency + flip), FS/FT -> flK; rfS;
lkS; lk0, lkAll; ThetaOrd[D].lo : DP.LO -- theta D is a decidable linear
order for EVERY pre-dilator D).  Planted errors caught.
T3a DONE: ThetaFun.seg TF[D,D',S]: rn (rename trace points by S_n),
elemsRn, cAinv (Nat), mWinv, rnCmp (nested induction), srtRn, nfBRn, NzS
(Cart carries normality), nfZRn, arr : Map (ThetaOrd[D].lo) (ThetaOrd[D'].lo).
(Note: stp0/lenF0/P20 moved to top level of ThetaTerm so that Th[D] and
Th[D'] share them.)
T4 DONE: ThetaWF.seg: AccProp (Acc is a prop, J + funext); SQ[D].LOQ
(sub-order cut out by a prop Q) and SemQ (semantic lemma, copy of SemK
with the height bound replaced by Q); WFD[D,d] (d : IsDil D): Q = accessible,
X = accessible part, wfDX = d X wfX, claim by induction on D(X) with inner
structural induction (Step/CoreI), wfTheta : LW.WF (ThetaOrd[D].lo).
THE MATHEMATICAL CONTENT IS DONE: forall dilators D, theta D well-founded.
T3b DONE: ThetaFun2.seg: ThLaws/ThLawsC (functor laws), ThBack
(normality backwards along morphisms, via naturality), LGT (LabTreeG over
C2 with trace points, dummy tree) for supports, ThCont (pts, Rl: preimage
terms, Wit), ThStab (zip through LabTree2.Pbp, zpP1, Res), and
  thetaP : SF.SF[LOWF.C2]      (theta as a type-2 pre-ptyx)
  thetaP-ptyx : LOWF.IsPtyx thetaP   (= WFD.wfTheta).
All.seg 26,337 declarations, check.py exit 0 (17.1 s).  ~2000 lines.
Classically: "theta D well-founded for every dilator D" is equivalent to
Pi^1_1-CA0 over ATR0 (Freund); the reversal is not formalised.
