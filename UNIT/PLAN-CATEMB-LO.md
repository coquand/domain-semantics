# catemb.pdf in the linear-order case: dilators and ptykes (plan, 18 Nov 2026)

User directive: formalise catemb.pdf (categories of embeddings, closure under
stable exponentiation), in the special case needed for ptykes:

    LO  (linear orders, strictly increasing maps; finite objects = [n])
    Dil (dilators = stable continuous functors LO -> LO, cartesian nat. transf.)
    Ptyx2 = stable continuous functors Dil -> LO (user choice: target LO).

catemb's theorem used twice: Dil is again a category of embeddings, so
functors on it make sense and are determined by their finite part.
NOT the goal: D_inf / domain equations (Coherence* files are only the
poset shadow).

## Existing material

- `Dilator.seg` (= ~/CANONICITY/unit/dilators/dilator.seg): finite-valued
  pre-dilators on finite ordinals, maps = words over {o,i}; `PreDil`
  (Sup: least support, Den/fwd/bwd: normal form, trace), `PDS` bundled,
  `Nat` (natural transformations t : N -> Wd; trT: traces to traces,
  denT), `NatEq` (determined by the trace), `Restr` (sub-pre-dilator from a
  Bool subset of the trace).
- `DilatorSub.seg`, `DilatorSubCDI.seg`, `DilatorMorphisms.seg`:
  Sub(D) ~ Omega^(Tr D) (a CDI), morphisms act by rigid e-p pairs.

## Status

- Step 1 DONE (18 Nov 2026): `CatDil.seg` — `Dil`, `Mor`, `mor-ext`, `idM`,
  `compM` (with `comp-assoc` of words), `id-left`, `id-right`, `assoc`;
  `Cart[D,E,T,w,x,hx]`: `supp-eq` (T preserves least supports) and
  `reflect` (naturality squares are pull-backs: T x in Im E(w) => x in
  Im D(w)); `Up` (a point is in Im D(u) for every u above its support).
  Trace map injective and determination by the trace already exist
  (DilatorMorphisms.tau-inj, Dilator.NatEq).  check.py exit 0, All.seg
  18,978.
- Step 2 DONE (18 Nov 2026): `DilFinite.seg` — `On[D].Sub[c]` (subdilator
  D|c of a Bool trace subset, `dil`, `inc : Mor`, `member`: x in D|c iff
  its trace component is in c, `trace-in`), `Trunc[K]` (D|K, `bounded`:
  trace levels <= K, `covers`), `union` (every point of D(n) is in D|n),
  `directed` (D|K in D|K' for K <= K'), `inter` (intersection = meet of
  subsets); `Bounded`, `FinDil`, `finite D K`.  All.seg 19,006.
- Step 4 (definition) DONE (18 Nov 2026), after discussion with the user:
  NO least supports constructively (as for nominal sets / Eilenberg-Zilber
  without decidable degeneracies); what matters is that supports are
  closed under finite intersection.  `DilPtyx.seg`: `LO` (decidable
  comparison), `Map` (strictly increasing, `map-inj`), `Up` (inclusion
  D|c -> D|c' for c <= c', `tri`), `record Ptyx` {F, arr, arr-id,
  arr-comp, support (mere finite truncation support), meet (supports
  closed under intersection)}, `Supports[P,D]`: `mono`, `inter`, `exists`,
  `unique` (the supports of y form a filter).  `DilPtyxEval.seg`:
  `Eval[n].ptyx`, the ptyx D |-> D(n).  All.seg 19,106.
- Step 5 (part) DONE (18 Nov 2026): `PtyxMor.seg` — morphisms of
  ptykes `Mor P Q` = natural family of LO maps that is CARTESIAN (if
  a D y is supported by D|c, so is y); `preserve` (converse, by
  naturality), `idP`, `compP`, `MorEq` + `id-left/id-right/assoc` (refl);
  `act`/`act-id`/`act-comp`/`actMap` (D(w) as LO map); `EvalMor[w]` :
  Eval[ones w] -> Eval[len w] (finite ordinals act on evaluation ptykes;
  cartesian by Restr.Inv: D(w) preserves traces).  `PtyxTwice.seg` —
  `Twice[n].ptyx` : D |-> D(D(n)), arr T = E(T n) . T(D n); x supported
  by D|c iff x in Im(D(chi n) . chi(F n)) = Im D(chi n) /\ D|c(D n)
  (Restr.pb), i.e. least support of x inside D|c(n) and trace in c;
  stability and continuity (level D(n)+n).  First non-evaluation ptyx:
  the definition of Ptyx is confirmed on it.  All.seg 19,262, check.py
  exit 0.
  `PtyxDen.seg` (18 Nov 2026) — `Den[X].ptyx` : D |-> D(X) for any
  decidable LO X (values = denotation orders, infinite in general),
  `ptyxOmega` = D(omega).  T acts on the trace part (a,z) |-> (a,T(|a|)z)
  (Nat.trT); order preserved by naturality along the merge words;
  (a,z) supported by D|c iff c |a| z (via `SuppEq`, CatDil.Cart at any
  level); stability = conjunction, continuity at level |a|.  All.seg
  19,347, check.py exit 0.
  `PtyxFinite.seg` (18 Nov 2026) — a ptyx is determined by its finite
  part, with NO least supports and NO decidability of supports (user:
  decidable supports = decidable degeneracies, rejected):
  `lo-set`/`o3-set` (Hedberg: values are sets, equations are props);
  `Det`/`det` (natural families agreeing on all D|K agree everywhere:
  mere support + naturality); `Factor` (morphism with image in E|c
  factors through E|c), `TruncFactor` (D|K -> D -> E factors through
  E|K: supports preserved, D|K bounded); `Ext` (a natural family on
  FinDil extends to all dilators by UNIQUE CHOICE: value = Q(inc)(a z)
  for any z over y, independent of the witness by pushing to level
  K+K' and injectivity; strictly increasing, natural, `ext-eq`,
  `unique`); `supp-prop` (a support is a proposition), `FinCart`
  (naturality squares on finite dilators are pull-backs) and `ExtMor`
  (then the extension is a ptyx morphism, cartesian); `Iso.retract`
  (ptykes iso on finite dilators are iso).  All.seg 19,551, check.py
  exit 0.
  `DilImage.seg` + `PtyxPull.seg` (18 Nov 2026) — the converse of
  ExtMor.  `DilImage`: `Lift` (M : G -> E with Im M(n) <= Im T(n)
  factors through T : A -> E; Factor is the case T = inclusion), `mono`
  (morphisms are monos), `Image[A,B,T]`: c k z = at (T k) z, Im T(n) =
  B|c(n) (`le-fwd` by CatDil least-support preservation via
  PtyxDen.SuppEq, `le-bwd` by naturality along the least support), so
  T = inc . iso with `iso`/`inv` inverse (`iso-inv`, `inv-iso`): Dil is
  a category of embeddings, every morphism is iso to a subdilator
  inclusion.  `PtyxPull`: `pull` (naturality squares of a ptyx morphism
  along ANY dilator morphism are pull-backs), `fin-cart` (restriction to
  FinDil satisfies FinCart), `Corr.back` (ExtMor of the restriction is
  the morphism again).  So Mor P Q ~ natural FinCart families on FinDil.
  All.seg 19,679, check.py exit 0.
  Object version, route (a) (user choice, 18 Nov 2026): germs.
  `PtyxGerm.seg`: `FinPtyx` (functor FinDil -> LO + intersection axiom
  for subsets of the trace of a finite dilator), `subFin`; `Germ[FP,D]`:
  germs (K, z in FP(D|K)), comparison at a common level (`cmpAt-indep`),
  quotient Car = (p : Germ -> Bool) * Ex (cls g = p) (a set by funext
  only), LO structure by unique choice, `iota`, `surj`.
  `PtyxGermArr.seg`: action of T : D -> E via T_K : D|K -> E|K
  (`Sq`: commutes with the pushes, by DilImage.mono), `ArrId`, `ArrComp`.
  `PtyxGermPtyx.seg`: `TraceMap` (T sends the trace point (k,a) of b to
  (k, T(k) a); subsets pull back by `pre T c` -- subsets of the trace
  of D are not subsets of the trace of D|L as they stand), `SubIm`,
  `LeSub`, `FullIso` (K-bounded A ~ A|K), `Support`, `MeetW`/`meetH`
  (push to a common level L, finite meet in D|L for the pulled-back
  subsets, Lift to (D|(c^c'))|L), `hat FP : Ptyx`.
  `PtyxGermFin.seg`: `Fin` (on finite A, hat FP (A) ~ FP(A): `from`,
  `to`, inverse, strictly increasing), `FinNat`, `restrict P`,
  `iso-fincart`, `Recover[P]`: mutually inverse ptyx morphisms
  P <-> hat (restrict P) (`left`, `right`).  So ptykes = finite ptykes,
  on objects (here) and on morphisms (PtyxPull.Corr).  All.seg 20,126,
  check.py exit 0.
  Ptyx as a category of embeddings (18 Nov 2026): `PtyxSub.seg` —
  `mono`; subptyx = predicate S (propositional, preserved and reflected
  by every P(T)), `SubPtyx` (ptyx + cartesian `inc`, `lift`/`drop` of
  supports), `Image` of a morphism (reflection = PtyxPull.pull; `m` :
  Q ~ im with inverse `minv`, `tri`), `Inter`, `Union`.  `PtyxGen.seg` —
  `pb` (ptykes preserve pull-backs: P(T) y supported by D|c => y
  supported by A|pre T c; via DilImage + meet + Lift), `Gen[P,A,y]`
  (points with a common origin with y; reflected by pb; `self`,
  `least`: the least subptyx containing y), `cover` (every point is in
  Gen of a point over a truncation).  So finitely generated subptykes
  (finite unions of Gen over finite dilators, PtyxSub.Union) form a
  directed family covering P.  All.seg 20,298, check.py exit 0.
  Directed colimits (18 Nov 2026): `LOColim.seg` — the germ quotient
  abstracted: `Colim[Fo,up,up-id,up-comp]` (colimit of an N-indexed
  directed system of LOs; `cl-push`, `eq-at`, `ind`/`ind2`, `Desc`:
  descent of invariant maps into sets by unique choice), `Ind` (map of
  colimits induced by a map of systems).  `PtyxColim.seg` — `Sys[P,e,..]`:
  directed system of ptykes P i, e i j (i <= j) coherent; `colim : Ptyx`
  computed pointwise (support from P_i, meet in P_L at a common level);
  `iota i` cartesian, `iota-e`; `Univ`: every cocone of ptyx morphisms
  factors uniquely (`mor`, `fac`, `uniq`).  So Ptyx has directed
  colimits of N-chains, with the finitely generated subptykes
  (PtyxGen) as the finite objects: catemb's structure one level up.
  (PtyxGerm could now be re-expressed through LOColim; not done.)
  All.seg 20,500, check.py exit 0.
  NEXT (open): the next type level (functors Ptyx -> LO, using that Ptyx
  is again a category of embeddings); is EvalMor full (side question) (every Eval m -> Eval n is a w)?
  (Superseded idea:) finite enumeration of the trace of a finite
  dilator (levels <= K, t < D0 m, decidable trace test), so subobjects of a
  finite dilator = Bool vectors over it; then pre-ptyx F0 : FinDil -> N,
  F1 on Mor (words), functor laws, preserves intersections; least support
  of y in F(D) = intersection of all supporting subsets (finite, decidable
  via `at`), exactly as Dilator.PreDil.Sup does with words.

## Steps

1. `CatDil.seg`: Dil as a category: Mor D E (bundled Nat data), identity,
   composition (needs compW associativity), laws; morphisms are
   CARTESIAN (supports preserved: supp(T x) = supp x, so x in Im D(w) iff
   T x in Im E(w)); a morphism is determined by its trace map tau
   (NatEq), tau injective (DilatorMorphisms).
2. Finite dilators: finite trace (bounded level + Bool trace test).
   Subdilators = Restr; every D is the directed union of its finite
   subdilators (Restr to levels <= N); intersections (pullbacks) of
   subdilators.  => Dil is a category of embeddings (catemb Def.) with
   finite objects the finite dilators.
3. Finite dilators as finite combinatorial data (trace + comparison
   order of denotations, Girard 8.3), with decidable iso: the analogue of
   words for O.  Needed to quantify over finite objects.
4. Ptyx2: F0 on finite dilators (into N, finite-valued first, like
   dilator.seg), F1 on morphisms of finite dilators, functor laws,
   preserves pullbacks.  Normal form: least support (a finite
   subdilator) of each point; trace of a ptyx; ptyx determined by trace.
5. Examples: F(D) = D(n), F(D) = D(D(1)); morphisms of ptykes
   (cartesian nat. transf.); Ptyx2 is a category of embeddings (catemb
   main theorem one level up).

## Side track (18 Nov 2026): Towsner's bounds and Pi^1_2 axioms

Towsner, "Proofs that modify proofs" (arXiv 2403.17922v1), sec. 5: sorts
Ord, products, theta -> Ord; order f < g = eventual strict domination
(Def 5.1); explicit bounds (Lem 5.7-5.10, Thm 5.11): beta, max{Omega}+k,
k, omega, evaluations Omega(...), finite sums, beta1 + beta2,
beta1 # beta2 (natural sum), omega^beta, composition (Thm 5.12); collapse
(Thm 5.14) by a sup over all d' with a given bound.
Check against dilators (pen and paper, not formalised):
- dilators: identity, constants, ordered sum X+Y (binary), omega^X,
  composition, evaluation (= PtyxDen.Den / DilPtyxEval at level 2).
- NOT dilators: max(X,Y) (D(1,1)=1 < D(1,0)+D(0,1): no pull-backs);
  natural sum X#Y: a binary predilator with D(m,n)=m+n has trace
  {(1,0),(0,1)}, so it is X+Y or Y+X, but 1#omega = omega#1 = omega+1.
  # is used because the comparison needs STRICT monotonicity in each
  tag; X+Y is not strictly monotone in X.  Possible repair (unchecked):
  (X+Y)+(Y+X) is a binary dilator strictly increasing in both.
- comparison: eventual strict domination is neither implied by nor
  implies the existence of a morphism (Id -> 1+Id exists, not strict).
- collapse (Thm 5.14): defined by a sup over a class, no finite data:
  functoriality cannot be checked; this is where Girard's ptyx-level
  collapse would be needed.
- OUR gap: Dil = finite-valued one-argument pre-dilators (dilator.seg).
  omega, omega^X, omega + X (D(n) infinite) and binary bounds are
  outside it; 2^X (Dilator.ExpDil) is the finite-valued substitute.
`DilWO.seg`: WF (Acc), WFPres D (= Dilator.IsDil over DilPtyx.LO / Den),
pol-wfpres (proved for Id,1,+,.,2^D), two-wfpres (X wo => 2^X wo, a
theorem), BH[D,X].Collapse (Freund, supports = the list a of the
denotation), BHP (stated, not assumed).  All.seg 20,520, check.py exit 0.
Open: does BHP restricted to finite-valued one-argument predilators with
Acc keep Pi^1_1-CA0 strength? (Freund's class allows infinite D(n).)

## Base level beyond finite values: routes (a) AND (b) (user, 18 Nov 2026)

Problem found: CatDil.Dil is finite-valued, one argument; omega, omega+X,
omega^X are missing, and Dil is NOT closed under directed colimits (the
chain k+X has colimit omega+X), so Dil alone is not a catemb category of
embeddings (subobjects/images/finite objects yes, colimits no).
- (b) DONE: `PDil.seg` — record PDil (Freund-style predilator on finite
  ordinals: F n any decidable LO, mp w with side proofs, supp, nf with
  F(supp) nf = x, supp-nat); `On`: mp-irr, mp-wd, supp-least, Hit (the
  support condition = pull-backs); `FinPD D`: every CatDil.Dil is a PDil
  (least supports of PreDil.Sup, naturality via Restr.Inv).
- (a) DONE (one direction): `PDilChain.seg` — Chain[Dc,e,e-id,e-comp]:
  a directed system of finite-valued dilators gives a PDil by LOColim
  at each level; supports descend (morphisms preserve least supports,
  PtyxDen.SuppEq); normal forms by unique choice (F(w) injective).
  All.seg 20,644, check.py exit 0.
- DONE (1) `OmegaPlus.seg`: KP k (= k + X), embeddings E a b via the
  word front a b ++ id, coherent; omegaPlus = colimit; `omega` : N maps
  strictly increasingly into F(0) (infinite values).
- DONE (2) `PDilMor.seg`: Mor of PDil (natural + support preserving),
  idP/compP/laws, finMor (CatDil morphisms), Cocone[..]: iota, iota-e,
  Univ (mor, fac, uniq): the chain colimit is a colimit in PDil (for
  cocones out of the finite stages).
- DONE (4) `PDen.seg`: PDen[D,X] denotations of a PDil at a decidable LO
  (merge, independence, linear order, equality via supports), WFPresP,
  BHP collapse and BHPP over PDil (Freund's class).  Not proved: PDen of
  FinPD D agrees with PtyxDen.Den (expected: order iso).
  All.seg 20,803, check.py exit 0.
- TODO: (3) (b) -> (a): a PDil with enumerated values is
  the colimit of its finite-trace subdilators; (5) ptykes over PDil
  (extension from finite dilators by germs).

## Girard, PTLC ch. 12 (ptykes of type 2) — ~/COLL/GIRARD/ptlc2.pdf (18 Nov 2026)

Match: 12.1.1 ~ DilPtyx.Ptyx; 12.1.3 ~ PtyxFinite.det; 12.1.4 normal form
~ Supports filter (no least supports); 12.1.14 ~ PtyxColim; 12.1.11(iii)
~ PtyxGen.Gen; 12.1.29 ~ PtyxGen.cover; 12.1.34 ~ PtyxGerm.hat.
FINDING: Girard's preptyx (12.1.30) also requires (iii) preservation of the
ordering of morphisms; for well-ordered values it is 12.1.25 (via 12.1.23,
which needs an infinite-valued D'' and W inflationary on a well-order);
not derivable for LO values.  Same gap at type 1 (PDS has no Mono).
DONE: `PtyxMono.seg` — MorLe (12.1.22), MonoAt/MonoP, MonoDil; eval-mono,
den-mono, twice-mono (at monotone E); mono-reflect (subptykes, images),
ColimMono, hat-mono (from MonoFin, via TfLe), restrict-mono.
`PtyxSum.seg` — SumLO, SumMap, Sum[P,Q] (12.1.21: support/meet
componentwise), injections inL/inR (cartesian), SumMor, Sum.mono.
`PtyxShift.seg` — sumDil, idPlus (functorial), Through (Lift transport),
Shift[A,D] = A o (D + Id) (12.1.40's ptyx: continuity via TraceMap along
the right injection, stability via images of id + inc_c), plus-le,
shift-mono.  All.seg 21,116, check.py exit 0.
`PtyxShiftMor.seg` — plusId (T + id_E), plus-comm, imgSupp, ShiftMor:
A(T + id) : A o (D+Id) -> A o (D'+Id) is a ptyx morphism (12.1.40 (ii);
cartesian via PtyxGen.pb); InTr / Tr (12.1.9) as propositions, tr-pres,
tr-refl, trMap (12.1.10).  All.seg 21,185, check.py exit 0.
NEXT from Girard: connected decomposition/kinds (12.1.38-41, classical:
needs a constructive formulation); 12.1.23/25 over PDil.

## Validation of PDen and ptykes on chains (18 Nov 2026)
`PDenFin.seg`: for finite-valued D, PDen[FinPD D, X] and PtyxDen.Den[X] D
are the same data rearranged with the SAME comparison (refl): Iso, and
fin-wfpres / pol-wfpresP (WFPresP for all polynomial dilators, from polDil).
`PtyxChain.seg`: Ext[P, chain] = colim_i P(Dc i) (a ptyx evaluated at a
chain-presented predilator); eval-ext (refl: the evaluation ptyx gives
the colimit's value); DenIso[X]: colim_i Dc i (X) -> PDen[colim, X] is
strictly increasing and onto (denotations of the colimit = colimit of
denotations: routes (a) and (b) agree at every X).  All.seg 21,275.
OPEN: WFPresP for omegaPlus (not an instance of a general theorem:
colimits of dilators along chains need not be dilators, e.g. omega*);
functoriality of Ext in chain morphisms / independence of presentation.

## Type 3: ptykes on Ptyx (18 Nov 2026)

Ptyx is a category of embeddings, so stable continuous functors on it
make sense.  SIZE: Ptyx is large; existentials over ptykes cannot be
truncated into U l (Replacement only for small domains).  So every
existential at type 3 is indexed by SMALL data: `Gens P` = finite list of
(finite dilator, point), `FG[P,g]` = finitely generated subptyx (finite
union of PtyxGen.Gen).
- `Ptyx3.seg`: map-eq, nat-prop, cart-prop, `mor-eq` (morphisms of
  ptykes equal when pointwise equal; uses funext), `Sub` (bundled
  subptyx), `SubOf`, `meetSub`, `Incl`, `Gens`/`FG`; `record Ptyx3`
  {G : Ptyx -> LO, arr, arr-id, arr-comp, support (mere finitely
  generated support), meet (any two subptykes)}; `Supports3` (mono,
  inter, exists, unique, supp-prop); `Eval3[D]` (P |-> P(D); support by
  PtyxGen.cover); `Mor3` (natural + cartesian), idP3/compP3/laws;
  `EvalMor3` (T : D -> E gives Eval3[D] -> Eval3[E], cartesian because
  subptykes are reflected), functorial (evalMor3-id/-comp).
- `Ptyx3Pull.seg`: `Inv` (image of a ptyx morphism with its inverse as a
  morphism, triangles as Id), `pull3`: squares of Mor3 are pull-backs
  along ALL ptyx morphisms.
- `Ptyx3Sub.seg`: mono3, Pred3/SProp3/Fwd3/Bwd3, `SubPtyx3` (type-3
  ptyx + cartesian inc), `Image3` (reflection = pull3; m, minv),
  `Inter3`, `Union3`.
- `Ptyx3Fin.seg`: `Det3`/`det3` (agreement on finitely generated
  subptykes => equal), `Coreg` (corestriction), `PushFG` (FG g of R ~
  FG (U g) of A over any U : R -> A: k, kinv, both composites id,
  triangles; pull-back direction by PtyxPull.pull).
- `Ptyx3Gen.seg`: `Pre` (preimage subptyx), `pb3` (type-3 ptykes
  preserve pull-backs), `Gen3[X,A,y]` with SMALL origins over FG
  subptykes of A (reflection: pb3 to the pull-back Pb, finite support in
  Pb by continuity, PushFG back to A), `self`, `least`, `cover3`.
- `Ptyx3Colim.seg`: directed N-colimits of type-3 ptykes (mechanical port
  of PtyxColim): colim is a Ptyx3, iota cartesian, Univ (mor, fac, uniq).
So the catemb structure (subobjects, images, pull-backs, finite
generation, directed colimits) holds at type 3.  All.seg 21,819,
check.py exit 0.
NEXT (open): (i) Ext3 / germs at type 3 (a type-3 ptyx is determined by
its restriction to finitely generated ptykes, object version);
(ii) ABSTRACT the step: a record "category of embeddings" (objects,
monos, subobjects as props closed under meets, small finite
generators, pull-back of subobjects, directed colimits) and ONE theorem
CE -> CE for stable functors into LO; Dil -> Ptyx -> Ptyx3 are then
instances instead of copies (this is catemb's main theorem proper).

## Abstract catemb (18 Nov 2026, user: "go ahead" with CE -> CE)

DONE (stages 1-2), All.seg 22,073, check.py exit 0:
- `CatEmb.seg`: record CE {Obj : U l+, Mor : small, category laws as Id,
  mono, pull-backs (pb, p1, p2, pb-sq, pb-univ), Fin : U l small codes,
  fin : Fin -> Obj (non-injective), dir (two maps from finite objects
  merely factor through a common one)}.
- `StabFun.seg`: record SF[C] (functor to LO, cont: point from some
  finite object, stab: pull-back preservation in image form);
  Over[C]: morphisms = FINITE PARTS (natural + Cart on finite objects) so
  Mor is SMALL; mor-eq, idS/compS, id-l/id-r/assoc/mono as Id;
  Ext: extension of a finite part to all objects by unique choice
  (indep by dir), fin-eq, incr, nat-all, cart-all (pull back along the
  finite witness, finite witness in the pull-back, Cart), det.
- `StabPb.seg`: pull-backs in Stab(C), pointwise {(y,y') | s y = s' y'}
  (extensions): SF, pr1, pr2 (cartesian via Cart of the other side), sq,
  Univ (h, h1, h2).
So Stab(C) satisfies every CE axiom except Fin'/dir'.
Replacement: NOT needed for small hom-sets (finite parts) nor for
non-injective codes.

OBSTRUCTION at stage 3 (small codes Fin' for finite stable functors):
catemb itself (sec. 2): "in the stable case one can only describe the
finite elements less than one given element".  A finitely generated u
inside t is generated by (A,a) and ALL its restrictions (X, x <= a); a
t-independent code needs the predicate R(psi) = "a restricts along psi"
as small data: Bool-valued (decidable) or resizing.  Plain generator
codes (i, f : fin c_i -> A) fail stability when generators are not at
their least support.  Proposed (needs user decision): require finite
objects of C to be BISHOP-FINITE in structure (Hom(fin c, fin d) finite
with decidable equality, pull-backs of finite objects finite); then
inside finite objects decidability is DERIVED (u(B) a finite LO, R
decidable), not assumed for all objects; codes = finite-ordinal-valued
stable functors on finite objects + germ decoding; and the theorem
must re-prove Bishop-finiteness for Stab(C)'s finite objects.
NEXT: user decision on that hypothesis; stage 4 (Dil instance) is
independent and can proceed.
UPDATE (same day, user: "Bishop finite looks natural"): Bishop-finite
finite objects of C are NOT sufficient.  Cover (every point x of X(fin c)
in the image of a coded finite object) needs the finite object to
contain all restrictions of x that exist in X (morphisms are cartesian),
i.e. decide "x in Im X(s)" for the finitely many subobjects s of fin c.
Decidable iff X(fin c) finite (finite search); otherwise it is the
support question (least support merely existing already gives P \/ ~P).
Options put to the user: (1) restrict to FINITE-VALUED stable functors
(X(fin c) finite ordinal; decidability derived; omega+X, D(omega) only
as ind-objects) -- recommended; (2) supports as data (PDil-style);
(3) propositional resizing.
CORRECTION (same day): supports ARE decidable, derived, not assumed.
`StabDec.seg` (checked, All.seg 22,109): given s : B -> A and a
self-amalgamation w, w' : A -> D (s;w = s;w', pull-back of w,w'
factoring through s), for every stable X: x in Im X(s) <-> X(w)x =
X(w')x, an equation in the LO X(D), hence decidable (`Dec.dec`).
Analogy: degeneracy is decidable for simplicial sets with decidable
equality.  So the non-injective presentation route is not needed; the
classical catemb picture (least supports by finite search over the
Bishop-finite subobjects of a finite object, finite subobjects,
embeddings only) should hold constructively.  New CE axiom needed:
self-amalgamation over subobjects (at least of finite objects);
holds for finite ordinals; to check for Dil and to PROVE for Stab(C)
(pointwise amalgam ordered by A-position then copy, using decidable
membership in the subobject, available by StabDec one level down).

### Abstract catemb, constructive normal forms (18 Nov 2026, user: go ahead)
All.seg 22,451, check.py exit 0.
- `CatEmbFin.seg`: record CEF {C : CE; Bishop-finite homs between finite
  objects (homN, hom, hom-surj, hom-dec); finite list of subobjects of
  each finite object (subN, subo, subm; total index) with sub-cover
  (every map into fin c image-equivalent to a listed one, merely);
  self-amalgamation of each listed subobject (amal*); rigid (only
  endomorphism of a finite object is id); mor-set}.  Bounded search over
  W.N (search, lt-split), Fac / fac-comp / fac-pre, DecFac.
- `StabSupp.seg`: LS[F,X,c,x]: least support by finite search (decS via
  StabDec, Below via DecFac, existence by folding pull-backs over the
  list, `least`); `min` (minimal against any supporting map), `minx0`
  (every map supporting x0 has a section), `uniq` (NORMAL FORMS UNIQUE:
  X(k)x0 = X(k')x0 => k = k', using rigidity).
- `StabCode.seg`: record Code[F] (m generators gen i, comparison ord at
  each finite level on normal forms (i, k), inv/orefl/oflip/otrans/oeq)
  -- SMALL; Decode[F,K]: points at A = normal forms (i, k : fin gen i -> A),
  compared at a common finite refinement (unique choice; independence by
  mono + inv), NO quotient; LO, action by postcomposition, cont, stab
  (pb-univ, via J on the generator index), `obj : SF`.
- `StabCover.seg`: Gen1 (one-generator code from the least support of a
  point; ord from X; oeq by uniq), `mor` : Decode -> X CARTESIAN (by
  minx0), Cover.cover: every y in X(A) is the image under (the extension
  of) a morphism from a decoded code.  Constructive version of "every
  object is the directed colimit of its finite subobjects", along
  embeddings.
NEXT: (a) dir' for Stab(C): merge two codes mapping into X (dedupe
generators in the same orbit: decidable by hom enumeration + LO
equality); (b) the CEF axioms for Stab(C) (Bishop-finite Mor' between
decoded codes needs a further finiteness axiom on C: finitely many
joint types of pairs of maps from finite objects; subobject lists;
amalgamation of decoded codes: pointwise amalgam); (c) instances:
finite ordinals, then Dil; compare with DilPtyx/Ptyx3.

### Stab(C) is a category of embeddings (2026-11-19)
- `StabDir.seg`: states = lists of MINIMAL, pairwise NON-DUPLICATE
  generator points of X (record St; gen total, default from the input
  code).  GenN: the code of a state (ord from X; oeq from Collide +
  non-duplication + rigidity) and a CARTESIAN morphism Decode -> X
  (minimality).  Ins: inserting a minimal point is DECIDABLE (search over
  generators and hom-sets, LO equality; a new generator goes in front, so
  gen' (suc i) = gen i definitionally; non-duplication via Flip).  Fold:
  insert a finite family.  MinGen: generators of a code sent into X by a
  morphism are minimal (cart-all + J on the index).  Lift: a morphism
  whose values lie in the image of a cartesian j factors through j.
  DirS: dir for two maps Decode K -> X, Decode K' -> X (insert all
  generator images of K then K').  StabCE[F].ce : CE.CE -- Stab(C) with
  finite objects = codes is a CATEGORY OF EMBEDDINGS (pull-backs from
  StabPb).  All.seg 22,699, check.py exit 0.
NEXT (b) CEF[Stab(C)]:
  * hom-dec: morphisms are determined by the images of the generators,
    each in a finite LO -> decidable (no new axiom);
  * rigid: each level Decode K (fin d) is a Bishop-finite LO, and an
    order-preserving self-map of a finite LO is the identity (no new
    axiom; needs the finite-LO lemma);
  * subobjects = subsets of the generators (2^m), amalgamation = pointwise
    copy of the generators outside the subset, ordered by
    (underlying normal form, then tag);
  * hom enumeration: candidates = generator n |-> (n', k iso); deciding
    that a candidate is ORDER-PRESERVING at all levels needs a NEW AXIOM
    on C: finitely many joint types of pairs of maps from finite objects
    (every (f : a -> d, g : b -> d) factors through one of finitely many
    listed (u_t : a -> c_t, v_t : b -> c_t)).  To iterate, the same axiom
    must then be proved for Stab(C) (joint types of two decoded codes =
    identification data + comparisons on joint types of generators).

### Exact multicoproducts and the base instance (2026-11-19)
- `CatEmbFin.seg`: enumerations are JUNK-TOLERANT (entries in Opt, so a
  finite list may be filtered by a decidable test; EnumDec decides an
  existential over such a list); jt* restated as Diers's finite
  multicoproducts with finitely many members (jt-cover, jt-uniq, jt-epi;
  JT = cospans, JFac = factorisations).  Reading: Osmond/Diers (see
  ~/CANONICITY/dier1-3.pdf): stable functor = unique factorisation through
  a candidate (our least support + uniq); N_B = sum of representables (our
  Decode: no quotient); multicolimit = exact jt.
- `FinOrd.seg`: FINITE ORDINALS with words as a CE (ce: pull-backs =
  andW, dir = union orW) and a CEF (cef): hom-sets = words of length d
  (binary enumeration bin/code, filtered by ones), subobjects = all words
  of length c, amalgamation A1/A2 (double the points outside s), rigidity
  (len = ones forces idW), multicoproducts = jointly surjective shuffles,
  enumerated as interleaved pairs of words of length a+b (padding by
  zeros for coverage; uniqueness and epimorphy by union of images).
- `FinOrdEx.seg`: dilCE = StabCE[cef].ce (DILATORS, finite-level form,
  form a category of embeddings); idD = identity dilator as SF; COMPUTED
  by #conv: least support of 2 in [5] is {2} (j0 = 4, word o o i o o,
  x0 = 0); Gen1 codes of 0 and 1 in [2] merge (DirS) into ONE generator
  (duplicate detection computes).  All.seg 23,022, check.py exit 0.
NEXT: generic CEF[Stab(C)] (hom enumeration via jt, rigidity via finite
LO, subsets of generators, pointwise amalgam, multicoproducts of decoded
codes) => ptykes = Stab(Stab(FinOrd)), etc.

### CEF for Stab(C): layers 1-4 (2026-11-19)
- `StabFin.seg`: morphisms of SF form a set (mor-set); GI: a morphism out
  of a decoded code is determined by the generator images (val, det);
  equality of such morphisms is decidable (Dec).
- `FinList.seg`: junk-tolerant finite enumerations as lists, membership up
  to a relation (no funext needed): genL/fromIdx, appL, mapO, prodL,
  sigL (dependent pairs), filterO/filterS, DecAll, decOpt, toEnum.
- `StabHom.seg` (HomE[F,K,K']): morphisms Decode K -> Decode K' are
  BISHOP-FINITE: assignments of generator images enumerated generator by
  generator; validity (sections of the image maps + agreement of
  comparisons on the listed multicoproduct cospans) decidable; Mk builds
  the morphism (order at all levels via jt-cover); Surj: every morphism is
  listed (det).  homN/hom/hom-surj.
- OBSTRUCTION FOUND AND FIXED: CEF.sub-cover over ARBITRARY domains B would
  imply LEM for Stab(C) (subfunctor cut out by an undecided proposition).
  sub-cover now quantifies over FINITE domains only; StabSupp (PbStep,
  Min) reduces to them through continuity of X.  FinOrd adapted.
- `StabSub.seg`: Restr[F,K,T]: restriction of a code to a subset T of the
  generators, with the cartesian inclusion; SubCov: a cartesian map
  Decode K2 -> Decode K is image-equivalent to the restriction to the
  generators it hits (decidable: finite levels are Bishop-finite).
All.seg 23,365, check.py exit 0.
REMAINING for CEF[Stab(C)]: (5) amalgamation (plan: amalD = D(K) x {L,R}
lexicographic, w = tag L, w' = tag L on T, R outside; t from the generic
pull-back); (6) rigidity (finite-LO lemma: an order-preserving self-map of
a Bishop-finite LO is the identity, at each finite level); (7) finite
multicoproducts of decoded codes (partial matchings of generators +
comparisons on joint types of generators); then assemble StabCEF : CEF and
iterate (ptykes = Stab(Stab(FinOrd))).

### CEF for Stab(C): layers 5-6 and assembly (2026-11-19)
- `StabAmal.seg`: amalgamation of Decode K over Decode K|T: X2 = Decode K x
  {L,R} (LexB: lexicographic product of an LO with Bool), w = tag L,
  w' = tag L on T and R outside; t : Pull(w,w') -> Decode K|T, t;sub = p1.
- `StabRigid.seg`: constructive pigeonhole by counting (cnt of entries
  below y is strictly monotone in y); FinLO/Fix: an order-preserving
  self-map of a Bishop-finite LO is the identity; Rig: decoded codes rigid.
- `CatEmbFin.seg`: record CEF0 = CEF without the multicoproduct fields.
- `StabCEF.seg`: StabCEF0[F].cef0 : CEF0 -- Stab(C) satisfies every CEF
  axiom except finite multicoproducts; dilCEF0 = StabCEF0[FinOrd.cef].cef0.
All.seg 23,563, check.py exit 0.
OPEN (layer 7): finite multicoproducts of decoded codes.  Design points:
 (a) listed cospans are codes whose CROSS comparisons (K1-generator vs
     K2-generator) are data indexed by C's listed joint types; defining
     ord by unique choice from jt-cover needs the listed index to be
     unique (no duplicates in C's jt list; FinOrd's list has duplicates
     from padding -- filter to canonical padding);
 (b) validity of a candidate (transitivity) needs ternary joint types,
     obtainable by iterating binary ones (pair, then with the third);
 (c) identifications of a K2-generator with a K1-generator (iso of
     generators, unique by rigidity) are part of the candidate data.

### Layer 7 design (multicoproducts of decoded codes K1, K2)
No new axiom on C: duplicates in C's jt list are handled by a decidable
CONSISTENCY condition on tables (instead of unique indices).
- 7a `StabJt0.seg` (generic, F : CEF): decJFac (factorisation through a
  listed cospan is decidable: hom search); findJ (a COMPUTED listed joint
  type for any pair of maps into a finite object: search, None refuted by
  jt-cover); ternary joint types (pairs (t1,t2): (a,b) via t1, then
  (c_t1, c) via t2) with a computed cover.
- 7b `StabSum.seg`: Sum[K1,K2,tbl]: generators K1 then K2 (index side via
  W.cut m1; view' by split on the cut value, so no transport inside
  branches); ord: same side = K ord, cross = tbl at findJ (flip for 2-1).
  Validity SV (decidable): SV1 consistency of tbl across listed indices
  whose cospans factor through each other, SV2 tbl never eq, SV3
  transitivity of ordS at listed ternary cospans for all generator triples.
  Laws: inv (lookup invariant: jt-uniq + SV1), orefl, oflip, oeq (SV2),
  otrans (ternary cover + inv + SV3).  inl : D K1 -> D Sum.
- 7c `StabJt.seg`: candidate = (T2 subset of K2 kept, tbl over K1 x K2|T2,
  sigma_v assignment D K2 -> D Sum), valid = SV and HomE[K2,Sum].V; listed
  cospan (Sum, inl, Mk sigma_v).  Cover for (f,g) into D K3: T2 = K2
  generators whose g-image is not in the image of f (decidable), tbl read
  in D K3 at listed joint types, sigma_v from identifications; m : D Sum ->
  D K3 by HomE[Sum,K3].Mk; u;m = f, v;m = g by det.
- 7d: jt-uniq (data determined by the cospan; funext on tables; J on the
  code path), jt-epi (det on Sum's generators).
7a DONE (StabJt0: decJFac, FindJ computed, Tern).  7b DONE (StabSum: Side
views/in1/in2/back-view/view-post; SumC table, SV1-3; SumCode.code).
7c refined: listed cospans = for each T2 (bin word) and each table g
(enumerated as a DEPENDENT function list, proofs-as-arguments so that
agreement = funext-equality) passing decSV: c' = SumCode[K1, K2|T2, g];
then ALL pairs (u', v') from HomE[K1,c'].homL x HomE[K2,c'].homL.  Cover
for (f,g) into Y = Decode K3: T2 = non-identified K2 generators (hit test),
table read in Y at listed joint types; the listed table agrees, so ordS =
Y.cmp of images ("realised in Y") gives SV and a morphism m' : D c' -> Y
(MkX: generic morphism from a code into an SF given minimal generator
points and ord compatibility); u0, v0 = Lift of f, g through m'; u0, v0
are listed (HomE.Surj); JFac = (m', Lift.eq).  7d (exactness) later:
restrict to jointly surjective entries, canonical data, funext on tables.
7c DONE (StabJt.seg): MkX; Tab (DepFun enumeration of tables, decidable
SV1-3: dSV); JL (the list: T2 words x valid tables x ALL pairs of
morphisms from HomE.homL); Cov (hit test, T2, table read in Y), Real
(realisation ordS = Y.cmp of images; sv1-3 proved; NoId via Collide),
Fact (m' = MkX, u0/v0 = Lift), Cover7.result : jt-cover for decoded codes.
NOTE: SumCode uses F.jt-uniq (lookup invariance), so iterating needs
jt-uniq for Stab(C) (jt-epi is used nowhere).
7d TODO: restrict the list to CANONICAL entries (decidable: gimg u' n1 =
in1 (n1,id); n2 in T2 => gimg v' n2 = in2 (rank T2 n2, id); n2 not in T2
=> view of gimg v' n2 is inl); cover produces canonical entries; jt-uniq:
T2 = {n2 : g n2 not in Im f} and table values are determined by (f,g)
(SV1 + F.jt-uniq for duplicate indices), so tables equal by funext, the
SV proof is a function of the table (filterS stores the decision's
proof), codes equal by ap, maps equal by det after J; jt-epi: det on the
generators of the sum (each is a u- or v-image).
(2026-11-19) Refactors for 7d done: JL indexed by WORDS (Ix = (w, len w = m2),
ixM via code/bin), Cov uses T2 = wordOf m2 bit directly; VS j = (tb, OkS)
with OkS = "dSV tb is inl" (a boolean prop), svOf extracts the proof, so
entries with equal tables are equal (uip).  StabJt0/StabSum/StabJt in
All.seg.  NEXT 7d: Can (Can0 junk = lt, CanU, CanV) decidable; jtL2 =
mapO (toJT o fst) (filterS E1 Can e1L); cover canonical; Det: canonical
factoring entry = Cover7.tgt (words by wext-pt, tables by funext, q by
Sigma-eq+uip, maps by GI.det); jt-epi by det on sum generators; assemble.

### THE THEOREM DONE (2026-11-19): Stab(C) is a CEF when C is
7d DONE: CN (canonical entries: junk table entries = lt, u' = first
injection on generators, v' = cform on kept generators / K1-side on
dropped ones; decidable; canonical list jtL); CovCan (cover entry is
canonical); DetA (canonical factoring entry: maps act canonically, its
subset = cover's: ixEq), DetB (tables equal by funext: TV.qEq; maps equal
by det: MC; listedDet via J on Ix and on VS paths), CanP/Epi7 (jt-epi by
det on the sum generators), JtFields.
StabCEF.seg: StabCEF[F].cef : CEF for every F : CEF.  Instances:
dilCEF = StabCEF[FinOrd.cef] (dilators), ptyCEF = StabCEF[dilCEF]
(ptykes of type 2), pty3CEF = StabCEF[ptyCEF] (type 3), ... (checked by a
planted error).  All.seg 24,263, check.py exit 0 (16.5 s).
NEXT (ideas): computations in dilCEF (normal forms of dilator points by
the generic least-support search -- likely slow); compare dilCEF objects
with DilPtyx/CatDil dilators; type n by iteration; write up.

### LO base (2026-11-19, requested): ALL linear orders
Correction: every dilator/ptyx so far (CatDil, DilPtyx, Ptyx3, and the
dilCEF hierarchy) is over FINITE ORDINALS only; WF-preservation needs LO.
Plan (`LOCat.seg`, `LOFin.seg`, `LOCEF.seg`):
- CE: Obj = DP.LO, Mor = DP.Map (strictly increasing = embeddings), laws by
  map-eq (funext), mono by map-inj, pull-back = {(b,b') | f b = f' b'}
  ordered by b, Fin = N, fin n = [n] (FinOrdEx.G).  dir: images of i, i'
  as strictly sorted lists, MERGED (dedup), j = nth of the merge, k = rank
  (number of entries below), rank lemma ev l (rk l a) = a, rank strictly
  monotone.
- CEF by TRANSFER from FinOrd.cef along the iso words <-> Map [c] [d]
  (w |-> sel w; f |-> wordOf (image f)); amal-t through FinOrd's pb-univ on
  single points.
- Then WF hierarchy: WF on LO = accessibility; WF'(X) = all WF A -> WF X(A);
  dilators = WF' objects of Stab(LO), type-2 ptykes = WF'' objects, ...
LO CE DONE (LOCat.seg): idMap/compMap/map-eq, PB, ord n, SL (sorted lists:
merge with dedup, M3/M12 membership, S sortedness, ev/ev-mono, rank rk and
rankL: ev l (rk a l) = a, mkL/mkL-mem/mkL-inv/mkL-srt), DirL (k = rank in
the merge), LOCat.ce : CE.  NEXT LOFin.seg (CEF for LO), design:
- phi : FinOrd.Mor c d -> Map [c] [d] = FinOrdEx.arr (sel); phi-id, phi-comp
  (arr-id, arr-comp); phi injective (sel-ext); psi = toW: word of a strictly
  increasing f, by recursion on d (f 0 = 0 ? i : o, shift by pred);
  phi (psi f) = f.
- hom: mapO phi of FinOrd's list; hom-dec by DecAll pointwise; subobjects
  phi(FinOrd.subm), sub-cover via psi + phi-comp; amalgamation DIRECT:
  amalD = LexB[ord c] (StabAmal), w = (b,false), w' = (b, not (at s b)),
  t (b,b',e) = (rank s b) (sel-rank, sel-mono); jt: mapO (phi x phi) of
  FinOrd's jt list, cover/uniq/epi through psi and phi injective; rigid via
  psi + FinOrd.rigid; mor-set = StabFin.map-set.
- then LO hierarchy: StabCEF[LOcef]; WF predicates.
LO DONE (2026-11-19): LOFin (phi/psi words <-> maps, toW + spec),
LOCEF.cef : CEF (all linear orders; finiteness transported from FinOrd,
amalgamation via LexB), dilLO = StabCEF[cef], ptyLO = StabCEF[dilLO].
LOWF.seg: WF (accessibility), Lift/IsDil/IsPtyx hierarchy; idD dilator;
opD (X^op) pre-dilator, NOT a dilator (omega^op: no accessible point);
Ev[Z].ev evaluation at Z as a stable functor on Stab(LO) (Ext functorial
by det, cont by the covering theorem, stab pointwise); evOmega a type-2
ptyx.  All.seg in check.py exit 0.
NEXT: completeness reductions: tree T |-> pre-dilator D_T with
(T well-founded <-> D_T dilator) [Girard, Pi^1_2]; then the type-2 analogue.

