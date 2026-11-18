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
