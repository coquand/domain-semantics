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
  NEXT: the converse direction of Ext (restriction of a ptyx morphism to
  FinDil satisfies FinCart, i.e. PM.Cartesian => pull-backs along all
  morphisms of finite dilators); a ptyx built FROM finite data (a
  functor on FinDil -> LO with supports extends to a ptyx: the object
  version of Ext, F(D) = colimit of F(D|K) as a quotient/germs); Ptyx as a category of embeddings (subptykes, finite
  ptykes, directed union); is EvalMor full (every Eval m -> Eval n is a w)?
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
