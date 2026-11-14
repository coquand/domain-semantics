# Handoff: prove the recursive projector finitary using CGW

## Checked progress (2026-11-14)

The general dependent-product closure theorem is now checked for Scott
domains `A,D` and a continuous EP-valued family over `A` with coherent
embeddings of its fibers into `D`:

- `ScottEPDependentProduct.Sections.domain` constructs the Scott domain of
  continuous sections before an embedding of `A` into `D` is supplied.
- `ScottEPDependentProduct.Product.pair` embeds it into `D`, given EP pairs
  `A -> D` and `[D -> D] -> D`. Its `.finitary` is the resulting projector.
- `ScottDependentProductEmbedding.Embedding` gives the explicit maps
  `E(s)(z)=s(r_A z)` and `R(g)(a)=Q_a(g(e_A a))`, their continuity,
  `RE=id`, `ER<=id`, and the composite formula.
- `ScottFinitaryFamily` and `ScottFinitaryEPFamily` construct the continuous
  EP family of images from a continuous family of finitary projections.
- `DependentProductProjector.On.realizes` identifies the general construction
  with the exact Phi function clause. `SectionProjector.On.finitary` and
  the function case of `ProjectorInvariant` now use this general proof.
  The older explicit graph proof remains checked for comparison.

`ProjectorInvariant.Preserve.family` proves independent preservation of
normalized finitary families. `ProjectorNormalization`,
`NormalizedProjectorSup`, and `IndependentKleeneProjector` supply
normalization preservation, directed closure, and all iterate/limit laws.
`KleeneProjector.finitary` and `.normalization` use the independent proof.

`IndependentDependentProductCheck.seg` checks the general construction
with no filter-domain, MIN, or typing modules in scope (1,156 declarations).
`IndependentProjectorCheck.seg` checks its filter instance and invariant
without the typed projector/comparison modules or the old direct
common-code proof (3,849 declarations).
`check.py` now runs five sessions including these, the CUSL Fp session,
and the existing full and logical-relation checks; all report zero failures.

The dependent-sum and varying-function-space route is also now checked:

- `ScottDependentSum.Total.scott` constructs Sigma(A,B) for continuous
  finitary subdomain families; `EPFamily.component-equation` recovers the
  actual EP-fiber element from its ambient representation.
- `ScottDependentSumEmbedding.Embedding.pair` gives its EP embedding in
  C x D from an EP pair A -> C; `.finitary` is its induced projector.
- `ScottExponentialEPAction.Action` gives the general exponential EP action.
  `ScottVaryingFunctionSpace.Family.family` proves continuity of
  a |-> [Fix(Q_a) -> Fix(R)], represented by g |-> R o g o Q_a.
  `At.equivalence`, `represent-mono`, and `represent-reflect` identify
  each fixed image with the actual exponential.
- `ScottFunctionPayload.Payload` obtains the finitary total-space projector.
- `UniversePayloadProjector.On` specializes it to the code domain
  Fix(q(U,-)) and the fibers [Fix(q(a,-)) -> Fix(q(U,-))]. Its `Formula`
  and `FilterFormula` identify the exact Phi payload using normalization.
- `StructuralUniverseProductProjector.On.observe` transports simultaneous
  compact code/function witnesses to the Pi-headed filter clause.
  `ProjectorInvariant` now uses it. No graph-entry recursion or bespoke
  common-code joins are used in this clause proof. The old
  `UniverseProductProjector` remains checked in All but is excluded from
  the independent projector session by an import audit in `check.py`.

The general Fp construction is now checked on CUSLs too:

- `ScottCUSLClosedFamilies.On` constructs all compact subsets closed under
  bottom and ambient compatible joins. Its `scott` has a finite-generator
  basis; `compact-finite` characterizes every compact family.
- `ScottCUSLFpMaps.Between` constructs direct/inverse image as a continuous
  EP pair. `ScottCUSLFpFunctor.Domains` and `.Compacts` prove the functor laws.
- `ScottCUSLFpProjector.On` identifies closed families with all finitary
  projector operations on ideal completion and proves the adjunction,
  retraction and directed continuity of the greatest-projector operation.
- `ScottCUSLCoveredColimit.On.colimit` proves the universal property of a
  directed union, using unique compatible values without choice.
  `ScottCUSLDirectedUnion.Coverage` proves every existing small directed
  CUSL colimit has stage coverage. `ScottCUSLFpDirected` then proves the
  EP-exhaustion equation and compact-stage representation for Fp.
- `ScottCUSLFpContinuity.preserves` proves preservation of every existing
  small directed colimit, without assuming input coverage. The new generic
  directed-diagram interface includes all small directed poset diagrams.
- `ScottFpFunctor` and `ScottFpContinuity` transport the continuous functor
  to arbitrary Scott EP domains through the checked equivalence.
- `ScottFpAdjunction`, `ScottFpAdjunctionContinuity`, and
  `ScottFpRepresentation` give the general adjunction, continuity of both
  maps, and representation of all finitary operations on presented domains.
- `ScottCUSLFpRestriction.On.Extend.equation` and `.Restrict.equation`
  check the formulas e P r and kappa(r P e) on ideal domains.
- `CUSLFpCheck.seg` checks all of this without filter, MIN, typing or the
  specialized compact-family/projector modules. `check.py` audits that
  boundary and runs it in a separate process.

The last full check passed All (15,724 declarations), CUSL Fp (2,412),
the generic product/sum session (1,156), the independent projector session
(3,849), and the independent logical-relation session (6,349), each with
zero failures. All 40 frozen dependency hashes were verified.

These are the common-ambient-subdomain forms of CGW's dependent-product
and dependent-sum constructions. Unrestricted Propositions 7/8 without a
coherent common ambient domain and the higher parameterized constructions
of section 3.4 are not claimed by these additions.

**Correction to the stage plan below:** arbitrary EP conjugation `r P e`
does not preserve projection idempotence. `EPRestrictionObstruction.seg`
checks the finite-order counterexample: on `0<1<2<3`, take
`P=(0,0,2,2)`, embed `{0,1,3}`, and project `2` to `1`. Then `r P e`
sends `3` to `1` and `1` to `0`. In classical finite Scott domains this
also refutes the asserted generic finitary-projector restriction rule.
An independent proof for the particular direct stages still needs rank
compatibility; it cannot be inferred from global finitariness by that rule.
The existing typed stage comparison remains in place.

## Review against the PDF itself

Read the definitions and colimit criterion on printed pp. 126–129,
Propositions 7–8 and their proofs on pp. 132–136, the parameterized section
construction in §3.4 (pp. 140–143), and §7.2–7.3 (pp. 162–164), checking
the mathematical formulas against rendered PDF pages.

One distinction was missing from the earlier report. On p. 162 CGW states
that the inclusion `Fp(D) -> [D -> D]` is an EP embedding (citing Scott).
Its right adjoint is the greatest finitary projector below an endomap:

    kappa_D(f)(x) = sup { k <= x | k compact and k <= f(k) }.

`FinitaryInterior.At.below`, `.greatest`, `retract`, and `family-retract`
now check this construction on the filter domain. Its continuity is checked
by `FinitaryInteriorContinuity.DirectedSup.equation`.

Combining that EP retraction with the endomap action on p. 129 gives the
induced projection part of the Fp action as `P |-> kappa_D(r P e)`.
This formula is a deduction from the paper's constructions, not a displayed
formula in CGW. The counterexample above refutes dropping `kappa_D`, not
the existence of an Fp action. Thus the specific stage problem is to prove
that each raw `r_n p(e_n a,-) e_n` already equals its finitary interior.
The general action and both formulas are now checked by the CUSL route
described above. Only compatibility for the particular raw rank restrictions
remains outside this independent proof.

CGW Proposition 7 uses preservation of directed colimits to approximate a
fiber element over a compact base code (p. 134). The generic support proof
in `ScottDependentSum` now formalizes this obligation once for all
continuous finitary-subdomain families. Proposition 8's compact
steps on p. 136 match those in `SectionProjector`. No additional missing
hypothesis in the checked preservation theorem was found in this review.
The abstract common-ambient functor/section presentation is now checked
as described above. The varying-code total-space proof now uses the general dependent-sum
and varying-exponential results. Section 3.4 supplies further parameterized
constructions not formalized by these additions.

The remaining sections retain the original handoff, with the stage restriction
step corrected below; the checked progress above supersedes its old proof boundary.

## Objective

Give a checked, domain-theoretic proof that the least fixed point
`p = lfp(Phi)` has `p(a,-)` finitary for every `a`, without identifying it
with the projector generated by inductive compact typing. Then obtain
finitariness of the directly defined stage maps

\[
p_n(a,x)=r_n\bigl(p(e_n a,e_n x)\bigr)
\]

by the restriction action of `Fp` on embedding–projection pairs. The
independent proof should also establish the normalization law
`p(p(U,a),x) = p(a,x)`. Do not describe the current typed comparison as
this proof.

## The relevant result in `cgw.pdf`

Coquand, Gunter and Winskel, *Domain Theoretic Models of Polymorphism*,
Information and Computation 81 (1989), 123–167:

- Proposition 7, printed pp. 132–134: the dependent sum (total space)
  of a continuous functor from a Scott domain into the EP category is
  a Scott domain.
- Proposition 8, printed pp. 135–136: the domain of continuous sections
  of such a functor is a Scott domain. Its proof constructs compact
  sections from finitely many compact input/output observations.
- Section 7.2, printed pp. 162–163: the finitary-projection model uses
  these constructions. In particular, its projection onto a dependent
  function space has precisely the form of our function clause. The
  paper says this projection is finitary *by construction*.

The local PDF is `/Users/coquand/DOMAIN/cgw.pdf`. The extracted text is
`/tmp/cgw-domain.txt` if it survives the session. These are mathematical
results in a classical presentation; they must be adapted to the small,
constructive Scott-domain interface in `UNIT`, not assumed as axioms.

## The exact function-clause argument

Let `q : D -> Fp(D)` be Scott-continuous and write
`P_a = q(a,-)` and `D_a = Fix(P_a)`. For a product classifier `Pi(a,f)`,
define, for `v : D_a`, the finitary projection
`B(v) = q(f(v),-)`. Continuity of `q` and `f` should make the image
domains `Fix(B(v))` a continuous EP-valued family over `D_a`. This
continuity is a proof obligation, not just pointwise finitariness.

Let `Gamma(a,f)` be its domain of continuous sections: a section `s`
is a continuous function on `D_a` satisfying `B(v)(s(v)) = s(v)`.
CGW Proposition 8 makes `Gamma(a,f)` a Scott domain. Define

\[
E(s)(z)=s(P_a z),\qquad
R(g)(v)=B(v)(g(v))\quad(v\in D_a).
\]

Then `R E = id`, and `E R <= id` because both `B(v)` and `P_a` are
deflationary and `g` is monotone. Thus `E,R` form an EP pair, and
the induced finitary projection on `[D -> D]` is

\[
(E R)(g)(z)
 =q\bigl(f(q(a,z)),\,g(q(a,z))\bigr).
\]

This is exactly the function component of `Phi(q)(Pi(a,f),g)`. It
supplies the missing *finitariness*, beyond the elementary deflation
and idempotence calculations. It does not require normalization of `q`.

## The universe/product clause and the stronger invariant

Pointwise finitariness alone does **not** make `Phi(q)` pointwise
idempotent. Put `U_q = Fix(q(U,-))`. The necessary simultaneous invariant
is

\[
q(q(U,a),x)=q(a,x)\qquad\text{for all }a,x.
\tag{N}
\]

Indeed, applying the universe/product clause twice changes its use of
`q(a,-)` to `q(q(U,a),-)`; (N) identifies them. The calculation showing
that `Phi` preserves (N) is outlined in `UNIT/SECTION24.txt`, §2. It
must be formalized without appealing to `SemanticLaws.Normalize`.

For the finitary part, the product payload is projected by

\[
(a,f)\longmapsto
\bigl(q(U,a),\ z\mapsto q(U,f(q(a,z)))\bigr).
\]

Under (N), its image should be the dependent sum over `a : U_q` of
the spaces of continuous functions `D_a -> U_q`. Use CGW Proposition 8
for these function/section spaces, Proposition 7 for their total space,
and the coalesced-sum domain equation for the universe and product
heads. Check that the family of function spaces varies continuously
with `a` in the EP category; this is the substantive additional
obligation. The universe head is fixed, and the remaining head cases
give bottom.

The bottom binary map satisfies pointwise finitariness and (N). Once
`Phi` is shown to preserve both, its Kleene sequence stays in this
class. Directed suprema in `Fp(D)` are pointwise, so the least fixed
point `p` is finitary. Continuity/normalization at the supremum need
the diagonal cofinality argument in `UNIT/SECTION24.txt`, §4.

An alternative organization is to make the normalized `Fp`-valued
families a dcpo and restrict `Phi` to it. Show its fixed point agrees
with the existing `KleeneProjector.p` by pointwise Kleene iteration.

## Recovering the stages

`UNIT/DirectProjectorStages.seg` defines the displayed `p_n` and proves its
equality with `OperationalStages.p`. Global `p(a,-)` is now independently
finitary. This does **not** imply finitariness of `r_n p(e_n a,-) e_n`
by a generic EP restriction rule: that rule fails as recorded above.
Additional rank-specific compatibility is required to replace the existing
bounded-typing proof in `StageComparison`.

## Original checked code and proof boundary (before this session)

- `ProjectorOperator.seg` defines `Phi`; `OperatorContinuity.seg` proves
  its continuity; `KleeneProjector.seg` constructs the least fixed point.
- `Finitary.seg` and `ProjectorDomain.seg` present `Fp(D)` for the
  existing filter domain; `FixedImage.seg` constructs the image and
  its compact basis. They do not yet package the generic CGW
  continuous-section theorem.
- `ScottExponential.seg` gives compact finite-graph bases for ordinary
  Scott function spaces; `ScottEPExponential.seg` gives EP action on
  endomaps. These are likely ingredients for the section construction.
- `ScottCUSLColimit.seg` gives intrinsic compact representation for
  CUSL stage colimits, but its solution has not yet been identified
  with the old filter domain and its application. This CGW route can
  initially use the existing filter domain.
- `KleeneProjector.finitary` and `.normalization` currently go through
  `ProjectorFixedPoint`, `SemanticProjector`, and typed compact
  generators. `StageComparison.At.finitary` goes through bounded typing.
  None can discharge the new independent theorem.
- `UNIT/SECTION24.txt`, §3 contains an earlier *informal* direct
  compact-graph argument for finitariness. CGW provides a cleaner
  structural route and identifies the necessary general theorem.

Be careful about the import graph: `KleeneProjector.seg` contains the
independent Kleene construction and the later typed comparison in one
file. A strict independence check may require splitting these parts,
and possibly moving the domain-only `family-map` dependency out of
`ProjectorLeast.seg`.

## Suggested implementation order and completion criteria

1. Package generic finitary projections, their Scott-domain images,
   and EP transport at the required universe levels. Reuse the current
   specialized `Finitary`/`FixedImage` where possible.
2. Formalize the continuous EP family of images `Fix(B(v))`, then CGW
   Proposition 8 and the explicit `E,R` pair above. Check the equality
   with the `Phi` function component.
3. DONE: the general varying-function-space family and dependent-sum result
   supply the universe/product component, under (N).
4. Prove `Phi` preserves the combined invariant, including (N), and
   prove the Kleene supremum retains it. State a theorem identifying
   the resulting finitary operation with `KleeneProjector.candidate.at a`.
5. Prove the additional rank compatibility needed for finitariness of the direct
   `p_n` and update `scott-domains-revised.tex` only after the theorem
   is checked. Record exactly which use of inductive compact typing
   has been eliminated; retain it where the later logical relation
   genuinely needs it.

Run `python3 UNIT/check.py` after adding imports to `UNIT/All.seg`.
Its last recorded run before this handoff reported `All.seg: 13496
declarations, 0 failed` and `IndependentLogicalRelationCheck.seg: 4909
declarations, 0 failed`. There are many pre-existing workspace changes;
do not reset them. Completion means the new finitariness and
normalization theorems type-check **without** invoking
`SemanticProjector`, `StageTyping`, `StageCompatibility`,
`StageComparison`, or `ProjectorFixedPoint.Identify`.
