# Replacing finite-token induction by CUSL stages

## Checked result

`ScottCUSLColimit.On` now exposes three facts for any chain of CUSL
embeddings. Here `vertex` is the colimit CUSL, `D` is the corresponding
limit of ideal domains, and `leg n : C_n -> vertex` is the colimit map.

1. `CompactRepresentation[c].represented` proves, for every compact
   `c : vertex`, the mere existence of `n` and `a : C_n` with
   `leg n a = c`.
2. `CompactObservation[x,c,h].stage-hit` proves, for `c <= x` in `D`,
   the mere existence of `n` with `c <= e_n p_n x`.
3. `CompactInduction[Q,qprop,at-stage].result` proves a proposition `Q`
   on all compact elements from proofs on every stage image. The colimit
   uniqueness proof now uses this principle.
4. `AdmissibleStageInduction[Q]` proves that a lower admissible
   predicate on the ideal limit holds at `x` exactly when it holds at
   every finite-stage projection of `x`. Its `from-stage` theorem
   derives the predicate everywhere from proofs on embedded stage
   elements.

These are representation and observation lemmas about *intrinsic* stage
compacts. They make no reference to intersection-type tokens, a chosen
syntax for finite elements, or a rank on such syntax. They use only
compactness, the compact basis of the EP limit, and stage exhaustion.

The exact three-branch compact constructor is now also checked:

- `ScottEPBinaryProduct.seg` and `ScottEPExactCore.seg` give the
  embedding–projection action on `X × [X -> X]`.
- `ScottCUSLEndofunctorTransport.seg` transports presented EP
  endofunctors to CUSLs. `ScottEPEndomaps.seg` supplies the function
  branch, and `ScottCUSLExactCore.seg` supplies the Pi payload.
- `ScottCUSLAddBranch.seg` adds a lifted positive branch while using the
  original CUSL bottom as the shared bottom. Its action on embeddings
  and both bifunctor laws are checked. `ScottCUSLAddBottom.seg` separately
  checks the fresh-bottom lift functor.
- `ScottCUSLExactFunctor.seg` composes these constructions into a CUSL
  endofunctor with function, Pi, and universe branches. Its dependent
  head eliminator, Pi payload injection, and Pi/universe incompatibility
  are checked. If `B(C,P)` denotes `ScottCUSLAddBranch.object C P`,
  its object part is
  `B(B(K([Idl C -> Idl C]), K(Idl C × [Idl C -> Idl C])), 1)`.
  The function branch supplies the common bottom. The other two
  branches are positive lifts, represented with ordinary sums rather
  than a new inductive syntax for finite elements.
- `ScottCUSLExactChain.seg` constructs the initial chain and its CUSL
  colimit. Every compact has a finite-stage representation. Its first
  stage has incompatible Pi and universe heads, and the colimit
  embedding preserves this incompatibility. The module now checks
  unconditional fold/unfold maps, the fixed-point equation, injectivity
  of the folded Pi payload, and incompatibility of folded Pi and
  universe points.
- `ScottEPEndomapsPreservation.seg` proves that `[X -> X]` preserves
  countable EP-chain colimits. `ScottEPLimitBinaryProduct.seg`,
  `ScottEPExactCoreComparison.seg`, and
  `ScottEPExactCorePreservation.seg` prove the same for
  `X × [X -> X]`. `ScottCUSLEndofunctorPreservation.seg` transports
  both proofs to CUSLs. `ScottCUSLAddBranchComparison.seg` proves
  `colim B(C_n,P_n) ≅ B(colim C_n,colim P_n)` by constructing an
  embedding and using finite-stage representation for its surjectivity.
  `ScottCUSLBranchPreservation.seg` derives omega-continuity for the
  pointwise branch of two omega-continuous endofunctors.
  `CategoryConstantPreservation.seg` handles the singleton branch.
  `ScottCUSLExactPreservation.seg` composes these proofs into checked
  omega-continuity of the exact three-branch functor.
- `ScottCUSLExactSolution.seg` packages this initial algebra and
  transports it across the CUSL--Scott EP equivalence, yielding a
  checked initial algebra and object equation in the Scott-domain EP
  category for the transported endofunctor.
- `ScottCUSLBranchIdeals.seg` now classifies the ideal completion of
  every added branch `B(C,P)`. It checks an order isomorphism with a
  left ideal of `C`, a proposition-valued optional ideal of `P`, and
  the condition that a positive point forces the left ideal to bottom.
  Positive ideals are determined by their positive traces, and ideals
  with no positive point by their left traces. The inverse construction
  and both round trips are checked without deciding whether a positive
  point exists. It also characterizes the least branch ideal: its left
  trace is least and it has no positive point, and these conditions
  suffice to identify it.
- `ScottCUSLExactIdealShape.seg` applies the branch classification
  twice to the exact three-branch constructor and proves an order
  isomorphism with a flat shape. The flat data contain a function ideal,
  an optional Pi ideal, and an optional universe ideal. Pi and universe
  cannot coexist; either positive head forces the function ideal to
  bottom. Both carrier round trips and order reflection are checked.
- `ScottFilterFunctionComparison.seg` upgrades the old carrier
  equivalence `FD ≃ [D -> D]` to an order isomorphism with the Scott
  exponential of the filter domain. `ScottFilterProductComparison.seg`
  similarly identifies `D × FD`, with its componentwise order, with
  the Scott product of that domain and its endomap space.
- `ScottCUSLSingletonIdeals.seg` identifies the proposition-valued
  lifting of ideals of the one-point CUSL with small propositions,
  including the implication order. `ScottFilterSumOrder.seg` packages
  `Sum.RHS` as an ordered object, checks its order isomorphism with the
  filter domain, and proves agreement with `EquationOrder.Order`.
- `ScottFilterFunctionIdealComparison.seg` and
  `ScottFilterProductIdealComparison.seg` use the compact/ideal counit
  and the presented EP endofunctors to compare the exact functor's
  compact branch ideals with the old Scott function and product domains.
  `ScottFilterExactComponents.seg` composes these with the old `FD` and
  `D × FD` comparisons, yielding the component order isomorphisms
  needed by the flat shape. `ScottFilterExactBottom.seg` proves that
  the old bottom function maps to the least function ideal and that
  an old function is bottom exactly when its image is least.
- `ScottFilterExactShapeComparison.seg` now transports the flat shape
  across all three component isomorphisms. It checks maps in both
  directions with both round trips, preservation and reflection of the
  explicit order, and an order isomorphism
  `Idl(T(K(D))) ≅ Sum.RHS`. Composing with the old
  `D ≅ Sum.RHS` yields a checked embedding--projection isomorphism
  `D ≅ Idl(T(K(D)))` at the old filter domain.
- `ScottFilterCUSLAlgebra.seg` resolves the difference between the
  explicit and canonical small presentations of `T(K(D))`. It gives
  `K(D)` an algebra for `T`, obtains the unique algebra morphism from
  the initial CUSL solution into `K(D)`, and extends its embedding to
  ideal domains. It proves that coverage of every old compact by a
  finite-stage image would make the compact algebra map an isomorphism.
  It also proves that this coverage condition is equivalent to
  surjectivity of the canonical embedding, using compact stage
  representation in the reverse direction. `BasisReduction` reduces
  coverage to the old principal-filter basis indexed by `Domain.K`.
  Bottom is covered at stage zero, and `JoinClosure` proves that
  covered compatible compacts have a covered join. These proofs use
  intrinsic compact representation and no numerical token rank.
  `BasisMeet` identifies the join of two compatible principal filters
  with the principal filter of their consistent meet, so the meet
  constructor is covered whenever its two inputs are covered.
  The coverage hypothesis is explicit and has not been proved.

This gives a checked finite-stage initial algebra and fixed-point
equation without assigning ranks to raw tokens. It also gives semantic
Pi-payload injectivity in this new domain. No existing filter-model
rank module has been deleted.

## What can be removed from the Pi-injectivity route

The table describes a possible *replacement*, not a deletion already
performed. The current filter model and its independent logical relation
still compile with the old modules.

| Current layer | Stage-based replacement | Scope |
| --- | --- | --- |
| `CorrectedRank.seg` and the `Representative`/`Observation` records in `CorrectedStages.seg` | Use the stage index of an intrinsic compact; use `CompactRepresentation` and `CompactObservation` for compact observations. | Likely removable from the independent route once the relevant domain is identified with a CUSL-chain limit. |
| `CorrectedStages.seg` as a construction of `q_n` from token rank | Use the projections `e_n p_n` of the EP limit. Exhaustion and deflation then follow from the limit. | Replaceable, but the old stage zero contains bottom and `U`, whereas the new initial chain starts with one point and its first image already contains both `U` and a Pi point. A cofinal stage comparison is needed; a simple index shift will not suffice. |
| The rank bookkeeping in `RankProjection.seg` | Prove equations for the EP projections from the functor's stage comparison maps. | The generic projection laws are available. The application and Pi component equations are still specific proof obligations. |
| Structural inversion of raw tokens merely to show that an observation has a bounded-rank representative | Use compact stage representation and stage observation. | This is the clearest saving; raw-token equivalence need not preserve a numerical rank. |
| `StageFusion.seg`, `StageInterpolation.seg`, and `StageComparison.seg` | Possibly avoid their comparison of two finite approximant systems if the CUSL chain is the sole approximant system. | These modules are already absent from `IndependentLogicalRelationCheck.seg`; removing them would not shorten that check. |

## What remains necessary

- **Identification with the existing domain.** The generic ideal
  completion of each added branch now has a checked explicit shape,
  and the two nested shapes have been flattened with the precise
  head compatibility conditions of the constructive coalesced sum.
  The object-level order isomorphism with `Sum.RHS` and the resulting
  EP isomorphism with the old filter domain are checked. What remains
  is to prove that this comparison respects the recursive algebra
  structure and application, and to relate it to the chain projections.
- **A comparison with the existing filter domain.** Categorical
  initiality and the object equation now give a canonical algebra
  embedding from the new solution into the compacts of `Domain.D`.
  Surjectivity reduces to `ScottFilterCUSLAlgebra.StageCoverage`: every
  old compact must be the image of an element of some finite CUSL
  stage. This remains unproved. The new projections also have not been
  compared with the current `q_n`. These are the remaining bridges
  before deleting any module used by
  `IndependentLogicalRelationCheck.seg`.
- **Finite function information.** Compact maps still require finite
  compatible step graphs. Stage recursion does not eliminate that
  finite construction; it can make it the canonical finite presentation.
- **The semantic clauses.** The Pi head must expose its domain and
  family, and application must factor through the appropriate stage.
  The domain equation supplies components, but these compatibility
  properties still need proofs. The logical relation and its fundamental
  lemma still require recursion over semantic depth and derivations.
- **The final syntactic conclusion.** The compact observation
  corresponding to `Pi(bottom,bottom)` must still lead, through the
  logical relation, to equality of the two Pi components. A domain
  isomorphism alone does not imply syntactic injectivity.

`Types.seg`, `Consistency.seg`, `Parts.seg`, and `Sum.seg` belong to the
current filter presentation. A fully stage-based replacement might make
some of their domain-construction uses unnecessary. Their roles in
semantics, typing, and the final inversion argument must be audited
separately; the present result does not eliminate them.

## Next proof boundary

The object-level EP isomorphism `D ≅ Idl(T(K(D)))` and the induced
algebra embedding of the initial solution into `K(D)` are checked.
The next step is a rank-free proof of `StageCoverage` for old compact
filters. `BasisReduction` reduces this to the principal filters.
Bottom and the consistent-meet case are checked, leaving the universe,
Pi, and function constructors as the substantive cases. Their proofs
must show that the algebra map sends the corresponding new branches
to the old filter constructors. This is the precise surjectivity
obligation; the checked `IfCovered` theorem turns it into a CUSL
isomorphism. Application and
the projections must then be compared with the old semantics before
the independent logical relation can use the new stages. Only after
that bridge is checked can `CorrectedRank`,
`CorrectedStages`, and `RankProjection` be removed from the independent
Pi-injectivity import graph. The compact-induction theorem already
supplies the finite-observation part of this bridge.

The distinction between a stage compact and a syntactic representative
is essential: the latter's rank is not invariant under token
equivalence. The stage construction removes this artifact rather than
proving false rank invariance.
