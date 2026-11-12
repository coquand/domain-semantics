# A domain-theoretic programme for the logical relation

This programme concerns the ordinary Scott filter model of `paper1.pdf`,
not the newly constructed stable reflexive domain. The aim is to explain
the logical relation through compact observation, admissibility and the
recursive domain equation, while preserving the syntactic information
needed for definitional inversion.

The work has two distinct objectives:

1. Present the existing compact logical relation as an admissible relation
   on arbitrary domain elements, with a stage-free adequacy theorem.
2. Construct the relation independently from the domain equation and
   minimality, then compare it with the existing compact relation.

The first objective does not establish the second. In particular, hiding
fuel behind a definition is not a new existence proof.

## 1. Compact predicates and their admissible extension

Let `D` be a Scott domain with small compact basis `beta : B -> D`.
For a small proposition-valued predicate `R` on `B`, define

    Extend(R)(x) = forall b : B, beta(b) <= x -> R(b).

Prove the following without any assumptions about constructors or typing:

- `Extend(R)` is proposition-valued and downward closed.
- It preserves directed suprema as conjunctions:

      Extend(R)(sup_i x_i) <-> forall i, Extend(R)(x_i).

- If `R` is downward closed along the basis order, then

      Extend(R)(beta(b)) <-> R(b).

- If `Q : D -> Prop` is downward closed and closed under small directed
  suprema, then

      Q(x) <-> Extend(Q o beta)(x).

The last statement proves uniqueness of the admissible extension and
independence of a choice of basis. Bottom membership is an extra condition,
not a consequence of directed closure alone. Use "admissible" here to mean
directed-supremum-closed; specify strictness separately when bottom is needed.

Proof of directed closure: a compact basis observation below a directed
supremum lies below one family member. Eliminate that mere witness into
the proposition `R(b)`. Reconstruction uses the directed basis of `x`.

## 2. Instantiate the construction with the existing logical relation

`vendor/RelC.seg` already has a convenient interface in a fixed context:

    TyR(c; A,A')
    TmR(u; T,M,M').

The term relation has no separate semantic type-witness argument. Its
typing hypotheses occur in the laws and adequacy theorem. The internal
construction still uses fuel and proves fuel independence.

For each syntactic tuple, use the compact predicates

    Rty(k) = || TyR(k.token; A,A') ||
    Rtm(k) = || TmR(k.token; T,M,M') ||.

Here `||-||` is propositional truncation. The raw relations contain
reduction witnesses and derivations and are not assumed to be propositions.
The domain relations therefore assert a **mere witness for each compact
observation**, not a simultaneous choice of all witnesses:

    forall k, || R(k) ||

must not be replaced by `|| forall k, R(k) ||`.

Use `AdeqBase.cmono-ty` and `cmono-tm` to prove basis-order monotonicity.
Remember that token `Le` is opposite to the domain information order.
Prove exact recovery of the truncated relation on principal compacts,
strictness at bottom, directed closure, and invariance under equivalent
compact presentations. Also compare basis quantification with the simpler
filter-membership formulation over all tokens.

## 3. Lift adequacy to whole domain elements

For related substitutions `sigma,sigma'` and a fitting environment `rho`,
prove that the reflected denotation of a term satisfies the new domain
relation at the two substituted syntactic types. Obtain the type relation
for universe-typed terms as well.

There is an essential intermediate argument. An arbitrary compact
observation of a well-typed denotation need not itself have a compact
typing derivation. `Sound.HasTy` supplies a larger typed observation with
a classifier observed in the type denotation. Apply existing adequacy at
that typed observation and lower the result using compact monotonicity.
Eliminate reflected membership only into truncated relation witnesses.

This is a transport of the existing adequacy proof, not an independent
proof of adequacy. It should expose a stage-free statement:

    interpretation sends related substitutions to related results.

The existing related-substitution interface may initially remain as a
hypothesis; replacing it by a domain-level interface is a later theorem.

## 4. Constructor equations and application

Establish unfolding laws for the new relation in terms of the actual
domain constructors. These laws must retain:

- the universe head observation;
- typed head reduction (including conversion, without assuming subject
  reduction);
- the syntactic equalities of both components in a Pi observation;
- argument conversion and the self/cross application comparisons of the
  existing relation.

The observation `Pi(bottom,bottom)` must still extract component
equalities. A relation that records only equal denotations, or only
reductions to Pi heads, is insufficient for the paper's injectivity proof.

The function clause should be presented as preservation of related
arguments. The compact-step theorem should handle its finite-observation
proof. Do not assume that testing an arbitrarily chosen finite graph is
equivalent to the extensional clause: prove presentation independence and
the required approximation laws.

There is an additional constructive issue here: pointwise truncation does
not automatically commute with universal quantification in the function
clause. Extracting consequences from a truncated compact witness is valid;
assembling a truncated proof-relevant function from pointwise mere witnesses
may require choice. Record directional laws separately until equivalence
has actually been established. If needed, define proposition-valued clauses
directly and prove only the appropriate comparison to the raw relation.

### Checked application characterisation

For a fixed context and syntactic tuple `(T,M,M')`, the implementation now
distinguishes three conditions on a domain element `f`:

    Uniform(f) = forall k, beta(k) <= f -> || FunC(Can,k; T,M,M') ||
    Pointwise(f) = forall k, beta(k) <= f ->
                    forall test at k, || AppC(Can,test) ||
    Extensional(f) = preservation of related domain arguments.

A test includes a reduction `T ->* Pi(A,B)`, an arrow selection of `k`,
and a consistent argument token carrying a syntactic conversion derivation
and a raw compact term-relation witness. Extensional preservation instead
uses an arbitrary `x : D` related to `N,N'` at `A`, with the same conversion
derivation. Its conclusions at `eval(f,x)` and type `B[N]` are all three:

    M N  ~ M N'       M' N ~ M' N'       M N ~ M' N'.

The following implications/equivalences are checked:

    Term(f; T,M,M') <-> Type(f; M,M') and Uniform(f)
    Uniform(f) -> Pointwise(f)
    Pointwise(f) <-> Extensional(f)
    Extensional(f) <-> preservation on related principal compacts.

The last equivalence follows from a general theorem for continuous maps
and lower admissible predicates (`DomainPredicateMaps.Preservation`).
Pullback along a continuous map also preserves lower admissibility.
Although `Extensional` quantifies over the large domain, its equivalent
compact-test and pointwise formulations live in the small universe.
This supplies a small representative without a resizing axiom.

For the reverse implication from extensional preservation to pointwise
compact tests, a selection from a proper token has a proper input token.
Its consistency is supplied by the argument data, so its principal filter
is a domain element. Principal recovery gives a related argument; applying
the extensional clause and observing the output supplies the three mere
application witnesses. They combine using only finite products of
truncations. Conversely, a proper cover of a function observation supplies
an arrow selection; tokenwise relatedness supplies the argument witness,
and compact monotonicity lowers the result to the requested output.

What is **not** proved is a converse `Pointwise -> Uniform`, even with the
type component available. This would assemble a single proof-relevant
function covering all tests at a compact observation from pointwise mere
outputs. The exact unfolding above isolates this remaining obligation; it
does not show that such assembly is impossible for these particular
relations. None of the checked application laws uses the old adequacy
theorem, but their compact relations still come from `RelC`.

## 5. Independent construction by an invariant relation

The relation operator has mixed variance. Schematically,

    Arrow(R,S)(f,M,M') =
      forall (v,N,N') related by R,
        (f(v), M N, M' N') related by S.

It is contravariant in `R` and covariant in `S`. Thus the diagonal
`R -> Arrow(R,R)` is not a monotone operator to which ordinary Kleene
iteration applies.

Investigate a Pitts-style invariant-relation theorem:

1. Separate positive and negative occurrences of the mutually defined
   type and term relations.
2. Specify the class of relations and its completeness/admissibility
   properties, with the present universe and small-index conventions.
3. Prove that the constructor action respects this structure and typed
   reduction closure.
4. Connect `Minimal.identity-fixed` and `Minimal.Least.least` to the exact
   minimal-invariant hypothesis needed by the relation theorem.
5. Construct the invariant relation and its reasoning principle.
6. Compare its compact restriction with the existing relation.

No complete lattice of all large predicates, powerset resizing, classical
principle, or simultaneous choice is available without justification.
The existing minimality theorem is a starting point, not a checked
instantiation of Pitts's theorem.

An alternative constructive implementation is compatible relations along
the domain approximation chain, followed by an admissible limit. Its
compatibility proof must address contravariant input occurrences. An
arbitrary solution of a domain equation is not enough; the recursive
construction/minimality matters.

### Checked independent function and family constructors

The first constructor components now take arbitrary supplied lower
admissible predicates. They do not use `RelC`, fuel, or adequacy.
`ScottPredicates` supplies small intersections, conjunctions, and a small
basis presentation of predicate inclusion, equivalent to pointwise
inclusion on the domain.

`DomainPredicateArrow` defines

    Arrow(R,S)(f) = forall k : K,
      R(beta(k)) -> S(eval(f,beta(k))).

It proves equivalence to preservation on all domain arguments, lower
admissibility in `f`, and strictness when `S` contains bottom. Continuity of
application in its function parameter is supplied by `ApplicationParameter`.
The admissibility proof writes the clause as a small intersection of
conditional pullbacks. Its checked variance law is

    R' <= R, S <= S'  ==>  Arrow(R,S) <= Arrow(R',S').

`LogicalRelationClauses` instantiates these constructions with syntax.
Its function tests retain the reduction `T ->* Pi(A,B)` and a derivation
of `N = N' : A`. Its family tests retain that argument conversion and use
the three output type relations

    B[N] ~ B[N']       B'[N] ~ B'[N']       B[N] ~ B'[N'].

Both constructors have small predicate values, equivalence to testing all
domain arguments, lower admissibility, strictness under strict output
relations, and explicit mixed-variance laws. The term half of the
mutual operator is also defined:

    TermStep(Rminus,Rplus,TypesPlus; T,M,M') =
      TypesPlus(M,M') and Functions(Rminus,Rplus; T,M,M').

Its mixed variance is checked. This defines a constructor on supplied
relations; it does not yet construct an invariant relation.

The separate `DomainRelationClauseComparison` instantiates the new clauses
with the existing domain relation. It proves equivalence to the pointwise
compact clauses for both functions and dependent families. The old term
relation maps into `TermStep` at these arguments; a reverse implication is
not asserted. Uniform compact family witnesses imply the family clause,
but the reverse assembly of uniform witnesses remains open, as for functions.

`DomainRelationPi` connects this family comparison to actual Pi observations.
For literal products `Pi(A,B), Pi(A',B')` related at `X`, and a positive Pi
head of `X`, its extracted domain and family components satisfy:

    || A = A' : U  and  B = B' : U in context Delta,A ||,
    Type(domain(X); A,A'),
    Families(Term,Type; A,B,B')(family(X)).

Thus the family clause retains the syntactic information needed by the
paper. This last theorem is a forward comparison using `RelC` and its
head-reduction laws, not a new independent inversion proof.

### Checked independent type constructor and mutual operator

`LogicalRelationTypeClause` now constructs the type clause from an
independent negative term relation and positive type relation. It is small,
strict, downward closed and admissible, with the required mixed variance.
It retains universe reductions, Pi reductions, syntactic equality of both
Pi components, related domain components, and the dependent-family clause.

The admissibility proof uses a reformulation of the existential Pi data.
Let a head shape be `((A,B),(A',B'))`. Its evidence consists of reductions
of `T,T'` to these products and the two syntactic component equalities.
`LogicalTypeHeads` proves that any two evidenced head shapes agree, using
determinism of head reduction. Proofs of the evidence itself need not agree.
For any proposition-valued condition `Q` on shapes, it proves

    || exists s, Evidence(s) and Q(s) ||
      <-> || exists s, Evidence(s) ||
          and forall evidenced heads e, Q(shape(e)).

The reverse implication uses one mere head witness; the forward implication
transports `Q` along uniqueness of the shape. This is not an interchange
of arbitrary existential and universal quantifiers and needs no choice.

`DomainPredicateObservations` proves that `In(X,t) -> P` is lower
admissible for every small proposition `P`. It also identifies the
following compact conditions with the predicates on the extracted Pi
components whenever a Pi head is present:

    forall k, In(X,pi(k,om)) -> R(beta(k)),
    forall k, In(X,pi(om,k)) -> S(beta(k)).

The type clause is a small intersection of these observation tests:
universe observation requires mere universe reductions; a positive Pi
head requires mere evidenced heads; every evidenced head supplies the
two component predicates. `Step.equation` proves equivalence to the
natural formulation in which a positive Pi head supplies a mere tuple
containing reducts, syntactic equalities, and related domain/family
components. Admissibility thus follows from observation tests rather than
from choosing reducts along a directed family.

`LogicalRelationOperator` combines this type clause with the term clause
into `operator(Rminus,Rplus)`. It proves mixed variance and preservation
of strictness when the positive relations are strict. `Equations(R)` is
a small interface for both inclusions `R <-> operator(R,R)`, and the
`Invariant` module derives the natural folding and unfolding rules from
that interface. An independent inhabitant of this interface is now constructed below.

The operator's `Inversion` module needs only the forward inclusion
`R <= operator(R,R)`. It derives universe head reductions and mere
syntactic Pi-component equality from positive observations, without using
`RelC` or its laws. This is an independent conditional inversion principle. The new invariant
supplies its unfolding hypothesis; Section 6 now connects it to the
independent fundamental lemma and derives syntactic Pi inversion.

`DomainRelationTypeComparison` checks the full forward comparison

    R_old <= operator(R_old,R_old)

for arbitrary syntactic types and terms. Head determinism aligns the old
Pi witnesses with each tested shape. Only this comparison uses the old
logical-relation laws; the new constructor and operator do not. The
reverse inclusion, and the uniform-witness assembly issue, remain open.

### Checked independent finite-depth invariant

`LogicalRelationLocality`, `LogicalRelationStages`,
`CompatiblePredicateLimit` and `IndependentLogicalRelation` now construct
an independent strict lower admissible invariant and prove its uniqueness
among strict lower admissible solutions. No old logical relation or
adequacy theorem is used.

Write `q_d` for `CorrectedStages.approximate d`. The construction uses
agreement of predicates on elements fixed by `q_d`, rather than a
monotone iteration of the diagonal operator. Its crucial locality lemma is:

    P' -> P and Q -> Q' on depth-d elements
      ==> Arrow(P,Q)(f) -> Arrow(P',Q')(f)

whenever `f` has depth-d input/output support. Given a related arbitrary
argument `x`, lower its input evidence to `q_d(x)`, use the assumed
negative inclusion there, and test the original arrow at `q_d(x)`.
`RankProjection.AtApplication.factor` identifies its result with `f(x)`;
`range` puts the result in depth d, where the positive inclusion applies.
Thus the negative tests require no global input inclusion or choice.
`RankProjection.FixedInput` supplies this support for depth-(d+1)
functions and extracted Pi families, and fixes extracted Pi domains at d.

Define the type-before-term action by

    advance(R).ty = TypeStep(R.tm, R.ty)
    advance(R).tm = advance(R).ty and Functions(R.tm, R.tm).

Agreement of R and S at depth d implies agreement of `advance(R)` and
`advance(S)` at depth d+1. The freshly constructed type component is
essential: the original mutual operator's term component reads an input
type relation at the same depth and therefore does not satisfy this
particular one-step contractivity statement directly.

At depth zero, elements lie below the universe element, have no Pi head,
and their applications are bottom. Set both initial relations to the
universe-observation test (for terms, on the pair of terms). This is strict
and agrees at depth zero with `advance(R)` for any strict R. Recursion

    R_0 = initial
    R_(d+1) = advance(R_d)

therefore gives strict lower admissible relations with checked compatibility

    d <= e, q_d(x) = x  ==>  R_d(x) <-> R_e(x).

The limit is the small, countable intersection

    R_infinity(x) = forall d, R_d(q_d(x)),

separately for every syntactic type/term tuple. Continuous pullback and
intersection give lower admissibility; strictness is inherited. The
compatible-predicate limit theorem proves exact recovery

    q_d(x) = x  ==>  R_infinity(x) <-> R_d(x).

For this theorem, if e >= d use compatibility at x and lower to q_e(x);
if e <= d lower to q_e(x) first and use compatibility there. Natural-number
comparison is constructive. No witnesses are chosen simultaneously.

Contractivity and recovery give both inclusions between `R_infinity` and
`advance(R_infinity)` on each finite stage. Every principal compact is
fixed at its corrected token rank, so these yield small basis inclusions
and hence inclusions on all domain elements. The type equation then
translates the term equation from `advance` to the original mutual
`operator`. `IndependentLogicalRelation.At.equations` is the resulting
inhabitant of `LogicalRelationOperator.At.Equations`; its `Invariant` and
`Inversion` modules expose folding, unfolding and syntactic head inversion.

`Unique` proves any other strict invariant agrees with R_d at depth d,
by induction using the same base and contractivity arguments. Compact
reconstruction gives equivalence with `R_infinity`. Strictness is an
explicit hypothesis of this uniqueness theorem.

`IndependentLogicalRelationCheck.seg` checks this construction in a
separate process with the same ambient univalence/replacement parameters
and without importing `RelC`, `LawsC`, any `Adeq*` module, `Adequacy`,
`Consequences`, `SubjRed`, or the old domain logical relation. Basic token
typing, soundness and properness infrastructure remains available. This
separate driver is now run by `check.py` as well as `All.seg`.

### Possible transfer to the stable construction

The finite-depth argument should also apply to a stable model with suitable
constructor observations and the corresponding stage-locality laws. The
existing `RigidRankStages` gives hereditary rank, finite capture of compacts
and exhaustion; `ReflexiveSyntax.Function.Coordinate` gives the one-stage
link between represented functions and application. These could simplify
the rank/support part, replacing explicit token and finite-graph arguments.
This is a proposed transfer, not a checked stable invariant construction.

The present stable universe represents codes as rigid projectors. It does
not yet supply the universe/Pi head observations and component extraction
used by this type clause and its inversion principle. Those obligations,
the negative argument restriction, and the type-before-term dependency
remain. The stable rank machinery is promising; a simpler complete proof
of syntactic inversion has not yet been established.

## 6. Fundamental lemma and inversion

After the independent relation is available, prove preservation under
variables, universe, Pi, annotated lambda, application, conversion and
typed function extensionality. Extend the result to related substitutions.
Recover the compact fundamental lemma by observation, and derive Pi
injectivity by the `Pi(bottom,bottom)` test.

Do not use adequacy or Pi injectivity from the old relation in this new
fundamental proof. They may be used to validate a comparison theorem,
but doing so is not an independent derivation.

### Checked independent typed laws

`IndependentRelationReduction` establishes head-reduction transport,
term expansion, and classifier head-reduction invariance.
`IndependentRelationDiagonal` establishes left diagonal closure first at
finite depth and then on the invariant. `IndependentRelationRules` gives
universe, Pi and lambda introductions and application elimination directly
from the invariant equations. The Pi and lambda introductions have explicit
family/body premises. Their fundamental-lemma instances for arbitrary
fitting environments are now established below.

The five typed laws are now checked independently:

    Type(p U A; T,T')                         ==> Type(p U A; T',T)
    Type(p U A; T,V), Type(p U A; V,W)         ==> Type(p U A; T,W)
    Term(p A X; T,M,N)                        ==> Term(p A X; T,N,M)
    Term(p A X; T,M,N), Term(p A X; T,N,O)     ==> Term(p A X; T,M,O)
    Type(p U A; T,T'), Term(p A X; T,M,N)      ==> Term(p A X; T',M,N).

`IndependentRelationTypedSteps`, `IndependentRelationTypedTerms`, and
`IndependentRelationTypedStages` prove these mutually by relation depth.
At each successor, the new type laws precede the new term laws. For a
function projector, restrict a tested argument z to `p A z`; projector
idempotence identifies the resulting outputs. `ProjectorPredicateCases`
eliminates the projector into lower admissible predicates, while
`ProjectorFunctionSupport` isolates this restriction argument.

Passing to the invariant requires care: neither arbitrary lower
approximations nor rank projections of typed elements are assumed typed.
`IndependentRelationTypedLaws.Cover` instead finds a typed compact cover
and a proper compact classifier, chooses a common rank bound for both,
and uses exact finite-stage agreement there. Lowering and admissible
reconstruction give the five laws on the whole projected element.
`IndependentRelationRawLaws` then uses semantic typing to transfer them
to raw denotations. This uses soundness, not old adequacy.

### Fundamental statement and completed cases

`IndependentFundamentalRules.At.Fundamental` asserts that, for every fitting
environment rho and independently related substitutions s,s', every proper
compact observation of `sem M rho` relates `M[s]` to `N[s']` at **both**
`A[s]` and `A[s']`. Raw observation relatedness is equivalent to the domain
predicate on reflected consistent regular filters.

The following cases are checked:

- Variable and universe; beta using the body and argument induction hypotheses.
- Symmetry, transitivity and conversion, including symmetry of related
  substitutions over fitting environments in well-formed contexts.
- Instantiation under a binder, preserving both substituted result types.
- Application, including function and argument congruence, at both result
  types. The right type follows by instantiating the codomain hypothesis
  and applying the independent conversion law.
- Pi formation and equality, including both self comparisons and the cross
  comparison in the dependent family clause.
- Annotated lambda and typed function extensionality, at both substituted
  Pi types.

`IndependentFundamental.At.fundamental` now assembles all constructors of
`Der` in one derivation induction. Its `typing` and `equality` interfaces
inhabit the full fundamental statement above. The elementary cases remain
in `IndependentFundamentalRules`, `IndependentFundamentalStructural`,
`IndependentFundamentalSubstitution`, and `IndependentFundamentalApplication`.

The shared bridge in `IndependentFundamentalBinder` restricts an arbitrary
argument x to the raw semantic projection `projF (sem A rho) (raw x)`.
This projection is semantically typed and hence gives a fitting extended
environment. Lower closure supplies the left argument relation; the
independent typed conversion law supplies its right-type version. The
body induction hypothesis applies to the extended related substitutions.
Finite selection from semantic binder observations factors evaluation
through this restricted environment. Admissible reconstruction then lifts
all observed outputs to the domain predicate, eliminating truncations only
into propositions.

The bridge also obtains all three body comparisons. The left self
comparison uses diagonal substitutions. The cross comparisons at `(N,N)`
and `(N,N')`, combined by typed symmetry and transitivity on the body
denotation, give the right self comparison at the same left result type.
No pointwise witnesses are assembled into a uniform proof-relevant function.

`IndependentFundamentalPi` uses these outputs for the family clause and
retains the syntactic component equalities supplied by substitution and
cross-substitution. `IndependentFundamentalFunctions` folds the common
function clause after syntactic expansion. `IndependentFundamentalLambda`
specializes it using beta. `IndependentFundamentalExtensionality` uses
semantic eta, proved from soundness, and the pointwise body induction
hypothesis. Reversing substitutions and applying independent typed symmetry
gives the right substituted Pi type; no inversion of a syntactic Pi
equality is needed.

`IndependentAdequacy.At.Equality` gives the relation on the whole reflected
denotation at both substituted types, its type component, and compact
observation recovery. `IndependentInversion.pi-injectivity` then derives

    G |- Pi A B = Pi A' B' : T
      ==> || (G |- A = A' : U) and (G,A |- B = B' : U) ||.

The bottom environment fits every well-formed context, and its identity
substitution is independently related by strictness. The literal Pi
semantics contains `Pi(bottom,bottom)` there. Applying the fundamental
lemma and independent head inversion to that observation gives the mere
pair of component equality derivations. This does not remove propositional
truncation from the conclusion. No old adequacy or syntactic Pi injectivity
is used in any of these proofs.

## Validation and implementation status

Implementation updated on 12 November 2026. The combined check reports
**9,414 declarations, zero failures, 40 frozen dependency hashes verified**
with `python3 UNIT/check.py`. The separate independence check reports
**4,909 declarations, zero failures**, including all the new typed laws,
the full fundamental lemma and its inversion corollary with their
104-module dependency closure.

| File | Checked results |
| --- | --- |
| [ScottPredicates.seg](ScottPredicates.seg) | Small lower admissible predicates; compact-observation extension; directed-supremum equivalence; recovery on basis elements; uniqueness and reconstruction; small predicate inclusion, intersections and conjunctions. |
| [DomainLogicalRelation.seg](DomainLogicalRelation.seg) | Extension of the actual compact type/term relations; bottom; principal recovery; equivalent presentations; equivalence with all-token membership; reconstruction from the corrected rank approximations. |
| [DomainAdequacy.seg](DomainAdequacy.seg) | Whole-denotation term adequacy at both substituted types, and type adequacy for universe equality, transported using typed covers and compact monotonicity. |
| [DomainRelationInversion.seg](DomainRelationInversion.seg) | A universe observation gives mere head reductions; a `Pi(bottom,bottom)` observation relating literal products gives mere syntactic domain/codomain equality derivations. |
| [DomainPredicateMaps.seg](DomainPredicateMaps.seg) | Continuous pullbacks of lower admissible predicates; preservation on all domain elements iff preservation on principal compacts. |
| [DomainRelationApplication.seg](DomainRelationApplication.seg) | Application preserves all three self/cross relations; finite assembly of output observations; compact-argument testing equivalence. |
| [DomainRelationFunctions.seg](DomainRelationFunctions.seg) | Exact uniform unfolding of the extended term relation; uniform-to-pointwise comparison; pointwise clauses equivalent to extensional preservation and to small compact tests. |
| [ApplicationParameter.seg](ApplicationParameter.seg) | Application is continuous in the function parameter. |
| [DomainPredicateArrow.seg](DomainPredicateArrow.seg) | Independent small function predicate; arbitrary-argument equivalence, lower admissibility, conditional strictness, and mixed variance. |
| [LogicalRelationClauses.seg](LogicalRelationClauses.seg) | Independent function and dependent-family clauses retaining all self/cross comparisons; admissibility and mixed variance; the term half of the mutual operator. |
| [DomainRelationClauseComparison.seg](DomainRelationClauseComparison.seg) | Instantiation with the existing relation; equivalence with pointwise compact function/family clauses; forward comparison with the term operator. |
| [DomainRelationPi.seg](DomainRelationPi.seg) | Literal-product Pi observations yield syntactic component equalities, related domain components, and the new family clause on extracted family components. |
| [DomainPredicateObservations.seg](DomainPredicateObservations.seg) | Lower admissible observation tests; compact Pi-component tests equivalent to predicates on the extracted domain and family. |
| [LogicalTypeHeads.seg](LogicalTypeHeads.seg) | Unique syntactic head shapes; coherent existential/universal reformulation; recovery of literal-product component equalities. |
| [LogicalRelationTypeClause.seg](LogicalRelationTypeClause.seg) | Independent strict lower admissible type constructor; natural existential unfolding; mixed variance. |
| [LogicalRelationOperator.seg](LogicalRelationOperator.seg) | Complete mutual operator, mixed variance, strictness preservation, invariant interface, conditional folding/unfolding and inversion. |
| [LogicalRelationLocality.seg](LogicalRelationLocality.seg) | Local mixed-variance laws on fixed rank stages; negative argument restriction; type-before-term contractivity. |
| [LogicalRelationStages.seg](LogicalRelationStages.seg) | Independent strict finite-depth relations; depth-zero analysis; compatibility on all earlier stages. |
| [CompatiblePredicateLimit.seg](CompatiblePredicateLimit.seg) | Countable admissible limit of projected predicates; exact recovery at each finite stage. |
| [IndependentLogicalRelation.seg](IndependentLogicalRelation.seg) | Independent invariant existence, both mutual equations, strictness, folding/unfolding, inversion, and uniqueness among strict invariants. |
| [IndependentRelationReduction.seg](IndependentRelationReduction.seg), [IndependentRelationDiagonal.seg](IndependentRelationDiagonal.seg) | Head-reduction transport, term expansion, classifier invariance, and left diagonal closure. |
| [IndependentRelationRules.seg](IndependentRelationRules.seg), [IndependentRelationSubstitutions.seg](IndependentRelationSubstitutions.seg) | Invariant introduction/elimination rules; raw reflection; independent related substitutions and their extension. |
| [ProjectorPredicateCases.seg](ProjectorPredicateCases.seg), [ProjectorFunctionSupport.seg](ProjectorFunctionSupport.seg) | Admissible elimination of the semantic projector; argument restriction and idempotent function support. |
| [IndependentRelationClauseLaws.seg](IndependentRelationClauseLaws.seg), [IndependentRelationPiData.seg](IndependentRelationPiData.seg) | Generic function-clause laws and exact Pi-component witnesses. |
| [IndependentRelationTypedSteps.seg](IndependentRelationTypedSteps.seg), [IndependentRelationTypedTerms.seg](IndependentRelationTypedTerms.seg), [IndependentRelationTypedStages.seg](IndependentRelationTypedStages.seg) | Mutual finite-depth symmetry, transitivity and conversion, with types established before terms. |
| [IndependentRelationTypedLaws.seg](IndependentRelationTypedLaws.seg), [IndependentRelationRawLaws.seg](IndependentRelationRawLaws.seg) | Typed compact-cover lifting to the invariant, then to raw typed denotations. |
| [IndependentFundamentalRules.seg](IndependentFundamentalRules.seg), [IndependentFundamentalStructural.seg](IndependentFundamentalStructural.seg) | Fundamental statement; variable, universe, beta, symmetry, transitivity and conversion cases. |
| [IndependentFundamentalSubstitution.seg](IndependentFundamentalSubstitution.seg), [IndependentFundamentalApplication.seg](IndependentFundamentalApplication.seg) | Binder instantiation and application at both substituted dependent result types. |
| [IndependentFundamentalBinder.seg](IndependentFundamentalBinder.seg) | Typed argument restriction, fitting extensions, three body comparisons, and admissible lifting of binder evaluation. |
| [IndependentFundamentalPi.seg](IndependentFundamentalPi.seg) | Pi formation and equality over arbitrary fitting environments and related substitutions. |
| [IndependentFundamentalFunctions.seg](IndependentFundamentalFunctions.seg), [IndependentFundamentalLambda.seg](IndependentFundamentalLambda.seg), [IndependentFundamentalExtensionality.seg](IndependentFundamentalExtensionality.seg) | Common function clause; annotated lambda and typed function extensionality at both substituted Pi types. |
| [IndependentFundamental.seg](IndependentFundamental.seg) | Complete derivation induction, with typing and equality interfaces. |
| [IndependentAdequacy.seg](IndependentAdequacy.seg), [IndependentInversion.seg](IndependentInversion.seg) | Whole-denotation adequacy, compact recovery, and mere syntactic Pi-component equality derived independently. |
| [IndependentLogicalRelationCheck.seg](IndependentLogicalRelationCheck.seg) | Standalone check with the old relation and adequacy modules out of scope. |
| [DomainRelationTypeComparison.seg](DomainRelationTypeComparison.seg) | The existing relation maps into the independent mutual operator, including arbitrary syntactic type expressions. |

Sections 1--3 are implemented with the existing related-substitution
interface. The inversion results also check that the proposition-valued
extension retains the information essential to the application.
All new proof modules are imported by `All.seg`; the standalone check has
its own driver. Vendor files and the global
univalence/replacement interface are unchanged.

Section 4 now has the application and family characterisations above,
including the forward Pi-component theorem. Full constructor equations
and assembly of uniform witnesses from pointwise data remain open.
Section 5 now has independent invariant existence and uniqueness among
strict lower admissible solutions, constructed using compatible finite-depth
relations. Both equations of the original mutual operator hold. Inversion
is instantiated with this new relation and connected to the completed
independent fundamental lemma in Section 6. Whole-denotation and compact
adequacy, and mere syntactic Pi inversion, are checked independently.

The function and family tests retain syntactic argument conversion, and
the term relation has no separate semantic type witness. Typed argument
restriction now connects arbitrary-argument tests to the body hypotheses
on fitting environments. The comparison with the old uniform compact
relation, including the reverse witness-assembly issue, remains separate
from the completed independent construction and fundamental lemma. Transfer
to the stable reflexive-domain construction also remains a separate task.

## Sources

- [Scott-domain account](scott-domains.tex), especially compact functions
  and finite-observation proofs.
- [The paper](../paper1.pdf), Sections 2.6--2.8.
- [Existing compact relation](vendor/RelC.seg),
  [its laws](vendor/LawsC.seg), and [adequacy](vendor/Adequacy.seg).
- [Minimality of the Scott model](Minimal.seg).
- A. M. Pitts, [Computational Adequacy via Mixed Inductive Definitions](https://www.cl.cam.ac.uk/~amp12/papers/compavm/compavm.pdf).
- A. M. Pitts, [Relational Properties of Domains](https://www.cl.cam.ac.uk/~amp12/papers/relpod/relpod.pdf).
