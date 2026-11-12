Section 2 in Unit, using intersection types and filters
=====================================================

This constructs the MLTT domain, its finitary projectors, and a bridge to
the existing Unit MIN soundness and adequacy proofs. All.seg checks 11,736
declarations, with 0 failures, using the recorded checker (2026-11-12).

Run from DOMAIN:

    python3 UNIT/check.py

Or specify another Unit checker (UNIT_CHECKER also works):

    python3 UNIT/check.py /absolute/path/to/seg

The type-checker is a compiled Haskell program. The Python script only
verifies the frozen dependency hashes and launches that checker on All.seg,
then on IndependentLogicalRelationCheck.seg in a separate process (4,909
declarations, zero failures) with the old relation and adequacy out of scope.
No external Python packages or Agda checker are needed. The Unit checker
binary itself is not bundled.

Main construction
-----------------

The central result is an order isomorphism implementing

    D = [D -> D] + Lift(D x [D -> D]) + Lift(1),

with coalesced sum, constructive lifting, and continuous functions.
This is an actual equivalence of types, using univalence for extensional
equality. D is a set, has all small directed and bounded suprema, and has
a small compact basis. Continuity can equivalently be specified by finite
character or by preservation of small directed suprema, with monotonicity.

There is also a general Scott-domain interface. For any two such domains,
the Scott-continuous function space is again a Scott domain, with pointwise
suprema and a small compact basis of finite compatible step graphs.
The filter domain instantiates this interface, and its existing continuous
maps are equivalent to the generic ones. A general Kleene least-fixed-point
theorem is checked. SCOTT.txt explains the constructive proof, universe
conventions, and why graph compatibility must test finite selections.

The embedding-projection category now supports a concrete recursive
domain equation. For any presented Scott domain A, the checked constructor
F_A(X) = A x [X -> X] acts functorially on embedding-projection pairs.
For any precategory C and endofunctor F, CategoryAlgebras constructs the
precategory of F-algebras and commuting morphisms. If C is univalent, so
is this algebra category; no continuity or colimit assumption on F is needed.
The chain of F_A from the one-point domain has a presented Scott-domain limit
mu_A, with mutually inverse continuous fold/unfold maps between
F_A(mu_A) and mu_A. The algebra (mu_A, fold) is initial: for every
presented EP algebra a : F_A(Y) -> Y, the type of EP algebra morphisms
from it to (Y,a) is contractible. The categorical isomorphism gives an
equality of unpresented domain objects by univalence. The proof uses the
universal property of presented EP-chain colimits and checked comparisons
with function space, fixed products, and the shifted chain. An abstract
initial-chain theorem is now checked for any category with an initial
object and countable-chain colimits preserved by an endofunctor. It gives
an initial algebra, inverse fold/unfold maps, and object equality in a
univalent category. The Scott EP specialization now applies to any
endofunctor preserving countable-chain colimits, with no separately
supplied colimit of its initial chain.
Here omega-continuity means preservation of existing countable-chain
colimits; the implication from continuity on ordered homs to that
preservation is not yet proved.

For the CUSL category, the missing colimits are now constructed. A chain
of CUSL embeddings is sent to a chain of presented ideal domains; the
compact elements of its EP limit form the colimit CUSL. The mediator is
obtained by ideal extension, and uniqueness follows because every compact
element of the limit is represented by a compact basis element at some
stage. The one-point CUSL is initial. Therefore every CUSL endofunctor
preserving countable-chain colimits has an initial algebra, inverse
fold/unfold maps, and an equality X = F(X). Preservation is a proposition:
the universal property of a fixed cocone is a proposition. No countable
choice is used in selecting small presentations for the ideal domains.
The categorical structure identity principle is now checked at these
universe levels: equivalent univalent categories are equal as Category
records. The proof uses univalence on the object types and fiberwise on
the hom types; functor laws identify identity and composition, while
hom-set and category laws are propositions. The CUSL--EP equivalence
therefore gives an equality of categories. Transport along this equality
makes the unpresented Scott EP category omega-cocomplete, including chains
whose stages have merely existing bases. A direct generic transfer proof
via the quasi-inverse is also checked independently.
Consequently every EP endofunctor preserving countable-chain colimits
has an initial algebra, an isomorphism, and object equality X = F(X).

The univalent category of Scott domains and embedding-projection pairs is
now equivalent to the univalent category of conditional upper semilattices
(CUSLs) and embeddings, as in paper1.pdf, Theorem 2.10. The functors take a
domain to its compact elements and a CUSL to its ideals. Both functor laws,
the two reconstruction isomorphisms and their naturality are checked. The
CUSL carrier is merely small; univalence turns this property into a unique
small presentation when ideal completion needs one. Replacement supplies
a small presentation of the compact elements of an unpresented domain.

D consists of consistent proposition-valued filters generated by proper
tokens. Proper arrows have consistent inputs; Pi families contain only
arrows. The restriction is essential: an unrestricted arrow with an
inconsistent input can carry information invisible to application. Every
typed MIN token has an order-equivalent proper representative.

The identity is a fixed point of the domain action Phi. For every strict
continuous delta with Phi(delta) <= delta, id <= delta. This is proved by
induction on proper tokens. Separately, finite-depth finitary projections
give an increasing chain starting at bottom, with supremum the identity;
their fixed-point stages form embedding-projection pairs.

Compact families containing bottom and closed under compatible joins
represent finitary projectors. Each induces a continuous, idempotent
deflation with exactly that family of compact fixed points. Every projector
with compact fixed-point density is recovered this way. Families form an
algebraic domain with a basis of finite generators; directed projector
suprema are pointwise. Projector images are Scott domains, whose compact
elements are precisely their ambient compact fixed points.

Semantic typing gives a continuous map D -> Fp(D). On consistent regular
MIN filters, its projector agrees with MIN's projF after truncation.
Well-typed denotations are fixed by their semantic type projectors, and
judgemental equality gives identity in D. Adequacy is transported to
truncated membership. MIN's original full adequacy, Pi-injectivity and
subject-reduction proofs remain checked imports.

The recursive projector equations of Section 2.4 now also hold for arbitrary
domain arguments, without extra typing hypotheses. The projector is least
among continuous binary maps satisfying their lower-bound clauses.
The explicit Phi/Kleene construction is now checked as well: its limit
is a least fixed point, agrees with the typed construction, and inherits
finitariness and normalization. SECTION24.txt gives the proof routes.
The corrected rank-stage version of Proposition 2.27 now has a direct
fixed-point proof: stage-n observations of the Kleene sequence stabilize
at P_(n+1). OperationalStages defines its stage operation by this finite
unfolding and proves compatibility without the sandwich lemma or typing
identification. StageComparison separately identifies it with the earlier
bounded-typing stage projector and transfers finitariness. PROPOSITION227.txt
gives both routes and the retained obstruction to the printed base rules.

Theorem map
-----------

New names except Proper and Regular are under All.Theory, at universe l.

  Proper.typed-rep; Regular.typed-regular
    Proper representatives of typed tokens and typed filters.
  ExtFilter.filt-ext; Domain.ext; Domain.domain-set
    Extensional identity and sethood.
  ConsStable.cons-stable
    Recover consistency from mere consistency, without choice.
  Domain.Sup; Domain.BasisD.equation; Domain.compact-principal
    Directed completeness, algebraicity and compact characterization.
  Bounded.Sup
    Bounded completeness, including the empty family.
  Continuous.Preserve.equation; Continuous.from-scott
    Finite character and directed-supremum continuity.
  ScottDomain.Scott; ScottOrder.On.order-set
    Abstract pointed Scott domains with small compact bases and small order.
  ScottDomainObjects.Domain / from-presented / same-presentation
    A domain object with merely existing small compact basis; two chosen
    bases over the same ordered, complete, pointed domain give equal objects.
    The existing ScottDomain.Scott retains a basis for calculations.
  ScottDomainObjects.complete-prop / fiber-prop / order-univalent / domain-univalent
    Completeness and the remaining domain structure add no choices over
    an order. Equality of domain objects is equivalent to order isomorphism.
    Both inverse equations are checked via the contractible total space of
    isomorphisms, independently of the later category structures.
  ScottDomainMaps.Between.Map / Triple.compose
    Continuous maps between unpresented domain objects, with identity and
    composition independent of a selected compact basis.
  ScottDomainCategories.Continuous.category / univalent
    The univalent category of Scott domains and continuous maps. Its
    categorical isomorphisms correspond to order isomorphisms.
  ScottDomainCategories.EmbeddingProjection.category / univalent
    The univalent category whose arrows are continuous embedding-projection
    pairs (e,p) with p o e = id and e o p <= id.
  ScottCUSL.CategoryUnivalence.category
    The univalent category of merely small conditional upper semilattices
    and embeddings preserving bottom and compatible joins while reflecting
    order and compatibility.
  ScottCUSLEquivalence.equivalence
    A categorical equivalence between that CUSL category and the Scott EP
    category. ScottCUSLIdeals constructs the domain of ideals with principal
    compact basis; ScottCUSLCompacts constructs the CUSL of compacts.
    ScottCUSLIdealMaps and ScottCUSLCompacts prove the two functor actions.
    ScottCUSLEquivalence.Unit and Counit give the natural reconstruction
    isomorphisms. CategoryEquivalence packages the generic quasi-inverse
    notion for univalent categories.
  CategoryInitialChain.OmegaContinuous / OmegaCocomplete / General / UnivalentGeneral
    An abstract endofunctor preserving countable-chain colimits has an
    initial algebra in an omega-cocomplete category with initial object.
    General.isomorphism proves fold/unfold inverse; Algebra.initial proves
    contractibility of the algebra-morphism type. UnivalentGeneral turns
    the solution isomorphism into object equality.
  CategoryInitialChain.ColimitProof.proposition / OmegaContinuousProof.proposition
    A fixed cocone's universal property and preservation of countable-chain
    colimits are propositions.
  CategoryEquivalenceTransport.On.object-equality / hom-equivalence
    Equivalence of univalent categories gives equality of object types
    and equivalence on each hom type.
  CategoryEquivalenceColimits.On.transported
    Generic transfer of countable-chain colimits across a categorical
    equivalence.
  CategorySIPTheorem.On.equality / ScottEPTransport.category-equality
    Categorical SIP: an equivalence of univalent categories gives equality
    of their Category records. The CUSL--EP equivalence is instantiated.
    CategorySIPFixed proves the hom-family step; CategorySIPReindex handles
    object reindexing; CategorySIPFamily proves fiberwise univalence.
  ScottCUSLInitial.initial / ScottCUSLColimit.cocomplete
    The one-point CUSL is initial; every countable chain of CUSL embeddings
    has a colimit, built from compact elements of a presented EP limit.
  ScottCUSLFixedPoint.On.equation / Algebra.initial
    A colimit-preserving CUSL endofunctor has a solution X = F(X), whose
    fold map is an initial algebra.
  ScottEPTransport.cocomplete / On.equation / On.Algebra.initial
    Transport of CUSL omega-cocompleteness along category equality gives
    unpresented EP omega-cocompleteness. A colimit-preserving endofunctor
    has an initial algebra and X = F(X).
  CategoryAlgebras.On.pre / Univalent.category
    The algebra category for any endofunctor on a precategory, and its
    univalence when the base category is univalent. An algebra isomorphism
    gives equality of both the underlying object and its structure map.
  ScottEPInitial.initial / ScottEPInitialChain.On.equation
    The one-point domain is initial in the unpresented EP category. Given
    a colimit of an endofunctor's initial chain and omega-continuity,
    univalence gives equality between the solution and its image.
  ScottEPInitialChain.WithAllColimits.Algebra.initial
    The Scott-category corollary under a supplied omega-cocompleteness
    structure for unpresented domains.
  ScottEPExponential.FunctorLaws / ScottEPProduct.FunctorLaws
    Endomap conjugation and fixed product act functorially on EP pairs.
  ScottEPLimitBasis.On.scott / ScottEPLimitCone.On.At.pair
    The coherent-sequence limit of a presented countable EP chain is a
    Scott domain, with canonical EP pairs from its stages.
  ScottEPLimitColimit.On.mediator / ConeLaw.law / Unique.equation
    The universal property of that construction as a presented EP colimit.
  ScottEPLimitExponential.On.order-iso / ScottEPLimitProduct.On.iso
    Endomap spaces and fixed products commute with these chain limits.
  ScottReflexiveFunctor.Constructor.action-composition
    Functor laws for F_A(X) = A x [X -> X].
  ScottReflexiveSolution.On.fold / unfold / fold-unfold / unfold-fold / equation
    The explicit F_A fixed-point isomorphism, both inverse equations,
    and the resulting equality
    of unpresented Scott-domain objects.
  ScottReflexiveInitial.On.algebra-law / Unique.equation / initial
    The canonical mediator is an algebra morphism; every such morphism
    equals it, and the algebra-morphism type is contractible.
  ScottMaps.Between.Pointwise.lub / complete
    Directed and bounded suprema of continuous maps are pointwise.
  ScottStepApprox.Between.Step.compact / FiniteJoin.compact
    Direct compactness of steps and their bounded finite joins.
  ScottStepApprox.Between.Approximation.equation / compact-finite
    Direct density below each continuous function and the converse compact
    characterization, without admissible-graph evaluation.
  ScottExponential.Exponential.scott / compact-graph
    D -> E is a Scott domain; its compacts are finite compatible step graphs.
  ScottFilter.scott / map-equivalence / function-scott
    The filter domain and its existing maps instantiate the general theory.
  ScottFixpoint.Kleene.equation / Below.least
    The supremum of the iterates from bottom is the least fixed point.
  Abstraction.function-space; Abstraction.beta; Abstraction.eta
    Function-shaped filters are exactly continuous maps D -> D.
  Equation.domain-equation
    Equivalence D ~ Sum.RHS, including both inverse identities.
  EquationOrder.decode-mono; EquationOrder.EncodeMono.inclusion
    Both directions preserve the order.
  Minimal.identity-fixed; Minimal.Least.least
    Fixed-point equation and minimality among strict pre-fixed maps.
  Projector.map; Projector.idempotent; Projector.At.below
    Continuous idempotent deflations from compact families.
  Projector.compact-fixed; Projector.fixed-compact
    The family is exactly the compact fixed points.
  Finitary.Compacts.reconstruction; Finitary.family-recovered
    Recovery from compact fixed points.
  ProjectorDomain.Basis.equation; ProjectorDomain.compact-finite
    Algebraicity of compact families and their finite generators.
  ProjectorDomain.Pointwise.equation
    Directed projector suprema are computed pointwise.
  FixedImage.Image.Basis.equation; FixedImage.Image.BoundedSup
    Projector images are Scott domains.
  FixedImage.Image.ambient-to-image; FixedImage.Image.image-to-ambient
    Compactness in the image agrees with ambient compactness.
  SemanticProjector.ContinuousTypes.equation
    Continuity of the interpretation of types as projectors.
  SemanticProjector.Compare.equation
    Agreement with MIN's projF.
  SemanticLaws.Generators.equation; SemanticLaws.Normalize.equation
    Typed generators need no extra closure; p(p(U,A),X) = p(A,X).
  ProjectorEquations.UniversePi.equation / FunctionClause.equation
    The universe/Pi and function clauses for arbitrary domain arguments.
  ProjectorZero
    The remaining zero cases, including data arguments to Pi projectors.
  ProjectorLeast.Least.least
    Leastness among continuous maps satisfying the recursive lower clauses.
  ProjectorFixedPoint.solution / finitary-after-least
    Existence of a least recursive solution; finitariness derived from its
    universal property, without assuming projector laws of the candidate.
  ProjectorOperator.At / Monotone.inclusion
    The explicit guarded recursive functional and its monotonicity.
  OperatorContinuity.Phi / Approximate.cover
    Continuity in both arguments and joint directed continuity in the
    binary operation and its arguments.
  KleeneProjector.equation / Below.least / identification / finitary
    The explicit Kleene least fixed point, its identification with the
    typed projector, and finitariness obtained after construction.
  KleeneProjector.normalization
    p(p(U,A),X) = p(A,X) for the Kleene-defined p.
  StageBaseObstruction.different / not-compatible
    A first-stage obstruction for a permissive extension of the printed
    typing rules. See PROPOSITION227.txt for the precise scope.
  CorrectedRank.zero-form
    The corrected stage-zero compact classes are exactly bottom and U.
  StageInterpolation.interpolate
    Two-sided bounded-rank interpolation of a typed value and its code.
  CorrectedStages.Stage.retract / Between.retract / Exhaust.equation
    The corrected rank stages, embedding-projection pairs and exhaustion.
  StageCompatibility.proposition-2-27
    r_n(p(e_n A)(e_n X)) = p_n A X, as an identity in the corrected D_n,
    for Kleene-defined p and independently defined bounded-typing p_n.
  StageCompatibility.first-pi-equation
    The corrected first-stage projector fixes Pi(bottom,bottom).
  RankProjection.Successor.equation / Zero.equation
    Structural equations for the rank projections, independent of typing.
  StageFusion.base / successor / eventual
    One unfolding lowers the comparison stage; stage n stabilizes after
    n+1 unfoldings, for arbitrary continuous binary operations in the
    one-step comparison lemma.
  OperationalStages.proposition-2-27 / stabilizes
    Direct compatibility of the global least fixed point with independently
    defined finite-unfolding stage operations.
  StageComparison.agreement / At.finitary
    Comparison with bounded-typing stages; finitariness of their ambient
    operational extensions. This separate bridge uses the sandwich proof.
  Stages.Stage.retract; Stages.Between.retract; Stages.Exhaust.equation
    Stage embedding-projection pairs and exhaustion of D.
  Model.Denotation.soundness; Model.conversion
    Soundness as projector fixedness and equality in D.
  LogicalRelation.At.Equality.adequacy; LogicalRelation.pi-not-U
    Reflected adequacy; constructor disjointness in arbitrary contexts.
  ScottPredicates.On.Extend / Reconstruct
    Lower admissible predicates are determined by compact observations.
  DomainLogicalRelation.At.For.principal-equation / stage-equation
    The actual logical relation extended to domain elements; recovery on
    compacts and from corrected rank approximations.
  DomainAdequacy.At.Equality.adequacy / TypeEquality.adequacy
    Whole-denotation adequacy transported from the compact theorem, using
    typed covers for observations that are not themselves typed.
  DomainRelationInversion.At.Products.inversion
    A Pi(bottom,bottom) observation retains syntactic component equalities.
  DomainPredicateMaps.Pullback / Preservation.equation
    Continuous pullbacks preserve lower admissibility; preservation of
    these predicates is equivalent to testing principal compacts.
  DomainRelationApplication.At.Applications.forward / equation
    Related application, with all three self/cross comparisons, and the
    equivalence between compact and arbitrary argument tests.
  DomainRelationFunctions.At.Function.unfolding / extensional-equation
    Exact uniform unfolding; pointwise compact function clauses are
    equivalent to preservation of related domain arguments. Assembling
    uniform raw witnesses from pointwise mere witnesses remains open.
  DomainPredicateArrow.Arrow / Variance
    Independent small function predicates, lower admissibility,
    equivalence to testing all arguments, and mixed variance.
  LogicalRelationClauses.At.Functions / Families / TermStep
    Function and dependent-family constructors from supplied admissible
    relations, retaining syntactic tests and all self/cross comparisons.
    Their closure and mixed-variance laws use no compact logical relation.
  DomainRelationClauseComparison.At.Functions / Families
    The new clauses instantiate to the existing pointwise compact clauses.
  DomainRelationPi.At.Products.syntactic / domain / family
    Positive Pi observations relating literal products yield syntactic
    equalities and related domain and family components.
  LogicalRelationTypeClause.At.Step.equation / Variance
    Independent strict admissible type clause; coherent head tests are
    equivalent to existential Pi data, without choice.
  LogicalRelationOperator.At.operator / variance / Inversion
    The mutual operator and its mixed variance; folding/unfolding under
    an explicit invariant interface; inversion from forward unfolding.
    Independent invariant existence and the full fundamental lemma are
    supplied below.
  LogicalRelationLocality.At.contractive
    Agreement at depth n gives agreement of the type-before-term action
    at depth n+1; negative tests use restricted arguments.
  LogicalRelationStages.At.compatible
    Independent finite-depth relations agree on every earlier rank stage.
  CompatiblePredicateLimit.Tower.equation
    A countable admissible limit recovers each compatible finite stage.
  IndependentLogicalRelation.At.equations / Unique.equivalence
    Independent strict invariant of the original mutual operator, unique
    among strict lower admissible invariants. Invariant and Inversion
    expose folding/unfolding and syntactic head inversion. No old logical
    relation or adequacy is used. The independent fundamental lemma below
    connects this invariant to derivable judgements.
  IndependentRelationTypedStages.At.laws
    Mutual symmetry, transitivity and conversion at every relation depth,
    proving the type laws before the term laws at each successor.
  IndependentRelationTypedLaws.At.laws / IndependentRelationRawLaws.At.On
    The same typed laws on the invariant and raw typed denotations.
    Typed compact covers bound value and classifier at a common rank;
    arbitrary lower observations are not assumed to remain typed.
  IndependentFundamentalRules.At.Fundamental
    Independent statement over fitting environments and related substitutions,
    with the result related at both substituted types. Variable, universe,
    and beta cases are checked here.
  IndependentFundamentalStructural.At
    Related-substitution symmetry and fundamental symmetry, transitivity,
    and conversion, using only the independent relation laws.
  IndependentFundamentalSubstitution.At.instantiate
  IndependentFundamentalApplication.At.application
    Binder instantiation and application at both dependent result types.
  IndependentFundamentalBinder.At.Under / Outputs
    Arbitrary argument tests restrict to semantically typed arguments;
    fitting extended environments and typed laws supply all three body
    comparisons. Evaluation factors through the same restriction.
  IndependentFundamentalPi.At.formation / equality
  IndependentFundamentalLambda.At.lambda
  IndependentFundamentalExtensionality.At.extensionality
    The remaining constructor cases, including both substituted types.
    Extensionality uses semantic eta from soundness and the body hypothesis.
  IndependentFundamental.At.fundamental / typing / equality
    Complete induction on every derivation constructor.
  IndependentAdequacy.At.Equality.left / right / types / compact
    The full reflected denotation satisfies the independent relation at
    both substituted types; compact observations recover the relation.
  IndependentInversion.pi-injectivity
    Pi equality in any well-formed context yields a mere pair of syntactic
    component equality derivations. Derived using the bottom environment
    and Pi(bottom,bottom), without old adequacy or syntactic Pi injectivity.
    The standalone check includes all 104 dependency modules.
  DomainRelationTypeComparison.At.forward
    The existing relation maps into the mutual operator for arbitrary
    syntax. This is a forward inclusion, not an invariant existence proof.

The imported Consequences.pi-injectivity and SubjRed.subject-reduction /
subject-reds are outside Theory and need neither univalence nor replacement.

dI-domain work
--------------

ScottMeet, RigidProjector, RigidImage and RigidSubdomain prove the general
rigid-projection algebra, the Scott image and compactness theorem, and
construction from downward-closed predicates closed under bounded joins.
DIDomain and DIImage specify the extra dI axioms explicitly and prove
that rigid images inherit them. The Boolean instance now takes small propositional excluded middle as
an explicit local argument; no classical global assumption is added.

RigidSections constructs dependent section projections over a supplied
function-domain interface, proves monotonicity and the intersection laws,
and instantiates that interface for the existing continuous exponential.
StableMaps, StableDirected and StableComplete now construct the genuine
stable order and its pointwise directed and bounded joins. StablePatches
and StableExponential prove that stable maps between dI-domains form a
Scott domain with a small compact basis; stable compactness agrees with
ordinary compactness for stable maps. CompactIdeals derives the needed
local classical reasoning from the explicit finite-discrete I-axiom.
StableSections supplies the actual stable function-domain instance and
finite tests. SectionContinuity proves continuity in a Scott parameter
with continuous fibre evaluations, also when the function argument varies.

StableMeet identifies compatible meets pointwise. StableDistributive and
StableFiniteIdeals prove the extra dI axioms and package the stable
exponential as DIDomain.DI. FiniteEnumeration and FiniteRange supply the
finite products, finite choice and duplicate removal used by the I-axiom.
ScottProduct, DIProduct and StableProduct construct products and stable
pairing/projections. StableEvaluation and StableCurrying prove joint
stable evaluation and currying/uncurrying with beta and eta identities.
RigidSpace constructs the dI-domain of rigid projections as the principal
ideal below identity. StableFamilies proves both joint stability of
(B,f) |-> R_B(f) and stability of B |-> R_B into rigid projections of the
stable function domain, for stable families over the fixed input domain.

The combined check reports 11,736 declarations and zero failures.
StableInputRestriction, StableImageMaps and StableVaryingFamilies now
handle varying rigid input domains: input restriction is rigid, stable
maps on its image extend/restrict with beta/eta, and Q_(p,B) is the
greatest supported section, stable in the input projection and family.
StableInternalComposition and RigidOperations supply the internal
composition and evaluation operations used in these constructions.
StableFixpoint proves the least-fixed-point operator itself stable.
StableProjectorFixpoint supplies rigid recursive stages, their pointwise
least limit, and absorption of earlier stages.

RigidEmbedding, RigidUniverse and RigidUniverseRecursion give a
conditional internal-universe theorem. Explicit rigid embeddings of R(D)
and [D=>D] into D imply stable typing, U:U, stable term application with
beta, and stable Pi codes with introduction and elimination. The code
embedding alone gives stable recursive-type formation, its unfolding
and leastness laws, and a bottom-starting stage chain with the required
limit. These theorems take representation data as explicit arguments.

RigidReflexiveDomain now constructs that representation from ANY seed
dI-domain. RigidEmbeddingExponential lifts embeddings through stable
endomorphism spaces. RigidLimitDI constructs countable rigid limits,
including a compact basis and both dI axioms. RigidLimitExponentialLaws
proves that restriction and assembly are inverse stable maps between
the endomorphism space of the limit and the limit of the endomorphism
spaces. RigidExponentialTower and the tail isomorphism yield a domain
D_infinity isomorphic to [D_infinity=>D_infinity]. The rigid-code
embedding follows from the function embedding. The seed embeds rigidly
and faithfully, so a nontrivial seed gives a nontrivial represented
universe. No function/code representation is assumed of the seed.

BooleanDI supplies the concrete two-element seed under a local small
excluded-middle parameter, and BooleanReflexive proves its represented
domain nontrivial. StableSyntax interprets every existing Syntax.Tm as a
stable map on finite-product environments. StableSubstitution proves
renaming, substitution and beta at type-fixed arguments; StableSyntaxTyping
proves semantic dependent-function introduction and elimination.
RigidRankStages proves finite capture of compact observations and stable
approximation of term maps. ReflexiveSyntax identifies coordinate n+1
of a represented function with its restriction to tower stage n.

A seed without classical input, full Syntax.Der soundness, and comparison
with syntactic/Scott-filter ranks remain open. The earlier Scott filter
model and rank stages are not identified with this stable construction.
See DI.txt and di-domains.tex/pdf for details.

Assumptions and universes
------------------------

All.seg exposes exactly these additional ambient parameters:

  ua           univalence at every universe level;
  images       chosen small images (Replacement.Images);
  surjections  their propositional elimination property at every level.

The latter two together constitute the replacement interface. Images alone
would not suffice. Function and proposition extensionality are derived
from univalence; propositional truncation is derived from replacement.
No excluded middle, choice, resizing, domain equation or minimality axiom
is assumed. There are no proof holes.

Tokens and compact presentations live in U l; D, continuous maps and
compact families live in U (l+). Suprema are indexed by U l types and
orders are U l-valued. This is small-index completeness, not completeness
over all U (l+) families. Compact witnesses exist propositionally. Reflected
adequacy likewise asserts mere logical-relation witnesses; it does not
extract syntax derivations from truncated observations.

Relation to Section 2
---------------------

The reference is Definitional Inversion, Without Normalisation, Section 2
(../paper1.pdf). This implements the filter alternative to its CUSL
construction, with these precise differences:

* The domain equation uses explicit filter decomposition/reconstruction;
  minimality uses proper-token induction.
* Typing is MIN's finite intersection-type relation. The global recursive
  equations, leastness and explicit Kleene construction are checked
  independently of the stage diagrams. OperationalStages proves the
  corrected rank-stage identity directly by finite stabilization.
  StageCompatibility gives the separate bounded-typing proof, and
  StageComparison identifies the constructions. This is not a separately encoded Figure 2 stage relation,
  and equivalence with such a relation has not been formalised. The
  printed stage-zero obstruction is detailed in PROPOSITION227.txt.
* Stages proves projection/exhaustion results, but does not identify each
  successor stage with F of the previous one, or establish equality with
  the paper's particular C_n presentations.
* Finitary uses the compact-density formulation discussed after 2.22.
  FixedImage proves image algebraicity and the compactness characterization.
  ScottDomain now gives a general interface and ScottExponential proves
  closure under continuous function spaces. Theorem 2.10's categorical
  equivalence with CUSLs is checked, including both natural isomorphisms.
  A formal equivalence with other abstract definitions is not included.
* The syntax bridge reflects MIN denotations for well-typed terms in fitting
  MIN environments. It is not a new total interpretation of all untyped
  terms in arbitrary D-valued environments. Original semantic substitution
  is reused. The original adequacy bridge is separate from the independent
  invariant and its complete fundamental proof described above.

Categorical uniqueness of minimal invariants and the LAZY variant are
outside this development.
These distinctions add no assumptions to the listed theorems.

Provenance
----------

vendor/ contains unchanged snapshots of Unit MIN, projector and foundation
sources. Top-level symlinks point relatively into vendor/. The manifest
records original paths, SHA-256 hashes, source Git revision and checker
hash. Original sources were not modified. Category.seg,
CategoryArrows.seg and EquivalenceLemmas.seg are local copies of the
category library in CANONICITY/unit-indexed/sag/categories; they supply
the precategory, total-space univalence and iso-arrow lemmas. New proof
files are ordinary top-level .seg files. ExtFilter adapts Unit's
domain/ideal/Filter.seg to
MIN's tokens. ARGUMENT.txt explains the proof architecture.
