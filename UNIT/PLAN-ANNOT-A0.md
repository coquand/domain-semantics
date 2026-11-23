# A0. Context annotations for the bounded Ehrhard GAT

This is the design note requested by §7 of [PLAN-ANNOT.md](PLAN-ANNOT.md). The
rule shapes are specified below. The lifting and coherence proofs are designs
and remain open in Seg.

## Syntax and rules

The six annotations follow Definitions 2, 4 and 7 of the paper. Definition 11
forgets those fields and interprets explicit substitutions as simultaneous
substitutions. Here `fg` only drops the fields. The existing `et`, `es` and `ec`
can then interpret its output. The bounded universe rules and Ehrhard's
`lift` and `sec` are those of the current implementation.
[sterbac4.pdf](../sterbac4.pdf), [GAT.seg](GAT.seg).

Use `U_n(G) = auu n G`, `C_m^n(G) = auc m n G`, `id_G = aid G`,
`()_G = aeps G`, `p_{G,A} = ap G A` and `q_{G,A} = aq G A`.
Here `G.A` is raw context extension, `X[s]` is the raw type or term action,
and `s ∘ d` applies `d` first. `T_n`, `lf_m^n`, `pic_n`, `Π`, `λ`,
`app`, `lift_A` and `sec_A` are the copies of the corresponding raw
constructors. Each row names its source rule. The copied rule keeps that
rule's premise order and level bounds, with the occurrences below replaced
in place. An omitted premise contains none of the six leaves.

| Formation rule | Annotated premises containing leaves | Annotated conclusion |
| --- | --- | --- |
| `gs-id` | | `id_G : G → G` |
| `gs-eps` | | `()_G : G → 1` |
| `gs-p` | | `p_{G,A} : G.A → G` |
| `gt-uu` | | `G ⊢ U_n(G) type` |
| `gt-el` | `G ⊢ a : U_n(G)` | `G ⊢ T_n(a) type` |
| `gm-pic` | `G ⊢ a : U_n(G)`, `G.T_n(a) ⊢ b : U_n(G.T_n(a))` | `G ⊢ pic_n(a,b) : U_n(G)` |
| `gm-uc` | | `G ⊢ C_m^n(G) : U_n(G)` |
| `gm-lf` | `G ⊢ a : U_m(G)` | `G ⊢ lf_m^n(a) : U_n(G)` |
| `gm-q` | | `G.A ⊢ q_{G,A} : A[p_{G,A}]` |

| Type or term equation | Annotated premises containing leaves | Annotated conclusion |
| --- | --- | --- |
| `ge-el` | `G ⊢ a = a' : U_n(G)` | `G ⊢ T_n(a) = T_n(a')` |
| `ge-el-lf` | `G ⊢ a : U_m(G)` | `G ⊢ T_n(lf_m^n(a)) = T_m(a)` |
| `ge-el-pic` | `G ⊢ a : U_n(G)`, `G.T_n(a) ⊢ b : U_n(G.T_n(a))` | `G ⊢ T_n(pic_n(a,b)) = Π(T_n(a),T_n(b))` |
| `ge-el-uc` | | `G ⊢ T_n(C_m^n(G)) = U_m(G)` |
| `ge-sb-id` | | `G ⊢ A[id_G] = A` |
| `ge-uu-sb` | | `D ⊢ U_n(G)[s] = U_n(D)` for `s : D → G` |
| `ge-el-sb` | `G ⊢ a : U_n(G)` | `D ⊢ T_n(a)[s] = T_n(a[s])` for `s : D → G` |
| `gm-epic` | `G ⊢ a : U_n(G)`, `G ⊢ a = a' : U_n(G)`, `G.T_n(a) ⊢ b = b' : U_n(G.T_n(a))` | `G ⊢ pic_n(a,b) = pic_n(a',b') : U_n(G)` |
| `gm-elf` | `G ⊢ a = a' : U_m(G)` | `G ⊢ lf_m^n(a) = lf_m^n(a') : U_n(G)` |
| `gm-eta` | | `G ⊢ f = λ(A,B,app(A[p],B[lift_A(p)],f[p],q_{G,A})) : Π(A,B)`, where each `p` is `p_{G,A}` |
| `gm-lf-pic` | `G ⊢ a : U_n(G)`, `G.T_n(a) ⊢ b : U_n(G.T_n(a))` | `G ⊢ lf_n^p(pic_n(a,b)) = pic_p(lf_n^p(a),lf_n^p(b)) : U_p(G)` |
| `gm-lf-uc` | | `G ⊢ lf_n^p(C_m^n(G)) = C_m^p(G) : U_p(G)` |
| `gm-lf-lf` | `G ⊢ a : U_m(G)` | `G ⊢ lf_n^p(lf_m^n(a)) = lf_m^p(a) : U_p(G)` |
| `gm-sb-id` | | `G ⊢ a[id_G] = a : A` |
| `gm-pic-sb` | `G ⊢ a : U_n(G)`, `G.T_n(a) ⊢ b : U_n(G.T_n(a))` | `D ⊢ pic_n(a,b)[s] = pic_n(a[s],b[lift_{T_n(a)}(s)]) : U_n(D)` |
| `gm-uc-sb` | | `D ⊢ C_m^n(G)[s] = C_m^n(D) : U_n(D)` |
| `gm-lf-sb` | `G ⊢ a : U_m(G)` | `D ⊢ lf_m^n(a)[s] = lf_m^n(a[s]) : U_n(D)` |
| `gm-q-lift` | | `D.A[s] ⊢ q_{G,A}[lift_A(s)] = q_{D,A[s]} : (A[s])[p_{D,A[s]}]` |
| `gm-q-sec` | | `G ⊢ q_{G,A}[sec_A(a)] = a : A` |

| Substitution equation | Annotated conclusion |
| --- | --- |
| `gq-idl` | `id_G ∘ s = s : D → G` |
| `gq-idr` | `s ∘ id_D = s : D → G` |
| `gq-eps` | `s = ()_G : G → 1` |
| `gq-lift-id` | `lift_A(id_G) = id_{G.A} : G.A[id_G] → G.A` |
| `gq-p-lift` | `p_{G,A} ∘ lift_A(s) = s ∘ p_{D,A[s]} : D.A[s] → G` |
| `gq-p-sec` | `p_{G,A} ∘ sec_A(a) = id_G : G → G` |
| `gq-lift-p-sec-q` | `lift_A(p_{G,A}) ∘ sec_{A[p_{G,A}]}(q_{G,A}) = id_{G.A} : G.A → G.A` |

The `gq-lift` and `gq-sec` congruences have no explicit leaf occurrences.
Their conclusions use the left-hand endpoints and indices,
`lift_A(s) = lift_{A'}(s') : D.A[s] → G.A` and
`sec_A(a) = sec_{A'}(a') : G → G.A`. The right sides are typed there using
the copied `gs-cx`. The other conversion rules also keep the raw expression
and its existing annotations as they change the context or type.

The table covers all 35 declarations in the current `GDer` with an explicit
occurrence of one of the six leaves. The generator should read the constructor
list from `GAT.seg`, which currently has 81 constructors. The handoff's count
of 104 differs from the source.

## Congruence for annotation arguments

Each rule below uses the annotated context and type equalities as premises.
The two endpoints of a context equality are well formed by presupposition.
In the last two rows the type equality is over `G`, so its right side is
transported to `G'` when forming the right-hand leaf.

| Proposed rule | Premises | Conclusion |
| --- | --- | --- |
| `ae-uu-cx` | `G = G'`, `LeN n N` | `G ⊢ U_n(G) = U_n(G')` |
| `am-uc-cx` | `G = G'`, `LeN (suc m) n`, `LeN n N` | `G ⊢ C_m^n(G) = C_m^n(G') : U_n(G)` |
| `aq-id-cx` | `G = G'` | `id_G = id_{G'} : G → G` |
| `aq-eps-cx` | `G = G'` | `()_G = ()_{G'} : G → 1` |
| `aq-p-cx` | `G = G'`, `G ⊢ A = A'` | `p_{G,A} = p_{G',A'} : G.A → G` |
| `am-q-cx` | `G = G'`, `G ⊢ A = A'` | `G.A ⊢ q_{G,A} = q_{G',A'} : A[p_{G,A}]` |

For the presupposition proof, keep the left endpoints of the judgements in
this table. Extend the context-equality branch of the presupposition
motive to return the reversed equation along with the two
well-formedness proofs. For `gc-ext`, reverse the last-type equality
and move it to the right prefix using the forward prefix equality,
then extend the reversed prefix equation from the induction
hypothesis. This makes symmetry available inside the presupposition
proof, including in the new congruence cases. In projection congruence,
extension congruence gives
`G.A = G'.A'`. Convert both endpoints of the right substitution with
`gs-cx` using the reversed prefix and extension equations. For variable
congruence, first move the right variable from
`G'.A'` to `G.A`. Substitution congruence applied to `A = A'` and the
projection equality gives `A[p_{G,A}] = A'[p_{G',A'}]` there. This permits
term-type conversion of the transported variable. The presupposition proof
may use the projection congruence constructor directly, with the endpoint
typings built from its input premises.

For code congruence, transport the right code to `G` and convert its type
via universe congruence. Recover the level bound from a typing of
`auu n X` over any current context, by following `gt-cx` back to
`gt-uu`. That bound proof can be defined before presuppositions. After
presuppositions and context-equality transitivity, the same generation
argument recovers `G = X` from
`G ⊢ U_n(X)`. This lets a premise at a transported universe use the
local universe annotation when needed.

Universe types in the codomain of reindexing use the destination context,
as in `ge-uu-sb`. For `gm-pic-sb`, first use that equation to convert
the reindexed body's type to `U_n(D.T_n(a)[s])` over `D.T_n(a)[s]`.
Move it to `D.T_n(a[s])` using `ge-el-sb` under extension, then change its type
to `U_n(D.T_n(a[s]))` by universe congruence. The same two transports
apply to the right body of `gm-epic` and `gm-lf-pic`, using respectively
decoding congruence and `ge-el-lf`. In `gq-lift-id` the identity comes
from the codomain `G.A`. Convert its domain to `G.A[id_G]` using
`ge-sb-id` under extension. These are extra checks for a port of
[GPresup.seg](GPresup.seg).

Derive substitution-equality transport from the rules above and the copied
substitution calculus. For `s = t : D → G` and context equalities
`D = D'`, `G = G'`, type `id_{D'} : D' → D` and
`id_{G'} : G → G'` using `gs-cx`. Compose the equation with those two
identities. At `D' → G'`, the converted typings of `s` and `t` allow
the copied left and right unit equations with those exact identity
annotations to cancel them on each side.

For A2, the copied rules forget to their namesakes. All six annotation
congruences forget to reflexivity at the bare left endpoints, constructing
the bare leaf typing from the premises and their presuppositions.

## A4. Choose U1, comparing the explicit syntax directly

Prove the following comparisons in the annotated system, before using
them for A3. The input identity is equality in raw `GE` after `fg`. It
retains explicit substitution, universe lifting and decoding. For types
and terms, assume that the current annotated contexts are already
judgementally equal. State the outputs over the left context, with the
right expressions transported there.

- For two types with the same raw image, produce a type equality.
- For two terms with the same raw image, produce an equality of their
  actual types and a term equality at the left type. The actual types
  may have different raw images because the typings can end in
  `gm-conv`.
- For two substitutions with the same raw image and equal domains,
  produce a codomain equality and a substitution equality at the left
  endpoints. The codomains may have different raw images because the
  typings can end in `gs-cx`.

Use generation for typing derivations to recover the introduction
premises and a comparison with the original judgement. Follow `gt-cx`,
`gm-cx`, `gm-conv` and `gs-cx` in this generation pass. Keep the
contexts of the introduction rule together with equalities to the
current contexts. For terms also keep the equality from the type at
introduction to the advertised type, in the advertised context.
Well-formedness and context-equality inversion for extensions recover
the prefix and last type. The indexed case motives in `ext-inv` and
`ty-gpi-inv` and the treatment of context equality in `tr-inv` are
templates for the needed inversions.
[GLean.seg](GLean.seg), [RGAT.seg](RGAT.seg).

Package the three comparisons in one induction on the common raw expression
in `GE`, with both annotated expressions and their typings quantified in
the motive. The constructor cases use raw injectivity on the surviving
fields.

- For `p` and `q`, compose the given context equality with the equalities
  from generation to compare their original extension contexts. Invert
  this equality for their prefix and last type, and apply the projection
  or variable congruence. For `q`, use projection congruence and type
  substitution congruence to compare the two principal types. Context
  equality inversion supplies the equality of the last types directly.
- For `lift_A(s)`, invert the equality of the two original domains
  `D.A[s]` and `D'.A'[s']` to compare `D` and `D'`. Compare the
  immediate subexpressions `s,s'` and then `A,A'` in the equal
  resulting codomains. Use `gq-lift` and context transport. For
  `sec_A(a)`, compare the immediate subexpressions `A,A'` and then
  `a,a'` and use `gq-sec`. For composition, compare the second
  substitution first to obtain equal intermediate contexts.
- For `X[s]`, compare `s,s'` first. Their codomain equality supplies
  the hypothesis for comparing `X,X'` there. Reindex the result using
  `ge-sb` or `gm-esb`. For a term action, the type equality supplied
  by the comparison of `X,X'` is what allows the two reindexed types
  to be compared.
- For binders, compare the explicit domain types, or compare the domain
  codes and use decoding congruence. Extend the context equality to
  compare the body data. Use the existing congruences for the resulting
  equalities. For application, compare the principal result types by
  type action congruence and section congruence on the already compared
  arguments.

Derive that two well-formed contexts with the same raw image are equal
by a separate induction on the common raw context. Compare the
prefixes first, use the type comparison on the last types, and extend.
The main comparison uses equality of supplied contexts as an input, so
this context corollary is downstream. For equality judgements, apply
the comparisons to the presupposed typings and align each side of the
judgement. This yields the fixed-context statements and their
substitution counterparts.

**Expected cost.** The work is in the indexed generation pass, endpoint
transport, and constructor cases. Test `p`, `q`, `lift`, and type
and term action through conversion first. Those cases exercise the
dependency on substitutions and the annotated endpoints. Generate the
routine off-index cases from the rule list.

**U2 assessment.** Annotating a `section-*` output with A3 would
produce a representative. The proof that an arbitrary annotated term
equals that representative would still require choosing coherent
representatives at binders and comparing explicit substitution with
evaluation under the erased simultaneous substitution. For example,
in `A[s]` the annotation of the lift of `et A` can choose a different
context from the annotated codomain obtained for `s`. The bare Lemma 19 uses
Lemma 18's naturality, environment equality and substitution for this
case. Using the bare equations to prove the annotated comparison
would itself require lifting the equations and aligning their
endpoints. U1 supplies this alignment with an induction on the more
informative raw image.
[Thm20.seg](Thm20.seg), [L19.seg](L19.seg), [gat-ehrhard.pdf](gat-ehrhard.pdf).

## A3. Lift into prescribed well-formed contexts

Follow the pattern of `SecJ` and `AllJ`. Carry
well-formed annotated witnesses for the external contexts of each
bare judgement in the derivation motive, along with a lifting function
quantified over well-formed annotated representatives of those
contexts. This supplies intermediate context witnesses from the
recursive premises in the composition and conversion cases. Types,
terms and all three indexed equality judgements carry strict raw
image identities for their result expressions. For substitutions and
substitution equations use the stronger fixed-endpoint interface,
with prescribed well-formed representatives of both ends. For a
context equation use prescribed representatives of its two contexts.
To return a codomain as part of the result, use its well-formed witness
from the motive. [TSection.seg](TSection.seg).

The reason for using coherence during lifting is already visible in
`ge-trans`: the two independently lifted middle types can have
different annotations despite having the same raw image. Similarly,
`gm-conv` needs a comparison of the lifted premise types, and
`gq-trans` needs one for the middle substitution. The direct U1
comparisons supply these equalities and use only annotated rules and
their presuppositions. Put these comparisons upstream of the general
A3 induction to avoid relying on the theorem being constructed.

- For `gs-lift`, invert the raw images of the prescribed ends as
  extensions. Recursively lift the inner substitution between their
  prefixes. Use the last type of the prescribed codomain to form the
  lift. Its natural domain is equal to the prescribed domain by
  strict-image type coherence on the last type. Apply `gs-cx`.
  For `gs-sec`, move the prescribed codomain's last type to the
  domain along prefix coherence, align the lifted argument at this
  type, and transport the resulting codomain back.
- In a bare context conversion, lift the context equation via its own
  recursive premise, with the old context chosen from a recursive
  witness and the new context supplied by the caller. Lift the
  underlying judgement at the old context, then transport it. This
  preserves the raw image even when the bare context equality changes
  the raw context. For fixed-endpoint `gc-ext`, lift the prefix
  equation first, lift the last-type equation over the left prefix,
  and align its two sides with the last types of the prescribed
  endpoints, transporting the right last type to the left prefix.
- For a binder, lift its domain first and use the resulting extension
  for the body premises. Compare their independently lifted types
  with the types needed by the formation rule. For a premise at a bare
  universe, obtain the bound from the annotated typing's
  presupposition and convert to the universe tagged with the current
  context.
- For an equation whose natural conclusion has an extended context,
  such as `gm-q-lift` or `gq-lift`, build that natural annotated
  extension from the lifted inputs. Use strict-image context
  coherence to reach the caller's extension and transport the
  equation. This also handles the converted endpoints built into
  `gq-lift-comp`.

Once this lift is available, a bare equation between the images of
two existing annotated expressions can be lifted and its endpoints
aligned by U1. In A5 the bare equations come from `gu-*` and
`gu-cx1`, bare existence comes from `r2g-*`, and soundness follows
from A2 and `g2r-*`. [RGAT.seg](RGAT.seg).
