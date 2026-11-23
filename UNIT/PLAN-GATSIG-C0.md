# C0 — Cartmell's rules for the Ehrhard signature

Fix `N` in `BoundedSyntax`. The Part A claim is that `FADer J` and `CDer J`
imply each other for every `J : FAJ`, where `CDer` presents the closed term
judgements of Cartmell's GAT with the bounded Ehrhard signature. This
includes judgements about contexts, types, terms and substitutions, and
their four equality forms. In particular, `Γ` in `Ty(Γ)` is a **closed term
of sort `ctx`**. Closed here means that the ambient Cartmell telescope is
empty. Object-level weakening and substitution remain operations in the
signature.

The references for the signature are Coquand–Sterbac §2.1, Definitions 1–7,
and `gat-ehrhard.tex` §§1, 6, 12, 13 and 15. Use the paper's Ehrhard
generators and §13 annotations, with the strict lifts and bound from
§1. Cartmell's publisher full text was inaccessible. The rule references
below are to his thesis §§1.6–1.7, including the definition of a well-formed
axiom and the substitution lemma. [Cartmell's thesis](https://ncatlab.org/nlab/files/Cartmell-Thesis.pdf) · [1986 article](https://doi.org/10.1016/0168-0072(86)90053-9)

## Signature and representation

Use `FA` and the eight `FAJ` indices unchanged. At the level of the
signature, a separate sort expression is one of `ctx`, `Sub(D,G)`,
`Ty(G)`, `Tm(G,A)`. Read typing as `t : S` and equation as `t = u : S`.
For example, `a : Tm(G,A)` is `fjtm G a A`, and `G = H : ctx` is
`fjeqcx G H`. The raw `FA` constructor for each fully applied term symbol
stores every telescope argument, including every context and type
annotation. Its spine order can differ from the telescope order. For
example, `fmsb D G A a s` has telescope
`D : ctx, G : ctx, A : Ty(G), a : Tm(G,A), s : Sub(D,G)`.

The sort declarations are `ctx` over the empty telescope, `Sub` over
`D : ctx, G : ctx`, `Ty` over `G : ctx`, and `Tm` over `G : ctx,
A : Ty(G)`. Use the 19 operation declarations of `FA` with the result
sorts in `PLAN-ANNOT-FULL.md` and the full telescope for each. For example,
`fcomp` takes three context arguments and two substitution arguments,
even though `fs-comp` needs just the two substitution typings. Level
parameters are indices selecting symbols in the bounded signature.
Represent the bounds with `LeN`, and strictness with `LeN (suc m) n`.
Congruence compares arguments at a fixed level index.

The 32 term equation schemes are the following. The IDs identify the
corresponding equations in the current `FGAT.seg`.

| Group | Equation IDs |
|---|---|
| Category and terminal | `fq-idl`, `fq-idr`, `fq-assoc`, `fq-eps` |
| Functoriality of actions | `fe-sb-id`, `fe-sb-comp`, `fm-sb-id`, `fm-sb-comp` |
| Ehrhard | `fq-lift-id`, `fq-lift-comp`, `fq-p-lift`, `fq-p-sec`, `fq-sec-comp`, `fq-lift-p-sec-q`, `fm-q-lift`, `fm-q-sec` |
| Products | `fe-pi-sb`, `fm-lam-sb`, `fm-app-sb`, `fm-beta`, `fm-eta` |
| Universe naturality | `fe-uu-sb`, `fe-el-sb`, `fm-pic-sb`, `fm-uc-sb`, `fm-lf-sb` |
| Tarski and lift equations | `fe-el-pic`, `fe-el-uc`, `fe-el-lf`, `fm-lf-pic`, `fm-lf-uc`, `fm-lf-lf` |

Store each axiom's telescope, common sort, both raw sides and level
conditions in `CSig.py`, along with the sort and operation declarations.
Use `CGen.py` to emit `CGAT.seg` deterministically from that input. The
file names follow the requested `C` prefix. The current `FADer` has 104
constructors, counting `f-nil`. Its constructors provide a coverage
inventory for C3.

## Closed rule schemes

Write a telescope as `x₁ : S₁, …, xₖ : Sₖ`, where `Sᵢ` can use the
preceding variables. A closed instance `u` supplies a typing
`uᵢ : Sᵢ[u<ᵢ]` for each `i`.

1. **Formation.** A sort or an operation is formed by supplying its
   full telescope and level conditions. An operation with declared result
   `R` gives `f(u) : R[u]`. This is Cartmell CF2.
2. **Axioms.** For `l = r : R` over a telescope, supply a closed instance
   and the two typings `l[u] : R[u]` and `r[u] : R[u]`. Conclude
   `l[u] = r[u] : R[u]`. These typings are the closed form of Cartmell's
   A2 premises. The written signature must also have the two typings in
   the generic telescope. The frame derivations used to verify that
   condition may use previously established equations. For example, the
   type action's identity law types `id_(G.A)` at the source `G.A[id_G]`
   required by the lift identity axiom. In Π-code naturality, the source
   `D.(Tₙ(a)[s])` of the lifted substitution and the body context
   `D.Tₙ(a[s])` are equal by decoding naturality. Give the dependency
   order explicitly when porting witnesses for these axioms.
3. **Equality and congruence.** Generate reflexivity from typing, and
   symmetry and transitivity at a common sort, for all four sorts.
   Given `uᵢ = vᵢ : Sᵢ[u<ᵢ]` for each `i`, conclude
   `f(u) = f(v) : R[u]` simultaneously in all argument positions. The
   equality at position `i` compares the right argument after conversion
   to the left sort. The equalities for earlier arguments give
   `Sᵢ[u<ᵢ] = Sᵢ[v<ᵢ]`, so these premises also type the right tuple at its
   own telescope. The right result is converted back from `R[v]` to
   `R[u]`. The same scheme for sort symbols gives sort equality. This
   specializes Cartmell's equality and simultaneous substitution rules.
   Reflexivity supplies the congruence for the nullary operation `fnil`.
4. **Sort equality and conversion.** The only sort equalities here are
   between instances of the same sort symbol. `Ty(G) = Ty(H)` is induced
   by `G = H : ctx`. `Sub(D,G) = Sub(E,H)` is induced by `D = E : ctx`
   and `G = H : ctx`. `Tm(G,A) = Tm(H,B)` is induced by `G = H : ctx`
   and `A = B : Ty(G)`. `ctx` has its reflexive sort equality. Convert
   both typings and equations along these equalities, preserving the
   raw terms on either side. These are Cartmell T1 and LI7. Generate
   the corresponding specialized `FAJ` constructors for `Ty`, `Sub`
   and `Tm`. Sort formation and sort equality are represented by the
   typing and equality tuples of their indices. Sort reflexivity,
   symmetry and transitivity on these tuples are admissible using the
   corresponding term rules and conversion. For `Tm`, symmetry moves
   the reversed type equation to `Ty(H)`, and transitivity first moves
   the second type equation back to `Ty(G)`.

## Why the empty telescope suffices

There is a closed instance lemma at the level of the presentation. For
an open judgement over `P`, let `ρ` assign a closed term to every
variable of `P`, with a derivation at its sort instantiated by the
earlier assignments. Interpret each raw expression by simultaneous
replacement. The open derivation then gives a closed derivation at
`ρ`. Under two assignments `ρ` and `ρ'` related pointwise at the left
sorts, each sort expression in a well-formed judgement has equal
instances, and each typed term expression has equal instances at the
left sort.

Here is the induction for the version with templates and explicit
substitution. A variable reads its typing or equality from the
assignment. Sort and operation formation use the respective
congruence rule on the induction results for the arguments. For
conversion, the equality between instances of the source sort, the
conversion at each assignment and sort transitivity provide the
required result sort equality and let the term equality be stated at
the left result sort. For equality judgements, retain the closed
instances of the equality and the comparisons of the two instances
of each endpoint. Reflexivity, symmetry and transitivity assemble
these from the premise data. An axiom uses the instantiated typings of
its endpoints and the closed axiom rule. Weakening and renaming
restrict or rename the assignment. In the substitution case the
argument derivations under `ρ,ρ'` supply the new typed and related
assignments for the induction hypothesis of the substituted template.
For Cartmell's mixed substitution into `l = r : S`, take the equality
at the left assignment and compose with the comparison between the
two instances of `r` at the left sort. The sort equality case is the
same composition with the sort of the right endpoint. Equivalently,
one can use the substitution lemma in Cartmell §1.7, keeping its
variable and axiom cases explicit in this presentation.

An empty ambient telescope has its unique empty assignment. Conversely,
each closed rule is an instance or specialization of Cartmell's generic
rules. Hence the closed comparison requires neither open `FA` syntax
nor an internal substitution operation for Cartmell variables. The
argument here is metatheoretic. The Unit comparison will quantify over
`FAJ` and the two derivation families.

## Proof plan and checks

- **C1.** Generate formation, axiom instances, equivalence rules,
  simultaneous congruences and the specialized conversions above. Use
  `CCheck.seg` as the driver. Check byte-for-byte regeneration and apply
  the deliberate-error check after a first green check of each new
  Seg file.
- **C2.** Map `CDer` to `FADer` by induction. Use `fpresup`,
  `f-cx-sym`, `f-cx-trans`, the context conversion helpers in `FCtx`,
  and `move-se` in `FSubTransport` for substitution **equation**
  conversion. To prove simultaneous congruence, first change the
  ordinary arguments with the raw annotation coordinates held in the
  left frame. Then change annotation coordinates individually. Move
  each intermediate equation back to the original result sort before
  taking transitivity. Keep dependent body or operand typings in the
  current formation frame at every step. The composition case needs
  both operands transported when the middle context changes. The term
  action case needs conversion of the operand after changing `A`, and
  type-action congruence to compare the intermediate result sorts.
- **C3.** First generate `CPresup` over `CDer` so that weaker hand-written
  premises can supply the full telescope. Equality and sort conversion
  cases recover endpoints by induction on their premises. Axiom cases
  already carry endpoint typings. Congruence cases construct the two
  formations by applying the operation to the two typed tuples and
  converting its right result back. Generate these endpoint proofs
  from the sort templates. Then translate `FADer` by induction, reading
  missing typings from the translated premises. For axiom cases build
  the two endpoint witnesses from previously justified equations,
  using `FPresup`, `FEquationFrames` and `FSubEquationFrames` as proof
  templates. `fc-nil` is reflexivity of the empty context, `fc-ext` is
  context extension congruence, and `fs-cx` is one `Sub` conversion
  with both endpoint equalities.
- **C4.** Compose with the `r2f-*` and `f2r-*` maps in `FRGAT`. Retain
  the raw Russell image equalities carried by the lifting results.
  Transfer their coherence clauses through C2 and C3. State the
  conclusion for the judgement forms with a Russell counterpart.

Use small checks for simultaneous composition congruence with a
changed middle context and operand, term action with changed context
and operand type, substitution conversion at both ends, lift identity,
Π-code naturality, and the Russell variable lift and erasure. The
indexed baseline `GATCheck.seg` checks 3,728 declarations with zero
failures. Existing drivers and the paper require approval before editing.

## Status at the report before C3–C4

C1 is generated and checked. `CSig.py` declares 19 operations and 32
axiom schemes. `CGen.py` reproduces `CGAT.seg` byte for byte, with 87
constructors. C2 proves `c-to-full : (J : FAJ) -> CDer J -> FADer J`.
`CCheck.seg` checks 444 declarations with zero failures, including closed
examples for composition, term action, two-ended substitution equation
conversion and lift identity. The checker rejected a deliberate type
error in each of the five new Seg files. All five were restored and the
driver passed again. C3 and C4 are open.
