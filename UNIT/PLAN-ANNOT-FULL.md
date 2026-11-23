# Completely annotated Ehrhard GAT

## Goal and working rules

Define bounded T_E^full inside the existing `BoundedSyntax (N : Base.Nat)`.
Forget the additional sort arguments to T_E^a and prove existence and
coherence of full annotations. Compose with `ARGAT.seg` to relate the
full theory to T_Russell. Keep Ehrhard's lift and section operations.
Pairing is a separate decision.

Develop new Seg files against `FullCheck.seg`. Add imports to
`GATCheck.seg` and `All.seg` only after the full import set checks.
Keep the earlier theories and their proofs in their existing files.
Extend `gen_aannot.py` without changing its existing output. Use
`gat-ehrhard.tex` for F6. Test new files with a deliberate error and
restore them. Never use `git add -u` or `git add -A`. Stage only explicit
paths and ask before committing.

## F0. Sort arguments and formation rules

Use one raw family `FA` with a separate constructor for each typed
action. The judgement indices `FAJ` and the eight judgement forms are
the same as for `GAJ`. The formation premises below are all at the
displayed sort arguments. Conversion rules still move the outer
judgement and leave the raw expression intact.

| Raw expression | Formation premises | Result |
|---|---|---|
| `fnil` | none | context |
| `fext G A` | `A : Ty(G)` | context |
| `fpi G A B` | `A : Ty(G)`, `B : Ty(G.A)` | `Ty(G)` |
| `fuu n G` | `G` well formed, `n ≤ N` | `Ty(G)` |
| `fel n G a` | `a : El(G, fuu n G)` | `Ty(G)` |
| `ftsb D G A s` | `A : Ty(G)`, `s : Sub(D,G)` | `Ty(D)` |
| `flam G A B b` | `A : Ty(G)`, `B : Ty(G.A)`, `b : El(G.A,B)` | `El(G, fpi G A B)` |
| `fapp G A B c a` | `A : Ty(G)`, `B : Ty(G.A)`, `c : El(G, fpi G A B)`, `a : El(G,A)` | `El(G, ftsb G (G.A) B (fsec G A a))` |
| `fpic n G a b` | `a : El(G, fuu n G)`, `b : El(G.Tₙ(a), fuu n (G.Tₙ(a)))` | `El(G, fuu n G)` |
| `fuc m n G` | `G` well formed, `m < n ≤ N` | `El(G, fuu n G)` |
| `flf m n G a` | `a : El(G, fuu m G)`, `m < n ≤ N` | `El(G, fuu n G)` |
| `fq G A` | `A : Ty(G)` | `El(G.A, ftsb (G.A) G A (fp G A))` |
| `fmsb D G A a s` | `A : Ty(G)`, `a : El(G,A)`, `s : Sub(D,G)` | `El(D, ftsb D G A s)` |
| `fid G` | `G` well formed | `Sub(G,G)` |
| `fcomp T D G s d` | `s : Sub(D,G)`, `d : Sub(T,D)` | `Sub(T,G)` |
| `feps G` | `G` well formed | `Sub(G,fnil)` |
| `fp G A` | `A : Ty(G)` | `Sub(G.A,G)` |
| `flift D G A s` | `s : Sub(D,G)`, `A : Ty(G)` | `Sub(D.A[s],G.A)` |
| `fsec G A a` | `A : Ty(G)`, `a : El(G,A)` | `Sub(G,G.A)` |

Here `G.A` is the raw constructor `fext G A`, `Tₙ(a)` at G is
`fel n G a`, and `D.A[s]` uses `ftsb D G A s`. The six leaves already
have their sort arguments in T_E^a. The levels are meta-level natural
number indices with the same bounds as in `AGAT.seg`. A path of natural
number indices can be used by transport in Unit.

Generate all inherited derivation rules from `AGAT.seg`. Keep their
names with the `f` prefix, their premise order, and their level
bounds. Give each compound occurrence the formation frame in the table.
For an inherited equation, annotate its two sides at their respective
formation frames and state the equation at the left frame or at the
result type already specified by the inherited rule. In particular:

- In type and term substitution composition, a right-associated action
  uses `fcomp T D G s d`. The outer action on the left uses `T,D`,
  and the inner action uses `D,G`. The left outer term action records
  `ftsb D G A s` as its operand type.
- In β, the result type is `ftsb G (G.A) B (fsec G A a)` and
  the right side is `fmsb G (G.A) B b (fsec G A a)`. In η, the
  weakened function records `fpi G A B` as its operand type.
- In Π-code naturality, the substituted body is formed using
  `flift D G (fel n G a) s`. Its source extension is
  `D.(Tₙ(a)[s])`. The right product code expects its body at
  `D.Tₙ(a[s])`, using context and universe conversion.
- In lift of a Π-code, the lifted body is formed at `G.Tₙ(a)`.
  The right product code expects the body at `G.Tₚ(lf a)`.
  The type equation for decoding a lift identifies the extensions.
- In the q/lift equation for `s : Sub(D,G)`, the term-action
  annotation for the left `q` is `ftsb (G.A) G A (fp G A)`.
  The result type of the equation is the type of the right `q`
  in `D.A[s]`. The projection/lift and action composition equations
  supply the type conversion.

### Congruences of sort arguments

Add one rule for each new raw annotation coordinate, with its two
expressions identical in the other coordinates. Each rule takes the
formation premises for the left expression and one equality for the
coordinate that changes. Its conclusion uses the left context and
the left result type or endpoints from the formation table. The
right hand side is the constructor with just that coordinate
replaced. This convention determines the rule indices explicitly.

| Constructor | Coordinate changed in a single rule | Extra equality premise |
|---|---|---|
| `fpi`, `flam`, `fapp` | G (one rule for each constructor) | `G = G'` |
| `fel`, `fpic`, `flf` | G (one rule for each constructor) | `G = G'` |
| `ftsb` | D or G | `D = D'` or `G = G'`, respectively |
| `fmsb` | D, G, or A | `D = D'`, `G = G'`, or `G ⊢ A = A'`, respectively |
| `fcomp` | T, D, or G | `T = T'`, `D = D'`, or `G = G'`, respectively |
| `flift` | D or G | `D = D'` or `G = G'`, respectively |
| `fsec` | G | `G = G'` |

For example the type-coordinate rule for term action is

    A : Ty(G)    a : El(G,A)    s : Sub(D,G)    G ⊢ A = A'
    ------------------------------------------------------
    D ⊢ fmsb D G A a s = fmsb D G A' a s : ftsb D G A s

The right term is formed using term conversion in G, then converted
back at D using type-action congruence. For the G-coordinate rule
for a lift, form `flift D G' A s` after moving s and A across
`G = G'`. The endpoints of the right lift are then converted
using the G-coordinate rule for type action and context extension
equality. For the G-coordinate rule for a Π-code, use decoding
congruence to
identify the body contexts and universe congruence to change the
body's universe annotation. For composition a change of the middle
context retypes the codomain of d and the domain of s.

The inherited congruences cover the original fields. In particular
the inherited projection and variable congruences cover the context
and extension type, and the inherited lift and section congruences
cover the recorded type. Their one-coordinate forms are obtained
with reflexivity in the other fields. No new equality rules are
required for the meta-level natural number indices.

## F1–F2. Syntax, erasure, and generation

**DONE.** `gen_aannot.py --full` generates `FGAT.seg`, `FForget.seg`
and `FGen.seg`. The 87 inherited rules and 17 new congruences all
erase to derivations in T_E^a. `FPresup.seg` proves presuppositions
for every full rule. `FCtx.seg` and `FGen.seg` recover context
equality and the introduction frames of types, terms and
substitutions. The `FullCheck.seg` examples check a changed
composition middle context and a term action with different
convertible operand type annotations. The default generator still
reproduces `AAnnot.seg` byte for byte.

Extend the generator with a separate full mode. Parse the inherited
signature once, distinguish type and term action by their sort, and
record the typing frame explicitly where it is lost by the syntax
of the inherited declaration. Generate the inductive definitions
and the corresponding erasure skeleton from the same signatures.
The default mode must still regenerate the existing `AAnnot.seg`
byte for byte.

The raw map `ff : FA -> GA` retains the six original leaf
annotations, drops all the new fields, and sends both actions to
`asb`. Erasure of a copied rule is the inherited rule on erased
arguments, including the appropriate typed action introduction.
Each new congruence erases to reflexivity of the left expression,
using its erased formation premises. The annotation-equality
premise is unnecessary for this erasure.

Port presuppositions and generation against the full rules. In
generation remember the introduced frame from the constructor and
collect outer context and type conversions as in `AGen.seg`. For
term action the operand type is the recorded A and the introduced
output type is `ftsb D G A s`. For composition there is a recorded
middle context. Wrong-sort cases for the two actions are now
distinct. Recover bounds from the universe typing premise through
conversion, and keep the existing convention that a level that
does not appear in a derivation premise has its own bound premise.

## F3–F4. Prescribed contexts and coherence

**DONE.** `FCoherence.seg` compares full contexts, types, terms and
substitutions by induction on their common `GA` image. Term comparison
also returns equality of the typing types. Substitution comparison
returns equality of the targets and an equation at the left endpoints.
`FSubTransport.seg` transports substitution equations by changing the
middle annotation and applying each unit law.

`FAnnot.seg` reuses the original alignment plans for 81 rules and
adds lifts for the six leaf congruences. It checks all eight judgement
forms and gives exact raw erasure. The fixed-context interface quantifies
over both endpoints of substitutions and their equations.

Use the lifting interface of `AAnnot.seg`. Each derivable judgement
has a full representative whose raw forgetful image is the given
judgement. Types, terms and equations must be realizable at any
well-formed full context with the required image. For substitutions
and substitution equations both endpoints may be prescribed.
Build formation frames from the recursive results. Use context
and type conversion to align independently chosen representatives
without changing the raw forgetful image. The conversions that
align independently lifted premises use F4, so F3's induction can
be specified before F4 and checked once the required coherence
lemmas are available.

Extend U1 by induction on the common raw `GA` expression. Use
generation to recover each introduced frame and the conversions
to the outer judgement. For substitutions assume equality of the
domains and return both equality of the codomains and a substitution
equation at the left endpoints. In the composition case the
comparison for d supplies equality of the middle contexts for s.
For actions compare the substitutions first, then compare the
operands over the identified target. Use the annotation congruences
and ordinary payload congruences to combine the results.

For terms use the strengthened U1 statement. Given equal outer
contexts and equal raw forgetful images, return equality of the
typing types as well as equality of the terms at the left type.
In the term-action case the forgotten operand types A and A' need
not have equal raw images. Their equality comes from the recursive
comparison of the operands typed at A and A', then changes the
stored type field via its annotation congruence. This avoids
recursing on an erased argument outside the common raw tree.
A common raw `asb` has both a type and a term comparison branch.
Generation rejects the wrong-sorted full action in either branch.

When moving a substitution equation to new endpoints, insert identities
as in `ACtx.move-se`. Change the middle annotation with
`fq-comp-middle` before applying the unit equation. First cancel the
inner identity while its codomain is the old target. Then change the
outer middle context and cancel the outer identity.

Before wiring the induction, check a composition with changed
middle context and a term action whose different operand type
annotations erase to different but convertible raw types.

## F5–F6. Russell correspondence and paper

**DONE.** `FRGAT.seg` gives lifting, erasure and coherence at the
Russell image through `ARGAT`. The smoke checks cover changed middle
contexts, different erased operand types for term action, prescribed
substitution equation endpoints, and lifting and erasing a Russell
variable. `FullCheck.seg` checked 3,776 declarations and
`GATCheck.seg` checked 3,728, with zero failures. The full Unit suite
passed. Deliberate errors were rejected in every new Seg file, and
both generator modes reproduced their checked files byte for byte.
Section 15 and the file table in `gat-ehrhard.tex` were compiled
twice and checked in a scratch PDF because the repository PDF has
local edits.

Compose the strict lifting and forgetful maps with `ARGAT.seg`.
If two full lifts have equal double erasure, use ARGAT uniqueness
to obtain annotated equations and lift these at the prescribed
full contexts. Use F4 to compare the lifted equation endpoints
with the given full endpoints. Include well-formed contexts, types,
terms and both equality judgement forms in the correspondence.

Add a section and a file-table row to `gat-ehrhard.tex`. State
which sort arguments are now explicit, why the two action
constructors have the same forgetful image, and the existence and
coherence theorems. Retain the common bound N and Ehrhard's
generators.

## Checklist

- [x] F0 design of rules, congruences, and induction motives
- [x] F1 generated `FGAT.seg`
- [x] F2 erasure, presuppositions, and generation
- [x] F3 annotated representatives at prescribed contexts
- [x] F4 coherence extending U1
- [x] F5 composition with `ARGAT`
- [x] F6 paper section and file table
