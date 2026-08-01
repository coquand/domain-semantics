# OBSTINATION/ — Colson's ultimate obstination, and the value at the infinite point

A self-contained Agda formalisation of two results about primitive-recursive
terms read as monotone maps on the lazy naturals.

> **Une preuve directe du Théorème d'Ultime Obstination** — [`min1.pdf`](../min1.pdf)
>
> **The value of a primitive recursive term at the infinite point** —
> [`prinf.pdf`](prinf.pdf) ([source](prinf.tex))

The first is a *direct constructive* proof of Colson's 1989
ultimate-obstination theorem, together with its corollary: **the denotations of
primitive-recursive terms are computable objects**. As a concrete instance we
run a primitive-recursive `min` on two copies of the infinite element `S^ω(⊥)`
and watch it return `⊥`.

The second proves that computability statement again, from a weaker starting
point: **from the term's trace alone**, with the ultimate-obstination property
used nowhere. That matters because the property is outright *false* for
mutually recursive blocks, while the trace-level invariant is not.

Everything is machine-checked with Agda `2.9.0`, `--safe --without-K
--exact-split`, **no standard library, no postulates, no holes, no pragmas**
(not even `BUILTIN NATURAL`). The obstination cone is 64 modules, the trace
cone 127; all green.

**Spartan by design:** the only indexed inductive type used anywhere is `Eq`
(propositional equality). The `n`-tuples `Dⁿ` are plain `List`s indexed by
`Nat` — no `Fin`, no `Vec` — and arity is never tracked in a type; when a
statement needs it, the arity is `length A`.

## The domain

`D`, the *lazy naturals*, is far simpler than the reflexive domain of `MIN/` —
no universe, function codes, coherence, rank, logical relation, or adequacy.

| notation | constructor | meaning |
|---|---|---|
| `Sᵏ(0)` | `cpl k` | complete (maximal) |
| `Sᵏ(⊥)` | `bot k` | incomplete finite (`bot 0 = ⊥`) |
| `S^ω(⊥)` | `inf` | the unique infinite element |

The order is `Sᵏ(⊥) ≤ S^ω(⊥)` and `Sᵏ(⊥) ≤ Sˡ(x)` for `k ≤ l`, with `Sᵏ(0)`
and `S^ω(⊥)` maximal. `PR` is the syntax of primitive-recursive functions
(constant `0`, projections, successor, composition, primitive recursion); its
finite interpretation is `evalF : PR → FTup → FEl`.

## Main results — where they are proved

| Result | File | Name |
|---|---|---|
| **Ultimate obstination (Proposition 1)** | [`Prop1.agda`](Prop1.agda) | `prop1` |
| **Computability of the extension** | [`Computable.agda`](Computable.agda) | `fhat`, `fhat-diag` |
| **`min` at the infinite diagonal** | [`PredMin.agda`](PredMin.agda) | `min-inf` |
| **`MP1` for every PR term's trace** | [`TrTermMP1.agda`](TrTermMP1.agda) | `traceOf-MP1np` |
| **The value at `S^ω(⊥)`, from the trace alone** | [`PRInfMP1.agda`](PRInfMP1.agda) | `prValMP`, `prValMP-lub` |

```agda
prop1 : (p : PR) (A : Tup) -> Wf p (length A) -> UO (evalF p) A
```

`prop1` proves, by induction on the primitive-recursive term `p`, that its
finite interpretation `evalF p` satisfies the **ultimate-obstination property**
`UO` at every point `A` of `p`'s arity (`Wf p n` is the arity predicate). The
property [`Property.agda`](Property.agda) says: at `A` there is a finite
`A₀ ≤ A` and one of three cases — `f` is eventually the constant `Sᵐ(0)`;
or eventually `Sᵐ(⊥)` pinned at an incomplete-finite coordinate; or, at an
infinite coordinate, governed by a numeric witness `φ` (constant or strictly
increasing).

## The computability corollary

Read intuitionistically, the property *carries the value*: from a `UO f A`
witness one computes the value `f̂(A)` of the Scott-continuous extension —
`uoValue` in [`Property.agda`](Property.agda). Since `prop1` and `uoValue` are
total, postulate-free functions, their composition **is** the algorithm:

```agda
fhat      : (f : PR) (A : Tup) -> Wf f (length A) -> D          -- f-hat at every arity point
fhat-diag : (f : PR) (n : Nat) -> Wf f n         -> D          -- ...at (S^ω⊥, …, S^ω⊥)
```

so `f̂` is computable at every domain point, including the infinite diagonal
`x = S^ω(⊥)`.

## `pred` and `min` at `S^ω(⊥)` — obstination made concrete

[`PredMin.agda`](PredMin.agda) defines three standard PR terms and checks (by
`refl`) that they are the real functions on total inputs, then evaluates their
extensions at the infinite diagonal:

```agda
predPR = prec zerf (proj 0)                                 -- pred 0 = 0, pred (S x) = x
subPR  = prec (proj 0) (comp predPR [ proj 1 ])             -- sub'(y,x) = x ∸ y   (recursion on y)
minPR  = comp subPR [ comp subPR [ proj 1 , proj 0 ] , proj 0 ]   -- min x y = x ∸ (x ∸ y)
```

| denotation at `x = S^ω(⊥)` | value | why |
|---|---|---|
| `pred̂(x)` | `S^ω(⊥)` | `pred` is lazy in its argument |
| `sub'̂(x, x)` | `⊥` | recursion on the first argument never terminates — `S^ω(⊥)` has no outermost successor to peel |
| **`min̂(x, x)`** | **`⊥`** (not `x`!) | `min = x ∸ (x ∸ y)` inherits subtraction's obstination |
| `add̂(x, x)` | `S^ω(⊥)` | positive contrast: the step is `succ`, so `uₖ = Sᵏ(⊥)` rises to infinity (case 3, `φ` strict) |

That a primitive-recursive `min` yields `⊥` on `(S^ω⊥, S^ω⊥)` — rather than the
`S^ω⊥` the *ideal* min would give — is Colson's ultimate obstination in one
line: **no** PR algorithm can be lazy enough to answer here. Addition, whose
step function is strictly increasing, instead climbs to `S^ω(⊥)` (`∞+∞=∞`) — the
denotation faithfully tracks the algorithm. A high-level write-up is
[`obstination.tex`](obstination.tex).

## The trace, and the value at the infinite point

[`prinf.pdf`](prinf.pdf) proves the computability statement a second time, from
a different and weaker starting point. A **trace** records what the computation
looks like from outside: substitute `⊥` for every variable, ask for the normal
form, replace by `S(xᵢ)` the variable it is stuck on, and repeat. What comes out
is a walk `iv(0), iv(1), …` — the variable demanded at each step — a value
sequence `ov(0), ov(1), …` — what the term has produced when it sticks — and a
continuation for each coordinate that turns out to be a numeral rather than an
`Sᵏ(⊥)`. The trace is built by induction on the term and *proved to denote* it,
so it is not a separate model to be related to `evalF` afterwards
([`TraceDef.agda`](TraceDef.agda), [`TrTerm.agda`](TrTerm.agda)).

The invariant `MP1` [`TrMP1.agda`](TrMP1.agda) asks, at every node of a trace:
the walk is eventually constant, and the value sequence has a *verdict* —
either some `ov(k)` is complete, or the height of `ov` is eventually constant or
eventually strictly increasing.

| Result | File | Name |
|---|---|---|
| `MP1` holds for the trace of every PR term | [`TrTermMP1.agda`](TrTermMP1.agda) | `traceOf-MP1np` |
| `f(S^ω⊥, …, S^ω⊥)` is computable, and is the lub of the diagonal chain | [`PRInfMP1.agda`](PRInfMP1.agda) | `prValMP`, `prValMP-lub` |
| `MP1` alone does **not** imply ultimate obstination | [`TrUOFail.agda`](TrUOFail.agda) | `uo-fails` |
| the ingredient it is missing, totality | [`PRTot.agda`](PRTot.agda) | `evalF-tot` |

Neither result uses the ultimate-obstination property; the only thing either
takes from that development is its well-formedness *predicate*. The two closure
arguments are composition ([`TrCompMP1.agda`](TrCompMP1.agda)) and primitive
recursion ([`TrPrecOvP.agda`](TrPrecOvP.agda), on the general lemma
[`TrFeedR.agda`](TrFeedR.agda): a trace fed a monotone family, with descents).

**Mutual recursion.** Section 7 of [`prinf.pdf`](prinf.pdf) treats a block of
simultaneously defined functions, where ultimate obstination is outright false
but the trace-level statement is not. A block has a trace of exactly the same
kind — primitive recursion with its layer a vector, unfolding on the numeral
depth — carrying value sequences and continuations, and it is proved to denote
the block; for two functions the verdict then follows from the step terms alone,
with no obstinacy hypothesis. David's static "recursively calls" graph is
readable off the walk's own eventually-constant label, and is also avoidable, at
the price of an `r`-ary rather than a unary iteration. (Those modules are not in
this repository yet.)

## How the obstination proof works (high level)

Induction on the PR term:

- **`zerf` / `proj` / `succ`** — obstinate at every point of the right arity
  ([`Prop1Base.agda`](Prop1Base.agda)); these are the paper's "vérifient
  clairement cette propriété".
- **`comp g hs`** — the witness functions `φ` are closed under composition, so
  the composite is obstinate; assembled generically over an inner tuple of
  obstinate functions ([`CompDispatch.agda`](CompDispatch.agda)).
- **`prec g h`** — the heart. For the infinite first argument one forms the
  Kleene sequence `u₀ = ⊥`, `u_{k+1} = ĥ(S^ω⊥, uₖ, Y)`; a constructive
  dichotomy decides whether it stabilises (finite limit) or keeps up with the
  diagonal, splitting into the paper's two principal cases with the numeric
  witness `ψ` built from `φ` ([`USeq*`](USeq.agda), [`PrecInf*`](PrecInf.agda),
  [`PrecBot*`](PrecBotStep.agda), assembled in [`PrecAll.agda`](PrecAll.agda)).
  Berry **stability** (every PR element is stable) is what tames the coupling —
  the note's "récurrence directe", not the stronger Kahn–Plotkin sequentiality
  (see [`sequentiality-note.md`](sequentiality-note.md)).

The recursion chain is proved once over an *abstract* base/step bundle
`RecData` ([`PrecFun.agda`](PrecFun.agda)); the top level then feeds it the
**arity-guarded** interpretations of the sub-terms — `guard n (evalF g)` is
total and obstinate ([`Arity.agda`](Arity.agda)) — and transports the result
back to the concrete interpreter ([`PrecGuard.agda`](PrecGuard.agda),
[`Prop1Comp.agda`](Prop1Comp.agda)). This is what lets a plain induction go
through even though a sub-term is obstinate only at its own arity.

**Remaining (not the theorem itself):** Phase 4 — the page-4 characterisation
of the witness functions `φ` and the "not quadratic" corollary answering
Colson 1991.

## Building

Requires Agda `2.9.0`, no external library. Type-check the headline results:

```sh
agda --safe --without-K --exact-split OBSTINATION/Prop1.agda      # Proposition 1
agda --safe --without-K --exact-split OBSTINATION/PredMin.agda    # pred / min at S^ω(⊥)
agda --safe --without-K --exact-split OBSTINATION/TrTermMP1.agda  # MP1 for every PR term
agda --safe --without-K --exact-split OBSTINATION/PRInfMP1.agda   # the value at S^ω(⊥)
```

Green-check the whole cone:

```sh
for f in OBSTINATION/*.agda; do
  agda --safe --without-K --exact-split "$f" || echo "FAIL: $f"
done
```
