# ERTUU — Tarski ⇔ Russell ⇔ PTS for U : U

The type-in-type variant of `ERT/` (paper `sterbac1.pdf`, §4.2):
a single universe containing its own code, no levels, no lifts.

* Tarski (`TarskiTyping`): `UCode : U`, `PiCode a b : U`,
  `El UCode = U`, `El (PiCode a b) = Π (El a) (El b)`, βη.
* Russell (`RussellTyping`): `U : U`, βη.

Results (all checked with `--safe --without-K --exact-split`, no
postulates, no pragmas):

* Lemma 4.6  `EraseDeriv.erase-*`: erasure of Tarski derivations.
* Lemma 4.10 `Uniqueness`: same erasure ⇒ convertible
  (`type-uniq`, `term-uniq`, `uniq-El`).  With one universe there is no
  "common lift" alternative, and NO property of conversion is needed
  (no injectivity, no no-confusion, no model): only syntactic
  inversion, by structural recursion on the Tarski expressions.
* Theorem 4.13 `Equivalence.lift-*`: every Russell judgement lifts to a
  Tarski one; the record `Equivalence.equivalence` packages the result.

Built by specialising the `ERT/` sources (Tarski metatheory,
lift-back) and rewriting the uniqueness lemma, which becomes much
simpler.

## §4.3: T_R ⇔ T_P (added 2026-09-25)

T_P = unannotated Russell theory (λ keeps its domain, application keeps
nothing), `strip : T_R → T_P`.  With U : U, T_P does NOT normalise, so a
proof through normal forms is impossible; the one non-syntactic
ingredient, Π-injectivity of T_R, comes from the domain model.

* `PiInjectivityR.PiInj-R`: Π(C0,B0) = Π(C1,B1) ⇒ C0 = C1, B0 = B1, by
  adequacy of the finite-element model (`Dom/`, `Model/`, `Valid/`,
  `Adeq/`, ported from `ERT/` with levels removed from the syntax;
  the model keeps its levelled universe codes and interprets U as the
  level-0 universe, which is sound because membership ignores levels).
* `StripDeriv` (Thm 4.15): T_R derivations strip to T_P derivations.
* `StripUniq` (Lemma 4.17/4.18): strip u0 = strip u1 ⇒ Γ ⊢ T0 = T1 and
  Γ ⊢ u0 = u1 : T0.  No cumulativity, so the paper's induction on the
  term works as written (contrast `ERT/Gap417`, `ERT/StripUniqNF`).
* `SectionR` (Thm 4.19): every T_P judgement lifts into every T_R
  context over its context, uniquely up to conversion.

The T_R rules now carry the presupposition premises of `ERT/`'s
binder congruences (the paper's rules are `RussellMeta.mk-*`);
`EraseDeriv` / `Equivalence` patched accordingly.

Check everything: `~/.cabal/bin/agda-2.9.0 --safe ERTUU/All.agda`
(from scratch ≈ 13 s).
