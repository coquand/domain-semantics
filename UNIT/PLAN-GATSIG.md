# PLAN-GATSIG: T_E^full derives exactly what the GAT derives (Part A)

Handoff, 2026-11-23. Read this whole file before touching code.

## 1. Goal

The paper will use Ehrhard's generators (id, σ∘δ, (), p, q, lift_A(σ),
sec_A(a)). The completely annotated theory T_E^full (`FGAT.seg`, §13 of
`gat-ehrhard.tex`) is a deductive system written *by hand*, following the
shape of a GAT. It is related to T_Russell by `FRGAT`.

What is missing is the statement that T_E^full derives exactly the
judgements of the generalised algebraic theory with this signature, in
Cartmell's sense.

Goal: for every closed judgement J,

    T_E^full ⊢ J   ⟺   GAT(Σ_E) ⊢ J

where GAT(Σ_E) is the deductive system *generated* from the signature Σ_E
by Cartmell's generic rules. Composing with `FRGAT` then relates T_Russell
to the GAT itself. Initiality of the syntactic model is out of scope (§6).

## 2. Ground rules (from the user)

- **Git.** Never `git add -u` or `git add -A` in DOMAIN; the user keeps
  uncommitted tex/pdf work. Stage explicit paths. Commit or push only when
  the user asks.
- **Wording.** Say "U : U", never "Type:Type".
- **Status.** Report status plainly: proved, open, stuck on X. Flag an
  obstruction as soon as you see it.
- **Proof checks are fast.** Each file should check in seconds. Split by
  rule groups.
- **Check that a new file is really checked.** After a first green check,
  plant a deliberate error, see it rejected, then restore the file.
- **Coordinate with other sessions.**
  - Only create new files: suggested prefix `C` (Cartmell), e.g. `CSig.seg`,
    `CGAT.seg`, `CToFull.seg`, `CFromFull.seg`, `CCheck.seg`.
  - Use your own driver `CCheck.seg` while working. Add one import line to
    `GATCheck.seg` and `All.seg` only when green.
  - Do not edit existing files; ask the user if you need to.
  - Do not touch the user's untracked files (`Syntactic*.seg`,
    `SmallQuotient.seg`, `Scott*`, `Presheaf*`, `_dev*`, ...).
- **Checker.** The indexed checker:

      SEG=/Users/coquand/CANONICITY/unit-indexed/dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg
      cd ~/DOMAIN/UNIT && $SEG GATCheck.seg      # 3728 declarations, 0 failed
      cd ~/DOMAIN && python3 UNIT/check.py        # everything

## 3. Read first

- `~/DOMAIN/sterbac4.pdf` §2.1 (Definitions 1–7: sorts, operations with
  their telescopes, equations).
- `UNIT/gat-ehrhard.tex` §§1, 6, 12, 13, 15 (rebuild the PDF if needed).
- `UNIT/FGAT.seg` (generated: raw syntax `FA`, judgements `FAJ`, rules
  `FADer`, 128 constructors), `UNIT/PLAN-ANNOT-FULL.md`, and the generators
  `gen_aannot.py --full`, `gen_full_*.py`.
- Cartmell, "Generalised algebraic theories and contextual categories"
  (1986), for the generic rules.

## 4. The signature Σ_E

Fix the level bound N, as everywhere (module `BoundedSyntax (N)`).
- **Sorts:** ctx; Sub(Δ, Γ); Ty(Γ); Tm(Γ, A) for A : Ty(Γ).
- **Operations, each with its full typed telescope:**
  - contexts: 1, Γ.A;
  - substitutions: id_Γ, σ∘_{Θ,Δ,Γ}δ, ()_Γ, p_{Γ,A},
    lift_{Δ,Γ,A}(σ), sec_{Γ,A}(a);
  - actions: A[σ]_{Δ,Γ}, a[σ]_{Δ,Γ,A};
  - variable: q_{Γ,A};
  - products: Π_Γ(A,B), λ_Γ(A,B,b), app_Γ(A,B,c,a);
  - universes: (U_n)_Γ, T_{n,Γ}(a), Π_{n,Γ}(a,b), (U^n_m)_Γ (m < n),
    t^n_{m,Γ}(a) (m < n);
  - all levels ≤ N.
- **Axioms, each with its full typed telescope:**
  - the category laws, uniqueness of ();
  - Ehrhard's equations (§1 of the tex);
  - naturality of every former;
  - β, η;
  - the six Tarski equations;
  - the lift equations.

Take the list from the axiom rules of `FGAT.seg` (or `GAT.seg`), one
axiom per equation rule. Record the signature in a data file or a Python
module, e.g. `sig_ehrhard.py`, from which the rules are generated. Later
changes of generators then only change this input.

## 5. Plan

- **C0. Design note** (`PLAN-GATSIG-C0.md`; report before coding C3–C4).
  Fix:
  1. The generic Cartmell rules to generate, for closed judgements:
     - formation/introduction of each operation from its telescope;
     - each axiom at any well-sorted instance;
     - reflexivity, symmetry and transitivity at each sort (including ctx);
     - congruence of every operation in *all* arguments simultaneously
       (sort arguments included);
     - sort equality: Γ = Δ, A = B ⇒ Ty(Γ) = Ty(Δ), Tm(Γ,A) = Tm(Δ,B),
       Sub(Δ,Γ) = Sub(Δ',Γ');
     - sort conversion (t : S, S = S' ⇒ t : S').
  2. Whether open judgements (GAT variables) are needed. Argue, or prove
     as a lemma, that closed judgements have closed derivations
     (substitution for GAT variables). The intended answer is: generate
     only closed rules, where axioms are instantiated directly by closed
     terms.
  3. The representation: reuse the raw syntax `FA` of `FGAT.seg`
     (judgements `FAJ`) if possible, so that the equivalence is between
     two inductive families over the same raw judgements.
- **C1. Generator and generated system.** `gen_cartmell.py` reads the
  signature and writes `CGAT.seg` (`data CDer : FAJ -> U l`). Commit the
  script with its output; the output must be reproducible byte for byte.
- **C2. `CGAT ⊢ J ⇒ T_E^full ⊢ J`** (`CToFull.seg`, by induction on
  `CDer`).
  - Main work: derive the simultaneous congruences in all arguments from
    `FGAT`'s one-argument congruences, by transitivity and conversion.
  - Sort conversion comes from the `*-cx` / `*-conv` rules.
  - Axiom instances are `FADer` rules, possibly using the presuppositions
    (`FPresup`).
- **C3. `T_E^full ⊢ J ⇒ CGAT ⊢ J`** (`CFromFull.seg`, by induction on
  `FADer`). Each `FGAT` rule must be an instance or a derived rule of
  `CGAT`. Watch for:
  - converting a substitution at both ends at once;
  - context equality rules (`fc-*`);
  - rules whose premises are *weaker* than the full telescope. Those need
    `CGAT`'s presuppositions, so prove the presupposition lemma for `CGAT`
    first, generated like `FPresup`.
- **C4. Composition.** `CRGAT.seg`: T_Russell ↔ GAT(Σ_E), from C2, C3 and
  `FRGAT`.
- **C5. Documentation.**
  - In `gat-ehrhard.tex` §13, add a short paragraph and the theorem (the
    mathematical statement only; no file names in §§1–14).
  - In §15, add a table row and a sentence.
  - Re-read the file right before editing; others edit it too.

## 6. Out of scope

Initiality of the syntactic model (Part B) is not part of this task. The
user decided that Part A is enough for now; do not start it.

## 7. Checklist

DONE 2026-11-23: CSig.py/CGen.py generate CGAT.seg (19 operations, 32 axiom
schemes); CToFull (CDer -> FADer), CPresup, CFromFull (FADer -> CDer),
CRGAT (c-derivability, T_Russell <-> GAT); gat-ehrhard.tex section 13.

- [x] C0 design note reported
- [x] C1 `gen_cartmell.py` + `CGAT.seg` (reproducible)
- [x] C2 CGAT ⇒ T_E^full
- [x] C3 T_E^full ⇒ CGAT (with CGAT presuppositions)
- [x] C4 T_Russell ↔ GAT(Σ_E)
- [x] C5 tex
