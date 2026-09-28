# Next session: §4.3 of sterbac1.pdf (T_R ⇔ T_P)

Checker: `~/.cabal/bin/agda-2.9.0 ERT/<File>.agda` from `~/DOMAIN`.
Rules: `--without-K --exact-split`, no postulates, no TERMINATING, ≤20 s/file.
ERT/ is gitignored: snapshots in the session scratchpad only.

## DONE (2026-09-24, all EXIT 0, no postulates/pragmas)

* **Adequacy of the domain model for T_R** — `ERT/Adeq/`:
  `Stmt` (statements Adq/AdqConv/AdqE1 + type forms AdqTy/AdqConvTy/AdqETy,
  converters, soundness wrappers evFwd/evBwd, Ann-refl), `Pi` (Π formation,
  Sup transports, app-transport), `PiConv` (Π two-sub + conv-Ty-Pi),
  `Lam` (λ with convertible annotations, beta-ann, lamSel), `LamConv`
  (λ two-sub), `LamCong` (Lam-body, Lam-Ty, Adq-right/AdqConv-right),
  `App`, `AppCong` (App-fun; App-arg generalised to any `Ann` pair, which
  also covers conv-cong-App-Ty), `Beta` (Adq-subst1, β), `Eta`,
  `Driver` (mutual adqTy/adqTyC/adqTm/adqTmC/adqCTy/adqCTm, STRUCTURAL).
  Whole cone recompiles clean in ~3 s.
* **Π-injectivity for T_R** — `ERT/PiInjectivityR.agda`:
  `PiInj-R : ConvTy G (Pi C0 B0) (Pi C1 B1) -> Pair (ConvTy G C0 C1) (ConvTy (extend G C0) B0 B1)`
  (adequacy at idSub, bottom env, code PiCode Bot nil).
* **T_P** — `ERT/PTyping.agda` (paper A.4, lean rules, syntax = Model.Core).
* **Theorem 4.15** — `ERT/StripDeriv.agda` (strip-WfCtx/IsType/HasType/ConvTy/ConvTm).
* `ERT/Gap417.agda` — see OBSTRUCTION below (also `U-inj-R` from soundness).

### Rule change made this session (flag to user)
The value-only adequacy driver needs the two-substitution validity of the
codomain / body, which T_R's binder congruences did not carry as
subderivations (exactly MIN's conv-Pi obstruction).  Fixed as MIN did:
`conv-Ty-Pi`, `conv-cong-Pi`, `conv-cong-Lam-body`, `conv-cong-Lam-Ty` now
also take the LEFT typing of B (resp. b) as a premise.  These are
presuppositions; the paper's rules are the `mk-*` lemmas of RussellMeta.
§4.2 files patched (RussellMeta, RussellMetaCong, EraseDeriv via
RM.presup-l-*, Equivalence, Model/RussellSound): all EXIT 0.
(Pre-existing, untouched: `UniquenessTermPartial.agda` term-uniq has a
CoverageNoExactSplit WARNING.)

## OBSTRUCTION: the paper's proof of Lemma 4.17 has a gap (cumulativity)

`ERT/Gap417.agda` (verified): f0 = λ(U1,U1,v0) : Π(U1,U1),
f1 = λ(U1,U2,v0) : Π(U1,U2); u0 = app(U1,U1,f0,U0) : U1 ≤ U2 (last rule
cumulativity), u1 = app(U1,U2,f1,U0) : U2.  strip u0 = strip u1,
A0 = A1 = U2, so 4.17's hypotheses hold; the app case of the proof needs
Π(U1,U1) = Π(U1,U2), which is refuted (`no-Pi-conv`).  The statement is
not refuted (`u0=u1` holds by β).  The paper's step "strip'(B0[a0]) =
strip'(B1[a1])" assumes the last rule is app, ignoring cumulativity.
Same issue already for the TYPE part (types with β-redexes whose λ's
codomain annotations differ by cumulativity), which Thm 4.19's EXISTENCE
also needs.  Candidate routes (need user decision):
 A. syntactic Kripke logical relation "cumulative similarity" (extensional
    relation when types differ only at universe leaves), closed under
    substitution;
 B. normalisation / NbE completeness for T_R, compare normal forms;
 C. change T_R (e.g. make λ's codomain annotation not subject to cum).
Useful available facts: whnf of types from adequacy (ValTy2 at UCode /
PiCode gives Red3), strip commutes with head reduction, PiInj-R, U-inj-R,
no-confusion (EvalRel of Pi at UCode is Empty).

## UPDATE: Lemma 4.18 PROVED assuming weak β-normalisation of T_P (2026-09-24)
User's direction: follow Streicher (bstreicher1.pdf Thm 4.12/4.13 method) with
only β-normal forms assumed.  All EXIT 0, no postulates (WN is a module param).
* `PReduction.agda` — full β on T_P, `Ne`/`Nf`, hypothesis `WN-P`.
* `RussellStep.agda` — T_R β-steps at stripped-visible positions; `liftStep`/
  `liftStar`: a T_P step of strip(u) lifts to EVERY preimage u.
* `RussellInversion.agda` — `SubTy` (conversion or universe-cumulativity),
  inversion lemmas peeling conv+cum, `U-inj-R`, `Pi-U-noconf` (soundness).
* `SubjectReductionR.agda` — `SR`/`SR-star`: reduct CONVERTIBLE (β case via PiInj-R).
* `StripUniq.agda` — `ne-conv`/`nf-conv` (strip-equal terms with β-normal
  stripping are convertible; neutral heads force annotations; λ via
  Π-injectivity; cumulativity only at root); under `(wn : WN-P)`:
  `type-uniq-R`, `term-uniq-conv-R`, `term-uniq-R` (= Lemma 4.18).
NEXT: Theorem 4.19 (section of strip) using term-uniq-R, same WN parameter.

## UPDATE: Theorem 4.19 PROVED under WN-P (2026-09-24)
* `SectionR.agda`: `lift-IsType/HasType/ConvTy/ConvTm` lift a T_P judgement
  into EVERY well-formed T_R context over its context (structural on the T_P
  derivation; premises reconciled by type-uniq-R / term-uniq-conv-R);
  `lift-WfCtx` (recursion on the context), `section-HasType/IsType`
  (existence), `section-uniq-Tm/Ty` (uniqueness up to conversion = 4.18).
* To keep this structural, T_P rules now carry the presupposition premises
  of T_R (PTyping), and T_R `conv-cong-App-Ty` also takes IsType (Γ.A) B.
  All §4.2 files and the adequacy cone re-patched; whole ERT cone
  rechecks from scratch (SectionR cone ~12 s total), no postulates/pragmas.
§4.3 is complete MODULO the hypothesis WN-P (weak β-normalisation of T_P).

## UPDATE (2026-09-25): 4.18 and 4.19 WITHOUT NORMALISATION
* `StripUniqNF.agda` (~500 lines, <1 s): structural induction on the term,
  using only PiInj-R, U-inj-R, Pi-U-noconf (the paper's Thms 7-9).
  Key idea: η-coercions `coe (piC A B L k) t = λ(A,L, coe k (app(A↑,B↑,t↑,v0)))`
  and `Join G T0 T1 L k0 k1` (pointwise-max of types differing in universe
  levels, also under Π).  `main`: strip-equal u0:T0, u1:T1 ⇒ Join + coe u0 = coe u1 : L.
  `Join-diag` (T0 = T1 ⇒ t0 = t1, via η; universe join level is exactly max so no
  lowering needed).  Exports type-uniq-NF / term-uniq-conv-NF / term-uniq-NF.
* `SectionR.agda` now imports StripUniqNF: Theorem 4.19 unconditional.
* `StripUniqNFTest.agda`: the Gap417 example closed by the lemma.
* WN route (StripUniq, PReduction, RussellStep, SubjectReductionR) kept, superseded.
* sec43.tex §"Lemma 4.18 without normalisation" written, PDF rebuilt.
