# MAHLO — coordination handoff: P2 and P3 in parallel

**Roles.**
- This session is the **coordinator**.
- Two peer terminals are open in `~/DOMAIN`: **`domain-e2`** does P2 and **`domain-6c`** does P3. Check the names with `ListAgents` and message them with `SendMessage`; the names may change if a terminal is restarted.

**State.**
- The plan is `mahlo-plan.tex` / `.pdf`.
- P1 is DONE (`MAHLO/All.agda`, `--safe`; see `MAHLO/NEXT_SESSION_P2.md` and memory `project_mahlo_p1_done`).

**Conventions (all sessions).**
- Use `~/.cabal/bin/agda-2.9.0`, with `timeout 20` per file.
- `--without-K --exact-split --safe`; no postulates.
- Spartan Agda; Eq premises instead of indexed constructors.

## Step 0 (coordinator, before the peers start)

Write `MAHLO/Syntax.agda` and type-check it, then **freeze** it: no session edits it afterwards without asking the coordinator. It contains:
- de Bruijn raw terms with **non-curried** constructors, following plan §1.1 and §6.1. Constructors: Var, Lam (annotated), App, Pi, Sigma, Pair, Fst, Snd, Nat, Zero, Suc, Rec, V, Ucode f g, Fhat f g A F, Ghat f g A F c;
- renaming and substitution, with their basic lemmas (follow `MIN/Syntax/Raw.agda` and `MIN/Syntax/Substitution.agda`);
- declarative typing and judgemental equality for the annotated Russell Mahlo rules of plan §1.2: subsumption U_{f,g} ⊆ V, closure rules with family argument λx:A.B, δ-equations in V only, rule (R′), plus Π, Σ with surjective pairing, η, ℕ with rec.

Possibly split into `Syntax.agda` and `Typing.agda`, each under 20 s.

## Step 1: send the briefs

**To `domain-e2` (P2, PER-model soundness, plan §6 Theorem 16), working in `MAHLO/`:**
1. Large types `Type` over the fixed point V*: V, the elements of V*, and Π/Σ over Type. Use an inductive relation with an interpretation, as in Abel–Coquand App. B, and prove that it end-extends V*.
2. Extend `TermModel` (in a NEW file, not by editing P1) with the denotation and substitution laws of Abel–Coquand §5.1, and add Σ with projections.
3. Define validity and prove the soundness theorem by induction on derivations, using `MAHLO.Fixpoint.Mahlo` for the universe rules ("key observation": a valid code already carries Indep and Op).
4. Use only the frozen `Syntax`/`Typing`. Report back when done or blocked.

**To `domain-6c` (P3, Step 1: Π/Σ-injectivity for the Mahlo rules, plan §3), working in a NEW directory `MAHLOINJ/`:**
1. Reuse the paper1-style adequacy of `MIN/` and `NAT/` (copy, do not edit the originals). Every universe denotes the single code U, and f̂/ĝ denote applications of f/g.
2. Add Σ with surjective pairing (paper1 §3.1) and the Mahlo rules. The universe clause of the logical relation records V versus U_{f,g} (with f ≡ f′ and g ≡ g′). Typed head reduction includes δ-steps, typed in V only.
3. Targets: Π- and Σ-injectivity, no-confusion, inversion of typing (plan Lemma 18), subject reduction for weak-head β.
4. Use only the frozen `MAHLO/Syntax`/`Typing`. Report back when done or blocked.

## Step 2: monitor
- Poll with `ListAgents`, and answer the peers' questions.
- Only the coordinator may change the shared modules; if a change is needed, notify both peers.
- Update `mahlo-plan.tex` (§7 Agda paragraph and the status table) and memory as the phases finish.

## Step 0 — DONE (2026-10-08), FROZEN
- `MAHLO/Syntax.agda` (<1 s) and `MAHLO/Typing.agda` (<1 s), `--safe`, EXIT 0; sanity test `MAHLO/TypingTest.agda`.
- Design: scope sizes `Num`; families are TERMS (`Pi A F`, `Sigma A F`, `Rec C z s n`, `Fhat f g A F`, `Ghat f g A F c`), so `Lam` is the ONLY binder; typing uses `PiB A B = Pi A (Lam A B)`, `SigmaB`, `Arr`, `OpF`, `OpG f`, `RecStep C`.
- Judgements `WfCtx / IsType / HasType / TyEq / ConvTm`; `Univ u` (Eq premises: u = V or u = Ucode f g); V has no type.
- η as `conv-funext`, surjective pairing as `conv-pairext`; Lam- and Pair-congruence omitted (derivable). δ (`conv-delta-f/g`) at V only; (R') = `conv-R'`; subsumption `ty-sub`/`conv-sub`.
- Grey premises (MIN style) on binder rules for structural recursion.
- 2026-10-08: domain-e2 found that P1 has no Σ, so V* is not closed under Σ and ty-Sigma is unsound in the model. The coordinator APPROVED adding Σ in place to the P1 files (TermModel, Pre, Congruence, Gamma, EndExt, Fixpoint), on condition that All.agda stays --safe and EXIT 0. Syntax and Typing are untouched.
- 2026-10-08: CHANGE to frozen Typing, at P3's request, with both peers notified. ty-Fhat, ty-Ghat, conv-delta-f and conv-delta-g gain the extra premises `HasType G f OpF` and `HasType G g (OpG f)`, needed for erased-model soundness and a structural fundamental lemma. P3 estimates 30–40k lines (a NAT/ copy plus Σ through the whole cone). Asked P3 to report layer by layer and to consider doing the Σ-free fragment first.
- 2026-10-08: P3 chose to add Σ to the Domain layer first, with no Σ-free pass, because the frozen Typing has Σ rules anyway. MAHLOINJ/Domain is copied from NAT/Domain and checks under --safe. Next: PairEl and SigmaCode, paper1 §3.1, with (⊥,⊥)=⊥ enforced by Coherent.
- 2026-10-08: P3 layer 1 DONE and verified by the coordinator. `MAHLOINJ/Domain/All.agda` checks under --safe, EXIT 0 (20 files, about 7k lines, no postulates, only BUILTIN NATURAL). It is NAT's domain plus PairEl/SigmaCode (paper1 §3.1), with (⊥,⊥)=⊥ via Coherent (PairNB). MAHLOINJ uses MAHLO.Basic.Eq. Next layer: Model (EvalRel over MAHLO.Syntax).
- 2026-10-08: **P2 DONE**, verified by the coordinator: a clean rebuild of MAHLO/All.agda takes 2.7 s, EXIT 0, --safe. Thm 16 is proved for every rule of the frozen Typing (new files Model, Type, Validity, ValPi, ValNat, ValU, Soundness), plus wt-safe = (T2a) in the model. It is relative to the abstract Model record and the Fixpoint hypothesis (Lemma 14). Σ was added to P1 in place. The plan's §7 and status table are updated. Not committed.
- 2026-10-08: SPLIT for P3. domain-e2 takes the syntactic metatheory in MAHLOINJ/Syntax/*: weakening, well-typed substitution, context conversion, presupposition, OpF/OpG/RecStep substitution instances, and TyEq (OpG f)(OpG f'). It must report any frozen rule whose presupposition fails for lack of a grey premise. domain-6c keeps MAHLOINJ/Domain, Model, Validity and Adequacy.
- 2026-10-08: P3 Model progress (checked by the coordinator): Model/Comb, Eval (EvalRel over MAHLO.Syntax, about 200 lines; V and Ucode both map to UCode; Fhat/Ghat are iterated App) and EvalSubst. Next: forward substitution, then soundness (InvTyp/InvConv). 6c's needs from e2: presupposition, well-typed substitution, TyEq (OpG f)(OpG f').
- 2026-10-08: **MAHLOINJ/Syntax DONE** (domain-e2), verified by the coordinator: a clean build takes 2.6 s, EXIT 0, --safe, 8 files, about 1.4k lines. It contains Weaken, Subst, CtxConv, Funct (CSub), Presup (pTm/pTE/pCv, opGEq) and Lemmas. Presupposition goes through with the frozen grey premises, so no Typing change is needed.
- 2026-10-08: domain-e2's NEXT task: inversion (Lemma 18) and SR for weak-head β/π/ι, proved syntactically from a hypothesis record `InjHyp` (Π/Σ-injectivity, no-confusion of type heads and Ucode-injectivity, all for TyEq). domain-6c's end target is now to inhabit InjHyp from the adequacy.
- 2026-10-08: **MAHLOINJ/Inversion DONE** (domain-e2), verified: clean build EXIT 0. It has inversion for every former and SR for weak-head β/π/ι, modulo `InjHyp` = {Pi-inj, Sig-inj, U-Pi, U-Sig, U-Nat, U-V}, all on TyEq. FINDING: no Fhat/Ghat no-confusion holds (δ+β gives Fhat f g A F ≡ Pi A F for f = λA F. Pi A F), and none is needed. So the plan's "no-confusion" target must exclude f̂/ĝ heads.
- 2026-10-08: **MAHLOINJ/Model DONE** (domain-6c), verified: a clean Domain+Model build takes 4.4 s, EXIT 0. It proves soundness of every frozen rule in the erased finite-element model. Next: Validity, Adequacy, then inhabit InjHyp. Risk: U-V, because V and Ucode have the same code in the erased model, so the universe clause must separate them syntactically.
- 2026-10-08: U-V was REMOVED from InjHyp; it was not really needed. InjHyp is now {Pi-inj, Sig-inj, U-Pi, U-Sig, U-Nat}, verified with a clean rebuild, EXIT 0. The erased model separates all three U-* heads, so the earlier U-V risk is gone. domain-6c has been told.
- 2026-10-08: domain-6c will get U-Pi/U-Sig/U-Nat from the model alone (Model/NoConf). The universe clause of the relation is SIMPLIFIED to "both reduce to some universe", with no V/Ucode record and no f≡f'. So Ucode-injectivity is NOT delivered, and is OPEN (possibly relevant for T3). The remaining P3 target is Pi-inj and Sig-inj via the fundamental lemma at the identity substitution.
- 2026-10-08: **MAHLOINJ/Valid DONE** (domain-6c), verified: 7 files, about 2.5k lines, each under 3 s from a clean start, EXIT 0. The logical relation has RT/RM clauses, is stage-stratified, and has a generic Π/Σ clause record. It has sym, trans, transport, mono, join, head expansion, and stage stability. Last P3 step: Adequacy (fundamental lemma over CSub) ⇒ Pi-inj/Sig-inj ⇒ inhabit InjHyp.
- 2026-10-08: COMMITTED on new branch `mahlo-universe` (off main, built via a temporary index, so the working tree is untouched): commit 980e779, with MAHLO/, MAHLOINJ/{Domain,Model,Syntax,Inversion,Valid} and mahlo-plan. Checked in a fresh worktree: all EXIT 0. MAHLOINJ/Adq is NOT included (in progress).
- 2026-10-08: domain-e2's NEXT task: a concrete βδ term model discharging P2's `Model` record (MAHLO/Concrete/), starting with confluence of βδ (extending MIN/Syntax/Confluence).
- 2026-10-08: domain-e2 BLOCKED, correctly: P1/P2 state every equation on D with Agda Eq, but the concrete D is βδ-classes, and there are no quotients and no canonical representatives. APPROVED (A), a setoid refactor in place: ≈ becomes a TermModel field, with respect fields on N/S/NatR, candidate ≈-closure derived, and a sanity instance at ≈ := Eq. Then confluence, then the PERs, then (A2)–(A4). The pre-refactor state is on branch mahlo-universe (980e779). P3 is unaffected.
- 2026-10-08: SETOID REFACTOR GREEN (domain-e2), verified: a clean MAHLO/All build takes 2.9 s, EXIT 0. `_~~_` is a TermModel field; Cand has closure fields R-cl, I-idx, I-el, I-er, preserved by Γ (cannot be derived, since V* is abstract); EqInstance is the sanity instance. Syntax and Typing are unchanged. Concrete model plan: D = erased terms without fhat/ghat (den does δ), ~~ = βπι-conversion. Coordinator suggested defining ⇓ by arbitrary reduction to a normal value, so that S-resp needs only confluence and standardisation is avoided.
- 2026-10-08: domain-e2 ADOPTED ⇓ := →* to a normal value. S-resp = CR + normality, L3 (standardisation) is DROPPED, and NatR is inductive on ~~-representatives. (A3) uses forward stability of reduction under a renaming RETRACTION (fresh x beyond the free variables of v, v'). Now on L1–L2 (terms, parallel reduction, Takahashi confluence).
- 2026-10-08: CONCRETE L1+L2 DONE (domain-e2), verified: MAHLO/Concrete/{Tm,Red,Confluence,Conv} each EXIT 0. Church–Rosser, ~~ = common reduct, (A1) injectivity and disjointness. APPROVED a local change: NatR-ind gets a ~~-closed motive premise (Model, ValNat). η = equality of the computed η-normal form `etanf`. Next: L4 (values, ⇓, N/S/NatR, PERs), then L5.
- 2026-10-08: **P2's Model hypothesis DISCHARGED** (domain-e2), verified: a clean MAHLO/All build takes 3.8 s, EXIT 0. MAHLO/Concrete has 14 files, about 3.1k lines. `concreteTM`, `concreteModel`; `Concrete/Sound.normalise` = (T2a) for closed terms, a module parameter of `Fixpoint concreteTM` ONLY. Plan §7 and the status table are updated. NOT committed (branch mahlo-universe holds the earlier snapshot).
- 2026-10-08: **P3 DONE** (domain-6c), verified: a clean MAHLOINJ/Final.agda build takes 19.5 s, EXIT 0, --safe, only BUILTIN NATURAL, about 19k lines. It proves unconditional Pi-inj, Sig-inj, U-Pi, U-Sig, U-Nat, inversion for every former, and SR for weak-head β/π/ι. The relation is not Kripke; the identity environment is built by induction on the context. Ucode-injectivity is NOT proved. Plan §7 and the status table are updated.
- 2026-10-08: COMMITTED the second commit on `mahlo-universe`: 1a14f19 (setoid refactor, Concrete, Adq, Final, plan). Verified in a fresh worktree: MAHLO/All and MAHLOINJ/Final both EXIT 0.
- 2026-10-08: NEXT TASKS. domain-e2: Lemma 14 FEASIBILITY STUDY first (stages/ordinals, impredicative, IR, minimal axiom), verdict in MAHLO/NEXT_SESSION_FIXPOINT.md, no long formalisation before the user sees it. domain-6c: T3, algorithmic conversion + soundness (MAHLOINJ/Algo/), then a plan for completeness/termination.
- 2026-10-08: T3 choices APPROVED (domain-6c):
  - the UNTYPED lfsigma §3 algorithm, as the plan says;
  - a constructive proof of Thm algsound, with the case split from derivation data (invFhat/invGhat) and a lexicographic (run, at-V) induction — the plan's proof splits on the undecidable "C ≅ U(f,g)"; correct the plan when it lands;
  - only λ-annotations are ignored (the rec motive is compared);
  - a principal-type lemma, with V≇Π and V≇Σ added to NoConf.
  Step 3 must say whether U(f,g)-injectivity (needed for completeness) comes from the PER model.
- 2026-10-08: Lemma 14 FEASIBILITY VERDICT (domain-e2; MAHLO/NEXT_SESSION_FIXPOINT.md; spike MAHLO/FixpointSpike.agda EXIT 0). There is no known --safe Agda proof, and an extra principle is likely needed. The ω-stage union is proved to be a candidate and a least upper bound, and X_ω ⊑ Γ X_ω is proved. General limits need directed unions; termination is classical. Unions over all ordinals hit a size problem (Set1). IR is inapplicable (Γ not strictly positive; Setzer). Pataraia applies, given an impredicative Prop. Recommendation: keep `Fixpoint` as the single, minimal hypothesis. Awaiting the user's choice among: (1) directed unions, (2) the metatheoretic-Mahlo route, (3) stop.
- 2026-10-08: USER DECISION: option 3 (keep Fixpoint as the hypothesis), CONDITIONAL on showing that the hypotheses of the fixed-point theorem in fix.pdf hold (Coquand 1995: a monotone map on a conditional sup-semilattice with ⊥ and directed sups has a fixed point; constructive but impredicative). domain-e2 task: MAHLO/FixHyp.agda covers ⊥ = seed, Γ maps P to P and is monotone, directed sups, conditional binary sups, and `FixThm → Fixpoint`.
- 2026-10-08: FixHyp FLAG (domain-e2): the fix.pdf hypotheses 1, 2, 3, 5 hold unconditionally (EndExt.mono needs no side condition), and 4 holds for Set-indexed families. But FixThm with Set-indexed sups over a Set1 carrier is INCONSISTENT (counterexample: W-ordinals with successor; this answers fix.pdf's closing question negatively). APPROVED split: FixThm with LARGE sups + `LargeSups` (Set1-indexed directed unions of candidates are candidates; impredicative, likely propositional resizing) ⇒ Fixpoint. Machine-checked refutation in MAHLO/FixCounter.agda.
- 2026-10-08: **T3 SOUNDNESS DONE** (domain-6c), verified: MAHLOINJ/Algo/* EXIT 0, with `algsound` and `algsound-ty`. The constructive proof of Thm algsound is in the header of Algo/Sound.agda, to be copied into the plan. Step-3 plan APPROVED:
  - (a) weak-head standardisation for Concrete βπι;
  - (b) simulation den/HR;
  - (c) completeness (lfsigma 7.4–7.6);
  - (d) termination/Dec;
  - (e) assembly, with U-inj as a corollary.
  These go in NEW files (MAHLO/Concrete/Std.agda, MAHLOALG/); existing Concrete files are untouched. Everything is relative to Fixpoint only.
- 2026-10-08: T3 (a) GREEN (domain-6c), verified: MAHLO/Concrete/Std.agda (338 lines, EXIT 0), with Takahashi factorisation, postponement, and `wn` (⇓ ⇒ weak-head normalises). No existing Concrete file was touched by 6c; Concrete/Sound.agda was edited by e2 for FixHyp (normalise-fix / normalise-pfix). Next for 6c: (b) the den simulation, in MAHLOALG/.
- 2026-10-08: **FixHyp DONE** (domain-e2), verified: a clean MAHLO/All build takes 5 s, EXIT 0. All the concrete hypotheses of fix.pdf are proved for (Cand, <<), with no side conditions. FixCounter.refute: the small-sup FixThm is inconsistent. `PFix` (every monotone endomap of Cand has a fixed point) ⇒ Fixpoint, and FixThm + LargeSups ⇒ PFix. LargeSups = propositional resizing, provided N/S/NatR/~~ are truncated too (or with large unique choice). Thm 16 and (T2a) are now relative to PFix. Plan: "The fixed point" paragraph, status table, and bibitem{fix}. Not committed.
- 2026-10-08: T3 completeness: UNTYPED completeness is FALSE (etanf identifies λx.r x and (r.1, r.2), which the algorithm rejects). APPROVED typed completeness via Π≇Σ; plan §6.4 to be corrected. Dec(t = t' : C) via deciding S (computed values + etanf + deceq) + completeness + algsound, relative to PFix. (d), termination of the algorithm itself, is DEFERRED (it needs a deterministic AlgEq). Decidable type checking is not yet addressed.
- 2026-10-08: USER: commit only after T3 is finished. domain-e2's NEXT task: decidable TYPE CHECKING in MAHLOTC/, modulo a parameter record `DecConv` (to be inhabited by 6c's (e)). Bidirectional, with an inferable/checkable split (pairs are checkable only).
- 2026-10-08: TYPE CHECKING scope (domain-e2 flag, accepted): unannotated pairs make typing of β-redexes with check-only bodies a higher-order matching problem. Typing is not closed under β-expansion (App (Lam V (Pair x0 y)) Nat). So decidable type checking is proved for the bidirectional fragment Chk (it contains all β-normal terms), and for arbitrary raw terms it is OPEN; correct the plan's (T3). TCHyp = {decTyEq, decPi, decSig, decU} + InjHyp, to be inhabited by 6c's (e).
- 2026-10-08: **T3 CONVERSION HALF DONE** (domain-6c), verified: a clean MAHLOALG/All build of the whole cone takes 28.8 s, EXIT 0 (heaviest file Complete, 3.1 s).
  - (a) Std; (b) Sim (HR simulated by Wh, δ lowers the head count); (c) Complete (TYPED completeness, Π≇Σ added to NoConfV).
  - (e) T3 (parameter `Fixpoint concreteTM`): decConv, decTyEq, decPi/decSig/decU (the TCHyp fields), U-inj (now proved, relative to Fixpoint).
  - (d) deferred, with a note on a deterministic AlgEq.
  Waiting for e2's type checker, then COMMIT.
- 2026-10-08: **T3 DONE** (both halves), verified. MAHLOTC (domain-e2): decHasType/decIsType/decWfCtx for the bidirectional fragment Chk, with the instance from MAHLOALG.T3 + injHyp. MAHLOALG/T3PFix gives everything relative to PFix. Plan §6.4 corrected (typed completeness), new "(T3): done in Agda" paragraph, status table updated. **COMMITTED 7996d34** on mahlo-universe (35 files, +6482); a fresh-worktree build of MAHLO/All, MAHLOINJ/Final, MAHLOALG/All and MAHLOTC/All is all EXIT 0.
  REMAINING OPEN: PFix itself (impredicative); decidable type checking for raw terms; termination of the deterministic algorithm; Russell ⇔ Tarski equivalence.
- 2026-10-08: NEW PHASE (user approved): Russell (R') ⇔ Tarski (reflection), ERT-style, in MAHLORT/. domain-e2 drafts TarskiSyntax/TarskiTyping (setzer1 Def 3.5(a), recursive subuniverses, T̂ embedding, reflection rule) plus the erasure, for coordinator review and FREEZE. domain-6c writes a PLAN for uniqueness (the CommonLift analogue with T̂) and section, including which injectivities are needed and whether it is relative to PFix.
- 2026-10-08: **MAHLORT/TarskiSyntax + TarskiTyping FROZEN** (drafted by domain-e2, reviewed by the coordinator). They follow Setzer Def 3.5(a), recursive subuniverses with full decoding: ElU ≡ ElV ∘ That; That commutes with PiU/SigU/NatU; That∘Fhat/Ghat = fApp/gApp is the δ-analogue, at V; conv-reflect. App/Pair/Fst/Snd are annotated, so Tarski types are unique. Erasure.agda maps everything to MAHLO.Syntax, and each Tarski rule erases to a Russell rule.
- 2026-10-08: CHANGE to the frozen Tarski modules (6c's request): T̂ is UNANNOTATED (`That a`), so same-type extraction needs no Tarski U-inj. Re-checked EXIT 0; e2 notified (EraseLemmas needs a 2-line fix).
  6c's PLAN APPROVED:
  - MAHLO Russell is T_P-like (App/Pair unannotated), so uniqueness takes a Coh form (same / univ via T̂ into V / pi via η / sigma) = ERT 4.10 + 4.18 merged;
  - DIRECT route: Tarski adequacy (a MAHLOINJ port) for Π/Σ-inj_T;
  - Tarski no-confusion via erasure, plus a new V≢U model variant;
  - the target is a HYPOTHESIS-FREE equivalence (PFix does not help).
- 2026-10-08: **Lemma 4.6 DONE** (domain-e2), verified: MAHLORT/EraseLemmas + EraseDeriv EXIT 0, with erW/erI/erH/erT/erC (each Tarski judgement erases to a Russell one). Next for e2: Tarski metatheory (MAHLORT/Syntax/), in the order 6c needs.
- 2026-10-08: CHANGE 2 to the frozen TarskiTyping (6c's request): annotation-changing congruences. conv-App/Fst/Snd are generalised in place with TyEq premises; conv-Lam and conv-Pair are NEW. Without them, Lam A t ≡ Lam A' t is underivable in Tarski and the section fails. Re-checked EXIT 0; e2 is fixing EraseDeriv. 6c: RNoConf (V≢U, free: V is never a term) and TNoConf (all 10 cases) are DONE, so steps 1–2 are done. The Tarski adequacy reuses Domain and Model through erasure and ports only Valid and Adq.
- 2026-10-08: e2 absorbed change 2. EraseDeriv is fixed, via new Russell congruences cvLam/cvPair in MAHLORT/RussellCong (my earlier pointer to MAHLOINJ/Syntax/Funct was WRONG; they were not there). Tarski metatheory so far: Syntax/SubstLemmas, Lemmas, Weaken, Subst. Next: Wf, CtxConv, Funct, Presup.
- 2026-10-08: **Tarski metatheory COMPLETE** (e2), verified: a clean MAHLORT/Syntax/All build is EXIT 0 (Wf, CtxConv, Ops, CodeCong, Funct, Presup). Finding: code congruences that MOVE f,g (PiU f g ≡ PiU f' g' …) are derived via REFLECTION (CodeCong), so reflection is load-bearing in the metatheory too. Next for e2: Tarski inversion lemmas (B7).
- 2026-10-08: B7 (Tarski inversion, MAHLORT/Syntax/Inv) DONE, verified. SPLIT: e2 takes Coh-uniqueness, the section and the equivalence, MODULO `TInjHyp` (Pi-inj_T, Sig-inj_T); 6c's Tarski adequacy will inhabit TInjHyp.
- 2026-10-08: 6c (verified: Valid/Public and Adq/Env EXIT 0): the Tarski relation layer is done. The universe clause RECORDS V vs U, which is consistent because V≢U; decoding depends on it. The App/Fst/Snd fields quantify over convertible annotations. Now porting the rest of Adq. The split (e2 does uniqueness/section modulo TInj) is agreed by both.
- 2026-10-08: e2 has started uniqueness/section. TInj (MAHLORT/Hyp) = {Pi-inj_T, Sig-inj_T} ONLY, agreed with 6c case by case: no U-inj (That is unannotated), and no-confusion comes from TNoConf. Files: Hyp, Coh, Uniq, Section, Equivalence.
- 2026-10-08: **UNIQUENESS DONE** relative to TInj (e2), verified: Hyp, Coh, UniqLemmas and Uniq all EXIT 0. term-uniq: same erasure ⇒ Coh; type-uniq; extract (Coh at equal types ⇒ conversion, via reflection, no U-inj). Structural mutual recursion on the derivations. Next for e2: Section, then Equivalence.
- 2026-10-08: **TARSKI ADEQUACY DONE** (6c), verified: a clean MAHLORT/TFinal build takes 23.9 s, EXIT 0, --safe, no pragmas. `tInj : TInj` is HYPOTHESIS-FREE (Tarski Π/Σ-inj). Design points:
  - head reduction includes the T̂-equations and El-decodings, and ignores annotations;
  - the universe clause records the kind V/U;
  - a new annotation-irrelevance expansion lemma (HR commutes with annotation change);
  - envElU.
  Only e2's Section + Equivalence remain.
- 2026-10-08: **RUSSELL ⇔ TARSKI DONE, HYPOTHESIS-FREE**, verified: a clean MAHLORT/EquivalenceFinal build takes 38.5 s, EXIT 0, about 13k lines, --safe, no pragmas. The `Equivalence` record covers sound-* (4.6), lift-* (4.13) and uniq-* (4.10+4.18 as Coh). Plan updated (remark, new paragraph, status table). **COMMITTED bfc9092** on mahlo-universe (63 files, +13106); a fresh worktree builds all five top modules, EXIT 0.
