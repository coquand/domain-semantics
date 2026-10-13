# MAHLO — phase P2: DONE (2026-10-08)

**State.**
- `mahlo-plan.tex` / `.pdf` (top level of `~/DOMAIN`) is the plan.
- P1 is DONE and now **includes Σ**, added in place with the coordinator's approval:
  - TermModel: `Sig`, `pr1`, `pr2`, `Sig-inj`, disjointness from Pi/Nat/U/neutrals, `S-Sig`, `ne-fst`, `ne-snd`, `ext-pair`.
  - Candidate: `SigF`. Pre: `pre-sig`; `Indep` gives `(R Pi * R Sig) * ...`.
  - Gamma: `gsig`/`isig`. Congruence/EndExt: the Σ cases. Fixpoint: `close-sig`.
- **P2 is DONE**: soundness of the PER model (plan §6, Theorem 16).
  - Relative only to the abstract `Model` (TermModel plus the denotation) and the `Fixpoint` hypothesis (Lemma 14).
  - `MAHLO/All.agda` is `--safe`, has 0 postulates, holes or pragmas, and runs EXIT 0. The whole cone rebuilds from scratch with every file under 1 s.

## P2 modules
| file | content |
|---|---|
| `Model.agda` | `Model` record over a TermModel: Vd, zero/suc/rec, pairing; NatR intro and induction; `den : Expr n -> Env n -> D` with one equation per constructor and `den-subst` (Abel–Coquand §5.1). Fhat/Ghat denote f A F / g A F c (δ holds in D). Derived: `den-ext`, `den-ren`, `den-wk-cons`, `den-subst1`, `den-sucSub`. Syntax's Pi/Sigma/Nat/V are renamed tPi/tSigma/tNat/tV. |
| `Type.agda` | `TyR a b X` (large types, interpretation X), clauses V / small (`R a b`, X ~ I a) / Pi / Sigma. `Vnotin`; end-extension `eeL`/`eeR`; `per`, `funL`, `funR` (the interpretation depends on either endpoint), `sym`, `trans`, `lo`, `hi`, `safe`; inversion `invV`/`invPi`/`invSig`; builders `piTy`/`sigTy` via `mkFam` (a proof-independent family); `famCoh`. |
| `Validity.agda` | `TmV`, `EnvR` (a PER), `ValTy`/`ValTm`/`ValTyEq`/`ValConv`/`ValCtx`; variables; `vconv-l`/`vconv-r`; equivalence and conversion rules; `piIntro`/`piElim`/`sigIntro`/`sigElim1,2`. |
| `ValPi.agda` | Π/Σ types, λ, App, Pair, Fst, Snd, β, funext (η), surjective pairing. |
| `ValNat.agda` | V as a type, Nat, 0, S, rec (by `NatR-ind`; neutral case via `ne-rec` and `lo`), ι-rules. |
| `ValU.agda` | **Key observation** `invU`: a valid code yields Indep and Op from Γ's U-clause. Subsumption, (R'), Nat/Π/Σ in V and in U_{f,g} (module `Fam`); `decodeF`/`decodeG`/`opSem` ([OpF], [OpG f] ⇒ Op(V*)) + `mahlo-code` for U_{f,g}:V and its congruence; f̂, ĝ, δ. |
| `Soundness.agda` | `sTy/sTm/sTyEq/sConv` (mutual, every Typing rule); `wfTy/wfTm`, `sCtx`, `neutralEnv`; `soundness`, `soundness-ne`, `wt-safe` ((T2a) in the concrete model), `soundness-closed`. |

## Design notes
- Interpretations are relations `Rel = D -> D -> Set`. TyR is an indexed data type in Set1; equalities of D are Eq premises.
- Families from validity depend on proofs of `XA v v`; `mkFam XA Y v = Σ (XA v v) (Y v)` removes that dependence, and functionality makes it ~ every instance.
- f/g premises of ty-Fhat/ty-Ghat/δ: only f's validity is used (to relate f ρ with f' ρ' in the congruences, via `decodeF`/`decodeG`); g's validity is used for ĝ.

## Open / next
- The `Model` fields are argued in plan §6.2; they are not machine-checked (that would need the concrete βδ term model).
- Lemma 14 (the existence of the fixed point) remains a hypothesis.

## Setoid refactor (2026-10-08, approved by the coordinator)
- D is a SETOID. `_~~_` is a TermModel field: an equivalence and a congruence for app/Pi/Sig/U/pr1/pr2.
- N, S and NatR are ~~-closed (`N-resp`, `S-resp`, `NatR-resp`). Injectivity and disjointness hold up to ~~.
- Cand has closure fields `R-cl`, `I-idx`, `I-el`, `I-er`, and Γ preserves them. Element closure is not derivable for the abstract fixed point.
- Γ/Pre clauses are `a ~~ Pi A F`. `Pre-cong`, `Indep-cong` and `Op-cong` give respect in f, g.
- TyR closure is derived: `TyR-cl2`, `TyR-elL/R`, `TyR-el2`.
- The Model laws hold up to ~~, with new congruences sucD/recD/pairD.
- `EqInstance.agda` shows the old Eq form is an instance.
- Reason for the refactor: the concrete βδ model is a quotient, and --safe Agda has no quotients.
- Next: the concrete model (L1 terms, L2 confluence, L3 head reduction and inductive normalisation, L4 PERs, L5 (A1)–(A4)).

## Concrete model: DONE (2026-10-08)
- `MAHLO/Concrete/` (14 files, ~3.1k lines, --safe) gives `concreteTM : TermModel` and `concreteModel : Model concreteTM`. **P2 soundness now depends ONLY on the Fixpoint hypothesis** (`Concrete/Sound.agda`; the corollary `normalise` is (T2a)).
- D is erased untyped de Bruijn terms with no fhat/ghat: δ is performed by `den`. Reductions are β/π/ι. ~~ means "has a common reduct", and Church–Rosser comes from Takahashi complete development.
- ⇓ is reduction to a value (arbitrary reduction; closure under ~~ by CR only).
- η-equality is Eq of a computed `etanf` (decidable syntactic equality plus a shift test). Lemmas: `etanf-val` (values are preserved) and `etanf-ren` (commutes with renamings that have a retraction).
- (A3) `ext`: the fresh variable is `tvar (max (bound v) (bound v'))`. Proved by induction on the reduction of v x, via the renaming `fr m` and its inverse `fr' m` (Bnd.agda). `ext-pair` is analogous.
- NatR-ind now requires a ~~-closed motive (Model field changed; ValNat proves its motive closed).
