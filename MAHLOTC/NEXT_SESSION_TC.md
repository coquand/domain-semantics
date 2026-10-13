# MAHLOTC — (T3) decidable type checking: DONE (2026-10-08), relative to TCHyp

## Theorem (`MAHLOTC/Check.agda`, `--safe`, about 1.6k lines, every file < 0.6 s)
- `decHasType : WfCtx G → Chk t → IsType G C → Dec (HasType G t C)`
- `decHasType' : WfCtx G → Chk t → ChkTy C → Dec (HasType G t C)`
- `decIsType : WfCtx G → ChkTy A → Dec (IsType G A)`
- `decWfCtx : ChkCtx G → Dec (WfCtx G)`

These hold for the bidirectional fragment (`Frag.agda`), which **contains every β-normal term**.

## Hypotheses `TCHyp` (for domain-6c's decidable conversion to inhabit)
- `decTyEq` (decidable type equality of two types).
- `decPi` / `decSig` / `decU`: weak-head form of a type, with witnesses.
- `InjHyp` from MAHLOINJ (Pi-inj, Sig-inj, U-Pi, U-Sig, U-Nat).
- Not needed: Dec ConvTm, U-inj, U-V, or any other no-confusion.

## Design
- **Inference** returns a finite LIST of types, sound and complete up to TyEq.
  - The list is saturated under U(f,g) ≤ V, so checking is just "C ≡ some element"; there is no subsumption case.
  - Lam with an inferable body has TWO types (PiB A T and PiB A V), which are not TyEq-related. Lam is therefore not principal, which is why lists are used.
- **Inferable:** Var, App, Fst, Snd, Rec (literal motive Lam Nat C), Lam (inferable body), Pi/Sigma (inferable domain), Zero, Suc, Ucode, Fhat, Ghat.
- **Check-only:**
  - Pair (unannotated);
  - Nat (it belongs to every valid U(f,g), so it has infinitely many types);
  - Lam/Pi/Sigma whose body/domain is check-only.
- Pi/Sigma/Fhat/Ghat require F = Lam A B with the SAME A syntactically (`decExpr`, generated DecEq on Expr). Rec requires the motive annotation to be literally Nat.
- Completeness of every rule is by MAHLOINJ inversion plus TCHyp. Π/Σ elimination exposes the type via decPi/decSig, and Pi-inj/Sig-inj relate the witnesses.

## Open / excluded
- β-redexes `App (Lam A b) c` with a check-only body b, and projections of non-inferable terms, are outside the fragment.
- Projections of literal pairs would be easy to add: Fst (Pair a b) : C ⇔ a : C ∧ b typable.
- Redexes with pair bodies are genuinely problematic (see the negative fact in `All.agda`). Their decidability is OPEN.

## Closed (2026-10-08)
- `MAHLOTC/Instance.agda` (Fx : Fixpoint concreteTM) builds `tcHyp : TCHyp` from domain-6c's `MAHLOALG/T3.agda` (decTyEq, decPi, decSig, decU) and `MAHLOINJ.Final.injHyp`. It re-exports `decHasType`, `decIsType` and `decWfCtx`.
- (T3) type checking for the bidirectional fragment is thus decidable **relative to the fixed point only**, hence relative to PFix via `fixpoint-of-pfix`.
