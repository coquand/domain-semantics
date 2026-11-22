# ERT/GAT: sterbac4 §4 (Ehrhard-GAT ⇔ T_T) in Agda, over ERT's T_T

Goal: one checker for the chain GAT ⇔ T_T ⇔ T_R ⇔ T_P, and inversion for
the GAT (sterbac4 §2, Thms 8-10) by transfer from T_T:
  PiInj-T (ERT/PiInjectivityT, from PiInj-R), U-inj / no-confusion
  (ERT/Injectivity).
Prototype: the seg development UNIT/{TSyntax..Thm20,GPresup,GLean}.seg
(UNIT/PLAN-GAT.md), checked; port its design, not its T_Tarski.

Decided 2026-11-22 (analysis: a seg-native Pi-injectivity would need either
UNIT's 104-module relation re-done for levelled T_Tarski, or ERT's ~18.7k-line
domain model ported to seg; in Agda it is ~50 lines from PiInj-R).

## Design
* GAT mirrors ERT's T_T exactly: strict lifts glf m l a (l < m), guc m l
  (code of U_l in U_m, l < m), the six Tarski equations of ERT.
* Scoped: GE n (types and terms, ONE family as in seg), GS n m (substitutions
  from a context of length n to one of length m), GC n.  No context
  annotations (as in seg).
* Judgements: GJ (plain data, implicit lengths), one family GDer : GJ -> Set,
  rules as in UNIT/GAT.seg incl. gs-cx.  Congruences "all change"; erasure
  uses ERT's split congruences + transitivity.
* Erasure eT/eS/eC into T.Expr / T.Sub / TT.Ctx (Definition 11).
* Lifting: ev : T.Expr n -> (Fin n -> GE k) -> GE k, up e fzero = gq,
  up e (fsuc i) = gsb (e i) gp.  Lemma 18 as in UNIT/L18*.seg.
* T_T side tools: TarskiMeta (subst, presup), TarskiMetaCong (subst-cong-*),
  LiftBack (ConvCtx, einj-*, mkConvCtx-from-erase).
* Compile budget: <= 20 s per file; use opaque/abstract if slow.

## Files
1. Syntax.agda    GE, GS, GC, erasure                       [x]
2. Rules.agda     GJ, GDer (variable-generalised lengths)   [x]
3. Sound.agda     Theorem 16                                [ ]
4. Ev.agda        ev, Lemma 17                              [ ]
5. L18*.agda      Lemma 18                                  [ ]
6. L19.agda, Thm20.agda                                     [ ]
7. Presup.agda    GAT presuppositions (port GPresup.seg)    [ ]
8. Inversion.agda Thms 8-10 for the GAT by transfer         [ ]
