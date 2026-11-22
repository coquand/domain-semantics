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
3. TLib.agda      WtSub/ConvTmSub ops, CxEq (general ctx conv),
                  record wrappers WtS/CTS (WtSub unfolds to a Pi in which
                  the codomain only occurs under lookup: not inferable)   [x]
   Sound.agda     Theorem 16                                [x]
4. Ev.agda        ev, Lemma 17                              [x]
5. L18*.agda      Lemma 18                                  [ ]
6. L19.agda, Thm20.agda                                     [ ]
7. Presup.agda    GAT presuppositions (port GPresup.seg)    [ ]
8. Inversion.agda Thms 8-10 for the GAT by transfer         [ ]

## Notes for the next steps (2026-11-22)
* Lemma 18 (port UNIT/L18Base..L18BE.seg, motive L18Var.L18J): one case per
  ERT T_T rule.  Differences with UNIT's T_Tarski: congruences are split
  (conv-cong-Lam-body / -Lam-Ty, App-fun / -arg (with cross-subst premise)
  / -Ty); ERT's binder congruences carry IsType G A like UNIT's; ERT
  conv-sym has no premise (UNIT eqtm-sym carried G |- A because L18 needed
  it: get it from TarskiMeta.presup-l-ConvTm).  ERT HasType has ty-var
  with lookup (no v0/vs split): the var case of L18 needs an induction on i.
* Agda inference: never leave WtSub / ConvTmSub / CxEq results in an
  un-annotated let (use WtS / CTS wrappers, or give contexts explicitly).
* Named implicit patterns must follow first-occurrence order of the
  generalised variables in the rule's type (Rules.agda).
