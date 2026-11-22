# PLAN-GAT: sterbac4.pdf Section 4 in Unit, with Ehrhard-GAT

Goal: Ehrhard-GAT (explicit substitutions id, o, (), p, q, lift, sec) is
equivalent to TTarski (implicit substitution), Lemmas 15-20 of sterbac4 §4.
Afterwards: short LaTeX note presenting the result (only if it works).

Check a dev driver with
  SEG=/Users/coquand/CANONICITY/unit-indexed/dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg
  $SEG _devgat.seg          (run from UNIT/)

## Design decisions

* UNSCOPED de Bruijn syntax for both systems (as the paper: alpha : N -> Tm).
  No Fin n indices.  Contexts: data Cx = cnil | csnoc G A.
* TTarski raw terms Tm: var i | pi A B | lam A B b | app A B c a | uu n |
  el n a (T_n) | pic n a b (Pi_n) | uc m n (code of U_m in U_n, m<n) |
  lf m n a (t^n_m, a : U_m, m<=n).
* TTarski var rules as in the paper (v0 / v_{n+1}); typed substitutions
  SubOk D G s by recursion on G: SubOk D (G.A) s = SubOk D G (s o suc) x
  D |- s 0 : A[s o suc].  Generic typed traversal over a kit (renaming:
  needs only the var rules; substitution: needs renaming).
* TTarski rules carry extra (admissible) presupposition premises only
  where Lemma 18 needs them: beta carries G.A |- B, eta carries G |- A,
  G.A |- B.  Record each such deviation here.
* TTarski context equality: a recursive predicate CxEq, not a judgement.
* Ehrhard-GAT raw syntax: ONE unscoped datatype for contexts, types,
  terms, substitutions.  NO context annotations (U_n, U^n_m, id, (), p, q
  are bare; the context is that of the judgement); type annotations kept:
  lam(A,B,b), app(A,B,c,a), lift_A(s), sec_A(a).  [Decided 2026-11-22:
  annotations on p,q,U force right-hand presuppositions in the relational
  lemmas; without them evaluation is context-free.]  Context-conversion
  rules and ctx-eq judgement (refl, nil, ext) kept.
* GAT equality-rule premises = exactly what soundness (Thm 16) needs.

## Lifting via environments (instead of the paper's ceil(-)_G)

  ev : Tm -> (Nat -> GE) -> GE   (context-free)
  ev (var i) e = e i ;  binder: ev B (up e),  up e 0 = q, up e (i+1) = (e i) p.
  ceil t := ev t idv,  idv i = q p^i.

Lemma 17 (raw): |ev t D r| = t[|r|], hence |ceil t| = t.
Renaming (raw, syntactic): ev (t[r]) D rho = ev t D (rho o r).

Lemma 18 = one mutual induction on TTarski derivations; motive for
d : G |- J is
  CtxInfo(G) x P(J) x NE(J) x E(J) x S1(J)
  P   : envs typed  => GAT derivation of ev J
  NE  : ev A rho sigma = ev A (rho sigma)              (naturality)
  E   : related envs (over convertible contexts) give equal values
  S1  : ev (A[s]) rho = ev A (ev s rho), for Good s; also typing
  P for equalities is RELATIONAL (related envs => ev A rho1 = ev B rho2)
  CtxInfo(G.A) = CtxInfo(G) x P(A) x NE(A) x E(A) x S1(A).
Every TTarski rule has a premise in the conclusion's context (or |- G),
which supplies CtxInfo.  Cases may live in separate files, dispatched
by one split.

Lemma 19: induction on GAT typing derivations:
  G |- a : A  =>  G |- a = ceil(|a|)_G : A ;
  s : D -> G  =>  EnvRel (idenv_G s) (ev |s| idenv_D).

## Status (2026-11-22): DONE, all of §4 checked (+ presup, 704 decls)

GATCheck.seg (import closure Base/Prelude/Lib + the files below): 607
declarations, 0 failed, 0.17 s.  Also imported at the end of All.seg
(python3 UNIT/check.py: All.seg 36864 declarations, 0 failed).

Files: TSyntax TTyping TSubst TSubCong TSubLib (T_Tarski, Lemma 15) ;
GAT GSound (Ehrhard-GAT, Theorem 16) ; Ev (ceil by evaluation, Lemma 17) ;
L18Base L18Good L18Var L18Bind L18Pi L18App L18U L18Eq L18BE L18 (Lemma 18) ;
L19Base L19 (Lemma 19) ; Thm20 (Theorem 20: section-*, unique-*, unique-cx).

Final shape of Lemma 18 motive (L18Var.L18J): for G |- A:
CtxS G x PT x NT x ET x ST; terms PM x NM x EM x SMt; equalities QT/QM
(relational).  NM and SMt are typed on the RIGHT (ev A (e s), ev A (ev s e)):
left typing needs naturality of the type, unavailable for tm-conv.

Admissible premises added (all presuppositions; admissibility PROVED,
see step 11: TLean/GLean):
  T_Tarski: eqty-pi/eqtm-lam/eqtm-app carry G |- A; eqtm-pic G |- a : U_n;
    eqtm-beta G |- A, G.A |- B; eqtm-eta G |- A, G.A |- B;
    eqtm-app G.A |- B, G |- a : A; eqtm-sym G |- A.
  GAT: gm-sb, gm-esb, gm-sym carry G |- A; gq-sec carries typings;
    congruences carry the left premise (as T_Tarski).

## Steps
1. TSyntax.seg   raw Tm, kit/trav, ren/sub, equations      [x]
2. TTyping.seg   Cx, Jf, Der (TTarski)                        [x]
3. TSubst.seg    typed traversal (ren, sub), subst1           [x]
4. TSubCong.seg  Lemma 15 second part                         [x]
   TSubLib.seg   comp-ok, subeq-*, cxconv-*                   [x]
5. GAT.seg       Ehrhard-GAT syntax, erasure, rules           [x]
6. GSound.seg    Theorem 16                                    [x]
7. Ev.seg        ev, idv, Lemma 17, renaming lemma             [x]
   (all checked by _devgat.seg in <0.1 s)
8. L18*.seg      Lemma 18 mutual block                         [x]
9. L19.seg, Thm20.seg                                          [x]
10. LaTeX note (gat-ehrhard.tex)                              [x]
11. Presuppositions + lean systems (2026-11-22)                 [x]
    TPresup.seg  T_Tarski presup (paper Lemmas 22-24), one induction
    TLean.seg    DerL = A.2 rules w/o extra premises; to-lean, to-der
    GAT.seg      NEW RULE gs-cx: s : D -> G, D = D', G = G' => s : D' -> G'
                 (needed: lift_A(id) = id : G.A[id] -> G.A has an untypable
                 RHS without it); GSound + L19 (L19Base.envok-dom/enveq-dom/
                 enveq-cod) extended
    GPresup.seg  GAT presup (explicit subst: no meta subst lemma)
    GLean.seg    GDerL (generated from GAT.seg), to-glean, to-gder;
                 Pi-inversion through gt-cx
    Remaining gap to A.2: sym + trans instead of the euclidean rule.
