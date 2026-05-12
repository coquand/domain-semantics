{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- OLD/ValiditySigma-Monotonicity.agda  --  ARCHIVED, NOT COMPILED
--
-- Extracted from ValiditySigma.agda lines 770-2292 (after commit f9c7ee7).
-- This is the "Part 2: Monotonicity" block — down/up/restrict + Pi/Sigma
-- helpers + transport*-sel — that was originally guarded by
--   {-# TERMINATING #-}
-- and shown to lack any sound rk-based termination measure (see
-- RankCounterexamplesSigma.agda in the project root for closed-form
-- counterexamples).
--
-- It is moved here because a project-wide grep confirmed that NONE of
-- the names defined in this block are referenced outside
-- ValiditySigma.agda itself.  The active Validity5/Adequacy5 stack
-- only consumes the upstream-of-Part-2 names from ValiditySigma
-- (Red-unique-Pi, Red-unique-Sigma, FinMem-Coherent, bU-from-cf-fmFun,
-- and the SelectionSigma re-exports).
--
-- The original module declaration was `module ValiditySigma where` --
-- this archive file is NOT a valid module by itself (no `module ...
-- where` line below, and no imports).  To revive: paste this body back
-- into ValiditySigma.agda after Part 1, restoring the imports and the
-- {-# TERMINATING #-} pragma.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Part 2: Monotonicity -- downward/upward transport
------------------------------------------------------------------------

-- Termination of the mutual block below (down/up/restrict + Pi/Sigma
-- helpers + transport*-sel) is ASSERTED by {-# TERMINATING #-}.  No
-- measure has been worked out, and the natural rk-based candidates
-- are provably WRONG.
--
-- See RankCounterexamplesSigma.agda for closed-form Agda witnesses
-- (every `Eq ... refl` there reduces) that on coherent data:
--   * rkFun (append f g)  >  max (rkFun f) (rkFun g)        [counterex 1]
--   * rk (Sup x y)        >  max (rk x) (rk y)              [counterex 2]
--   * rk (EvalFun f u)    >  rkFun f                        [counterex 3]
-- The smallest concrete witness: A = cons (Bot,UCode) repeated 3x,
-- f = cons (UCode, FunEl A) repeated 3x.  Then rkFun f = 6 but
-- rk (EvalFun f UCode) = 9.  All of f and A satisfy Coherent.
--
-- Why this kills rk as a measure: every cons in rkFun adds a `suc`,
-- so rkFun behaves like SIZE (additive under append), not DEPTH.  Sup
-- on FunEl appends the inner FunFuns, so any single Sup can grow rk
-- by the appended length, and EvalFun chains many Sups together.
--
-- Three attempted lex measures and where each one fails:
--
--   (a) "rk a1 for down/up, rk a for restrict" fails at
--           restrictVal G M A u u' UCode = downValTy G M u' u
--       (line ~2053): parent rk UCode = 0, child rk u unbounded.
--
--   (b) "max (rk u) (rk a) for restrict" fails at
--           upPiAppVal ... -> restrictVal u u1 b1     (line ~913)
--       because the lambda-bound u from Selection is not rk-bounded
--       by the surrounding primary code; LeCode is not rank-monotone
--       either (counterexample: u' = PiCode UCode (cons (UCode,UCode)
--       (cons (UCode,UCode) nil)), u = PiCode UCode (cons (UCode,UCode)
--       nil): both Coherent, LeCode u' u holds, rk u' = 3 > 2 = rk u).
--
--   (c) "rk descends through EvalFun" fails at
--           transportPiEdgeVal-sel -> downValTy ... v0 v1
--       with v1 = EvalFun f1 u0.  Counterexample 3 above shows the
--       bound rk (EvalFun f u) <= rkFun f is FALSE on coherent data,
--       so rk does not strictly descend here either.
--
-- The author's belief, by which this block is shipped: the call tree
-- on any CONCRETE input is finite.  Even though no rk-based lex
-- measure works, the data threaded through recursive calls is built
-- by EvalFun / Sup / selectionBelow from a fixed finite input, and
-- the reachable code set is finite.  This is a semantic argument, not
-- a syntactic well-foundedness argument, and Agda's TERMINATING
-- pragma does not verify it -- so the block ships on trust.
--
-- Promoting this to an actual termination proof would require either:
--   * finding a non-rank measure that survives Sup/append/EvalFun
--     (e.g. an ordinal or a multiset on the reachable-code closure),
--     proving it well-founded, and refactoring the block to recurse on
--     an Acc-style witness; or
--   * a semantic argument (e.g. via interpretation in the domain
--     model) that side-steps Agda's syntactic termination checker.
-- Neither has been done.

{-# TERMINATING #-}

-- Forward declarations for mutual recursion block
downVal : {n : Nat} (G : Ctx n) (M A : Expr n) (u a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
  Val G M A u a1 -> Val G M A u a0
downEqVal : {n : Nat} (G : Ctx n) (M N A : Expr n) (u a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
  EqVal G M N A u a1 -> EqVal G M N A u a0
downValTy : {n : Nat} (G : Ctx n) (M : Expr n) (u0 u1 : FinEl) ->
  LeCode u0 u1 -> FinMem u0 UCode -> FinMem u1 UCode ->
  ValTy G M u1 -> ValTy G M u0
downEqValTy : {n : Nat} (G : Ctx n) (M N : Expr n) (u0 u1 : FinEl) ->
  LeCode u0 u1 -> FinMem u0 UCode -> FinMem u1 UCode ->
  EqValTy G M N u1 -> EqValTy G M N u0
upVal : {n : Nat} (G : Ctx n) (M A : Expr n) (u a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 ->
  Coherent a0 -> Coherent a1 ->
  Val G M A u a0 -> ValTy G A a1 -> Val G M A u a1
upEqVal : {n : Nat} (G : Ctx n) (M N A : Expr n) (u a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 ->
  Coherent a0 -> Coherent a1 ->
  EqVal G M N A u a0 -> ValTy G A a1 -> EqVal G M N A u a1
restrictVal : {n : Nat} (G : Ctx n) (M A : Expr n) (u u' a : FinEl) ->
  LeCode u' u -> FinMem u' a -> FinMem u a ->
  Val G M A u a -> Val G M A u' a
restrictEqVal : {n : Nat} (G : Ctx n) (M N A : Expr n) (u u' a : FinEl) ->
  LeCode u' u -> FinMem u' a -> FinMem u a ->
  EqVal G M N A u a -> EqVal G M N A u' a

------------------------------------------------------------------------
-- Selection-based graph transport helpers (Pi)
------------------------------------------------------------------------

downPiAppVal : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  ValTy G A0 b1 ->
  PiAppVal G M A0 B0 b1 f1 g -> PiAppVal G M A0 B0 b0 f0 g
downPiAppVal G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U b0U allU0 allU1 le fmg0 vtb1 src
  u v sel N val-b0 =
  let cgt = cft-from-cf g cg
      cu = Coherent-Selection sel cgt
      fmu0 = FinMem-Selection b0 f0 sel fmg0 cgt cb0 b0U
      fmu1 = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
      val-b1 = upVal G N A0 u b0 b1 (fst le) fmu0 fmu1 cb0 cb1 val-b0 vtb1
      body = src u v sel N val-b1
      le-f = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
      c-ef0 = Coherent-EvalFun f0 u cf0 cu
      ef1U = EvalFun-in-UCode f1 u b1 cf1 cu allU1
      fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 cgt cf0 allU0
  in downVal G (App M N) (subst1 B0 N) v
       (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body

downPiAppEq : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  ValTy G A0 b1 ->
  PiAppEq G M A0 B0 b1 f1 g -> PiAppEq G M A0 B0 b0 f0 g
downPiAppEq G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U b0U allU0 allU1 le fmg0 vtb1 src
  u v sel N1 N2 eqv-b0 =
  let cgt = cft-from-cf g cg
      cu = Coherent-Selection sel cgt
      fmu0 = FinMem-Selection b0 f0 sel fmg0 cgt cb0 b0U
      fmu1 = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
      eqv-b1 = upEqVal G N1 N2 A0 u b0 b1 (fst le) fmu0 fmu1 cb0 cb1 eqv-b0 vtb1
      body = src u v sel N1 N2 eqv-b1
      le-f = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
      c-ef0 = Coherent-EvalFun f0 u cf0 cu
      ef1U = EvalFun-in-UCode f1 u b1 cf1 cu allU1
      fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 cgt cf0 allU0
  in downEqVal G (App M N1) (App M N2) (subst1 B0 N1) v
       (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body

downPiAppEqVal : {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  ValTy G A0 b1 ->
  PiAppEqVal G M N A0 B0 b1 f1 g -> PiAppEqVal G M N A0 B0 b0 f0 g
downPiAppEqVal G M N A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U b0U allU0 allU1 le fmg0 vtb1 src
  u v sel P val-b0 =
  let cgt = cft-from-cf g cg
      cu = Coherent-Selection sel cgt
      fmu0 = FinMem-Selection b0 f0 sel fmg0 cgt cb0 b0U
      fmu1 = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
      val-b1 = upVal G P A0 u b0 b1 (fst le) fmu0 fmu1 cb0 cb1 val-b0 vtb1
      body = src u v sel P val-b1
      le-f = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
      c-ef0 = Coherent-EvalFun f0 u cf0 cu
      ef1U = EvalFun-in-UCode f1 u b1 cf1 cu allU1
      fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 cgt cf0 allU0
  in downEqVal G (App M P) (App N P) (subst1 B0 P) v
       (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body

upPiAppVal : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
  FinMem b0 UCode -> FinMemAllU f0 b0 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  PiEdgeVal G A0 B0 b1 f1 ->
  PiAppVal G M A0 B0 b0 f0 g -> PiAppVal G M A0 B0 b1 f1 g
upPiAppVal G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 src
  u v sel N val-b1 =
  let cgt = cft-from-cf g cg
      cu = Coherent-Selection sel cgt
      cv = Coherent-Selection-val sel cgt
      fmu0 = FinMem-Selection b0 f0 sel fmg0 cgt cb0 b0U
      val-b0 = downVal G N A0 u b0 b1 (fst le) fmu0 cb0 b1U val-b1
      body = src u v sel N val-b0
      le-f = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
      c-ef0 = Coherent-EvalFun f0 u cf0 cu
      c-ef1 = Coherent-EvalFun f1 u cf1 cu
      fmem-v-f0 = FinMem-Selection-codomain b0 f0 sel fmg0 cgt cf0 allU0
      ef1U = EvalFun-in-UCode f1 u b1 cf1 cu allU1
      fmem-v-f1 = finMem-upward v (EvalFun f0 u) (EvalFun f1 u)
                    le-f c-ef0 c-ef1 fmem-v-f0 ef1U
      sb1  = selectionBelow f1 u cf1 cu
      u1   = fst sb1
      v1   = fst (snd sb1)
      sel1 = fst (snd (snd sb1))
      le-u1 = fst (snd (snd (snd sb1)))
      eq-v1 = snd (snd (snd (snd sb1)))
      cu1  = Coherent-Selection sel1 cf1
      fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
      fmu-b1 = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
      val-u1 = restrictVal G N A0 u u1 b1 le-u1 fmu1-b1 fmu-b1 val-b1
      vty-v1 = piEV1 u1 v1 sel1 N val-u1
      vty-ef1 = Eq-transport (ValTy G (subst1 B0 N)) (Eq-sym eq-v1) vty-v1
  in upVal G (App M N) (subst1 B0 N) v
       (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0 fmem-v-f1 c-ef0 c-ef1 body vty-ef1

upPiAppEq : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
  FinMem b0 UCode -> FinMemAllU f0 b0 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  PiEdgeVal G A0 B0 b1 f1 ->
  PiAppEq G M A0 B0 b0 f0 g -> PiAppEq G M A0 B0 b1 f1 g
upPiAppEq G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 src
  u v sel N1 N2 eqv-b1 =
  let cgt = cft-from-cf g cg
      cu = Coherent-Selection sel cgt
      cv = Coherent-Selection-val sel cgt
      fmu0 = FinMem-Selection b0 f0 sel fmg0 cgt cb0 b0U
      eqv-b0 = downEqVal G N1 N2 A0 u b0 b1 (fst le) fmu0 cb0 b1U eqv-b1
      body = src u v sel N1 N2 eqv-b0
      le-f = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
      c-ef0 = Coherent-EvalFun f0 u cf0 cu
      c-ef1 = Coherent-EvalFun f1 u cf1 cu
      fmem-v-f0 = FinMem-Selection-codomain b0 f0 sel fmg0 cgt cf0 allU0
      ef1U = EvalFun-in-UCode f1 u b1 cf1 cu allU1
      fmem-v-f1 = finMem-upward v (EvalFun f0 u) (EvalFun f1 u)
                    le-f c-ef0 c-ef1 fmem-v-f0 ef1U
      val-N1-b1 = Val-from-EqVal-first u b1 eqv-b1
      sb1  = selectionBelow f1 u cf1 cu
      u1   = fst sb1
      v1   = fst (snd sb1)
      sel1 = fst (snd (snd sb1))
      le-u1 = fst (snd (snd (snd sb1)))
      eq-v1 = snd (snd (snd (snd sb1)))
      fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
      fmu-b1 = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
      val-u1 = restrictVal G N1 A0 u u1 b1 le-u1 fmu1-b1 fmu-b1 val-N1-b1
      vty-v1 = piEV1 u1 v1 sel1 N1 val-u1
      vty-ef1 = Eq-transport (ValTy G (subst1 B0 N1)) (Eq-sym eq-v1) vty-v1
  in upEqVal G (App M N1) (App M N2) (subst1 B0 N1) v
       (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0 fmem-v-f1 c-ef0 c-ef1 body vty-ef1

upPiAppEqVal : {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFunTail f0 -> CoherentFunTail f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
  FinMem b0 UCode -> FinMemAllU f0 b0 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  PiEdgeVal G A0 B0 b1 f1 ->
  PiAppEqVal G M N A0 B0 b0 f0 g -> PiAppEqVal G M N A0 B0 b1 f1 g
upPiAppEqVal G M N A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 src
  u v sel P val-b1 =
  let cgt = cft-from-cf g cg
      cu = Coherent-Selection sel cgt
      cv = Coherent-Selection-val sel cgt
      fmu0 = FinMem-Selection b0 f0 sel fmg0 cgt cb0 b0U
      val-b0 = downVal G P A0 u b0 b1 (fst le) fmu0 cb0 b1U val-b1
      body = src u v sel P val-b0
      le-f = EvalFun-mon f0 f1 u cf0 cf1 cu (snd le)
      c-ef0 = Coherent-EvalFun f0 u cf0 cu
      c-ef1 = Coherent-EvalFun f1 u cf1 cu
      fmem-v-f0 = FinMem-Selection-codomain b0 f0 sel fmg0 cgt cf0 allU0
      ef1U = EvalFun-in-UCode f1 u b1 cf1 cu allU1
      fmem-v-f1 = finMem-upward v (EvalFun f0 u) (EvalFun f1 u)
                    le-f c-ef0 c-ef1 fmem-v-f0 ef1U
      sb1  = selectionBelow f1 u cf1 cu
      u1   = fst sb1
      v1   = fst (snd sb1)
      sel1 = fst (snd (snd sb1))
      le-u1 = fst (snd (snd (snd sb1)))
      eq-v1 = snd (snd (snd (snd sb1)))
      fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
      fmu-b1 = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
      val-u1 = restrictVal G P A0 u u1 b1 le-u1 fmu1-b1 fmu-b1 val-b1
      vty-v1 = piEV1 u1 v1 sel1 P val-u1
      vty-ef1 = Eq-transport (ValTy G (subst1 B0 P)) (Eq-sym eq-v1) vty-v1
  in upEqVal G (App M P) (App N P) (subst1 B0 P) v
       (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v-f0 fmem-v-f1 c-ef0 c-ef1 body vty-ef1

------------------------------------------------------------------------
-- Restriction helpers (selection-based, Pi)
------------------------------------------------------------------------

restrictPiAppVal-sel :
    {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b : FinEl) (f g g' : FinFun) ->
    CoherentFunTail f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
    FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
    PiEdgeVal G A0 B0 b f ->
    PiAppVal G M A0 B0 b f g -> PiAppVal G M A0 B0 b f g'
restrictPiAppVal-sel G M A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV src
    u' v' sel' N val-N =
  let cgt  = cft-from-cf g cg
      cgt' = cft-from-cf g' cg'
      cu' = Coherent-Selection sel' cgt'
      cv' = Coherent-Selection-val sel' cgt'
      fmu'-b = FinMem-Selection b f sel' fmg' cgt' cb bU
      sb  = selectionBelow g u' cgt cu'
      u_g  = fst sb
      v_g  = fst (snd sb)
      sel_g = fst (snd (snd sb))
      le-ug = fst (snd (snd (snd sb)))
      eq-vg = snd (snd (snd (snd sb)))
      cu_g = Coherent-Selection sel_g cgt
      cv_g = Coherent-Selection-val sel_g cgt
      fmu_g = FinMem-Selection b f sel_g fmg cgt cb bU
      val-ug = restrictVal G N A0 u' u_g b le-ug fmu_g fmu'-b val-N
      body = src u_g v_g sel_g N val-ug
      le-ef = EvalFun-mon-arg f u_g u' le-ug cf cu_g cu'
      c-efug = Coherent-EvalFun f u_g cf cu_g
      c-efu' = Coherent-EvalFun f u' cf cu'
      fmem-vg-efug = FinMem-Selection-codomain b f sel_g fmg cgt cf allU
      efuU' = EvalFun-in-UCode f u' b cf cu' allU
      fmem-vg-efu' = finMem-upward v_g (EvalFun f u_g) (EvalFun f u')
                        le-ef c-efug c-efu' fmem-vg-efug efuU'
      sb-f  = selectionBelow f u' cf cu'
      u_f   = fst sb-f
      v_f   = fst (snd sb-f)
      sel_f = fst (snd (snd sb-f))
      le-uf = fst (snd (snd (snd sb-f)))
      eq-ef = snd (snd (snd (snd sb-f)))
      fmu_f-b = FinMemAllU-Selection b sel_f allU cf cb bU
      val-uf = restrictVal G N A0 u' u_f b le-uf fmu_f-b fmu'-b val-N
      vty-vf = piEV u_f v_f sel_f N val-uf
      vty-efu' = Eq-transport (ValTy G (subst1 B0 N)) (Eq-sym eq-ef) vty-vf
      body2 = upVal G (App M N) (subst1 B0 N) v_g
                (EvalFun f u_g) (EvalFun f u') le-ef
                fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
      le-v'-efgu' = Selection-le-EvalFun g sel' le cgt' cgt cu'
      le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
      fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' cgt' cf allU
  in restrictVal G (App M N) (subst1 B0 N) v_g v' (EvalFun f u')
       le-v'-vg fmem-v'-efu' fmem-vg-efu' body2

restrictPiAppEq-sel :
    {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b : FinEl) (f g g' : FinFun) ->
    CoherentFunTail f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
    FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
    PiEdgeVal G A0 B0 b f ->
    PiAppEq G M A0 B0 b f g -> PiAppEq G M A0 B0 b f g'
restrictPiAppEq-sel G M A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV src
    u' v' sel' N1 N2 eqv-N =
  let cgt  = cft-from-cf g cg
      cgt' = cft-from-cf g' cg'
      cu' = Coherent-Selection sel' cgt'
      cv' = Coherent-Selection-val sel' cgt'
      fmu'-b = FinMem-Selection b f sel' fmg' cgt' cb bU
      sb  = selectionBelow g u' cgt cu'
      u_g  = fst sb
      v_g  = fst (snd sb)
      sel_g = fst (snd (snd sb))
      le-ug = fst (snd (snd (snd sb)))
      eq-vg = snd (snd (snd (snd sb)))
      cu_g = Coherent-Selection sel_g cgt
      cv_g = Coherent-Selection-val sel_g cgt
      fmu_g = FinMem-Selection b f sel_g fmg cgt cb bU
      eqv-ug = restrictEqVal G N1 N2 A0 u' u_g b le-ug fmu_g fmu'-b eqv-N
      body = src u_g v_g sel_g N1 N2 eqv-ug
      le-ef = EvalFun-mon-arg f u_g u' le-ug cf cu_g cu'
      c-efug = Coherent-EvalFun f u_g cf cu_g
      c-efu' = Coherent-EvalFun f u' cf cu'
      fmem-vg-efug = FinMem-Selection-codomain b f sel_g fmg cgt cf allU
      efuU' = EvalFun-in-UCode f u' b cf cu' allU
      fmem-vg-efu' = finMem-upward v_g (EvalFun f u_g) (EvalFun f u')
                        le-ef c-efug c-efu' fmem-vg-efug efuU'
      val-N1 = Val-from-EqVal-first u' b eqv-N
      sb-f  = selectionBelow f u' cf cu'
      u_f   = fst sb-f
      v_f   = fst (snd sb-f)
      sel_f = fst (snd (snd sb-f))
      le-uf = fst (snd (snd (snd sb-f)))
      eq-ef = snd (snd (snd (snd sb-f)))
      fmu_f-b = FinMemAllU-Selection b sel_f allU cf cb bU
      val-uf = restrictVal G N1 A0 u' u_f b le-uf fmu_f-b fmu'-b val-N1
      vty-vf = piEV u_f v_f sel_f N1 val-uf
      vty-efu' = Eq-transport (ValTy G (subst1 B0 N1)) (Eq-sym eq-ef) vty-vf
      body2 = upEqVal G (App M N1) (App M N2) (subst1 B0 N1) v_g
                (EvalFun f u_g) (EvalFun f u') le-ef
                fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
      le-v'-efgu' = Selection-le-EvalFun g sel' le cgt' cgt cu'
      le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
      fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' cgt' cf allU
  in restrictEqVal G (App M N1) (App M N2) (subst1 B0 N1) v_g v' (EvalFun f u')
       le-v'-vg fmem-v'-efu' fmem-vg-efu' body2

restrictPiAppEqVal-sel :
    {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
    (b : FinEl) (f g g' : FinFun) ->
    CoherentFunTail f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
    FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
    PiEdgeVal G A0 B0 b f ->
    PiAppEqVal G M N A0 B0 b f g -> PiAppEqVal G M N A0 B0 b f g'
restrictPiAppEqVal-sel G M N A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV src
    u' v' sel' P val-P =
  let cgt  = cft-from-cf g cg
      cgt' = cft-from-cf g' cg'
      cu' = Coherent-Selection sel' cgt'
      cv' = Coherent-Selection-val sel' cgt'
      fmu'-b = FinMem-Selection b f sel' fmg' cgt' cb bU
      sb  = selectionBelow g u' cgt cu'
      u_g  = fst sb
      v_g  = fst (snd sb)
      sel_g = fst (snd (snd sb))
      le-ug = fst (snd (snd (snd sb)))
      eq-vg = snd (snd (snd (snd sb)))
      cu_g = Coherent-Selection sel_g cgt
      cv_g = Coherent-Selection-val sel_g cgt
      fmu_g = FinMem-Selection b f sel_g fmg cgt cb bU
      val-ug = restrictVal G P A0 u' u_g b le-ug fmu_g fmu'-b val-P
      body = src u_g v_g sel_g P val-ug
      le-ef = EvalFun-mon-arg f u_g u' le-ug cf cu_g cu'
      c-efug = Coherent-EvalFun f u_g cf cu_g
      c-efu' = Coherent-EvalFun f u' cf cu'
      fmem-vg-efug = FinMem-Selection-codomain b f sel_g fmg cgt cf allU
      efuU' = EvalFun-in-UCode f u' b cf cu' allU
      fmem-vg-efu' = finMem-upward v_g (EvalFun f u_g) (EvalFun f u')
                        le-ef c-efug c-efu' fmem-vg-efug efuU'
      sb-f  = selectionBelow f u' cf cu'
      u_f   = fst sb-f
      v_f   = fst (snd sb-f)
      sel_f = fst (snd (snd sb-f))
      le-uf = fst (snd (snd (snd sb-f)))
      eq-ef = snd (snd (snd (snd sb-f)))
      fmu_f-b = FinMemAllU-Selection b sel_f allU cf cb bU
      val-uf = restrictVal G P A0 u' u_f b le-uf fmu_f-b fmu'-b val-P
      vty-vf = piEV u_f v_f sel_f P val-uf
      vty-efu' = Eq-transport (ValTy G (subst1 B0 P)) (Eq-sym eq-ef) vty-vf
      body2 = upEqVal G (App M P) (App N P) (subst1 B0 P) v_g
                (EvalFun f u_g) (EvalFun f u') le-ef
                fmem-vg-efug fmem-vg-efu' c-efug c-efu' body vty-efu'
      le-v'-efgu' = Selection-le-EvalFun g sel' le cgt' cgt cu'
      le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
      fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' cgt' cf allU
  in restrictEqVal G (App M P) (App N P) (subst1 B0 P) v_g v' (EvalFun f u')
       le-v'-vg fmem-v'-efu' fmem-vg-efu' body2

-- restrictVal-PiCode: the main proof
restrictVal-PiCode :
    {n : Nat} (G : Ctx n) (M A : Expr n) (g g' : FinFun)
    (b : FinEl) (f : FinFun) ->
    CoherentFunTail f -> Coherent b -> FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> Pair (FinMemFun g' b f) (CoherentFun g') ->
    ValTyPi G A b f ->
    ValPi G M A g b f -> ValPi G M A g' b f
restrictVal-PiCode G M A g g' b f cf cb allU bU le mem' vtypi src =
  let A0   = fst src
      B0   = fst (snd src)
      red  = fst (snd (snd src))
      cg   = fst (snd (snd (snd src)))
      fmg  = fst (snd (snd (snd (snd src))))
      pav  = fst (snd (snd (snd (snd (snd src)))))
      pae  = snd (snd (snd (snd (snd (snd src)))))
      Av   = fst vtypi
      Bv   = fst (snd vtypi)
      redv = fst (snd (snd vtypi))
      inner-vty = snd (snd (snd (snd (snd vtypi))))
      piEVv = fst (snd inner-vty)
      uniq = Red-unique-Pi red redv
      piEV : PiEdgeVal G A0 B0 b f
      piEV = Eq-transport (\ Y -> PiEdgeVal G A0 Y b f) (Eq-sym (snd uniq))
               (Eq-transport (\ X -> PiEdgeVal G X Bv b f) (Eq-sym (fst uniq)) piEVv)
  in mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma (snd mem')
       (mkSigma (fst mem')
       (mkSigma
         (restrictPiAppVal-sel G M A0 B0 b f g g' cf cg (snd mem') cb allU
           bU le (fst mem') fmg piEV pav)
         (restrictPiAppEq-sel G M A0 B0 b f g g' cf cg (snd mem') cb allU
           bU le (fst mem') fmg piEV pae))))))

restrictEqVal-PiCode :
    {n : Nat} (G : Ctx n) (M N A : Expr n) (g g' : FinFun)
    (b : FinEl) (f : FinFun) ->
    CoherentFunTail f -> Coherent b -> FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> Pair (FinMemFun g' b f) (CoherentFun g') ->
    ValTyPi G A b f ->
    EqValPi G M N A g b f -> EqValPi G M N A g' b f
restrictEqVal-PiCode G M N A g g' b f cf cb allU bU le mem' vtypi src =
  let A0   = fst src
      B0   = fst (snd src)
      red  = fst (snd (snd src))
      cg   = fst (snd (snd (snd src)))
      fmg  = fst (snd (snd (snd (snd src))))
      paev = snd (snd (snd (snd (snd src))))
      Av   = fst vtypi
      Bv   = fst (snd vtypi)
      redv = fst (snd (snd vtypi))
      inner-vty = snd (snd (snd (snd (snd vtypi))))
      piEVv = fst (snd inner-vty)
      uniq = Red-unique-Pi red redv
      piEV : PiEdgeVal G A0 B0 b f
      piEV = Eq-transport (\ Y -> PiEdgeVal G A0 Y b f) (Eq-sym (snd uniq))
               (Eq-transport (\ X -> PiEdgeVal G X Bv b f) (Eq-sym (fst uniq)) piEVv)
  in mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma (snd mem')
       (mkSigma (fst mem')
       (restrictPiAppEqVal-sel G M N A0 B0 b f g g' cf cg (snd mem') cb allU
         bU le (fst mem') fmg piEV paev)))))

------------------------------------------------------------------------
-- Transport PiEdgeVal/PiEdgeEq/PiEdgeEqTy
------------------------------------------------------------------------

transportPiEdgeVal-sel :
  {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  LeCode b0 b1 -> LeFunCode f0 f1 ->
  FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 -> FinMemAllU f1 b1 ->
  ValTy G A b1 ->
  PiEdgeVal G A B b1 f1 -> PiEdgeVal G A B b0 f0
transportPiEdgeVal-sel G A B b0 f0 b1 f1 cb0 cb1 b1U b0U le-b le-f allU0 cf0 cf1 allU1 vtb1 piEV1
  u0 v0 sel0 N val-b0 =
  let cu0 = Coherent-Selection sel0 cf0
      fmu0-b0 = FinMemAllU-Selection b0 sel0 allU0 cf0 cb0 b0U
      fmu0-b1 = finMem-upward u0 b0 b1 le-b cb0 cb1 fmu0-b0 b1U
      val-b1 = upVal G N A u0 b0 b1 le-b fmu0-b0 fmu0-b1 cb0 cb1 val-b0 vtb1
      sb = selectionBelow f1 u0 cf1 cu0
      u1 = fst sb
      v1 = fst (snd sb)
      sel1 = fst (snd (snd sb))
      le-u1 = fst (snd (snd (snd sb)))
      eq-v1 = snd (snd (snd (snd sb)))
      fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
      val-u1-b1 = restrictVal G N A u0 u1 b1 le-u1 fmu1-b1 fmu0-b1 val-b1
      vty-v1 = piEV1 u1 v1 sel1 N val-u1-b1
      le-v0-ef = Selection-le-EvalFun f1 sel0 le-f cf0 cf1 cu0
      le-v0-v1 = Eq-transport (LeCode v0) eq-v1 le-v0-ef
      fmem-v0-U = FinMem-Selection-UCode b0 sel0 allU0 cf0
      v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1 (EvalFun-in-UCode f1 u0 b1 cf1 cu0 allU1)
  in downValTy G (subst1 B N) v0 v1 le-v0-v1 fmem-v0-U v1U vty-v1

transportPiEdgeEq-sel :
  {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  LeCode b0 b1 -> LeFunCode f0 f1 ->
  FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 -> FinMemAllU f1 b1 ->
  ValTy G A b1 ->
  PiEdgeEq G A B b1 f1 -> PiEdgeEq G A B b0 f0
transportPiEdgeEq-sel G A B b0 f0 b1 f1 cb0 cb1 b1U b0U le-b le-f allU0 cf0 cf1 allU1 vtb1 piEE1
  u0 v0 sel0 N1 N2 eqv-b0 =
  let cu0 = Coherent-Selection sel0 cf0
      fmu0-b0 = FinMemAllU-Selection b0 sel0 allU0 cf0 cb0 b0U
      fmu0-b1 = finMem-upward u0 b0 b1 le-b cb0 cb1 fmu0-b0 b1U
      eqv-b1 = upEqVal G N1 N2 A u0 b0 b1 le-b fmu0-b0 fmu0-b1 cb0 cb1 eqv-b0 vtb1
      sb = selectionBelow f1 u0 cf1 cu0
      u1 = fst sb
      v1 = fst (snd sb)
      sel1 = fst (snd (snd sb))
      le-u1 = fst (snd (snd (snd sb)))
      eq-v1 = snd (snd (snd (snd sb)))
      fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
      eqv-u1-b1 = restrictEqVal G N1 N2 A u0 u1 b1 le-u1 fmu1-b1 fmu0-b1 eqv-b1
      eqvty-v1 = piEE1 u1 v1 sel1 N1 N2 eqv-u1-b1
      le-v0-ef = Selection-le-EvalFun f1 sel0 le-f cf0 cf1 cu0
      le-v0-v1 = Eq-transport (LeCode v0) eq-v1 le-v0-ef
      fmem-v0-U = FinMem-Selection-UCode b0 sel0 allU0 cf0
      v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1 (EvalFun-in-UCode f1 u0 b1 cf1 cu0 allU1)
  in downEqValTy G (subst1 B N1) (subst1 B N2) v0 v1 le-v0-v1 fmem-v0-U v1U eqvty-v1

transportPiEdgeEqTy-sel :
  {n : Nat} (G : Ctx n) (A : Expr n) (B B' : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  LeCode b0 b1 -> LeFunCode f0 f1 ->
  FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 -> FinMemAllU f1 b1 ->
  ValTy G A b1 ->
  PiEdgeEqTy G A B B' b1 f1 -> PiEdgeEqTy G A B B' b0 f0
transportPiEdgeEqTy-sel G A B B' b0 f0 b1 f1 cb0 cb1 b1U b0U le-b le-f allU0 cf0 cf1 allU1 vtb1 piEET1
  u0 v0 sel0 P val-b0 =
  let cu0 = Coherent-Selection sel0 cf0
      fmu0-b0 = FinMemAllU-Selection b0 sel0 allU0 cf0 cb0 b0U
      fmu0-b1 = finMem-upward u0 b0 b1 le-b cb0 cb1 fmu0-b0 b1U
      val-b1 = upVal G P A u0 b0 b1 le-b fmu0-b0 fmu0-b1 cb0 cb1 val-b0 vtb1
      sb = selectionBelow f1 u0 cf1 cu0
      u1 = fst sb
      v1 = fst (snd sb)
      sel1 = fst (snd (snd sb))
      le-u1 = fst (snd (snd (snd sb)))
      eq-v1 = snd (snd (snd (snd sb)))
      fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
      val-u1-b1 = restrictVal G P A u0 u1 b1 le-u1 fmu1-b1 fmu0-b1 val-b1
      eqvty-v1 = piEET1 u1 v1 sel1 P val-u1-b1
      le-v0-ef = Selection-le-EvalFun f1 sel0 le-f cf0 cf1 cu0
      le-v0-v1 = Eq-transport (LeCode v0) eq-v1 le-v0-ef
      fmem-v0-U = FinMem-Selection-UCode b0 sel0 allU0 cf0
      v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1 (EvalFun-in-UCode f1 u0 b1 cf1 cu0 allU1)
  in downEqValTy G (subst1 B P) (subst1 B' P) v0 v1 le-v0-v1 fmem-v0-U v1U eqvty-v1

------------------------------------------------------------------------
-- Transport SigmaEdgeVal/SigmaEdgeEq/SigmaEdgeEqTy
-- (exact mirror of PiEdge transport, using SigmaEdge families)
------------------------------------------------------------------------

transportSigmaEdgeVal-sel :
  {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  LeCode b0 b1 -> LeFunCode f0 f1 ->
  FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 -> FinMemAllU f1 b1 ->
  ValTy G A b1 ->
  SigmaEdgeVal G A B b1 f1 -> SigmaEdgeVal G A B b0 f0
transportSigmaEdgeVal-sel G A B b0 f0 b1 f1 cb0 cb1 b1U b0U le-b le-f allU0 cf0 cf1 allU1 vtb1 sigEV1
  u0 v0 sel0 N val-b0 =
  let cu0 = Coherent-Selection sel0 cf0
      fmu0-b0 = FinMemAllU-Selection b0 sel0 allU0 cf0 cb0 b0U
      fmu0-b1 = finMem-upward u0 b0 b1 le-b cb0 cb1 fmu0-b0 b1U
      val-b1 = upVal G N A u0 b0 b1 le-b fmu0-b0 fmu0-b1 cb0 cb1 val-b0 vtb1
      sb = selectionBelow f1 u0 cf1 cu0
      u1 = fst sb
      v1 = fst (snd sb)
      sel1 = fst (snd (snd sb))
      le-u1 = fst (snd (snd (snd sb)))
      eq-v1 = snd (snd (snd (snd sb)))
      fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
      val-u1-b1 = restrictVal G N A u0 u1 b1 le-u1 fmu1-b1 fmu0-b1 val-b1
      vty-v1 = sigEV1 u1 v1 sel1 N val-u1-b1
      le-v0-ef = Selection-le-EvalFun f1 sel0 le-f cf0 cf1 cu0
      le-v0-v1 = Eq-transport (LeCode v0) eq-v1 le-v0-ef
      fmem-v0-U = FinMem-Selection-UCode b0 sel0 allU0 cf0
      v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1 (EvalFun-in-UCode f1 u0 b1 cf1 cu0 allU1)
  in downValTy G (subst1 B N) v0 v1 le-v0-v1 fmem-v0-U v1U vty-v1

transportSigmaEdgeEq-sel :
  {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  LeCode b0 b1 -> LeFunCode f0 f1 ->
  FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 -> FinMemAllU f1 b1 ->
  ValTy G A b1 ->
  SigmaEdgeEq G A B b1 f1 -> SigmaEdgeEq G A B b0 f0
transportSigmaEdgeEq-sel G A B b0 f0 b1 f1 cb0 cb1 b1U b0U le-b le-f allU0 cf0 cf1 allU1 vtb1 sigEE1
  u0 v0 sel0 N1 N2 eqv-b0 =
  let cu0 = Coherent-Selection sel0 cf0
      fmu0-b0 = FinMemAllU-Selection b0 sel0 allU0 cf0 cb0 b0U
      fmu0-b1 = finMem-upward u0 b0 b1 le-b cb0 cb1 fmu0-b0 b1U
      eqv-b1 = upEqVal G N1 N2 A u0 b0 b1 le-b fmu0-b0 fmu0-b1 cb0 cb1 eqv-b0 vtb1
      sb = selectionBelow f1 u0 cf1 cu0
      u1 = fst sb
      v1 = fst (snd sb)
      sel1 = fst (snd (snd sb))
      le-u1 = fst (snd (snd (snd sb)))
      eq-v1 = snd (snd (snd (snd sb)))
      fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
      eqv-u1-b1 = restrictEqVal G N1 N2 A u0 u1 b1 le-u1 fmu1-b1 fmu0-b1 eqv-b1
      eqvty-v1 = sigEE1 u1 v1 sel1 N1 N2 eqv-u1-b1
      le-v0-ef = Selection-le-EvalFun f1 sel0 le-f cf0 cf1 cu0
      le-v0-v1 = Eq-transport (LeCode v0) eq-v1 le-v0-ef
      fmem-v0-U = FinMem-Selection-UCode b0 sel0 allU0 cf0
      v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1 (EvalFun-in-UCode f1 u0 b1 cf1 cu0 allU1)
  in downEqValTy G (subst1 B N1) (subst1 B N2) v0 v1 le-v0-v1 fmem-v0-U v1U eqvty-v1

transportSigmaEdgeEqTy-sel :
  {n : Nat} (G : Ctx n) (A : Expr n) (B B' : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  LeCode b0 b1 -> LeFunCode f0 f1 ->
  FinMemAllU f0 b0 -> CoherentFunTail f0 -> CoherentFunTail f1 -> FinMemAllU f1 b1 ->
  ValTy G A b1 ->
  SigmaEdgeEqTy G A B B' b1 f1 -> SigmaEdgeEqTy G A B B' b0 f0
transportSigmaEdgeEqTy-sel G A B B' b0 f0 b1 f1 cb0 cb1 b1U b0U le-b le-f allU0 cf0 cf1 allU1 vtb1 sigEET1
  u0 v0 sel0 P val-b0 =
  let cu0 = Coherent-Selection sel0 cf0
      fmu0-b0 = FinMemAllU-Selection b0 sel0 allU0 cf0 cb0 b0U
      fmu0-b1 = finMem-upward u0 b0 b1 le-b cb0 cb1 fmu0-b0 b1U
      val-b1 = upVal G P A u0 b0 b1 le-b fmu0-b0 fmu0-b1 cb0 cb1 val-b0 vtb1
      sb = selectionBelow f1 u0 cf1 cu0
      u1 = fst sb
      v1 = fst (snd sb)
      sel1 = fst (snd (snd sb))
      le-u1 = fst (snd (snd (snd sb)))
      eq-v1 = snd (snd (snd (snd sb)))
      fmu1-b1 = FinMemAllU-Selection b1 sel1 allU1 cf1 cb1 b1U
      val-u1-b1 = restrictVal G P A u0 u1 b1 le-u1 fmu1-b1 fmu0-b1 val-b1
      eqvty-v1 = sigEET1 u1 v1 sel1 P val-u1-b1
      le-v0-ef = Selection-le-EvalFun f1 sel0 le-f cf0 cf1 cu0
      le-v0-v1 = Eq-transport (LeCode v0) eq-v1 le-v0-ef
      fmem-v0-U = FinMem-Selection-UCode b0 sel0 allU0 cf0
      v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1 (EvalFun-in-UCode f1 u0 b1 cf1 cu0 allU1)
  in downEqValTy G (subst1 B P) (subst1 B' P) v0 v1 le-v0-v1 fmem-v0-U v1U eqvty-v1

------------------------------------------------------------------------
-- downVal
------------------------------------------------------------------------

downVal G M A u Bot              a1             le mem ca0 ca1 src = tt
downVal G M A u UCode            Bot            ()
downVal G M A u UCode            UCode          le mem ca0 ca1 src = src
downVal G M A u UCode            PropCode       ()
downVal G M A u UCode            (FunEl h)      ()
downVal G M A u UCode            (PiCode b f)   ()
downVal G M A u UCode            (SigmaCode b f) ()
downVal G M A u UCode            (PairCode x y)  ()
downVal G M A u PropCode         a1             le mem ca0 ca1 src = tt
downVal G M A u (FunEl g)        Bot            le mem ca0 ca1 src = tt
downVal G M A u (FunEl g)        UCode          le mem ca0 ca1 src = tt
downVal G M A u (FunEl g)        PropCode       le mem ca0 ca1 src = tt
downVal G M A u (FunEl g)        (FunEl h)      le mem ca0 ca1 src = tt
downVal G M A u (FunEl g)        (PiCode b f)   le mem ca0 ca1 src = tt
downVal G M A u (FunEl g)        (SigmaCode b f) le mem ca0 ca1 src = tt
downVal G M A u (FunEl g)        (PairCode x y)  le mem ca0 ca1 src = tt
downVal G M A u (PiCode b0 f0) Bot          ()
downVal G M A u (PiCode b0 f0) UCode        ()
downVal G M A u (PiCode b0 f0) PropCode     ()
downVal G M A u (PiCode b0 f0) (FunEl h)    ()
downVal G M A u (PiCode b0 f0) (SigmaCode b1 f1) ()
downVal G M A u (PiCode b0 f0) (PairCode x y) ()
-- PiCode/PiCode: split on u
downVal G M A Bot            (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
downVal G M A UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
downVal G M A PropCode       (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
downVal G M A (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src =
  let vty = fst src
      vpi = snd src
      fmem-pf = FinMem-a-in-U (FunEl g) (PiCode b0 f0) mem
      vty' = downValTy G A (PiCode b0 f0) (PiCode b1 f1) le fmem-pf ca1 vty
      A0  = fst vpi
      B0  = fst (snd vpi)
      red = fst (snd (snd vpi))
      sat = fst (snd (snd (snd vpi)))
      pav = fst (snd (snd (snd (snd (snd vpi)))))
      pae = snd (snd (snd (snd (snd (snd vpi)))))
      cf0 = snd ca0
      cf1 = snd (snd ca1)
      cb0 = fst ca0
      cb1 = coh-from-aU b1 (fst ca1)
      b1U = fst ca1
      allU1 = fst (snd ca1)
      b0U = fst fmem-pf
      allU0 = fst (snd fmem-pf)
      Av  = fst vty
      Bv  = fst (snd vty)
      redv = fst (snd (snd vty))
      uniq-dom = Red-unique-Pi red redv
      vtA0b1 : ValTy G A0 b1
      vtA0b1 = Eq-transport (\ X -> ValTy G X b1) (Eq-sym (fst uniq-dom))
                 (fst (snd (snd (snd (snd (snd vty))))))
      vpi' = mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma sat
               (mkSigma (fst mem)
               (mkSigma
                 (downPiAppVal G M A0 B0 b0 f0 b1 f1 g cf0 cf1 sat cb0 cb1 b1U b0U allU0 allU1 le (fst mem) vtA0b1 pav)
                 (downPiAppEq G M A0 B0 b0 f0 b1 f1 g cf0 cf1 sat cb0 cb1 b1U b0U allU0 allU1 le (fst mem) vtA0b1 pae))))))
  in mkSigma vty' vpi'
downVal G M A (PiCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
downVal G M A (SigmaCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
downVal G M A (PairCode x y) (PiCode b0 f0) (PiCode b1 f1) le ()
-- SigmaCode: split on u (all Top)
downVal G M A u (SigmaCode b0 f0) Bot          ()
downVal G M A u (SigmaCode b0 f0) UCode        ()
downVal G M A u (SigmaCode b0 f0) PropCode     ()
downVal G M A u (SigmaCode b0 f0) (FunEl h)    ()
downVal G M A u (SigmaCode b0 f0) (PiCode b1 f1) ()
downVal G M A u (SigmaCode b0 f0) (PairCode x y) ()
downVal G M A Bot            (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
downVal G M A UCode          (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
downVal G M A PropCode       (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
downVal G M A (FunEl g)      (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
downVal G M A (PiCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
downVal G M A (SigmaCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
downVal G M A (PairCode x y) (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
-- PairCode at a: FinMem u (PairCode ..) empty unless u = Bot or PairCode
downVal G M A u (PairCode x y) Bot          ()
downVal G M A u (PairCode x y) UCode        ()
downVal G M A u (PairCode x y) PropCode     ()
downVal G M A u (PairCode x y) (FunEl h)    ()
downVal G M A u (PairCode x y) (PiCode b f) ()
downVal G M A u (PairCode x y) (SigmaCode b f) ()
downVal G M A u (PairCode x0 y0) (PairCode x1 y1) le mem ca0 ca1 src = tt

------------------------------------------------------------------------
-- downEqVal
------------------------------------------------------------------------

downEqVal G M N A u Bot              a1             le mem ca0 ca1 src = tt
downEqVal G M N A u UCode            Bot            ()
downEqVal G M N A u UCode            UCode          le mem ca0 ca1 src = src
downEqVal G M N A u UCode            PropCode       ()
downEqVal G M N A u UCode            (FunEl h)      ()
downEqVal G M N A u UCode            (PiCode b f)   ()
downEqVal G M N A u UCode            (SigmaCode b f) ()
downEqVal G M N A u UCode            (PairCode x y) ()
downEqVal G M N A u PropCode         a1             le mem ca0 ca1 src = tt
downEqVal G M N A u (FunEl g)        Bot            le mem ca0 ca1 src = tt
downEqVal G M N A u (FunEl g)        UCode          le mem ca0 ca1 src = tt
downEqVal G M N A u (FunEl g)        PropCode       le mem ca0 ca1 src = tt
downEqVal G M N A u (FunEl g)        (FunEl h)      le mem ca0 ca1 src = tt
downEqVal G M N A u (FunEl g)        (PiCode b f)   le mem ca0 ca1 src = tt
downEqVal G M N A u (FunEl g)        (SigmaCode b f) le mem ca0 ca1 src = tt
downEqVal G M N A u (FunEl g)        (PairCode x y) le mem ca0 ca1 src = tt
downEqVal G M N A u (PiCode b0 f0)   Bot          ()
downEqVal G M N A u (PiCode b0 f0)   UCode        ()
downEqVal G M N A u (PiCode b0 f0)   PropCode     ()
downEqVal G M N A u (PiCode b0 f0)   (FunEl h)    ()
downEqVal G M N A u (PiCode b0 f0)   (SigmaCode b1 f1) ()
downEqVal G M N A u (PiCode b0 f0)   (PairCode x y) ()
-- PiCode/PiCode: split on u
downEqVal G M N A Bot            (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
downEqVal G M N A UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
downEqVal G M N A PropCode       (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
downEqVal G M N A (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src =
  let vty  = fst src
      vpiM = fst (snd src)
      vpiN = fst (snd (snd src))
      epi  = snd (snd (snd src))
      valM  = mkSigma vty vpiM
      valN  = mkSigma vty vpiN
      valM' = downVal G M A (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 valM
      valN' = downVal G N A (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 valN
      A0   = fst epi
      B0   = fst (snd epi)
      red  = fst (snd (snd epi))
      sat  = fst (snd (snd (snd epi)))
      paev = snd (snd (snd (snd (snd epi))))
      fmem-pf = FinMem-a-in-U (FunEl g) (PiCode b0 f0) mem
      cf0 = snd ca0
      cf1 = snd (snd ca1)
      cb0 = fst ca0
      cb1 = coh-from-aU b1 (fst ca1)
      b1U = fst ca1
      allU1 = fst (snd ca1)
      b0U = fst fmem-pf
      allU0 = fst (snd fmem-pf)
      Av   = fst vty
      Bv   = fst (snd vty)
      redv = fst (snd (snd vty))
      uniq-dom = Red-unique-Pi red redv
      vtA0b1 : ValTy G A0 b1
      vtA0b1 = Eq-transport (\ X -> ValTy G X b1) (Eq-sym (fst uniq-dom))
                 (fst (snd (snd (snd (snd (snd vty))))))
      epi' = mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma sat
               (mkSigma (fst mem)
               (downPiAppEqVal G M N A0 B0 b0 f0 b1 f1 g cf0 cf1 sat cb0 cb1 b1U b0U allU0 allU1 le (fst mem) vtA0b1 paev)))))
  in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
downEqVal G M N A (PiCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
downEqVal G M N A (SigmaCode a' ff) (PiCode b0 f0) (PiCode b1 f1) le ()
downEqVal G M N A (PairCode x y) (PiCode b0 f0) (PiCode b1 f1) le ()
-- SigmaCode: all Top
downEqVal G M N A u (SigmaCode b0 f0) Bot          ()
downEqVal G M N A u (SigmaCode b0 f0) UCode        ()
downEqVal G M N A u (SigmaCode b0 f0) PropCode     ()
downEqVal G M N A u (SigmaCode b0 f0) (FunEl h)    ()
downEqVal G M N A u (SigmaCode b0 f0) (PiCode b1 f1) ()
downEqVal G M N A u (SigmaCode b0 f0) (PairCode x y) ()
downEqVal G M N A Bot            (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
downEqVal G M N A UCode          (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
downEqVal G M N A PropCode       (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
downEqVal G M N A (FunEl g)      (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
downEqVal G M N A (PiCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
downEqVal G M N A (SigmaCode a' ff) (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
downEqVal G M N A (PairCode x y) (SigmaCode b0 f0) (SigmaCode b1 f1) le mem ca0 ca1 src = tt
-- PairCode
downEqVal G M N A u (PairCode x y) Bot          ()
downEqVal G M N A u (PairCode x y) UCode        ()
downEqVal G M N A u (PairCode x y) PropCode     ()
downEqVal G M N A u (PairCode x y) (FunEl h)    ()
downEqVal G M N A u (PairCode x y) (PiCode b f) ()
downEqVal G M N A u (PairCode x y) (SigmaCode b f) ()
downEqVal G M N A u (PairCode x0 y0) (PairCode x1 y1) le mem ca0 ca1 src = tt

------------------------------------------------------------------------
-- downValTy / downEqValTy
------------------------------------------------------------------------

downValTy G M Bot              u1             le fmem cu1 src = tt
downValTy G M UCode            Bot            ()
downValTy G M UCode            UCode          le fmem cu1 src = tt
downValTy G M UCode            PropCode       ()
downValTy G M UCode            (FunEl h)      ()
downValTy G M UCode            (PiCode b f)   ()
downValTy G M UCode            (SigmaCode b f) ()
downValTy G M UCode            (PairCode x y)  ()
downValTy G M PropCode         Bot            ()
downValTy G M PropCode         UCode          ()
downValTy G M PropCode         PropCode       le fmem cu1 src = tt
downValTy G M PropCode         (FunEl h)      ()
downValTy G M PropCode         (PiCode b f)   ()
downValTy G M PropCode         (SigmaCode b f) ()
downValTy G M PropCode         (PairCode x y) ()
downValTy G M (FunEl g)        u1             le ()
downValTy G M (PiCode b0 f0)   Bot          ()
downValTy G M (PiCode b0 f0)   UCode        ()
downValTy G M (PiCode b0 f0)   PropCode     ()
downValTy G M (PiCode b0 f0)   (FunEl h)    ()
downValTy G M (PiCode b0 f0)   (SigmaCode b1 f1) ()
downValTy G M (PiCode b0 f0)   (PairCode x y) ()
downValTy G M (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 src =
  let A    = fst src
      B    = fst (snd src)
      red  = fst (snd (snd src))
      sat1 = fst (snd (snd (snd src)))
      fmA1 = fst (snd (snd (snd (snd src))))
      inner = snd (snd (snd (snd (snd src))))
      vty-b1 = fst inner
      piEV   = fst (snd inner)
      piEE   = snd (snd inner)
      fmem-b0  = fst fmem
      fmemAll0 = fst (snd fmem)
      sat0     = snd (snd fmem)
      cb1 = coh-from-aU b1 (fst cu1)
      cu0 = FinMem-Coherent (PiCode b0 f0) UCode fmem
      cb0 = coh-from-aU b0 fmem-b0
      vty-b0 = downValTy G A b0 b1 (fst le) fmem-b0 (fst cu1) vty-b1
      piEV0 = transportPiEdgeVal-sel G A B b0 f0 b1 f1
                cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vty-b1 piEV
      piEE0 = transportPiEdgeEq-sel G A B b0 f0 b1 f1
                cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vty-b1 piEE
  in mkSigma A (mkSigma B (mkSigma red (mkSigma sat0
       (mkSigma fmemAll0 (mkSigma vty-b0 (mkSigma piEV0 piEE0))))))
-- SigmaCode/SigmaCode: mirror PiCode
downValTy G M (SigmaCode b0 f0) Bot          ()
downValTy G M (SigmaCode b0 f0) UCode        ()
downValTy G M (SigmaCode b0 f0) PropCode     ()
downValTy G M (SigmaCode b0 f0) (FunEl h)    ()
downValTy G M (SigmaCode b0 f0) (PiCode b1 f1) ()
downValTy G M (SigmaCode b0 f0) (PairCode x y) ()
downValTy G M (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 src =
  let A    = fst src
      B    = fst (snd src)
      red  = fst (snd (snd src))
      sat1 = fst (snd (snd (snd src)))
      fmA1 = fst (snd (snd (snd (snd src))))
      inner = snd (snd (snd (snd (snd src))))
      vty-b1 = fst inner
      sigEV  = fst (snd inner)
      sigEE  = snd (snd inner)
      fmem-b0  = fst fmem
      fmemAll0 = fst (snd fmem)
      sat0     = snd (snd fmem)
      cb1 = coh-from-aU b1 (fst cu1)
      cu0 = FinMem-Coherent (SigmaCode b0 f0) UCode fmem
      cb0 = coh-from-aU b0 fmem-b0
      vty-b0 = downValTy G A b0 b1 (fst le) fmem-b0 (fst cu1) vty-b1
      sigEV0 = transportSigmaEdgeVal-sel G A B b0 f0 b1 f1
                 cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vty-b1 sigEV
      sigEE0 = transportSigmaEdgeEq-sel G A B b0 f0 b1 f1
                 cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vty-b1 sigEE
  in mkSigma A (mkSigma B (mkSigma red (mkSigma sat0
       (mkSigma fmemAll0 (mkSigma vty-b0 (mkSigma sigEV0 sigEE0))))))
-- PairCode: ValTy is Top
downValTy G M (PairCode x y) u1 le ()

downEqValTy G M N Bot              u1             le fmem cu1 src = tt
downEqValTy G M N UCode            Bot            ()
downEqValTy G M N UCode            UCode          le fmem cu1 src = tt
downEqValTy G M N UCode            PropCode       ()
downEqValTy G M N UCode            (FunEl h)      ()
downEqValTy G M N UCode            (PiCode b f)   ()
downEqValTy G M N UCode            (SigmaCode b f) ()
downEqValTy G M N UCode            (PairCode x y) ()
downEqValTy G M N PropCode         Bot            ()
downEqValTy G M N PropCode         UCode          ()
downEqValTy G M N PropCode         PropCode       le fmem cu1 src = tt
downEqValTy G M N PropCode         (FunEl h)      ()
downEqValTy G M N PropCode         (PiCode b f)   ()
downEqValTy G M N PropCode         (SigmaCode b f) ()
downEqValTy G M N PropCode         (PairCode x y) ()
downEqValTy G M N (FunEl g)        u1             le ()
downEqValTy G M N (PiCode b0 f0)   Bot          ()
downEqValTy G M N (PiCode b0 f0)   UCode        ()
downEqValTy G M N (PiCode b0 f0)   PropCode     ()
downEqValTy G M N (PiCode b0 f0)   (FunEl h)    ()
downEqValTy G M N (PiCode b0 f0)   (SigmaCode b1 f1) ()
downEqValTy G M N (PiCode b0 f0)   (PairCode x y) ()
downEqValTy G M N (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 src =
  let vtyM1 = fst src
      vtyN1 = fst (snd src)
      core  = snd (snd src)
      A    = fst core
      B    = fst (snd core)
      A'   = fst (snd (snd core))
      B'   = fst (snd (snd (snd core)))
      redM = fst (snd (snd (snd (snd core))))
      redN = fst (snd (snd (snd (snd (snd core)))))
      sat1   = fst (snd (snd (snd (snd (snd (snd core))))))
      fmA1   = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
      tail8  = snd (snd (snd (snd (snd (snd (snd (snd core)))))))
      eqvty  = fst tail8
      piEEqT = snd tail8
      A_M    = fst vtyM1
      vtA_M  = fst (snd (snd (snd (snd (snd vtyM1)))))
      redM2  = fst (snd (snd vtyM1))
      uniqM  = Red-unique-Pi redM2 redM
      eqAMA  : Eq A_M A
      eqAMA  = fst uniqM
      vtA-b1 = Eq-transport (\ X -> ValTy G X b1) eqAMA vtA_M
      fmem-b0  = fst fmem
      fmemAll0 = fst (snd fmem)
      sat0     = snd (snd fmem)
      cb1 = coh-from-aU b1 (fst cu1)
      cu0 = FinMem-Coherent (PiCode b0 f0) UCode fmem
      cb0 = coh-from-aU b0 fmem-b0
      eqvty0 = downEqValTy G A A' b0 b1 (fst le) fmem-b0 (fst cu1) eqvty
      piEEqT0 = transportPiEdgeEqTy-sel G A B B' b0 f0 b1 f1
                  cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vtA-b1 piEEqT
      vtyM0 = downValTy G M (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 vtyM1
      vtyN0 = downValTy G N (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 vtyN1
      core0 = mkSigma A (mkSigma B (mkSigma A' (mkSigma B'
                (mkSigma redM (mkSigma redN (mkSigma sat0
                  (mkSigma fmemAll0 (mkSigma eqvty0 piEEqT0))))))))
  in mkSigma vtyM0 (mkSigma vtyN0 core0)
-- SigmaCode/SigmaCode: mirror PiCode
downEqValTy G M N (SigmaCode b0 f0) Bot          ()
downEqValTy G M N (SigmaCode b0 f0) UCode        ()
downEqValTy G M N (SigmaCode b0 f0) PropCode     ()
downEqValTy G M N (SigmaCode b0 f0) (FunEl h)    ()
downEqValTy G M N (SigmaCode b0 f0) (PiCode b1 f1) ()
downEqValTy G M N (SigmaCode b0 f0) (PairCode x y) ()
downEqValTy G M N (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 src =
  let vtyM1 = fst src
      vtyN1 = fst (snd src)
      core  = snd (snd src)
      A    = fst core
      B    = fst (snd core)
      A'   = fst (snd (snd core))
      B'   = fst (snd (snd (snd core)))
      redM = fst (snd (snd (snd (snd core))))
      redN = fst (snd (snd (snd (snd (snd core)))))
      sat1   = fst (snd (snd (snd (snd (snd (snd core))))))
      fmA1   = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
      tail8  = snd (snd (snd (snd (snd (snd (snd (snd core)))))))
      eqvty  = fst tail8
      sigEEqT = snd tail8
      A_M    = fst vtyM1
      vtA_M  = fst (snd (snd (snd (snd (snd vtyM1)))))
      redM2  = fst (snd (snd vtyM1))
      uniqM  = Red-unique-Sigma redM2 redM
      eqAMA  : Eq A_M A
      eqAMA  = fst uniqM
      vtA-b1 = Eq-transport (\ X -> ValTy G X b1) eqAMA vtA_M
      fmem-b0  = fst fmem
      fmemAll0 = fst (snd fmem)
      sat0     = snd (snd fmem)
      cb1 = coh-from-aU b1 (fst cu1)
      cu0 = FinMem-Coherent (SigmaCode b0 f0) UCode fmem
      cb0 = coh-from-aU b0 fmem-b0
      eqvty0 = downEqValTy G A A' b0 b1 (fst le) fmem-b0 (fst cu1) eqvty
      sigEEqT0 = transportSigmaEdgeEqTy-sel G A B B' b0 f0 b1 f1
                   cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vtA-b1 sigEEqT
      vtyM0 = downValTy G M (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 vtyM1
      vtyN0 = downValTy G N (SigmaCode b0 f0) (SigmaCode b1 f1) le fmem cu1 vtyN1
      core0 = mkSigma A (mkSigma B (mkSigma A' (mkSigma B'
                (mkSigma redM (mkSigma redN (mkSigma sat0
                  (mkSigma fmemAll0 (mkSigma eqvty0 sigEEqT0))))))))
  in mkSigma vtyM0 (mkSigma vtyN0 core0)
-- PairCode: EqValTy is Top
downEqValTy G M N (PairCode x y) u1 le ()

------------------------------------------------------------------------
-- upVal
------------------------------------------------------------------------

-- a0 = Bot, u = Bot: split a1
upVal G M A Bot Bot          Bot             le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot Bot          UCode           le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot Bot          PropCode        le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot Bot          (FunEl h)       le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot Bot          (PiCode b1 f1)  le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot Bot          (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot Bot          (PairCode x y)  le mem0 mem1 ca0 ca1 src vta1 = tt
-- a0 = Bot, u /= Bot: FinMem u Bot = Empty
upVal G M A UCode        Bot a1 le ()
upVal G M A PropCode     Bot a1 le ()
upVal G M A (FunEl g)    Bot a1 le ()
upVal G M A (PiCode a f) Bot a1 le ()
upVal G M A (SigmaCode a f) Bot a1 le ()
upVal G M A (PairCode x y) Bot a1 le ()
-- a0 = UCode, a1 = UCode: identity (split u for exact-split)
upVal G M A Bot              UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upVal G M A UCode            UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upVal G M A PropCode         UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upVal G M A (FunEl g')       UCode UCode le ()
upVal G M A (PiCode a' f')   UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upVal G M A (SigmaCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upVal G M A (PairCode x y)   UCode UCode le ()
-- a0 = UCode, a1 /= UCode: absurd from LeCode
upVal G M A u UCode Bot          ()
upVal G M A u UCode PropCode     ()
upVal G M A u UCode (FunEl h)    ()
upVal G M A u UCode (PiCode b h) ()
upVal G M A u UCode (SigmaCode b h) ()
upVal G M A u UCode (PairCode x y) ()
-- a0 = PropCode
upVal G M A u PropCode Bot            ()
upVal G M A u PropCode UCode          ()
upVal G M A Bot              PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A UCode            PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A PropCode         PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A (FunEl g')       PropCode PropCode le ()
upVal G M A (PiCode a' f')   PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A (SigmaCode a' f') PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A (PairCode x y)   PropCode PropCode le ()
upVal G M A u PropCode (FunEl h)      ()
upVal G M A u PropCode (PiCode b1 f1) ()
upVal G M A u PropCode (SigmaCode b1 f1) ()
upVal G M A u PropCode (PairCode x y) ()
-- a0 = FunEl: FinMem u (FunEl g) empty for u /= Bot
upVal G M A Bot            (FunEl g) Bot            le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot            (FunEl g) UCode          le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot            (FunEl g) PropCode       le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot            (FunEl g) (FunEl h)      le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot            (FunEl g) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot            (FunEl g) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot            (FunEl g) (PairCode x y) le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A UCode          (FunEl g) a1             le ()
upVal G M A PropCode       (FunEl g) a1             le ()
upVal G M A (FunEl g')     (FunEl g) a1             le ()
upVal G M A (PiCode a' f') (FunEl g) a1             le ()
upVal G M A (SigmaCode a' f') (FunEl g) a1          le ()
upVal G M A (PairCode x y) (FunEl g) a1             le ()
-- a0 = PiCode, a1 /= PiCode: absurd from LeCode
upVal G M A u (PiCode b0 f0) Bot       ()
upVal G M A u (PiCode b0 f0) UCode     ()
upVal G M A u (PiCode b0 f0) PropCode  ()
upVal G M A u (PiCode b0 f0) (FunEl h) ()
upVal G M A u (PiCode b0 f0) (SigmaCode b1 f1) ()
upVal G M A u (PiCode b0 f0) (PairCode x y) ()
-- a0 = PiCode, a1 = PiCode: split on u
upVal G M A Bot            (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
upVal G M A PropCode       (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
  let vpi = snd src
      A0  = fst vpi
      B0  = fst (snd vpi)
      red = fst (snd (snd vpi))
      sat = fst (snd (snd (snd vpi)))
      pav = fst (snd (snd (snd (snd (snd vpi)))))
      pae = snd (snd (snd (snd (snd (snd vpi)))))
      cf0 = snd ca0
      cf1 = snd ca1
      pf0 = snd (snd mem0)
      pf1 = snd (snd mem1)
      b0U = fst pf0
      b1U = fst pf1
      allU0 = fst (snd pf0)
      allU1 = fst (snd pf1)
      cb0 = coh-from-aU b0 b0U
      cb1 = coh-from-aU b1 b1U
      Av   = fst vta1
      Bv   = fst (snd vta1)
      redv = fst (snd (snd vta1))
      uniq = Red-unique-Pi red redv
      inner-vta1 = snd (snd (snd (snd (snd vta1))))
      piEVv = fst (snd inner-vta1)
      piEV1 : PiEdgeVal G A0 B0 b1 f1
      piEV1 = Eq-transport (\ Y -> PiEdgeVal G A0 Y b1 f1) (Eq-sym (snd uniq))
                (Eq-transport (\ X -> PiEdgeVal G X Bv b1 f1) (Eq-sym (fst uniq)) piEVv)
      vpi' = mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma sat
               (mkSigma (fst mem1)
               (mkSigma
                 (upPiAppVal G M A0 B0 b0 f0 b1 f1 g cf0 cf1 sat cb0 cb1 b1U allU1 b0U allU0 le (fst mem0) piEV1 pav)
                 (upPiAppEq G M A0 B0 b0 f0 b1 f1 g cf0 cf1 sat cb0 cb1 b1U allU1 b0U allU0 le (fst mem0) piEV1 pae))))))
  in mkSigma vta1 vpi'
upVal G M A (PiCode a f)      (PiCode b0 f0) (PiCode b1 f1) le ()
upVal G M A (SigmaCode a f)   (PiCode b0 f0) (PiCode b1 f1) le ()
upVal G M A (PairCode x y)    (PiCode b0 f0) (PiCode b1 f1) le ()
-- a0 = SigmaCode: absurd from LeCode or Top
upVal G M A u (SigmaCode b0 f0) Bot       ()
upVal G M A u (SigmaCode b0 f0) UCode     ()
upVal G M A u (SigmaCode b0 f0) PropCode  ()
upVal G M A u (SigmaCode b0 f0) (FunEl h) ()
upVal G M A u (SigmaCode b0 f0) (PiCode b1 f1) ()
upVal G M A u (SigmaCode b0 f0) (PairCode x y) ()
upVal G M A Bot              (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A UCode            (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
upVal G M A PropCode         (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A (FunEl g)        (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
upVal G M A (PiCode a f)     (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
upVal G M A (SigmaCode a f)  (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
upVal G M A (PairCode x y)   (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
-- a0 = PairCode: absurd or Top
upVal G M A u (PairCode x0 y0) Bot       ()
upVal G M A u (PairCode x0 y0) UCode     ()
upVal G M A u (PairCode x0 y0) PropCode  ()
upVal G M A u (PairCode x0 y0) (FunEl h) ()
upVal G M A u (PairCode x0 y0) (PiCode b f) ()
upVal G M A u (PairCode x0 y0) (SigmaCode b f) ()
upVal G M A Bot              (PairCode x0 y0) (PairCode x1 y1) le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A UCode            (PairCode x0 y0) (PairCode x1 y1) le ()
upVal G M A PropCode         (PairCode x0 y0) (PairCode x1 y1) le ()
upVal G M A (FunEl g)        (PairCode x0 y0) (PairCode x1 y1) le ()
upVal G M A (PiCode a f)     (PairCode x0 y0) (PairCode x1 y1) le ()
upVal G M A (SigmaCode a f)  (PairCode x0 y0) (PairCode x1 y1) le ()
upVal G M A (PairCode u1 v1) (PairCode x0 y0) (PairCode x1 y1) le mem0 mem1 ca0 ca1 src vta1 = tt

------------------------------------------------------------------------
-- upEqVal
------------------------------------------------------------------------

-- a0 = Bot, u = Bot: split a1
upEqVal G M N A Bot Bot          Bot             le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot Bot          UCode           le mem0 mem1 ca0 ca1 src vta1 = mkSigma tt (mkSigma tt tt)
upEqVal G M N A Bot Bot          PropCode        le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot Bot          (FunEl h)       le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot Bot          (PiCode b1 f1)  le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot Bot          (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot Bot          (PairCode x y)  le mem0 mem1 ca0 ca1 src vta1 = tt
-- a0 = Bot, u /= Bot: FinMem u Bot = Empty
upEqVal G M N A UCode        Bot a1 le ()
upEqVal G M N A PropCode     Bot a1 le ()
upEqVal G M N A (FunEl g)    Bot a1 le ()
upEqVal G M N A (PiCode a f) Bot a1 le ()
upEqVal G M N A (SigmaCode a f) Bot a1 le ()
upEqVal G M N A (PairCode x y) Bot a1 le ()
-- a0 = UCode, a1 = UCode: identity
upEqVal G M N A Bot              UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upEqVal G M N A UCode            UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upEqVal G M N A PropCode         UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upEqVal G M N A (FunEl g')       UCode UCode le ()
upEqVal G M N A (PiCode a' f')   UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upEqVal G M N A (SigmaCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upEqVal G M N A (PairCode x y)   UCode UCode le ()
-- a0 = UCode, a1 /= UCode: absurd
upEqVal G M N A u UCode Bot          ()
upEqVal G M N A u UCode PropCode     ()
upEqVal G M N A u UCode (FunEl h)    ()
upEqVal G M N A u UCode (PiCode b h) ()
upEqVal G M N A u UCode (SigmaCode b h) ()
upEqVal G M N A u UCode (PairCode x y) ()
-- a0 = PropCode
upEqVal G M N A u PropCode Bot            ()
upEqVal G M N A u PropCode UCode          ()
upEqVal G M N A Bot              PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A UCode            PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A PropCode         PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A (FunEl g')       PropCode PropCode le ()
upEqVal G M N A (PiCode a' f')   PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A (SigmaCode a' f') PropCode PropCode le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A (PairCode x y)   PropCode PropCode le ()
upEqVal G M N A u PropCode (FunEl h)      ()
upEqVal G M N A u PropCode (PiCode b1 f1) ()
upEqVal G M N A u PropCode (SigmaCode b1 f1) ()
upEqVal G M N A u PropCode (PairCode x y) ()
-- a0 = FunEl
upEqVal G M N A Bot            (FunEl g) Bot            le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot            (FunEl g) UCode          le mem0 mem1 ca0 ca1 src vta1 = mkSigma tt (mkSigma tt tt)
upEqVal G M N A Bot            (FunEl g) PropCode       le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot            (FunEl g) (FunEl h)      le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot            (FunEl g) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot            (FunEl g) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot            (FunEl g) (PairCode x y) le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A UCode          (FunEl g) a1             le ()
upEqVal G M N A PropCode       (FunEl g) a1             le ()
upEqVal G M N A (FunEl g')     (FunEl g) a1             le ()
upEqVal G M N A (PiCode a' f') (FunEl g) a1             le ()
upEqVal G M N A (SigmaCode a' f') (FunEl g) a1          le ()
upEqVal G M N A (PairCode x y) (FunEl g) a1             le ()
-- a0 = PiCode, a1 /= PiCode: absurd
upEqVal G M N A u (PiCode b0 f0) Bot       ()
upEqVal G M N A u (PiCode b0 f0) UCode     ()
upEqVal G M N A u (PiCode b0 f0) PropCode  ()
upEqVal G M N A u (PiCode b0 f0) (FunEl h) ()
upEqVal G M N A u (PiCode b0 f0) (SigmaCode b1 f1) ()
upEqVal G M N A u (PiCode b0 f0) (PairCode x y) ()
-- a0 = PiCode, a1 = PiCode: split on u
upEqVal G M N A Bot            (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
upEqVal G M N A PropCode       (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
  let vty  = fst src
      vpiM = fst (snd src)
      vpiN = fst (snd (snd src))
      epi  = snd (snd (snd src))
      valM  = mkSigma vty vpiM
      valN  = mkSigma vty vpiN
      valM' = upVal G M A (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 valM vta1
      valN' = upVal G N A (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 valN vta1
      A0   = fst epi
      B0   = fst (snd epi)
      red  = fst (snd (snd epi))
      sat  = fst (snd (snd (snd epi)))
      paev = snd (snd (snd (snd (snd epi))))
      cf0 = snd ca0
      cf1 = snd ca1
      pf0 = snd (snd mem0)
      pf1 = snd (snd mem1)
      b0U = fst pf0
      b1U = fst pf1
      allU0 = fst (snd pf0)
      allU1 = fst (snd pf1)
      cb0 = coh-from-aU b0 b0U
      cb1 = coh-from-aU b1 b1U
      Av   = fst vta1
      Bv   = fst (snd vta1)
      redv = fst (snd (snd vta1))
      uniq = Red-unique-Pi red redv
      inner-vta1 = snd (snd (snd (snd (snd vta1))))
      piEVv = fst (snd inner-vta1)
      piEV1 : PiEdgeVal G A0 B0 b1 f1
      piEV1 = Eq-transport (\ Y -> PiEdgeVal G A0 Y b1 f1) (Eq-sym (snd uniq))
                (Eq-transport (\ X -> PiEdgeVal G X Bv b1 f1) (Eq-sym (fst uniq)) piEVv)
      epi' = mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma sat
               (mkSigma (fst mem1)
               (upPiAppEqVal G M N A0 B0 b0 f0 b1 f1 g cf0 cf1 sat cb0 cb1 b1U allU1 b0U allU0 le (fst mem0) piEV1 paev)))))
  in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
upEqVal G M N A (PiCode a f)      (PiCode b0 f0) (PiCode b1 f1) le ()
upEqVal G M N A (SigmaCode a f)   (PiCode b0 f0) (PiCode b1 f1) le ()
upEqVal G M N A (PairCode x y)    (PiCode b0 f0) (PiCode b1 f1) le ()
-- a0 = SigmaCode: all Top
upEqVal G M N A u (SigmaCode b0 f0) Bot       ()
upEqVal G M N A u (SigmaCode b0 f0) UCode     ()
upEqVal G M N A u (SigmaCode b0 f0) PropCode  ()
upEqVal G M N A u (SigmaCode b0 f0) (FunEl h) ()
upEqVal G M N A u (SigmaCode b0 f0) (PiCode b1 f1) ()
upEqVal G M N A u (SigmaCode b0 f0) (PairCode x y) ()
upEqVal G M N A Bot              (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A UCode            (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
upEqVal G M N A PropCode         (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A (FunEl g)        (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
upEqVal G M N A (PiCode a f)     (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
upEqVal G M N A (SigmaCode a f)  (SigmaCode b0 f0) (SigmaCode b1 f1) le ()
upEqVal G M N A (PairCode x y)   (SigmaCode b0 f0) (SigmaCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
-- a0 = PairCode
upEqVal G M N A u (PairCode x0 y0) Bot       ()
upEqVal G M N A u (PairCode x0 y0) UCode     ()
upEqVal G M N A u (PairCode x0 y0) PropCode  ()
upEqVal G M N A u (PairCode x0 y0) (FunEl h) ()
upEqVal G M N A u (PairCode x0 y0) (PiCode b f) ()
upEqVal G M N A u (PairCode x0 y0) (SigmaCode b f) ()
upEqVal G M N A Bot              (PairCode x0 y0) (PairCode x1 y1) le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A UCode            (PairCode x0 y0) (PairCode x1 y1) le ()
upEqVal G M N A PropCode         (PairCode x0 y0) (PairCode x1 y1) le ()
upEqVal G M N A (FunEl g)        (PairCode x0 y0) (PairCode x1 y1) le ()
upEqVal G M N A (PiCode a f)     (PairCode x0 y0) (PairCode x1 y1) le ()
upEqVal G M N A (SigmaCode a f)  (PairCode x0 y0) (PairCode x1 y1) le ()
upEqVal G M N A (PairCode u1 v1) (PairCode x0 y0) (PairCode x1 y1) le mem0 mem1 ca0 ca1 src vta1 = tt

------------------------------------------------------------------------
-- restrictVal
------------------------------------------------------------------------

restrictVal G M A u u' Bot              le mem fmu src = tt
restrictVal G M A u u' UCode            le mem fmu src =
  downValTy G M u' u le mem fmu src
restrictVal G M A u u' PropCode         le mem fmu src = tt
restrictVal G M A u u' (FunEl h)        le mem fmu src = tt
-- a = PiCode: split on u, then u'
restrictVal G M A Bot Bot            (PiCode b f) le mem fmu src = tt
restrictVal G M A Bot UCode          (PiCode b f) le ()
restrictVal G M A Bot PropCode       (PiCode b f) ()
restrictVal G M A Bot (FunEl g')     (PiCode b f) ()
restrictVal G M A Bot (PiCode a2 f2) (PiCode b f) le ()
restrictVal G M A Bot (SigmaCode a2 f2) (PiCode b f) le ()
restrictVal G M A Bot (PairCode x y) (PiCode b f) ()
restrictVal G M A UCode Bot            (PiCode b f) le mem fmu src = tt
restrictVal G M A UCode UCode          (PiCode b f) le mem fmu src = tt
restrictVal G M A UCode PropCode       (PiCode b f) le mem ()
restrictVal G M A UCode (FunEl g')     (PiCode b f) le mem ()
restrictVal G M A UCode (PiCode a2 f2) (PiCode b f) le ()
restrictVal G M A UCode (SigmaCode a2 f2) (PiCode b f) le ()
restrictVal G M A UCode (PairCode x y) (PiCode b f) le ()
restrictVal G M A PropCode u'             (PiCode b f) le mem ()
restrictVal G M A (FunEl g) Bot            (PiCode b f) le mem fmu src = tt
restrictVal G M A (FunEl g) UCode          (PiCode b f) le ()
restrictVal G M A (FunEl g) PropCode       (PiCode b f) le ()
restrictVal G M A (FunEl g) (FunEl g')     (PiCode b f) le mem fmu src =
  let aU = FinMem-a-in-U (FunEl g) (PiCode b f) fmu
  in mkSigma (fst src)
    (restrictVal-PiCode G M A g g' b f (snd (snd aU)) (coh-from-aU b (fst aU)) (fst (snd aU)) (fst aU) le
      (mkSigma (fst mem) (fst (snd mem))) (fst src) (snd src))
restrictVal G M A (FunEl g) (PiCode a2 f2) (PiCode b f) le ()
restrictVal G M A (FunEl g) (SigmaCode a2 f2) (PiCode b f) le ()
restrictVal G M A (FunEl g) (PairCode x y) (PiCode b f) le ()
restrictVal G M A (PiCode a1 f1) Bot            (PiCode b f) le mem fmu src = tt
restrictVal G M A (PiCode a1 f1) UCode          (PiCode b f) le ()
restrictVal G M A (PiCode a1 f1) PropCode       (PiCode b f) le ()
restrictVal G M A (PiCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
restrictVal G M A (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) le mem fmu src = tt
restrictVal G M A (PiCode a1 f1) (SigmaCode a2 f2) (PiCode b f) le ()
restrictVal G M A (PiCode a1 f1) (PairCode x y) (PiCode b f) le ()
restrictVal G M A (SigmaCode a1 f1) Bot            (PiCode b f) le mem ()
restrictVal G M A (SigmaCode a1 f1) UCode          (PiCode b f) le ()
restrictVal G M A (SigmaCode a1 f1) PropCode       (PiCode b f) le ()
restrictVal G M A (SigmaCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
restrictVal G M A (SigmaCode a1 f1) (PiCode a2 f2) (PiCode b f) le ()
restrictVal G M A (SigmaCode a1 f1) (SigmaCode a2 f2) (PiCode b f) le ()
restrictVal G M A (SigmaCode a1 f1) (PairCode x y) (PiCode b f) le ()
restrictVal G M A (PairCode x1 y1) Bot            (PiCode b f) le mem ()
restrictVal G M A (PairCode x1 y1) UCode          (PiCode b f) le ()
restrictVal G M A (PairCode x1 y1) PropCode       (PiCode b f) le ()
restrictVal G M A (PairCode x1 y1) (FunEl g')     (PiCode b f) le mem ()
restrictVal G M A (PairCode x1 y1) (PiCode a2 f2) (PiCode b f) le ()
restrictVal G M A (PairCode x1 y1) (SigmaCode a2 f2) (PiCode b f) le ()
restrictVal G M A (PairCode x1 y1) (PairCode x2 y2) (PiCode b f) le ()
-- a = SigmaCode: all Top
restrictVal G M A Bot Bot            (SigmaCode b f) le mem fmu src = tt
restrictVal G M A Bot UCode          (SigmaCode b f) le ()
restrictVal G M A Bot PropCode       (SigmaCode b f) ()
restrictVal G M A Bot (FunEl g')     (SigmaCode b f) ()
restrictVal G M A Bot (PiCode a2 f2) (SigmaCode b f) le ()
restrictVal G M A Bot (SigmaCode a2 f2) (SigmaCode b f) le ()
restrictVal G M A Bot (PairCode x y) (SigmaCode b f) le mem fmu src = tt
restrictVal G M A UCode u' (SigmaCode b f) le mem ()
restrictVal G M A PropCode u' (SigmaCode b f) le mem ()
restrictVal G M A (FunEl g) u' (SigmaCode b f) le mem ()
restrictVal G M A (PiCode a1 f1) u' (SigmaCode b f) le mem ()
restrictVal G M A (SigmaCode a1 f1) u' (SigmaCode b f) le mem ()
restrictVal G M A (PairCode x1 y1) Bot            (SigmaCode b f) le mem fmu src = tt
restrictVal G M A (PairCode x1 y1) UCode          (SigmaCode b f) le ()
restrictVal G M A (PairCode x1 y1) PropCode       (SigmaCode b f) le ()
restrictVal G M A (PairCode x1 y1) (FunEl g')     (SigmaCode b f) le ()
restrictVal G M A (PairCode x1 y1) (PiCode a2 f2) (SigmaCode b f) le ()
restrictVal G M A (PairCode x1 y1) (SigmaCode a2 f2) (SigmaCode b f) le ()
restrictVal G M A (PairCode x1 y1) (PairCode x2 y2) (SigmaCode b f) le mem fmu src = tt
-- a = PairCode: Val always Top
restrictVal G M A Bot u' (PairCode x y) le mem fmu src = tt
restrictVal G M A UCode u' (PairCode x y) le mem ()
restrictVal G M A PropCode u' (PairCode x y) le mem ()
restrictVal G M A (FunEl g) u' (PairCode x y) le mem ()
restrictVal G M A (PiCode a1 f1) u' (PairCode x y) le mem ()
restrictVal G M A (SigmaCode a1 f1) u' (PairCode x y) le mem ()
restrictVal G M A (PairCode x1 y1) Bot            (PairCode x y) le mem fmu src = tt
restrictVal G M A (PairCode x1 y1) UCode          (PairCode x y) le ()
restrictVal G M A (PairCode x1 y1) PropCode       (PairCode x y) le ()
restrictVal G M A (PairCode x1 y1) (FunEl g')     (PairCode x y) le ()
restrictVal G M A (PairCode x1 y1) (PiCode a2 f2) (PairCode x y) le ()
restrictVal G M A (PairCode x1 y1) (SigmaCode a2 f2) (PairCode x y) le ()
restrictVal G M A (PairCode x1 y1) (PairCode x2 y2) (PairCode x y) le mem fmu src = tt

------------------------------------------------------------------------
-- restrictEqVal
------------------------------------------------------------------------

restrictEqVal G M N A u u' Bot              le mem fmu src = tt
restrictEqVal G M N A u u' UCode            le mem fmu src =
  mkSigma (downValTy G M u' u le mem fmu (fst src))
    (mkSigma (downValTy G N u' u le mem fmu (fst (snd src)))
             (downEqValTy G M N u' u le mem fmu (snd (snd src))))
restrictEqVal G M N A u u' PropCode         le mem fmu src = tt
restrictEqVal G M N A u u' (FunEl h)        le mem fmu src = tt
-- a = PiCode: split on u, then u'
restrictEqVal G M N A Bot Bot            (PiCode b f) le mem fmu src = tt
restrictEqVal G M N A Bot UCode          (PiCode b f) le ()
restrictEqVal G M N A Bot PropCode       (PiCode b f) ()
restrictEqVal G M N A Bot (FunEl g')     (PiCode b f) ()
restrictEqVal G M N A Bot (PiCode a2 f2) (PiCode b f) le ()
restrictEqVal G M N A Bot (SigmaCode a2 f2) (PiCode b f) le ()
restrictEqVal G M N A Bot (PairCode x y) (PiCode b f) ()
restrictEqVal G M N A UCode Bot            (PiCode b f) le mem fmu src = tt
restrictEqVal G M N A UCode UCode          (PiCode b f) le mem fmu src = tt
restrictEqVal G M N A UCode PropCode       (PiCode b f) le mem ()
restrictEqVal G M N A UCode (FunEl g')     (PiCode b f) le mem ()
restrictEqVal G M N A UCode (PiCode a2 f2) (PiCode b f) le ()
restrictEqVal G M N A UCode (SigmaCode a2 f2) (PiCode b f) le ()
restrictEqVal G M N A UCode (PairCode x y) (PiCode b f) le ()
restrictEqVal G M N A PropCode u'           (PiCode b f) le mem ()
restrictEqVal G M N A (FunEl g) Bot            (PiCode b f) le mem fmu src = tt
restrictEqVal G M N A (FunEl g) UCode          (PiCode b f) le ()
restrictEqVal G M N A (FunEl g) PropCode       (PiCode b f) le ()
restrictEqVal G M N A (FunEl g) (FunEl g')     (PiCode b f) le mem fmu src =
  let aU = FinMem-a-in-U (FunEl g) (PiCode b f) fmu
      valM  = mkSigma (fst src) (fst (snd src))
      valN  = mkSigma (fst src) (fst (snd (snd src)))
      epi   = snd (snd (snd src))
      valM' = restrictVal G M A (FunEl g) (FunEl g') (PiCode b f) le mem fmu valM
      valN' = restrictVal G N A (FunEl g) (FunEl g') (PiCode b f) le mem fmu valN
      epi'  = restrictEqVal-PiCode G M N A g g' b f (snd (snd aU)) (coh-from-aU b (fst aU)) (fst (snd aU)) (fst aU) le
                (mkSigma (fst mem) (fst (snd mem))) (fst src) epi
  in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
restrictEqVal G M N A (FunEl g) (PiCode a2 f2) (PiCode b f) le ()
restrictEqVal G M N A (FunEl g) (SigmaCode a2 f2) (PiCode b f) le ()
restrictEqVal G M N A (FunEl g) (PairCode x y) (PiCode b f) le ()
restrictEqVal G M N A (PiCode a1 f1) Bot            (PiCode b f) le mem fmu src = tt
restrictEqVal G M N A (PiCode a1 f1) UCode          (PiCode b f) le ()
restrictEqVal G M N A (PiCode a1 f1) PropCode       (PiCode b f) le ()
restrictEqVal G M N A (PiCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
restrictEqVal G M N A (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) le mem fmu src = tt
restrictEqVal G M N A (PiCode a1 f1) (SigmaCode a2 f2) (PiCode b f) le ()
restrictEqVal G M N A (PiCode a1 f1) (PairCode x y) (PiCode b f) le ()
restrictEqVal G M N A (SigmaCode a1 f1) Bot            (PiCode b f) le mem ()
restrictEqVal G M N A (SigmaCode a1 f1) UCode          (PiCode b f) le ()
restrictEqVal G M N A (SigmaCode a1 f1) PropCode       (PiCode b f) le ()
restrictEqVal G M N A (SigmaCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
restrictEqVal G M N A (SigmaCode a1 f1) (PiCode a2 f2) (PiCode b f) le ()
restrictEqVal G M N A (SigmaCode a1 f1) (SigmaCode a2 f2) (PiCode b f) le ()
restrictEqVal G M N A (SigmaCode a1 f1) (PairCode x y) (PiCode b f) le ()
restrictEqVal G M N A (PairCode x1 y1) Bot            (PiCode b f) le mem ()
restrictEqVal G M N A (PairCode x1 y1) UCode          (PiCode b f) le ()
restrictEqVal G M N A (PairCode x1 y1) PropCode       (PiCode b f) le ()
restrictEqVal G M N A (PairCode x1 y1) (FunEl g')     (PiCode b f) le mem ()
restrictEqVal G M N A (PairCode x1 y1) (PiCode a2 f2) (PiCode b f) le ()
restrictEqVal G M N A (PairCode x1 y1) (SigmaCode a2 f2) (PiCode b f) le ()
restrictEqVal G M N A (PairCode x1 y1) (PairCode x2 y2) (PiCode b f) le ()
-- a = SigmaCode: all Top
restrictEqVal G M N A Bot Bot            (SigmaCode b f) le mem fmu src = tt
restrictEqVal G M N A Bot UCode          (SigmaCode b f) le ()
restrictEqVal G M N A Bot PropCode       (SigmaCode b f) ()
restrictEqVal G M N A Bot (FunEl g')     (SigmaCode b f) ()
restrictEqVal G M N A Bot (PiCode a2 f2) (SigmaCode b f) le ()
restrictEqVal G M N A Bot (SigmaCode a2 f2) (SigmaCode b f) le ()
restrictEqVal G M N A Bot (PairCode x y) (SigmaCode b f) le mem fmu src = tt
restrictEqVal G M N A UCode u' (SigmaCode b f) le mem ()
restrictEqVal G M N A PropCode u' (SigmaCode b f) le mem ()
restrictEqVal G M N A (FunEl g) u' (SigmaCode b f) le mem ()
restrictEqVal G M N A (PiCode a1 f1) u' (SigmaCode b f) le mem ()
restrictEqVal G M N A (SigmaCode a1 f1) u' (SigmaCode b f) le mem ()
restrictEqVal G M N A (PairCode x1 y1) Bot            (SigmaCode b f) le mem fmu src = tt
restrictEqVal G M N A (PairCode x1 y1) UCode          (SigmaCode b f) le ()
restrictEqVal G M N A (PairCode x1 y1) PropCode       (SigmaCode b f) le ()
restrictEqVal G M N A (PairCode x1 y1) (FunEl g')     (SigmaCode b f) le ()
restrictEqVal G M N A (PairCode x1 y1) (PiCode a2 f2) (SigmaCode b f) le ()
restrictEqVal G M N A (PairCode x1 y1) (SigmaCode a2 f2) (SigmaCode b f) le ()
restrictEqVal G M N A (PairCode x1 y1) (PairCode x2 y2) (SigmaCode b f) le mem fmu src = tt
-- a = PairCode: EqVal always Top
restrictEqVal G M N A Bot u' (PairCode x y) le mem fmu src = tt
restrictEqVal G M N A UCode u' (PairCode x y) le mem ()
restrictEqVal G M N A PropCode u' (PairCode x y) le mem ()
restrictEqVal G M N A (FunEl g) u' (PairCode x y) le mem ()
restrictEqVal G M N A (PiCode a1 f1) u' (PairCode x y) le mem ()
restrictEqVal G M N A (SigmaCode a1 f1) u' (PairCode x y) le mem ()
restrictEqVal G M N A (PairCode x1 y1) Bot            (PairCode x y) le mem fmu src = tt
restrictEqVal G M N A (PairCode x1 y1) UCode          (PairCode x y) le ()
restrictEqVal G M N A (PairCode x1 y1) PropCode       (PairCode x y) le ()
restrictEqVal G M N A (PairCode x1 y1) (FunEl g')     (PairCode x y) le ()
restrictEqVal G M N A (PairCode x1 y1) (PiCode a2 f2) (PairCode x y) le ()
restrictEqVal G M N A (PairCode x1 y1) (SigmaCode a2 f2) (PairCode x y) le ()
restrictEqVal G M N A (PairCode x1 y1) (PairCode x2 y2) (PairCode x y) le mem fmu src = tt
