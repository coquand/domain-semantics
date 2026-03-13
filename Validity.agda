{-# OPTIONS --without-K --exact-split --type-in-type #-}

------------------------------------------------------------------------
-- Validity.agda
--
-- Logical relation (validity) for dependent type theory with
-- U : U, adapting the adequacy proof of Coquand & Huber 2018.
--
-- Defines:
--   FinMem       -- finite element membership (u : a)
--   Val / EqVal  -- term/equality validity: J | u : a
--   ValTy/EqValTy -- type validity (= Val at UCode)
--   ValPi/EqValPi -- term/eq validity at Pi-code (selection-based)
--   ValTyPi/EqValTyPi -- type validity at Pi-code (selection-based)
--
-- SELECTION-BASED PI CLAUSES
--
--   Selection f u v is a compatible sub-multiset of the graph f,
--   with u = Sup of selected keys and v = Sup of selected values.
--   The sel-take constructor carries Comp on both keys and values,
--   ensuring coherence of u and v.
--
--   PiEdgeVal/PiEdgeEq/PiEdgeEqTy quantify over Selection f u v
--   and use v directly as the ValTy/EqValTy argument.
--
--   PiAppVal/PiAppEq/PiAppEqVal quantify over Selection g u v
--   and use EvalFun g u / EvalFun f u for the result.
--
-- INVARIANT PACKAGE
--
--   1. FinMem u a is the finite typing relation ("u : a").
--
--   2. FinMem u a implies coherence of u (proved as FinMem-Coherent).
--
--   3. Pi witnesses carry saturation and codomain-graph data:
--      - FinMem (FunEl g) (PiCode b f) carries CoherentFun g
--      - FinMem (PiCode a f) UCode carries CoherentFun f
--      - ValPi/EqValPi carry CoherentFun g + FinMemFun g b f
--      - ValTyPi/EqValTyPi carry CoherentFun f + FinMemAllU f b
--
--   4. EvalFun monotonicity (graph and argument) is used only
--      through the proved coherent versions from PaperSemantics.
--
--   5. Three mutual monotonicity families:
--        downVal    : a' <= a, u : a' => J|u:a -> J|u:a'
--        upVal      : a <= a', u : a, u : a' => J|u:a -> J|u:a'
--        restrictVal: u' <= u, u' : a => J|u:a -> J|u':a
--
--   6. Val at Bot realizer is Top for ALL type codes.
--      Non-FunEl realizers at PiCode are Top (unreachable when typed).
--
-- Background postulates (contextual reduction + selection infrastructure).
-- Termination: rk(EvalFun f v) <= rkFun f < rk(PiCode b f).
------------------------------------------------------------------------

module Validity where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
              List ; nil ; cons ;
              isPos)
open import RawSyntax using (Expr ; Var ; U ; Pi ; Lam ; App ; wkExpr ;
  subst1 ; Fin ; fzero ; fsuc)
open import TypingRules using (Ctx ; empty ; extend ; ConvTm ; conv-sym ;
  conv-trans)
open import Reduction using (Red ; Red-wk ; red-to-conv ;
  Red-refl ; Red-trans ; Red-beta-expand ; Red-Pi-inj ; Red-from-conv)
open import PaperSemantics using (applyEl ; EvalFun ; EvalFun-step ;
  leFinEl ; leFinEl-sound ;
  LeCode ; LeFunCode ; LeCode-Bot ; LeCode-Sup-lub ;
  LeCode-Sup-left ; LeCode-Sup-right ;
  LeCode-refl ; LeCode-trans ;
  Sup ; append ; Comp ; CompStepFun ; Coherent-Sup ;
  Coherent ; CoherentFun ; CoherentFunTail ; CoherentWith ; cft-from-cf ;
  Coherent-EvalFun ; EvalFun-mon ; EvalFun-mon-arg ;
  CoherentFun-append ;
  Comp-value-EvalFun ; comp-Bot-r ;
  coh-from-aU ; LeCode-Comp ;
  FinMem ; FinMemFun ; FinMemAllU ; EvalFun-in-UCode ;
  FinMem-coh-u ;
  Sup-Bot-right ;
  Comp-refl ; comp-Sup ; finMem-Sup-left ; finMem-Sup-right ;
  finMemUCode-Sup ; FinMem-a-in-U ;
  Comp-down ; Comp-sym ;
  coherentWith-to-compStepFun ;
  finMem-upward ; finMemFun-upward ;
  FinMemFun-append ; FinMem-Sup-element)
open import Selection public
open import RawSemantics using (absurd)

------------------------------------------------------------------------
-- FinMem -- finite element membership (u : a)
------------------------------------------------------------------------

-- Selection, Edge, EdgeIn, Or, TypedGraph, SatFinFun, lookup lemmas,
-- selectionBelow, Selection-le-EvalFun, FinMem-Selection-codomain,
-- EvalFun-le-graph are all imported from Selection.agda above.

-- EvalFun-FinMem: defined below, after FinMem-Coherent



------------------------------------------------------------------------
-- FinMem-Coherent -- typed elements are coherent
------------------------------------------------------------------------

FinMem-Coherent : (u a : FinEl) -> FinMem u a -> Coherent u
FinMem-Coherent = FinMem-coh-u

------------------------------------------------------------------------
-- EvalFun-FinMem: semantic typing for function application
--
-- If g is typed with domain b and codomain f, and v : b,
-- then EvalFun g v : EvalFun f v.
------------------------------------------------------------------------

EvalFun-FinMem-step : (n : Nat) (p : Edge) (ps : FinFun)
  (b : FinEl) (f : FinFun) (v : FinEl) ->
  Eq (leFinEl (fst p) v) n ->
  FinMemFun (cons p ps) b f -> CoherentFunTail (cons p ps) ->
  CoherentFunTail f -> FinMemAllU f b ->
  Coherent v -> FinMem v b ->
  FinMem (EvalFun-step n (snd p) ps v) (EvalFun f v)

EvalFun-FinMem : (g : FinFun) (b : FinEl) (f : FinFun) (v : FinEl) ->
  FinMemFun g b f -> CoherentFunTail g ->
  CoherentFunTail f -> FinMemAllU f b ->
  Coherent v -> FinMem v b ->
  FinMem (EvalFun g v) (EvalFun f v)
EvalFun-FinMem nil b f v fmg cg cf allU cv mv =
  EvalFun-in-UCode f v b cf cv allU
EvalFun-FinMem (cons p ps) b f v fmg cg cf allU cv mv =
  EvalFun-FinMem-step (leFinEl (fst p) v) p ps b f v refl fmg cg cf allU cv mv

EvalFun-FinMem-step zero p ps b f v eq fmg cg cf allU cv mv =
  EvalFun-FinMem ps b f v (snd fmg) (snd (snd cg)) cf allU cv mv
EvalFun-FinMem-step (suc n) p ps b f v eq fmg cg cf allU cv mv =
  let le-k = leFinEl-sound (fst p) v (Eq-transport isPos (Eq-sym eq) tt)
      cpv = fst (snd (fst cg))
      cw = fst (snd cg)
      ih = EvalFun-FinMem ps b f v (snd fmg) (snd (snd cg)) cf allU cv mv
      c-efp = Coherent-EvalFun f (fst p) cf (fst (fst cg))
      c-efv = Coherent-EvalFun f v cf cv
      le-ef = EvalFun-mon-arg f (fst p) v le-k cf (fst (fst cg)) cv
      efvU = EvalFun-in-UCode f v b cf cv allU
      mem-p = finMem-upward (snd p) (EvalFun f (fst p)) (EvalFun f v)
                le-ef c-efp c-efv (snd (fst fmg)) efvU
      comp-pv = Comp-value-EvalFun p ps v le-k cv cpv cw
                  (coherentWith-to-compStepFun p ps cw)
  in FinMem-Sup-element (snd p) (EvalFun ps v) (EvalFun f v)
       comp-pv c-efv mem-p ih

------------------------------------------------------------------------
-- Red -- contextual typed multi-step reduction (postulated)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Validity relations (mutual, by structural recursion on a)
--
-- Selection-based Pi clauses: PiEdgeVal/PiEdgeEq/PiEdgeEqTy quantify
-- over compatible selections of the codomain graph f.
-- PiAppVal/PiAppEq/PiAppEqVal quantify over compatible selections of
-- the function graph g.
--
-- Val/EqVal at Bot realizer is Top for all type codes.
-- Val/EqVal at non-FunEl realizer at PiCode is Top (unreachable
-- when well-typed).
------------------------------------------------------------------------

{-# TERMINATING #-}

-- Val G M A u a : term M has type A, with realizer u at code a, in context G
Val : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set

-- EqVal G M N A u a : M = N at type A, with realizer u at code a, in context G
EqVal : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
  FinEl -> FinEl -> Set

-- ValTy G M u : type validity (= Val G M U u UCode), recurse on u
ValTy : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set

-- EqValTy G M N u : type equality validity, recurse on u
EqValTy : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set

-- ValTyPi G M b f : type validity at u = PiCode b f
ValTyPi : {n : Nat} -> Ctx n -> Expr n -> FinEl -> FinFun -> Set

-- EqValTyPi G M N b f : type equality at u = PiCode b f
EqValTyPi : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
  FinEl -> FinFun -> Set

-- ValPi G M A g b f : term validity at u = FunEl g, a = PiCode b f
ValPi : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
  FinFun -> FinEl -> FinFun -> Set

-- EqValPi G M N A g b f : equality validity at u = FunEl g, a = PiCode b f
EqValPi : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
  FinFun -> FinEl -> FinFun -> Set

-- PiEdgeVal G A B b f : codomain validity -- selection-based on f, uses v
PiEdgeVal : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set

-- PiEdgeEq G A B b f : codomain equality respect -- selection-based on f, uses v
PiEdgeEq : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set

-- PiEdgeEqTy G A B B' b f : heterogeneous codomain type equality -- selection-based
PiEdgeEqTy : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> Expr (suc n) ->
  FinEl -> FinFun -> Set

-- PiAppVal G M A0 B0 b f g : function application validity -- selection-based on g
PiAppVal : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) ->
  FinEl -> FinFun -> FinFun -> Set

-- PiAppEq G M A0 B0 b f g : function congruence -- selection-based on g
PiAppEq : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) ->
  FinEl -> FinFun -> FinFun -> Set

-- PiAppEqVal G M N A0 B0 b f g : extensional equality -- selection-based on g
PiAppEqVal : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Expr (suc n) ->
  FinEl -> FinFun -> FinFun -> Set

------------------------------------------------------------------------
-- Definitions
------------------------------------------------------------------------

-- Val: case split on a, with u-split at PiCode
Val G M A u Bot          = Top
Val G M A u UCode        = ValTy G M u
Val G M A u (FunEl h)    = Top
Val G M A Bot            (PiCode b f) = Top
Val G M A UCode          (PiCode b f) = Top
Val G M A (FunEl g)      (PiCode b f) = Pair (ValTy G A (PiCode b f)) (ValPi G M A g b f)
Val G M A (PiCode a' f') (PiCode b f) = Top

-- EqVal: case split on a, with u-split at PiCode
-- NOW BUNDLES Val G M A u a and Val G N A u a
EqVal G M N A u Bot          = Top
EqVal G M N A u UCode        = Pair (ValTy G M u) (Pair (ValTy G N u) (EqValTy G M N u))
EqVal G M N A u (FunEl h)    = Top
EqVal G M N A Bot            (PiCode b f) = Top
EqVal G M N A UCode          (PiCode b f) = Top
EqVal G M N A (FunEl g)      (PiCode b f) =
  Pair (ValTy G A (PiCode b f))
       (Pair (ValPi G M A g b f)
             (Pair (ValPi G N A g b f)
                   (EqValPi G M N A g b f)))
EqVal G M N A (PiCode a' f') (PiCode b f) = Top

-- ValTy: case split on u (type validity = Val at UCode)
ValTy G M Bot          = Top
ValTy G M UCode        = Top
ValTy G M (FunEl g)    = Top
ValTy G M (PiCode b f) = ValTyPi G M b f

-- EqValTy: case split on u
EqValTy G M N Bot          = Top
EqValTy G M N UCode        = Top
EqValTy G M N (FunEl g)    = Top
EqValTy G M N (PiCode b f) =
  Pair (ValTy G M (PiCode b f))
       (Pair (ValTy G N (PiCode b f))
             (EqValTyPi G M N b f))

EqValTy-fst : {n : Nat} (G : Ctx n) (M N : Expr n) (u : FinEl) ->
  EqValTy G M N u -> ValTy G M u
EqValTy-fst G M N Bot          _ = tt
EqValTy-fst G M N UCode        _ = tt
EqValTy-fst G M N (FunEl g)    _ = tt
EqValTy-fst G M N (PiCode b f) e = fst e

EqValTy-snd : {n : Nat} (G : Ctx n) (M N : Expr n) (u : FinEl) ->
  EqValTy G M N u -> ValTy G N u
EqValTy-snd G M N Bot          _ = tt
EqValTy-snd G M N UCode        _ = tt
EqValTy-snd G M N (FunEl g)    _ = tt
EqValTy-snd G M N (PiCode b f) e = fst (snd e)

-- PiEdgeVal: codomain validity -- selection-based on f, uses v directly
PiEdgeVal {n} G A B b f =
  (u v : FinEl) -> Selection f u v ->
  (N : Expr n) -> Val G N A u b ->
  ValTy G (subst1 B N) v

-- PiEdgeEq: codomain equality -- selection-based on f, uses v directly
PiEdgeEq {n} G A B b f =
  (u v : FinEl) -> Selection f u v ->
  (N1 N2 : Expr n) -> EqVal G N1 N2 A u b ->
  EqValTy G (subst1 B N1) (subst1 B N2) v

-- PiEdgeEqTy: heterogeneous codomain type equality -- selection-based
PiEdgeEqTy {n} G A B B' b f =
  (u v : FinEl) -> Selection f u v ->
  (P : Expr n) -> Val G P A u b ->
  EqValTy G (subst1 B P) (subst1 B' P) v

-- PiAppVal: function application validity -- selection-based on g
-- Realizer is v (selection value aggregate), code is EvalFun f u.
PiAppVal {n} G M A0 B0 b f g =
  (u v : FinEl) -> Selection g u v ->
  (N : Expr n) -> Val G N A0 u b ->
  Val G (App M N) (subst1 B0 N) v (EvalFun f u)

-- PiAppEq: function congruence -- selection-based on g
PiAppEq {n} G M A0 B0 b f g =
  (u v : FinEl) -> Selection g u v ->
  (N1 N2 : Expr n) -> EqVal G N1 N2 A0 u b ->
  EqVal G (App M N1) (App M N2) (subst1 B0 N1)
    v (EvalFun f u)

-- PiAppEqVal: extensional equality -- selection-based on g
PiAppEqVal {n} G M N A0 B0 b f g =
  (u v : FinEl) -> Selection g u v ->
  (P : Expr n) -> Val G P A0 u b ->
  EqVal G (App M P) (App N P) (subst1 B0 P)
    v (EvalFun f u)

-- ValTyPi: M is a type with Pi-structure at (PiCode b f)
ValTyPi {n} G M b f =
  Sigma (Expr n) \ A ->
  Sigma (Expr (suc n)) \ B ->
  Sigma (Red G M (Pi A B) U) \ _ ->
  Sigma (CoherentFun f) \ _ ->
  Sigma (FinMemAllU f b) \ _ ->
  Pair (ValTy G A b)
       (Pair (PiEdgeVal G A B b f)
             (PiEdgeEq G A B b f))

-- EqValTyPi: core equality data at PiCode b f (without bundled ValTy's)
EqValTyPi {n} G M N b f =
  Sigma (Expr n) \ A ->
  Sigma (Expr (suc n)) \ B ->
  Sigma (Expr n) \ A' ->
  Sigma (Expr (suc n)) \ B' ->
  Sigma (Red G M (Pi A B) U) \ _ ->
  Sigma (Red G N (Pi A' B') U) \ _ ->
  Sigma (CoherentFun f) \ _ ->
  Sigma (FinMemAllU f b) \ _ ->
  Pair (EqValTy G A A' b)
       (PiEdgeEqTy G A B B' b f)

-- ValPi: term M has type A at (FunEl g, PiCode b f) -- selection-based
ValPi {n} G M A g b f =
  Sigma (Expr n) \ A0 ->
  Sigma (Expr (suc n)) \ B0 ->
  Sigma (Red G A (Pi A0 B0) U) \ _ ->
  Sigma (CoherentFun g) \ _ ->
  Sigma (FinMemFun g b f) \ _ ->
  Pair (PiAppVal G M A0 B0 b f g)
       (PiAppEq G M A0 B0 b f g)

-- EqValPi: equality M = N at type A at (FunEl g, PiCode b f) -- selection-based
EqValPi {n} G M N A g b f =
  Sigma (Expr n) \ A0 ->
  Sigma (Expr (suc n)) \ B0 ->
  Sigma (Red G A (Pi A0 B0) U) \ _ ->
  Sigma (CoherentFun g) \ _ ->
  Sigma (FinMemFun g b f) \ _ ->
  PiAppEqVal G M N A0 B0 b f g

------------------------------------------------------------------------
-- Red/Val transport postulates (placed after Val/EqVal definitions)
------------------------------------------------------------------------

-- Extract Val for first/second term from EqVal (now provable by bundling)
Val-from-EqVal-first : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u b : FinEl) -> EqVal G M N A u b -> Val G M A u b
Val-from-EqVal-first u Bot ev = tt
Val-from-EqVal-first u UCode ev = fst ev
Val-from-EqVal-first u (FunEl h) ev = tt
Val-from-EqVal-first Bot (PiCode b f) ev = tt
Val-from-EqVal-first UCode (PiCode b f) ev = tt
Val-from-EqVal-first (FunEl g) (PiCode b f) ev =
  mkSigma (fst ev) (fst (snd ev))
Val-from-EqVal-first (PiCode a' f') (PiCode b f) ev = tt

Val-from-EqVal-second : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u b : FinEl) -> EqVal G M N A u b -> Val G N A u b
Val-from-EqVal-second u Bot ev = tt
Val-from-EqVal-second u UCode ev = fst (snd ev)
Val-from-EqVal-second u (FunEl h) ev = tt
Val-from-EqVal-second Bot (PiCode b f) ev = tt
Val-from-EqVal-second UCode (PiCode b f) ev = tt
Val-from-EqVal-second (FunEl g) (PiCode b f) ev =
  mkSigma (fst ev) (fst (snd (snd ev)))
Val-from-EqVal-second (PiCode a' f') (PiCode b f) ev = tt

------------------------------------------------------------------------
-- Val-conv-type / EqVal-conv-type -- DERIVED from Red infrastructure
--
-- At PiCode/FunEl (the only nontrivial case), the type A appears
-- only in Red G A (Pi A0 B0) U.  We replace this Red using
-- Red-from-conv (conv-sym conv) and Red-trans.
------------------------------------------------------------------------

Val-conv-type : {n : Nat} {G : Ctx n} {M A B : Expr n}
  (u a : FinEl) ->
  ConvTm G A B U -> Val G M A u a -> Val G M B u a
-- a = Bot: Val = Top
Val-conv-type u Bot conv val = tt
-- a = UCode: ValTy doesn't mention A
Val-conv-type u UCode conv val = val
-- a = FunEl: Val = Top
Val-conv-type u (FunEl h) conv val = tt
-- a = PiCode, u = Bot: Top
Val-conv-type Bot (PiCode b f) conv val = tt
-- a = PiCode, u = UCode: Top
Val-conv-type UCode (PiCode b f) conv val = tt
-- a = PiCode, u = FunEl g: Pair ValTy ValPi, replace Red in both
Val-conv-type {G = G} {A = A} {B = B} (FunEl g) (PiCode b f) conv val =
  let vty = fst val
      vpi = snd val
      -- Transport ValTy: A -> B in Red
      A0v  = fst vty
      B0v  = fst (snd vty)
      redv = fst (snd (snd vty))
      restv = snd (snd (snd vty))
      redv' = Red-trans (Red-from-conv (conv-sym conv)) redv
      vty' = mkSigma A0v (mkSigma B0v (mkSigma redv' restv))
      -- Transport ValPi: A -> B in Red
      A0  = fst vpi
      B0  = fst (snd vpi)
      red = fst (snd (snd vpi))
      cg  = fst (snd (snd (snd vpi)))
      fmg = fst (snd (snd (snd (snd vpi))))
      rest = snd (snd (snd (snd (snd vpi))))
      red' = Red-trans (Red-from-conv (conv-sym conv)) red
      vpi' = mkSigma A0 (mkSigma B0 (mkSigma red' (mkSigma cg (mkSigma fmg rest))))
  in mkSigma vty' vpi'
-- a = PiCode, u = PiCode: Top
Val-conv-type (PiCode a' f') (PiCode b f) conv val = tt

EqVal-conv-type : {n : Nat} {G : Ctx n} {M N A B : Expr n}
  (u a : FinEl) ->
  ConvTm G A B U -> EqVal G M N A u a -> EqVal G M N B u a
EqVal-conv-type u Bot conv eqv = tt
EqVal-conv-type u UCode conv eqv = eqv
EqVal-conv-type u (FunEl h) conv eqv = tt
EqVal-conv-type Bot (PiCode b f) conv eqv = tt
EqVal-conv-type UCode (PiCode b f) conv eqv = tt
EqVal-conv-type (FunEl g) (PiCode b f) conv eqv =
  let valM = mkSigma (fst eqv) (fst (snd eqv))
      valN = mkSigma (fst eqv) (fst (snd (snd eqv)))
      epi  = snd (snd (snd eqv))
      -- Transport Val M and Val N via Val-conv-type
      valM' = Val-conv-type (FunEl g) (PiCode b f) conv valM
      valN' = Val-conv-type (FunEl g) (PiCode b f) conv valN
      -- Transport EqValPi: A -> B in Red
      A0   = fst epi
      B0   = fst (snd epi)
      red  = fst (snd (snd epi))
      cg   = fst (snd (snd (snd epi)))
      fmg  = fst (snd (snd (snd (snd epi))))
      rest = snd (snd (snd (snd (snd epi))))
      red' = Red-trans (Red-from-conv (conv-sym conv)) red
      epi' = mkSigma A0 (mkSigma B0 (mkSigma red' (mkSigma cg (mkSigma fmg rest))))
  in mkSigma (fst valM') (mkSigma (snd valM') (mkSigma (snd valN') epi'))
EqVal-conv-type (PiCode a' f') (PiCode b f) conv eqv = tt

------------------------------------------------------------------------
-- Val-Bot -- Val at Bot realizer is Top for all type codes
------------------------------------------------------------------------

Val-Bot : {n : Nat} (G : Ctx n) (M A : Expr n) (a : FinEl) -> Val G M A Bot a
Val-Bot G M A Bot          = tt
Val-Bot G M A UCode        = tt
Val-Bot G M A (FunEl g)    = tt
Val-Bot G M A (PiCode b f) = tt

EqVal-Bot : {n : Nat} (G : Ctx n) (M N A : Expr n) (a : FinEl) -> EqVal G M N A Bot a
EqVal-Bot G M N A Bot          = tt
EqVal-Bot G M N A UCode        = mkSigma tt (mkSigma tt tt)
EqVal-Bot G M N A (FunEl g)    = tt
EqVal-Bot G M N A (PiCode b f) = tt

------------------------------------------------------------------------
-- ValTy-from-Bot / EqValTy-from-Bot
------------------------------------------------------------------------

ValTy-from-Bot : {n : Nat} (G : Ctx n) (M : Expr n) (w : FinEl) ->
  LeCode w Bot -> ValTy G M w
ValTy-from-Bot G M Bot          le = tt
ValTy-from-Bot G M UCode        ()
ValTy-from-Bot G M (FunEl g)    le = tt
ValTy-from-Bot G M (PiCode b f) ()

EqValTy-from-Bot : {n : Nat} (G : Ctx n) (M N : Expr n) (w : FinEl) ->
  LeCode w Bot -> EqValTy G M N w
EqValTy-from-Bot G M N Bot          le = tt
EqValTy-from-Bot G M N UCode        ()
EqValTy-from-Bot G M N (FunEl g)    le = tt
EqValTy-from-Bot G M N (PiCode b f) ()

------------------------------------------------------------------------
-- Red-unique-Pi: two Reds from the same term to Pi types are equal
------------------------------------------------------------------------

Red-unique-Pi : {n : Nat} {G : Ctx n} {A B B' : Expr n}
  {F : Expr (suc n)} {F' : Expr (suc n)} ->
  Red G A (Pi B F) U -> Red G A (Pi B' F') U ->
  Pair (Eq B B') (Eq F F')
Red-unique-Pi r1 r2 =
  let r = Red-trans (Red-from-conv (conv-sym (red-to-conv r1))) r2
  in Red-Pi-inj r

-- Derive FinMem b UCode from CoherentFun f and FinMemAllU f b
bU-from-cf-fmU : (f : FinFun) (b : FinEl) -> CoherentFun f -> FinMemAllU f b -> FinMem b UCode
bU-from-cf-fmU nil         b ()
bU-from-cf-fmU (cons p ps) b cf fmU = FinMem-a-in-U (fst p) b (fst (fst fmU))

------------------------------------------------------------------------
-- Part 2: Monotonicity -- downward/upward transport
------------------------------------------------------------------------

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
-- Selection-based graph transport helpers (downPiAppVal etc.)
--
-- With v-as-realizer PiAppVal, the realizer v (selection value) is
-- unchanged when transporting domain/codomain.  Only the code
-- (EvalFun f u) changes.
------------------------------------------------------------------------

downPiAppVal : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFun f0 -> CoherentFun f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  ValTy G A0 b1 ->
  PiAppVal G M A0 B0 b1 f1 g -> PiAppVal G M A0 B0 b0 f0 g
downPiAppVal G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U b0U allU0 allU1 le fmg0 vtb1 src
  u v sel N val-b0 =
  let cu = Coherent-Selection sel cg
      fmu0 = FinMem-Selection b0 f0 sel fmg0 cg cb0 b0U
      fmu1 = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
      val-b1 = upVal G N A0 u b0 b1 (fst le) fmu0 fmu1 cb0 cb1 val-b0 vtb1
      body = src u v sel N val-b1
      le-f = EvalFun-mon f0 f1 u (cft-from-cf f0 cf0) (cft-from-cf f1 cf1) cu (snd le)
      c-ef0 = Coherent-EvalFun f0 u (cft-from-cf f0 cf0) cu
      ef1U = EvalFun-in-UCode f1 u b1 (cft-from-cf f1 cf1) cu allU1
      fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 cg cf0 allU0
  in downVal G (App M N) (subst1 B0 N) v
       (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body


downPiAppEq : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFun f0 -> CoherentFun f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  ValTy G A0 b1 ->
  PiAppEq G M A0 B0 b1 f1 g -> PiAppEq G M A0 B0 b0 f0 g
downPiAppEq G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U b0U allU0 allU1 le fmg0 vtb1 src
  u v sel N1 N2 eqv-b0 =
  let cu = Coherent-Selection sel cg
      fmu0 = FinMem-Selection b0 f0 sel fmg0 cg cb0 b0U
      fmu1 = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
      eqv-b1 = upEqVal G N1 N2 A0 u b0 b1 (fst le) fmu0 fmu1 cb0 cb1 eqv-b0 vtb1
      body = src u v sel N1 N2 eqv-b1
      le-f = EvalFun-mon f0 f1 u (cft-from-cf f0 cf0) (cft-from-cf f1 cf1) cu (snd le)
      c-ef0 = Coherent-EvalFun f0 u (cft-from-cf f0 cf0) cu
      ef1U = EvalFun-in-UCode f1 u b1 (cft-from-cf f1 cf1) cu allU1
      fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 cg cf0 allU0
  in downEqVal G (App M N1) (App M N2) (subst1 B0 N1) v
       (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body

downPiAppEqVal : {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFun f0 -> CoherentFun f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  FinMemAllU f0 b0 -> FinMemAllU f1 b1 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  ValTy G A0 b1 ->
  PiAppEqVal G M N A0 B0 b1 f1 g -> PiAppEqVal G M N A0 B0 b0 f0 g
downPiAppEqVal G M N A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U b0U allU0 allU1 le fmg0 vtb1 src
  u v sel P val-b0 =
  let cu = Coherent-Selection sel cg
      fmu0 = FinMem-Selection b0 f0 sel fmg0 cg cb0 b0U
      fmu1 = finMem-upward u b0 b1 (fst le) cb0 cb1 fmu0 b1U
      val-b1 = upVal G P A0 u b0 b1 (fst le) fmu0 fmu1 cb0 cb1 val-b0 vtb1
      body = src u v sel P val-b1
      le-f = EvalFun-mon f0 f1 u (cft-from-cf f0 cf0) (cft-from-cf f1 cf1) cu (snd le)
      c-ef0 = Coherent-EvalFun f0 u (cft-from-cf f0 cf0) cu
      ef1U = EvalFun-in-UCode f1 u b1 (cft-from-cf f1 cf1) cu allU1
      fmem-v = FinMem-Selection-codomain b0 f0 sel fmg0 cg cf0 allU0
  in downEqVal G (App M P) (App N P) (subst1 B0 P) v
       (EvalFun f0 u) (EvalFun f1 u) le-f fmem-v c-ef0 ef1U body

upPiAppVal : {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) (g : FinFun) ->
  CoherentFun f0 -> CoherentFun f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
  FinMem b0 UCode -> FinMemAllU f0 b0 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  PiEdgeVal G A0 B0 b1 f1 ->
  PiAppVal G M A0 B0 b0 f0 g -> PiAppVal G M A0 B0 b1 f1 g
upPiAppVal G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 src
  u v sel N val-b1 =
  let cu = Coherent-Selection sel cg
      cv = Coherent-Selection-val sel cg
      fmu0 = FinMem-Selection b0 f0 sel fmg0 cg cb0 b0U
      val-b0 = downVal G N A0 u b0 b1 (fst le) fmu0 cb0 b1U val-b1
      body = src u v sel N val-b0
      le-f = EvalFun-mon f0 f1 u (cft-from-cf f0 cf0) (cft-from-cf f1 cf1) cu (snd le)
      c-ef0 = Coherent-EvalFun f0 u (cft-from-cf f0 cf0) cu
      c-ef1 = Coherent-EvalFun f1 u (cft-from-cf f1 cf1) cu
      fmem-v-f0 = FinMem-Selection-codomain b0 f0 sel fmg0 cg cf0 allU0
      ef1U = EvalFun-in-UCode f1 u b1 (cft-from-cf f1 cf1) cu allU1
      fmem-v-f1 = finMem-upward v (EvalFun f0 u) (EvalFun f1 u)
                    le-f c-ef0 c-ef1 fmem-v-f0 ef1U
      -- Derive ValTy G (subst1 B0 N) (EvalFun f1 u) from PiEdgeVal
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
  CoherentFun f0 -> CoherentFun f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
  FinMem b0 UCode -> FinMemAllU f0 b0 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  PiEdgeVal G A0 B0 b1 f1 ->
  PiAppEq G M A0 B0 b0 f0 g -> PiAppEq G M A0 B0 b1 f1 g
upPiAppEq G M A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 src
  u v sel N1 N2 eqv-b1 =
  let cu = Coherent-Selection sel cg
      cv = Coherent-Selection-val sel cg
      fmu0 = FinMem-Selection b0 f0 sel fmg0 cg cb0 b0U
      eqv-b0 = downEqVal G N1 N2 A0 u b0 b1 (fst le) fmu0 cb0 b1U eqv-b1
      body = src u v sel N1 N2 eqv-b0
      le-f = EvalFun-mon f0 f1 u (cft-from-cf f0 cf0) (cft-from-cf f1 cf1) cu (snd le)
      c-ef0 = Coherent-EvalFun f0 u (cft-from-cf f0 cf0) cu
      c-ef1 = Coherent-EvalFun f1 u (cft-from-cf f1 cf1) cu
      fmem-v-f0 = FinMem-Selection-codomain b0 f0 sel fmg0 cg cf0 allU0
      ef1U = EvalFun-in-UCode f1 u b1 (cft-from-cf f1 cf1) cu allU1
      fmem-v-f1 = finMem-upward v (EvalFun f0 u) (EvalFun f1 u)
                    le-f c-ef0 c-ef1 fmem-v-f0 ef1U
      -- Derive ValTy G (subst1 B0 N1) (EvalFun f1 u) from PiEdgeVal
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
  CoherentFun f0 -> CoherentFun f1 -> CoherentFun g ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMemAllU f1 b1 ->
  FinMem b0 UCode -> FinMemAllU f0 b0 ->
  Pair (LeCode b0 b1) (LeFunCode f0 f1) ->
  FinMemFun g b0 f0 ->
  PiEdgeVal G A0 B0 b1 f1 ->
  PiAppEqVal G M N A0 B0 b0 f0 g -> PiAppEqVal G M N A0 B0 b1 f1 g
upPiAppEqVal G M N A0 B0 b0 f0 b1 f1 g cf0 cf1 cg cb0 cb1 b1U allU1 b0U allU0 le fmg0 piEV1 src
  u v sel P val-b1 =
  let cu = Coherent-Selection sel cg
      cv = Coherent-Selection-val sel cg
      fmu0 = FinMem-Selection b0 f0 sel fmg0 cg cb0 b0U
      val-b0 = downVal G P A0 u b0 b1 (fst le) fmu0 cb0 b1U val-b1
      body = src u v sel P val-b0
      le-f = EvalFun-mon f0 f1 u (cft-from-cf f0 cf0) (cft-from-cf f1 cf1) cu (snd le)
      c-ef0 = Coherent-EvalFun f0 u (cft-from-cf f0 cf0) cu
      c-ef1 = Coherent-EvalFun f1 u (cft-from-cf f1 cf1) cu
      fmem-v-f0 = FinMem-Selection-codomain b0 f0 sel fmg0 cg cf0 allU0
      ef1U = EvalFun-in-UCode f1 u b1 (cft-from-cf f1 cf1) cu allU1
      fmem-v-f1 = finMem-upward v (EvalFun f0 u) (EvalFun f1 u)
                    le-f c-ef0 c-ef1 fmem-v-f0 ef1U
      -- Derive ValTy G (subst1 B0 P) (EvalFun f1 u) from PiEdgeVal
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
-- Restriction helpers (selection-based, proved)
--
-- Strategy: given PiAppVal at g, produce PiAppVal at g' (g' <= g).
-- 1. selectionBelow g u' -> (u_g, v_g, sel_g) with u_g <= u', EvalFun g u' = v_g
-- 2. restrictVal argument from u' to u_g
-- 3. Apply src at (u_g, v_g, sel_g) to get Val at (v_g, EvalFun f u_g)
-- 4. upVal in code from EvalFun f u_g to EvalFun f u' (monotonicity)
-- 5. restrictVal in realizer from v_g to v' (Selection-le-EvalFun)
------------------------------------------------------------------------

restrictPiAppVal-sel :
    {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b : FinEl) (f g g' : FinFun) ->
    CoherentFun f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
    FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
    PiEdgeVal G A0 B0 b f ->
    PiAppVal G M A0 B0 b f g -> PiAppVal G M A0 B0 b f g'
restrictPiAppVal-sel G M A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV src
    u' v' sel' N val-N =
  let cu' = Coherent-Selection sel' cg'
      cv' = Coherent-Selection-val sel' cg'
      fmu'-b = FinMem-Selection b f sel' fmg' cg' cb bU
      sb  = selectionBelow g u' cg cu'
      u_g  = fst sb
      v_g  = fst (snd sb)
      sel_g = fst (snd (snd sb))
      le-ug = fst (snd (snd (snd sb)))
      eq-vg = snd (snd (snd (snd sb)))
      cu_g = Coherent-Selection sel_g cg
      cv_g = Coherent-Selection-val sel_g cg
      fmu_g = FinMem-Selection b f sel_g fmg cg cb bU
      val-ug = restrictVal G N A0 u' u_g b le-ug fmu_g fmu'-b val-N
      body = src u_g v_g sel_g N val-ug
      le-ef = EvalFun-mon-arg f u_g u' le-ug (cft-from-cf f cf) cu_g cu'
      c-efug = Coherent-EvalFun f u_g (cft-from-cf f cf) cu_g
      c-efu' = Coherent-EvalFun f u' (cft-from-cf f cf) cu'
      fmem-vg-efug = FinMem-Selection-codomain b f sel_g fmg cg cf allU
      efuU' = EvalFun-in-UCode f u' b (cft-from-cf f cf) cu' allU
      fmem-vg-efu' = finMem-upward v_g (EvalFun f u_g) (EvalFun f u')
                        le-ef c-efug c-efu' fmem-vg-efug efuU'
      -- Derive ValTy G (subst1 B0 N) (EvalFun f u') from PiEdgeVal
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
      le-v'-efgu' = Selection-le-EvalFun g sel' le cg' cg cu'
      le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
      fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' cg' cf allU
  in restrictVal G (App M N) (subst1 B0 N) v_g v' (EvalFun f u')
       le-v'-vg fmem-v'-efu' fmem-vg-efu' body2

restrictPiAppEq-sel :
    {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b : FinEl) (f g g' : FinFun) ->
    CoherentFun f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
    FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
    PiEdgeVal G A0 B0 b f ->
    PiAppEq G M A0 B0 b f g -> PiAppEq G M A0 B0 b f g'
restrictPiAppEq-sel G M A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV src
    u' v' sel' N1 N2 eqv-N =
  let cu' = Coherent-Selection sel' cg'
      cv' = Coherent-Selection-val sel' cg'
      fmu'-b = FinMem-Selection b f sel' fmg' cg' cb bU
      sb  = selectionBelow g u' cg cu'
      u_g  = fst sb
      v_g  = fst (snd sb)
      sel_g = fst (snd (snd sb))
      le-ug = fst (snd (snd (snd sb)))
      eq-vg = snd (snd (snd (snd sb)))
      cu_g = Coherent-Selection sel_g cg
      cv_g = Coherent-Selection-val sel_g cg
      fmu_g = FinMem-Selection b f sel_g fmg cg cb bU
      eqv-ug = restrictEqVal G N1 N2 A0 u' u_g b le-ug fmu_g fmu'-b eqv-N
      body = src u_g v_g sel_g N1 N2 eqv-ug
      le-ef = EvalFun-mon-arg f u_g u' le-ug (cft-from-cf f cf) cu_g cu'
      c-efug = Coherent-EvalFun f u_g (cft-from-cf f cf) cu_g
      c-efu' = Coherent-EvalFun f u' (cft-from-cf f cf) cu'
      fmem-vg-efug = FinMem-Selection-codomain b f sel_g fmg cg cf allU
      efuU' = EvalFun-in-UCode f u' b (cft-from-cf f cf) cu' allU
      fmem-vg-efu' = finMem-upward v_g (EvalFun f u_g) (EvalFun f u')
                        le-ef c-efug c-efu' fmem-vg-efug efuU'
      -- Derive ValTy G (subst1 B0 N1) (EvalFun f u') from PiEdgeVal
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
      le-v'-efgu' = Selection-le-EvalFun g sel' le cg' cg cu'
      le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
      fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' cg' cf allU
  in restrictEqVal G (App M N1) (App M N2) (subst1 B0 N1) v_g v' (EvalFun f u')
       le-v'-vg fmem-v'-efu' fmem-vg-efu' body2

restrictPiAppEqVal-sel :
    {n : Nat} (G : Ctx n) (M N A0 : Expr n) (B0 : Expr (suc n))
    (b : FinEl) (f g g' : FinFun) ->
    CoherentFun f -> CoherentFun g -> CoherentFun g' -> Coherent b ->
    FinMemAllU f b -> FinMem b UCode ->
    LeFunCode g' g -> FinMemFun g' b f -> FinMemFun g b f ->
    PiEdgeVal G A0 B0 b f ->
    PiAppEqVal G M N A0 B0 b f g -> PiAppEqVal G M N A0 B0 b f g'
restrictPiAppEqVal-sel G M N A0 B0 b f g g' cf cg cg' cb allU bU le fmg' fmg piEV src
    u' v' sel' P val-P =
  let cu' = Coherent-Selection sel' cg'
      cv' = Coherent-Selection-val sel' cg'
      fmu'-b = FinMem-Selection b f sel' fmg' cg' cb bU
      sb  = selectionBelow g u' cg cu'
      u_g  = fst sb
      v_g  = fst (snd sb)
      sel_g = fst (snd (snd sb))
      le-ug = fst (snd (snd (snd sb)))
      eq-vg = snd (snd (snd (snd sb)))
      cu_g = Coherent-Selection sel_g cg
      cv_g = Coherent-Selection-val sel_g cg
      fmu_g = FinMem-Selection b f sel_g fmg cg cb bU
      val-ug = restrictVal G P A0 u' u_g b le-ug fmu_g fmu'-b val-P
      body = src u_g v_g sel_g P val-ug
      le-ef = EvalFun-mon-arg f u_g u' le-ug (cft-from-cf f cf) cu_g cu'
      c-efug = Coherent-EvalFun f u_g (cft-from-cf f cf) cu_g
      c-efu' = Coherent-EvalFun f u' (cft-from-cf f cf) cu'
      fmem-vg-efug = FinMem-Selection-codomain b f sel_g fmg cg cf allU
      efuU' = EvalFun-in-UCode f u' b (cft-from-cf f cf) cu' allU
      fmem-vg-efu' = finMem-upward v_g (EvalFun f u_g) (EvalFun f u')
                        le-ef c-efug c-efu' fmem-vg-efug efuU'
      -- Derive ValTy G (subst1 B0 P) (EvalFun f u') from PiEdgeVal
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
      le-v'-efgu' = Selection-le-EvalFun g sel' le cg' cg cu'
      le-v'-vg = Eq-transport (LeCode v') eq-vg le-v'-efgu'
      fmem-v'-efu' = FinMem-Selection-codomain b f sel' fmg' cg' cf allU
  in restrictEqVal G (App M P) (App N P) (subst1 B0 P) v_g v' (EvalFun f u')
       le-v'-vg fmem-v'-efu' fmem-vg-efu' body2

-- restrictVal-PiCode: the main proof
restrictVal-PiCode :
    {n : Nat} (G : Ctx n) (M A : Expr n) (g g' : FinFun)
    (b : FinEl) (f : FinFun) ->
    CoherentFun f -> Coherent b -> FinMemAllU f b -> FinMem b UCode ->
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
      -- Derive PiEdgeVal G A0 B0 b f from ValTyPi via Red-unique-Pi
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
    CoherentFun f -> Coherent b -> FinMemAllU f b -> FinMem b UCode ->
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
      -- Derive PiEdgeVal G A0 B0 b f from ValTyPi via Red-unique-Pi
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
-- Transport PiEdgeVal/PiEdgeEq/PiEdgeEqTy (PROVED using selectionBelow)
--
-- Strategy: given PiEdgeVal at (b1,f1), produce PiEdgeVal at (b0,f0).
-- 1. Get FinMem u0 b0 from FinMemAllU-Selection on f0
-- 2. upVal from b0 to b1
-- 3. selectionBelow f1 u0 to get selection on f1 with EvalFun f1 u0 = v1
-- 4. restrictVal from u0 to u1 (key of f1 selection)
-- 5. Apply piEV1 to get ValTy at v1
-- 6. downValTy from v1 to v0 using Selection-le-EvalFun
------------------------------------------------------------------------

transportPiEdgeVal-sel :
  {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  LeCode b0 b1 -> LeFunCode f0 f1 ->
  FinMemAllU f0 b0 -> CoherentFun f0 -> CoherentFun f1 -> FinMemAllU f1 b1 ->
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
      v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1 (EvalFun-in-UCode f1 u0 b1 (cft-from-cf f1 cf1) cu0 allU1)
  in downValTy G (subst1 B N) v0 v1 le-v0-v1 fmem-v0-U v1U vty-v1

transportPiEdgeEq-sel :
  {n : Nat} (G : Ctx n) (A : Expr n) (B : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  LeCode b0 b1 -> LeFunCode f0 f1 ->
  FinMemAllU f0 b0 -> CoherentFun f0 -> CoherentFun f1 -> FinMemAllU f1 b1 ->
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
      v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1 (EvalFun-in-UCode f1 u0 b1 (cft-from-cf f1 cf1) cu0 allU1)
  in downEqValTy G (subst1 B N1) (subst1 B N2) v0 v1 le-v0-v1 fmem-v0-U v1U eqvty-v1

transportPiEdgeEqTy-sel :
  {n : Nat} (G : Ctx n) (A : Expr n) (B B' : Expr (suc n))
  (b0 : FinEl) (f0 : FinFun) (b1 : FinEl) (f1 : FinFun) ->
  Coherent b0 -> Coherent b1 -> FinMem b1 UCode -> FinMem b0 UCode ->
  LeCode b0 b1 -> LeFunCode f0 f1 ->
  FinMemAllU f0 b0 -> CoherentFun f0 -> CoherentFun f1 -> FinMemAllU f1 b1 ->
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
      v1U = Eq-transport (\ x -> FinMem x UCode) eq-v1 (EvalFun-in-UCode f1 u0 b1 (cft-from-cf f1 cf1) cu0 allU1)
  in downEqValTy G (subst1 B P) (subst1 B' P) v0 v1 le-v0-v1 fmem-v0-U v1U eqvty-v1

------------------------------------------------------------------------
-- downVal: a0 <= a1, FinMem u a0, Val M A u a1 => Val M A u a0
------------------------------------------------------------------------

downVal G M A u Bot          a1             le mem ca0 ca1 src = tt
downVal G M A u UCode        Bot            ()
downVal G M A u UCode        UCode          le mem ca0 ca1 src = src
downVal G M A u UCode        (FunEl h)      ()
downVal G M A u UCode        (PiCode b f)   ()
downVal G M A u (FunEl g)    Bot            le mem ca0 ca1 src = tt
downVal G M A u (FunEl g)    UCode          le mem ca0 ca1 src = tt
downVal G M A u (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
downVal G M A u (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
downVal G M A u (PiCode b0 f0) Bot          ()
downVal G M A u (PiCode b0 f0) UCode        ()
downVal G M A u (PiCode b0 f0) (FunEl h)    ()
-- PiCode/PiCode: split on u
downVal G M A Bot            (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
downVal G M A UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
downVal G M A (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src =
  let vty = fst src
      vpi = snd src
      -- Transport ValTy from (PiCode b1 f1) to (PiCode b0 f0)
      fmem-pf = FinMem-a-in-U (FunEl g) (PiCode b0 f0) mem
      vty' = downValTy G A (PiCode b0 f0) (PiCode b1 f1) le fmem-pf ca1 vty
      -- Transport ValPi
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
      -- Extract ValTy G A0 b1 from vty via Red-unique-Pi
      -- vty : ValTyPi G A b1 f1, has Red G A (Pi Av Bv) U
      -- vpi has Red G A (Pi A0 B0) U. Red-unique-Pi gives A0 = Av.
      -- The domain validity from vty is ValTy G Av b1.
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

------------------------------------------------------------------------
-- downEqVal
------------------------------------------------------------------------

downEqVal G M N A u Bot          a1             le mem ca0 ca1 src = tt
downEqVal G M N A u UCode        Bot            ()
downEqVal G M N A u UCode        UCode          le mem ca0 ca1 src = src
downEqVal G M N A u UCode        (FunEl h)      ()
downEqVal G M N A u UCode        (PiCode b f)   ()
downEqVal G M N A u (FunEl g)    Bot            le mem ca0 ca1 src = tt
downEqVal G M N A u (FunEl g)    UCode          le mem ca0 ca1 src = tt
downEqVal G M N A u (FunEl g)    (FunEl h)      le mem ca0 ca1 src = tt
downEqVal G M N A u (FunEl g)    (PiCode b f)   le mem ca0 ca1 src = tt
downEqVal G M N A u (PiCode b0 f0) Bot          ()
downEqVal G M N A u (PiCode b0 f0) UCode        ()
downEqVal G M N A u (PiCode b0 f0) (FunEl h)    ()
-- PiCode/PiCode: split on u
downEqVal G M N A Bot            (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src = tt
downEqVal G M N A UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
downEqVal G M N A (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 src =
  let vty  = fst src
      vpiM = fst (snd src)
      vpiN = fst (snd (snd src))
      epi  = snd (snd (snd src))
      -- Transport Val M and Val N via downVal
      valM  = mkSigma vty vpiM
      valN  = mkSigma vty vpiN
      valM' = downVal G M A (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 valM
      valN' = downVal G N A (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem ca0 ca1 valN
      -- Transport EqValPi
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
      -- Derive ValTy G A0 b1 from ValTyPi via Red-unique-Pi
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

------------------------------------------------------------------------
-- downValTy / downEqValTy
------------------------------------------------------------------------

downValTy G M Bot          u1             le fmem cu1 src = tt
downValTy G M UCode        Bot            ()
downValTy G M UCode        UCode          le fmem cu1 src = tt
downValTy G M UCode        (FunEl h)      ()
downValTy G M UCode        (PiCode b f)   ()
downValTy G M (FunEl g)    u1             le ()
downValTy G M (PiCode b0 f0) Bot          ()
downValTy G M (PiCode b0 f0) UCode        ()
downValTy G M (PiCode b0 f0) (FunEl h)    ()
downValTy G M (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 src =
  let -- Project source witness (ValTyPi G M b1 f1)
      A    = fst src
      B    = fst (snd src)
      red  = fst (snd (snd src))
      sat1 = fst (snd (snd (snd src)))
      fmA1 = fst (snd (snd (snd (snd src))))
      inner = snd (snd (snd (snd (snd src))))
      vty-b1 = fst inner
      piEV   = fst (snd inner)
      piEE   = snd (snd inner)
      -- Project target FinMem
      fmem-b0  = fst fmem
      fmemAll0 = fst (snd fmem)
      sat0     = snd (snd fmem)
      -- Coherence: cu1 : Coherent (PiCode b1 f1)
      cb1 = coh-from-aU b1 (fst cu1)
      -- cu0 from FinMem-Coherent
      cu0 = FinMem-Coherent (PiCode b0 f0) UCode fmem
      cb0 = coh-from-aU b0 fmem-b0
      -- Domain: ValTy G A b0 from ValTy G A b1 (recursive, smaller rank)
      vty-b0 = downValTy G A b0 b1 (fst le) fmem-b0 (fst cu1) vty-b1
      -- Transport PiEdgeVal/PiEdgeEq from (b1,f1) to (b0,f0)
      piEV0 = transportPiEdgeVal-sel G A B b0 f0 b1 f1
                cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vty-b1 piEV
      piEE0 = transportPiEdgeEq-sel G A B b0 f0 b1 f1
                cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vty-b1 piEE
  in mkSigma A (mkSigma B (mkSigma red (mkSigma sat0
       (mkSigma fmemAll0 (mkSigma vty-b0 (mkSigma piEV0 piEE0))))))

downEqValTy G M N Bot          u1             le fmem cu1 src = tt
downEqValTy G M N UCode        Bot            ()
downEqValTy G M N UCode        UCode          le fmem cu1 src = tt
downEqValTy G M N UCode        (FunEl h)      ()
downEqValTy G M N UCode        (PiCode b f)   ()
downEqValTy G M N (FunEl g)    u1             le ()
downEqValTy G M N (PiCode b0 f0) Bot          ()
downEqValTy G M N (PiCode b0 f0) UCode        ()
downEqValTy G M N (PiCode b0 f0) (FunEl h)    ()
downEqValTy G M N (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 src =
  let -- Unbundle: src = Pair (ValTy G M ...) (Pair (ValTy G N ...) (EqValTyPi ...))
      vtyM1 = fst src
      vtyN1 = fst (snd src)
      core  = snd (snd src)
      -- Project EqValTyPi components
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
      -- Extract ValTy G A b1: need transport from vtyM1's domain to A
      A_M    = fst vtyM1
      vtA_M  = fst (snd (snd (snd (snd (snd vtyM1)))))
      redM2  = fst (snd (snd vtyM1))
      uniqM  = Red-unique-Pi redM2 redM
      eqAMA  : Eq A_M A
      eqAMA  = fst uniqM
      vtA-b1 = Eq-transport (\ X -> ValTy G X b1) eqAMA vtA_M
      -- Project target FinMem
      fmem-b0  = fst fmem
      fmemAll0 = fst (snd fmem)
      sat0     = snd (snd fmem)
      -- Coherence
      cb1 = coh-from-aU b1 (fst cu1)
      cu0 = FinMem-Coherent (PiCode b0 f0) UCode fmem
      cb0 = coh-from-aU b0 fmem-b0
      -- Domain equality: EqValTy G A A' b0 from EqValTy G A A' b1
      eqvty0 = downEqValTy G A A' b0 b1 (fst le) fmem-b0 (fst cu1) eqvty
      -- Transport PiEdgeEqTy from (b1,f1) to (b0,f0)
      piEEqT0 = transportPiEdgeEqTy-sel G A B B' b0 f0 b1 f1
                  cb0 cb1 (fst cu1) fmem-b0 (fst le) (snd le) fmemAll0 sat0 sat1 fmA1 vtA-b1 piEEqT
      -- Downward transport of bundled ValTy's
      vtyM0 = downValTy G M (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 vtyM1
      vtyN0 = downValTy G N (PiCode b0 f0) (PiCode b1 f1) le fmem cu1 vtyN1
      -- Build EqValTyPi core
      core0 = mkSigma A (mkSigma B (mkSigma A' (mkSigma B'
                (mkSigma redM (mkSigma redN (mkSigma sat0
                  (mkSigma fmemAll0 (mkSigma eqvty0 piEEqT0))))))))
  in mkSigma vtyM0 (mkSigma vtyN0 core0)

------------------------------------------------------------------------
-- upVal: a0 <= a1, FinMem u a0, FinMem u a1, Val M A u a0 => Val M A u a1
------------------------------------------------------------------------

-- a0 = Bot, u = Bot: split a1
upVal G M A Bot Bot          Bot             le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot Bot          UCode           le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot Bot          (FunEl h)       le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot Bot          (PiCode b1 f1)  le mem0 mem1 ca0 ca1 src vta1 = tt
-- a0 = Bot, u /= Bot: FinMem u Bot = Empty
upVal G M A UCode        Bot a1 le ()
upVal G M A (FunEl g)    Bot a1 le ()
upVal G M A (PiCode a f) Bot a1 le ()
-- a0 = UCode, a1 = UCode: identity (split u for exact-split)
upVal G M A Bot            UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upVal G M A UCode          UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upVal G M A (FunEl g')     UCode UCode le ()
upVal G M A (PiCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
-- a0 = UCode, a1 /= UCode: absurd from LeCode
upVal G M A u UCode Bot          ()
upVal G M A u UCode (FunEl h)    ()
upVal G M A u UCode (PiCode b h) ()
-- a0 = FunEl: FinMem u (FunEl g) empty for u /= Bot
upVal G M A Bot            (FunEl g) Bot            le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot            (FunEl g) UCode          le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot            (FunEl g) (FunEl h)      le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A Bot            (FunEl g) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A UCode          (FunEl g) a1             le ()
upVal G M A (FunEl g')     (FunEl g) a1             le ()
upVal G M A (PiCode a' f') (FunEl g) a1             le ()
-- a0 = PiCode, a1 /= PiCode: absurd from LeCode
upVal G M A u (PiCode b0 f0) Bot       ()
upVal G M A u (PiCode b0 f0) UCode     ()
upVal G M A u (PiCode b0 f0) (FunEl h) ()
-- a0 = PiCode, a1 = PiCode: split on u
upVal G M A Bot            (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upVal G M A UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
upVal G M A (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
  let vpi = snd src
      -- Transport ValPi upward
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
      -- Derive PiEdgeVal G A0 B0 b1 f1 from vta1 via Red-unique-Pi
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
upVal G M A (PiCode a f)   (PiCode b0 f0) (PiCode b1 f1) le ()

------------------------------------------------------------------------
-- upEqVal
------------------------------------------------------------------------

-- a0 = Bot, u = Bot: split a1
upEqVal G M N A Bot Bot          Bot             le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot Bot          UCode           le mem0 mem1 ca0 ca1 src vta1 = mkSigma tt (mkSigma tt tt)
upEqVal G M N A Bot Bot          (FunEl h)       le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot Bot          (PiCode b1 f1)  le mem0 mem1 ca0 ca1 src vta1 = tt
-- a0 = Bot, u /= Bot: FinMem u Bot = Empty
upEqVal G M N A UCode        Bot a1 le ()
upEqVal G M N A (FunEl g)    Bot a1 le ()
upEqVal G M N A (PiCode a f) Bot a1 le ()
-- a0 = UCode, a1 = UCode: identity (split u for exact-split)
upEqVal G M N A Bot            UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upEqVal G M N A UCode          UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
upEqVal G M N A (FunEl g')     UCode UCode le ()
upEqVal G M N A (PiCode a' f') UCode UCode le mem0 mem1 ca0 ca1 src vta1 = src
-- a0 = UCode, a1 /= UCode: absurd from LeCode
upEqVal G M N A u UCode Bot          ()
upEqVal G M N A u UCode (FunEl h)    ()
upEqVal G M N A u UCode (PiCode b h) ()
-- a0 = FunEl: FinMem u (FunEl g) empty for u /= Bot
upEqVal G M N A Bot            (FunEl g) Bot            le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot            (FunEl g) UCode          le mem0 mem1 ca0 ca1 src vta1 = mkSigma tt (mkSigma tt tt)
upEqVal G M N A Bot            (FunEl g) (FunEl h)      le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A Bot            (FunEl g) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A UCode          (FunEl g) a1             le ()
upEqVal G M N A (FunEl g')     (FunEl g) a1             le ()
upEqVal G M N A (PiCode a' f') (FunEl g) a1             le ()
-- a0 = PiCode, a1 /= PiCode: absurd from LeCode
upEqVal G M N A u (PiCode b0 f0) Bot       ()
upEqVal G M N A u (PiCode b0 f0) UCode     ()
upEqVal G M N A u (PiCode b0 f0) (FunEl h) ()
-- a0 = PiCode, a1 = PiCode: split on u
upEqVal G M N A Bot            (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 = tt
upEqVal G M N A UCode          (PiCode b0 f0) (PiCode b1 f1) le ()
upEqVal G M N A (FunEl g)      (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 src vta1 =
  let vty  = fst src
      vpiM = fst (snd src)
      vpiN = fst (snd (snd src))
      epi  = snd (snd (snd src))
      -- Transport Val M and Val N via upVal
      valM  = mkSigma vty vpiM
      valN  = mkSigma vty vpiN
      valM' = upVal G M A (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 valM vta1
      valN' = upVal G N A (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le mem0 mem1 ca0 ca1 valN vta1
      -- Transport EqValPi upward
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
      -- Derive PiEdgeVal G A0 B0 b1 f1 from vta1 via Red-unique-Pi
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
upEqVal G M N A (PiCode a f)   (PiCode b0 f0) (PiCode b1 f1) le ()

------------------------------------------------------------------------
-- restrictVal: u' <= u, FinMem u' a, Val M A u a => Val M A u' a
------------------------------------------------------------------------

restrictVal G M A u u' Bot          le mem fmu src = tt
restrictVal G M A u u' UCode        le mem fmu src =
  downValTy G M u' u le mem fmu src
restrictVal G M A u u' (FunEl h)    le mem fmu src = tt
-- a = PiCode: split on u, then u'
restrictVal G M A Bot Bot            (PiCode b f) le mem fmu src = tt
restrictVal G M A Bot UCode          (PiCode b f) le ()
restrictVal G M A Bot (FunEl g')     (PiCode b f) ()
restrictVal G M A Bot (PiCode a2 f2) (PiCode b f) le ()
restrictVal G M A UCode Bot            (PiCode b f) le mem fmu src = tt
restrictVal G M A UCode UCode          (PiCode b f) le mem fmu src = tt
restrictVal G M A UCode (FunEl g')     (PiCode b f) le mem ()
restrictVal G M A UCode (PiCode a2 f2) (PiCode b f) le ()
restrictVal G M A (FunEl g) Bot            (PiCode b f) le mem fmu src = tt
restrictVal G M A (FunEl g) UCode          (PiCode b f) le ()
restrictVal G M A (FunEl g) (FunEl g')     (PiCode b f) le mem fmu src =
  let aU = FinMem-a-in-U (FunEl g) (PiCode b f) fmu
  in mkSigma (fst src)
    (restrictVal-PiCode G M A g g' b f (snd (snd aU)) (coh-from-aU b (fst aU)) (fst (snd aU)) (fst aU) le
      (mkSigma (fst mem) (fst (snd mem))) (fst src) (snd src))
restrictVal G M A (FunEl g) (PiCode a2 f2) (PiCode b f) le ()
restrictVal G M A (PiCode a1 f1) Bot            (PiCode b f) le mem fmu src = tt
restrictVal G M A (PiCode a1 f1) UCode          (PiCode b f) le ()
restrictVal G M A (PiCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
restrictVal G M A (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) le mem fmu src = tt

------------------------------------------------------------------------
-- restrictEqVal: u' <= u, FinMem u' a, EqVal M N A u a => EqVal M N A u' a
------------------------------------------------------------------------

restrictEqVal G M N A u u' Bot          le mem fmu src = tt
restrictEqVal G M N A u u' UCode        le mem fmu src =
  mkSigma (downValTy G M u' u le mem fmu (fst src))
    (mkSigma (downValTy G N u' u le mem fmu (fst (snd src)))
             (downEqValTy G M N u' u le mem fmu (snd (snd src))))
restrictEqVal G M N A u u' (FunEl h)    le mem fmu src = tt
-- a = PiCode: split on u, then u'
restrictEqVal G M N A Bot Bot            (PiCode b f) le mem fmu src = tt
restrictEqVal G M N A Bot UCode          (PiCode b f) le ()
restrictEqVal G M N A Bot (FunEl g')     (PiCode b f) ()
restrictEqVal G M N A Bot (PiCode a2 f2) (PiCode b f) le ()
restrictEqVal G M N A UCode Bot            (PiCode b f) le mem fmu src = tt
restrictEqVal G M N A UCode UCode          (PiCode b f) le mem fmu src = tt
restrictEqVal G M N A UCode (FunEl g')     (PiCode b f) le mem ()
restrictEqVal G M N A UCode (PiCode a2 f2) (PiCode b f) le ()
restrictEqVal G M N A (FunEl g) Bot            (PiCode b f) le mem fmu src = tt
restrictEqVal G M N A (FunEl g) UCode          (PiCode b f) le ()
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
restrictEqVal G M N A (PiCode a1 f1) Bot            (PiCode b f) le mem fmu src = tt
restrictEqVal G M N A (PiCode a1 f1) UCode          (PiCode b f) le ()
restrictEqVal G M N A (PiCode a1 f1) (FunEl g')     (PiCode b f) le mem ()
restrictEqVal G M N A (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) le mem fmu src = tt

PiAppVal-lookup :
    {n : Nat} (G : Ctx n) (M A0 : Expr n) (B0 : Expr (suc n))
    (b : FinEl) (f : FinFun) (g : FinFun) ->
    PiAppVal G M A0 B0 b f g ->
    (e : Edge) -> EdgeIn e g ->
    (N : Expr n) -> Val G N A0 (fst e) b ->
    Val G (App M N) (subst1 B0 N) (snd e) (EvalFun f (fst e))
PiAppVal-lookup G M A0 B0 b f g pav e ein N valN =
  let sel = singleton-selection e g ein
      -- sel : Selection g (Sup (fst e) Bot) (Sup (snd e) Bot)
      eqU = Sup-Bot-right (fst e)
      eqV = Sup-Bot-right (snd e)
      -- Transport Val input: Val G N A0 (fst e) b -> Val G N A0 (Sup (fst e) Bot) b
      valN' = Eq-transport (\ x -> Val G N A0 x b) (Eq-sym eqU) valN
      -- Apply PiAppVal with singleton selection
      result = pav (Sup (fst e) Bot) (Sup (snd e) Bot) sel N valN'
      -- result : Val G (App M N) (subst1 B0 N) (Sup (snd e) Bot) (EvalFun f (Sup (fst e) Bot))
      -- Transport output back
  in Eq-transport (\ x -> Val G (App M N) (subst1 B0 N) x (EvalFun f (fst e)))
       eqV
       (Eq-transport (\ x -> Val G (App M N) (subst1 B0 N) (Sup (snd e) Bot) (EvalFun f x))
         eqU result)

------------------------------------------------------------------------
-- Val-to-EqVal: diagonal embedding Val -> EqVal
------------------------------------------------------------------------

{-# TERMINATING #-}

Val-to-EqVal : {n : Nat} {G : Ctx n} {M A : Expr n}
  (u a : FinEl) -> Val G M A u a -> EqVal G M M A u a

ValTy-to-EqValTy : {n : Nat} {G : Ctx n} {M : Expr n}
  (u : FinEl) -> ValTy G M u -> EqValTy G M M u

-- Val: case split on a, then u at PiCode
Val-to-EqVal u Bot val = tt
Val-to-EqVal u UCode val = mkSigma val (mkSigma val (ValTy-to-EqValTy u val))
Val-to-EqVal u (FunEl h) val = tt
Val-to-EqVal Bot (PiCode b f) val = tt
Val-to-EqVal UCode (PiCode b f) val = tt
Val-to-EqVal (FunEl g) (PiCode b f) val =
  let vty = fst val
      vpi = snd val
      A0  = fst vpi
      B0  = fst (snd vpi)
      red = fst (snd (snd vpi))
      cg  = fst (snd (snd (snd vpi)))
      fmg = fst (snd (snd (snd (snd vpi))))
      pav = fst (snd (snd (snd (snd (snd vpi)))))
      pae = snd (snd (snd (snd (snd (snd vpi)))))
      eqvpi = mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg
                (\ u' v' sel P valP ->
                  Val-to-EqVal v' (EvalFun f u') (pav u' v' sel P valP))))))
  in mkSigma vty (mkSigma vpi (mkSigma vpi eqvpi))
Val-to-EqVal (PiCode a' f') (PiCode b f) val = tt

-- ValTy: case split on u
ValTy-to-EqValTy Bot val = tt
ValTy-to-EqValTy UCode val = tt
ValTy-to-EqValTy (FunEl g) val = tt
ValTy-to-EqValTy (PiCode b f) val =
  let A   = fst val
      B   = fst (snd val)
      red = fst (snd (snd val))
      cf  = fst (snd (snd (snd val)))
      fmU = fst (snd (snd (snd (snd val))))
      vtA = fst (snd (snd (snd (snd (snd val)))))
      pev = fst (snd (snd (snd (snd (snd (snd val))))))
      peq = snd (snd (snd (snd (snd (snd (snd val))))))
  in mkSigma val (mkSigma val
       (mkSigma A (mkSigma B (mkSigma A (mkSigma B
         (mkSigma red (mkSigma red (mkSigma cf (mkSigma fmU
           (mkSigma (ValTy-to-EqValTy b vtA)
             (\ u' v' sel P valP ->
               ValTy-to-EqValTy v' (pev u' v' sel P valP))))))))))))

------------------------------------------------------------------------
-- EqValTy-sym + Val/EqVal transport along EqValTy (Lemma 8)
--
-- Proved by mutual induction on the complexity of the code.
-- Key insight: at PiCode b f, all recursive calls are at strictly
-- smaller codes (b, or values from selections/EvalFun).
------------------------------------------------------------------------

{-# TERMINATING #-}

-- EqValTy symmetry
EqValTy-sym : {n : Nat} {G : Ctx n} {M N : Expr n}
  (u : FinEl) -> Coherent u -> EqValTy G M N u -> EqValTy G N M u

-- Val transport along EqValTy (forward): change type expression in Val
Val-EqValTy-fwd : {n : Nat} {G : Ctx n} {C C' M : Expr n}
  (u b : FinEl) -> Coherent b -> EqValTy G C C' b ->
  Val G M C u b -> Val G M C' u b

-- EqVal transport along EqValTy (forward): change type expression in EqVal
EqVal-EqValTy-fwd : {n : Nat} {G : Ctx n} {C C' M N : Expr n}
  (u b : FinEl) -> Coherent b -> EqValTy G C C' b ->
  EqVal G M N C u b -> EqVal G M N C' u b

-- EqValTy transitivity
EqValTy-trans : {n : Nat} {G : Ctx n} {A B C : Expr n}
  (u : FinEl) -> Coherent u -> EqValTy G A B u -> EqValTy G B C u ->
  EqValTy G A C u


------------------------------------------------------------------------
-- EqValTy-sym: case split on u
------------------------------------------------------------------------

EqValTy-sym Bot cu eqv = tt
EqValTy-sym UCode cu eqv = tt
EqValTy-sym (FunEl g) cu eqv = tt
EqValTy-sym {G = G} {M = M} {N = N} (PiCode b f) cu eqv =
  let -- Unbundle
      vtyM = fst eqv
      vtyN = fst (snd eqv)
      core = snd (snd eqv)
      -- Extract EqValTyPi components
      C   = fst core
      D   = fst (snd core)
      C'  = fst (snd (snd core))
      D'  = fst (snd (snd (snd core)))
      rM  = fst (snd (snd (snd (snd core))))
      rN  = fst (snd (snd (snd (snd (snd core)))))
      cf  = fst (snd (snd (snd (snd (snd (snd core))))))
      fmU = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
      tail8 = snd (snd (snd (snd (snd (snd (snd (snd core)))))))
      eqC = fst tail8
      pet = snd tail8
      -- Coherent (PiCode b f) gives us Coherent b
      cb = fst cu
      -- Build symmetric core
      symCore = mkSigma C' (mkSigma D' (mkSigma C (mkSigma D
                  (mkSigma rN (mkSigma rM (mkSigma cf (mkSigma fmU
                    (mkSigma (EqValTy-sym b cb eqC)
                      (\ u' v' sel P valP ->
                        let valP-C = Val-EqValTy-fwd u' b cb (EqValTy-sym b cb eqC) valP
                            cv' = coh-from-aU v' (FinMem-Selection-UCode b sel fmU cf)
                            eqt    = pet u' v' sel P valP-C
                        in EqValTy-sym v' cv' eqt)))))))))
  in mkSigma vtyN (mkSigma vtyM symCore)


------------------------------------------------------------------------
-- Val-EqValTy-fwd: case split on b, then u at PiCode
------------------------------------------------------------------------

-- b = Bot: Val = Top
Val-EqValTy-fwd u Bot cb eqv val = tt
-- b = UCode: Val = ValTy, doesn't mention C
Val-EqValTy-fwd u UCode cb eqv val = val
-- b = FunEl: Val = Top
Val-EqValTy-fwd u (FunEl h) cb eqv val = tt
-- b = PiCode, u = Bot/UCode/PiCode: Val = Top
Val-EqValTy-fwd Bot (PiCode b0 f0) cb eqv val = tt
Val-EqValTy-fwd UCode (PiCode b0 f0) cb eqv val = tt
Val-EqValTy-fwd (PiCode a' ff) (PiCode b0 f0) cb eqv val = tt
-- b = PiCode b0 f0, u = FunEl g: ValPi transport
Val-EqValTy-fwd {G = G} {C = C} {C' = C'} {M = M}
  (FunEl g) (PiCode b0 f0) cb eqv val =
  let -- Unbundle: eqv = Pair (ValTy G C ...) (Pair (ValTy G C' ...) (EqValTyPi ...))
      vtyC  = fst eqv
      vtyC' = fst (snd eqv)
      core  = snd (snd eqv)
      -- Extract EqValTyPi components
      E   = fst core
      F   = fst (snd core)
      E'  = fst (snd (snd core))
      F'  = fst (snd (snd (snd core)))
      rC  = fst (snd (snd (snd (snd core))))
      rC' = fst (snd (snd (snd (snd (snd core)))))
      cf0 = fst (snd (snd (snd (snd (snd (snd core))))))
      fmU = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
      tail8 = snd (snd (snd (snd (snd (snd (snd (snd core)))))))
      eqE  = fst tail8
      pet  = snd tail8
      -- Extract ValPi components from snd of pair
      vpi  = snd val
      A0   = fst vpi
      B0   = fst (snd vpi)
      redC = fst (snd (snd vpi))
      cg   = fst (snd (snd (snd vpi)))
      fmg  = fst (snd (snd (snd (snd vpi))))
      pav  = fst (snd (snd (snd (snd (snd vpi)))))
      pae  = snd (snd (snd (snd (snd (snd vpi)))))
      -- Red-unique-Pi: A0 = E and B0 = F
      uniq = Red-unique-Pi redC rC
      eqA0E : Eq A0 E
      eqA0E = fst uniq
      eqB0F : Eq B0 F
      eqB0F = snd uniq
      -- Transport PiAppVal from (A0, B0) to (E', F')
      -- Step 1: from (A0, B0) to (E, F) via Eq
      pav-EF : PiAppVal G M E F b0 f0 g
      pav-EF = Eq-transport (\ X -> PiAppVal G M X F b0 f0 g) eqA0E
                 (Eq-transport (\ Y -> PiAppVal G M A0 Y b0 f0 g) eqB0F pav)
      pae-EF : PiAppEq G M E F b0 f0 g
      pae-EF = Eq-transport (\ X -> PiAppEq G M X F b0 f0 g) eqA0E
                 (Eq-transport (\ Y -> PiAppEq G M A0 Y b0 f0 g) eqB0F pae)
      -- Coherent b0 and FinMem b0 UCode
      cb0 = fst cb
      b0U = bU-from-cf-fmU f0 b0 cf0 fmU
      -- Step 2: from (E, F) to (E', F') via EqValTy transport
      -- For PiAppVal: need to convert domain and codomain
      pav-E'F' : PiAppVal G M E' F' b0 f0 g
      pav-E'F' = \ u' v' sel N valN ->
        let -- Convert input: Val G N E' u' b0 -> Val G N E u' b0
            valN-E = Val-EqValTy-fwd u' b0 cb0 (EqValTy-sym b0 cb0 eqE) valN
            -- Apply original PiAppVal
            body = pav-EF u' v' sel N valN-E
            -- Restrict Val from u' to u-f for pet
            cu' = Coherent-Selection sel cg
            sb  = selectionBelow f0 u' cf0 cu'
            u-f = fst sb
            v-f = fst (snd sb)
            sel-f = fst (snd (snd sb))
            le-uf = fst (snd (snd (snd sb)))
            eq-ef = snd (snd (snd (snd sb)))
            fmu-f = FinMemAllU-Selection b0 sel-f fmU cf0 cb0 b0U
            fmu' = FinMem-Selection b0 f0 sel fmg cg cb0 b0U
            valN-uf = restrictVal G N E u' u-f b0 le-uf fmu-f fmu' valN-E
            eqt-vf = pet u-f v-f sel-f N valN-uf
            eqt-ef : EqValTy G (subst1 F N) (subst1 F' N) (EvalFun f0 u')
            eqt-ef = Eq-transport (\ w -> EqValTy G (subst1 F N) (subst1 F' N) w)
                       (Eq-sym eq-ef) eqt-vf
            cev = Coherent-EvalFun f0 u' (cft-from-cf f0 cf0) cu'
        in Val-EqValTy-fwd v' (EvalFun f0 u') cev eqt-ef body
      -- PiAppEq: convert domain EqVal and codomain type
      -- Uses Val-from-EqVal-first to bridge EqVal input to pet's Val requirement
      pae-E'F' : PiAppEq G M E' F' b0 f0 g
      pae-E'F' = \ u' v' sel N1 N2 eqN ->
        let -- Convert input: EqVal G N1 N2 E' u' b0 -> EqVal G N1 N2 E u' b0
            eqN-E = EqVal-EqValTy-fwd u' b0 cb0 (EqValTy-sym b0 cb0 eqE) eqN
            -- Extract Val for N1 to call pet
            valN1-E = Val-from-EqVal-first u' b0 eqN-E
            -- Apply original PiAppEq
            body = pae-EF u' v' sel N1 N2 eqN-E
            -- Restrict Val from u' to u-f for pet
            cu' = Coherent-Selection sel cg
            sb  = selectionBelow f0 u' cf0 cu'
            u-f = fst sb
            v-f = fst (snd sb)
            sel-f = fst (snd (snd sb))
            le-uf = fst (snd (snd (snd sb)))
            eq-ef = snd (snd (snd (snd sb)))
            fmu-f = FinMemAllU-Selection b0 sel-f fmU cf0 cb0 b0U
            fmu' = FinMem-Selection b0 f0 sel fmg cg cb0 b0U
            valN1-uf = restrictVal G N1 E u' u-f b0 le-uf fmu-f fmu' valN1-E
            eqt-vf = pet u-f v-f sel-f N1 valN1-uf
            eqt-ef : EqValTy G (subst1 F N1) (subst1 F' N1) (EvalFun f0 u')
            eqt-ef = Eq-transport (\ w -> EqValTy G (subst1 F N1) (subst1 F' N1) w)
                       (Eq-sym eq-ef) eqt-vf
            cev = Coherent-EvalFun f0 u' (cft-from-cf f0 cf0) cu'
        in EqVal-EqValTy-fwd v' (EvalFun f0 u') cev eqt-ef body
  in mkSigma vtyC' (mkSigma E' (mkSigma F' (mkSigma rC' (mkSigma cg
       (mkSigma fmg (mkSigma pav-E'F' pae-E'F'))))))

------------------------------------------------------------------------
-- EqVal-EqValTy-fwd: case split on b, then u at PiCode
------------------------------------------------------------------------

-- b = Bot: EqVal = Top
EqVal-EqValTy-fwd u Bot cb eqv ev = tt
-- b = UCode: EqVal = EqValTy, doesn't mention C
EqVal-EqValTy-fwd u UCode cb eqv ev = ev
-- b = FunEl: EqVal = Top
EqVal-EqValTy-fwd u (FunEl h) cb eqv ev = tt
-- b = PiCode, u = Bot/UCode/PiCode: EqVal = Top
EqVal-EqValTy-fwd Bot (PiCode b0 f0) cb eqv ev = tt
EqVal-EqValTy-fwd UCode (PiCode b0 f0) cb eqv ev = tt
EqVal-EqValTy-fwd (PiCode a' ff) (PiCode b0 f0) cb eqv ev = tt
-- b = PiCode b0 f0, u = FunEl g: EqValPi transport
EqVal-EqValTy-fwd {G = G} {C = C} {C' = C'} {M = M} {N = N}
  (FunEl g) (PiCode b0 f0) cb eqv ev =
  let -- Unbundle
      vtyC  = fst eqv
      vtyC' = fst (snd eqv)
      core  = snd (snd eqv)
      -- Extract EqValTyPi components
      E   = fst core
      F   = fst (snd core)
      E'  = fst (snd (snd core))
      F'  = fst (snd (snd (snd core)))
      rC  = fst (snd (snd (snd (snd core))))
      rC' = fst (snd (snd (snd (snd (snd core)))))
      cf0 = fst (snd (snd (snd (snd (snd (snd core))))))
      fmU = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
      tail8 = snd (snd (snd (snd (snd (snd (snd (snd core)))))))
      eqE  = fst tail8
      pet  = snd tail8
      -- Extract from ev: Pair (ValTy) (Pair (ValPi M) (Pair (ValPi N) (EqValPi)))
      epi  = snd (snd (snd ev))
      -- Extract from EqValPi
      A0   = fst epi
      B0   = fst (snd epi)
      redC = fst (snd (snd epi))
      cg   = fst (snd (snd (snd epi)))
      fmg  = fst (snd (snd (snd (snd epi))))
      paev = snd (snd (snd (snd (snd epi))))
      -- Red-unique-Pi: A0 = E and B0 = F
      uniq = Red-unique-Pi redC rC
      eqA0E : Eq A0 E
      eqA0E = fst uniq
      eqB0F : Eq B0 F
      eqB0F = snd uniq
      -- Coherent b0 and FinMem b0 UCode
      cb0 = fst cb
      b0U = bU-from-cf-fmU f0 b0 cf0 fmU
      -- Transport PiAppEqVal from (A0, B0) to (E', F')
      paev-EF : PiAppEqVal G M N E F b0 f0 g
      paev-EF = Eq-transport (\ X -> PiAppEqVal G M N X F b0 f0 g) eqA0E
                  (Eq-transport (\ Y -> PiAppEqVal G M N A0 Y b0 f0 g) eqB0F paev)
      -- PiAppEqVal transport: convert domain Val and codomain type
      -- PiAppEqVal takes Val (not EqVal!) as input, so pet works directly
      paev-E'F' : PiAppEqVal G M N E' F' b0 f0 g
      paev-E'F' = \ u' v' sel P valP ->
        let -- Convert input: Val G P E' u' b0 -> Val G P E u' b0
            valP-E = Val-EqValTy-fwd u' b0 cb0 (EqValTy-sym b0 cb0 eqE) valP
            -- Apply original PiAppEqVal
            body = paev-EF u' v' sel P valP-E
            -- Restrict Val from u' to u-f for pet
            cu' = Coherent-Selection sel cg
            sb  = selectionBelow f0 u' cf0 cu'
            u-f = fst sb
            v-f = fst (snd sb)
            sel-f = fst (snd (snd sb))
            le-uf = fst (snd (snd (snd sb)))
            eq-ef = snd (snd (snd (snd sb)))
            fmu-f = FinMemAllU-Selection b0 sel-f fmU cf0 cb0 b0U
            fmu' = FinMem-Selection b0 f0 sel fmg cg cb0 b0U
            valP-uf = restrictVal G P E u' u-f b0 le-uf fmu-f fmu' valP-E
            eqt-vf = pet u-f v-f sel-f P valP-uf
            eqt-ef : EqValTy G (subst1 F P) (subst1 F' P) (EvalFun f0 u')
            eqt-ef = Eq-transport (\ w -> EqValTy G (subst1 F P) (subst1 F' P) w)
                       (Eq-sym eq-ef) eqt-vf
            cev = Coherent-EvalFun f0 u' (cft-from-cf f0 cf0) cu'
        in EqVal-EqValTy-fwd v' (EvalFun f0 u') cev eqt-ef body
      -- Transport Val M and Val N from C to C'
      valM-C : Val G M C (FunEl g) (PiCode b0 f0)
      valM-C = mkSigma (fst ev) (fst (snd ev))
      valN-C : Val G N C (FunEl g) (PiCode b0 f0)
      valN-C = mkSigma (fst ev) (fst (snd (snd ev)))
      valM-C' = Val-EqValTy-fwd (FunEl g) (PiCode b0 f0) cb eqv valM-C
      valN-C' = Val-EqValTy-fwd (FunEl g) (PiCode b0 f0) cb eqv valN-C
      -- Build EqValPi G M N C' g b0 f0
      eqvpi-C' = mkSigma E' (mkSigma F' (mkSigma rC' (mkSigma cg
                   (mkSigma fmg paev-E'F'))))
  in mkSigma vtyC' (mkSigma (snd valM-C') (mkSigma (snd valN-C') eqvpi-C'))

------------------------------------------------------------------------
-- EqValTy-trans: case split on u
------------------------------------------------------------------------

EqValTy-trans Bot cu eqAB eqBC = tt
EqValTy-trans UCode cu eqAB eqBC = tt
EqValTy-trans (FunEl g) cu eqAB eqBC = tt
EqValTy-trans {G = G} {A = A} {B = B} {C = C} (PiCode b f) cu eqAB eqBC =
  let -- Unbundle first: EqValTy G A B (PiCode b f)
      vtyA  = fst eqAB
      vtyB1 = fst (snd eqAB)
      coreAB = snd (snd eqAB)
      -- EqValTyPi G A B b f components
      A0   = fst coreAB
      B0   = fst (snd coreAB)
      A0'  = fst (snd (snd coreAB))
      B0'  = fst (snd (snd (snd coreAB)))
      rA   = fst (snd (snd (snd (snd coreAB))))
      rB1  = fst (snd (snd (snd (snd (snd coreAB)))))
      cf1  = fst (snd (snd (snd (snd (snd (snd coreAB))))))
      fmU1 = fst (snd (snd (snd (snd (snd (snd (snd coreAB)))))))
      tailAB = snd (snd (snd (snd (snd (snd (snd (snd coreAB)))))))
      eqDomAB = fst tailAB
      petAB   = snd tailAB
      -- Unbundle second: EqValTy G B C (PiCode b f)
      vtyB2 = fst eqBC
      vtyC  = fst (snd eqBC)
      coreBC = snd (snd eqBC)
      -- EqValTyPi G B C b f components
      A1   = fst coreBC
      B1   = fst (snd coreBC)
      A1'  = fst (snd (snd coreBC))
      B1'  = fst (snd (snd (snd coreBC)))
      rB2  = fst (snd (snd (snd (snd coreBC))))
      rC   = fst (snd (snd (snd (snd (snd coreBC)))))
      cf2  = fst (snd (snd (snd (snd (snd (snd coreBC))))))
      fmU2 = fst (snd (snd (snd (snd (snd (snd (snd coreBC)))))))
      tailBC = snd (snd (snd (snd (snd (snd (snd (snd coreBC)))))))
      eqDomBC = fst tailBC
      petBC   = snd tailBC
      -- Red-unique-Pi: rB1 : Red G B (Pi A0' B0') U
      --                rB2 : Red G B (Pi A1  B1 ) U
      -- gives A0' = A1, B0' = B1
      uniq = Red-unique-Pi rB1 rB2
      eqA0'A1 : Eq A0' A1
      eqA0'A1 = fst uniq
      eqB0'B1 : Eq B0' B1
      eqB0'B1 = snd uniq
      -- Coherent b from Coherent (PiCode b f)
      cb = fst cu
      bU = bU-from-cf-fmU f b cf1 fmU1
      -- Domain transitivity: EqValTy G A0 A0' b  and  EqValTy G A1 A1' b
      -- Transport eqDomBC : EqValTy G A1 A1' b  to  EqValTy G A0' A1' b
      eqDomBC' : EqValTy G A0' A1' b
      eqDomBC' = Eq-transport (\ X -> EqValTy G X A1' b) (Eq-sym eqA0'A1) eqDomBC
      -- Now chain: EqValTy G A0 A0' b -> EqValTy G A0' A1' b -> EqValTy G A0 A1' b
      eqDomAC : EqValTy G A0 A1' b
      eqDomAC = EqValTy-trans b cb eqDomAB eqDomBC'
      -- PiEdgeEqTy: for each selection (u', v') from f and P with Val G P A0 u' b:
      -- petAB gives EqValTy G (subst1 B0 P) (subst1 B0' P) v'
      -- petBC gives EqValTy G (subst1 B1 P') (subst1 B1' P') v' (for P' with Val G P' A1 u' b)
      -- Chain them using EqValTy-trans at v'
      petAC : PiEdgeEqTy G A0 B0 B1' b f
      petAC = \ u' v' sel P valP ->
        let -- Transport eqDomAB to get Val G P A0' u' b
            valP-A0' = Val-EqValTy-fwd u' b cb eqDomAB valP
            -- Transport further to Val G P A1 u' b using A0' = A1
            valP-A1 : Val G P A1 u' b
            valP-A1 = Eq-transport (\ X -> Val G P X u' b) eqA0'A1 valP-A0'
            -- petAB: EqValTy G (subst1 B0 P) (subst1 B0' P) v'
            eqt1 = petAB u' v' sel P valP
            -- petBC: EqValTy G (subst1 B1 P) (subst1 B1' P) v'
            eqt2 = petBC u' v' sel P valP-A1
            -- Transport eqt2 from B1 to B0' using B0' = B1
            eqt2' : EqValTy G (subst1 B0' P) (subst1 B1' P) v'
            eqt2' = Eq-transport (\ X -> EqValTy G (subst1 X P) (subst1 B1' P) v')
                       (Eq-sym eqB0'B1) eqt2
            -- Coherent v' from selection
            cv' = coh-from-aU v' (FinMem-Selection-UCode b sel fmU1 cf1)
            -- Chain: EqValTy-trans at v'
        in EqValTy-trans v' cv' eqt1 eqt2'
      -- Build result
      resultCore = mkSigma A0 (mkSigma B0 (mkSigma A1' (mkSigma B1'
                     (mkSigma rA (mkSigma rC (mkSigma cf1 (mkSigma fmU1
                       (mkSigma eqDomAC petAC))))))))
  in mkSigma vtyA (mkSigma vtyC resultCore)

------------------------------------------------------------------------
-- EqVal-sym: symmetry of term equality
--
-- EqVal G M N A u a -> EqVal G N M A u a
-- Proved by case analysis on a, with recursion at PiCode.
------------------------------------------------------------------------

{-# TERMINATING #-}
EqVal-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u a : FinEl) -> Coherent u -> Coherent a ->
  EqVal G M N A u a -> EqVal G N M A u a
-- a = Bot: Top
EqVal-sym u Bot cu ca ev = tt
-- a = UCode: swap ValTy pair + EqValTy symmetry
EqVal-sym u UCode cu ca ev =
  mkSigma (fst (snd ev))
    (mkSigma (fst ev) (EqValTy-sym u cu (snd (snd ev))))
-- a = FunEl: Top
EqVal-sym u (FunEl h) cu ca ev = tt
-- a = PiCode, u = Bot/UCode/PiCode: Top
EqVal-sym Bot (PiCode b f) cu ca ev = tt
EqVal-sym UCode (PiCode b f) cu ca ev = tt
EqVal-sym (PiCode a' ff) (PiCode b f) cu ca ev = tt
-- a = PiCode b f, u = FunEl g: swap EqValPi
EqVal-sym {G = G} {M = M} {N = N} {A = A}
  (FunEl g) (PiCode b f) cu ca ev =
  let vty  = fst ev
      vpiM = fst (snd ev)
      vpiN = fst (snd (snd ev))
      epi  = snd (snd (snd ev))
      A0   = fst epi
      B0   = fst (snd epi)
      redA = fst (snd (snd epi))
      cg   = fst (snd (snd (snd epi)))
      fmg  = fst (snd (snd (snd (snd epi))))
      paev = snd (snd (snd (snd (snd epi))))
      -- CoherentFun f from Coherent (PiCode b f)
      cf = snd ca
      -- Swap PiAppEqVal: M <-> N
      paev' : PiAppEqVal G N M A0 B0 b f g
      paev' = \ u' v' sel P valP ->
        let body = paev u' v' sel P valP
            cu' = Coherent-Selection sel cg
            cv' = Coherent-Selection-val sel cg
            cev = Coherent-EvalFun f u' (cft-from-cf f cf) cu'
        in EqVal-sym v' (EvalFun f u') cv' cev body
      epi' = mkSigma A0 (mkSigma B0 (mkSigma redA (mkSigma cg
               (mkSigma fmg paev'))))
  in mkSigma vty (mkSigma vpiN (mkSigma vpiM epi'))

------------------------------------------------------------------------
-- Val/EqVal transport along EqValTy in the TYPE EXPRESSION position
-- (Lemma 8, second part)
--
-- Val-EqValTy-expr : EqValTy G A B a -> Val G M A u a -> Val G M B u a
-- EqVal-EqValTy-expr : EqValTy G A B a -> EqVal G M N A u a -> EqVal G M N B u a
--
-- Proved by mutual induction on the complexity of a.
-- A only appears when a = PiCode b f and u = FunEl g.
-- Recursive calls are at EvalFun f u' which is smaller than PiCode b f.
------------------------------------------------------------------------

{-# TERMINATING #-}

Val-EqValTy-expr : {n : Nat} {G : Ctx n} {A B M : Expr n}
  (u a : FinEl) -> Coherent u -> Coherent a ->
  EqValTy G A B a -> Val G M A u a -> Val G M B u a

EqVal-EqValTy-expr : {n : Nat} {G : Ctx n} {A B M N : Expr n}
  (u a : FinEl) -> Coherent u -> Coherent a ->
  EqValTy G A B a -> EqVal G M N A u a -> EqVal G M N B u a

------------------------------------------------------------------------
-- Val-EqValTy-expr: case split on a, then u at PiCode
------------------------------------------------------------------------

-- a = Bot/UCode/FunEl: A does not appear in Val
Val-EqValTy-expr u Bot cu ca eqv val = tt
Val-EqValTy-expr u UCode cu ca eqv val = val
Val-EqValTy-expr u (FunEl h) cu ca eqv val = tt
-- a = PiCode, u = Bot/UCode/PiCode: Val = Top
Val-EqValTy-expr Bot (PiCode b f) cu ca eqv val = tt
Val-EqValTy-expr UCode (PiCode b f) cu ca eqv val = tt
Val-EqValTy-expr (PiCode a' ff) (PiCode b f) cu ca eqv val = tt
-- a = PiCode b f, u = FunEl g: transport ValTy and ValPi
Val-EqValTy-expr {G = G} {A = A} {B = B} {M = M}
  (FunEl g) (PiCode b f) cu ca eqv val =
  let -- EqValTy G A B (PiCode b f) = Pair (ValTyPi G A) (Pair (ValTyPi G B) (EqValTyPi G A B))
      vtyA  = fst eqv
      vtyB  = fst (snd eqv)
      core  = snd (snd eqv)
      -- EqValTyPi components
      C   = fst core
      D   = fst (snd core)
      C'  = fst (snd (snd core))
      D'  = fst (snd (snd (snd core)))
      rA  = fst (snd (snd (snd (snd core))))
      rB  = fst (snd (snd (snd (snd (snd core)))))
      cf  = fst (snd (snd (snd (snd (snd (snd core))))))
      fmU = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
      tail8 = snd (snd (snd (snd (snd (snd (snd (snd core)))))))
      eqC = fst tail8
      pet = snd tail8
      -- Coherent b and FinMem b UCode from Coherent (PiCode b f)
      cb = fst ca
      bU = bU-from-cf-fmU f b cf fmU
      -- Input: Val G M A (FunEl g) (PiCode b f) =
      --   Pair (ValTyPi G A b f) (ValPi G M A g b f)
      -- Extract ValPi G M A g b f
      vpi  = snd val
      A0   = fst vpi
      B0   = fst (snd vpi)
      redA = fst (snd (snd vpi))
      cg   = fst (snd (snd (snd vpi)))
      fmg  = fst (snd (snd (snd (snd vpi))))
      pav  = fst (snd (snd (snd (snd (snd vpi)))))
      pae  = snd (snd (snd (snd (snd (snd vpi)))))
      -- Red-unique-Pi: Red G A (Pi A0 B0) U and Red G A (Pi C D) U
      uniq = Red-unique-Pi redA rA
      eqA0C : Eq A0 C
      eqA0C = fst uniq
      eqB0D : Eq B0 D
      eqB0D = snd uniq
      -- Transport PiAppVal from (A0, B0) = (C, D) to (C', D')
      pav-CD : PiAppVal G M C D b f g
      pav-CD = Eq-transport (\ X -> PiAppVal G M X D b f g) eqA0C
                 (Eq-transport (\ Y -> PiAppVal G M A0 Y b f g) eqB0D pav)
      pae-CD : PiAppEq G M C D b f g
      pae-CD = Eq-transport (\ X -> PiAppEq G M X D b f g) eqA0C
                 (Eq-transport (\ Y -> PiAppEq G M A0 Y b f g) eqB0D pae)
      -- PiAppVal transport from (C, D) to (C', D')
      pav' : PiAppVal G M C' D' b f g
      pav' = \ u' v' sel N valN ->
        let -- Convert domain: Val G N C' u' b -> Val G N C u' b
            valN-C = Val-EqValTy-fwd u' b cb (EqValTy-sym b cb eqC) valN
            -- Apply original
            body = pav-CD u' v' sel N valN-C
            -- Get EqValTy at EvalFun f u' via selectionBelow
            cu' = Coherent-Selection sel cg
            sb  = selectionBelow f u' cf cu'
            u-f = fst sb
            v-f = fst (snd sb)
            sel-f = fst (snd (snd sb))
            le-uf = fst (snd (snd (snd sb)))
            eq-ef = snd (snd (snd (snd sb)))
            fmu-f = FinMemAllU-Selection b sel-f fmU cf cb bU
            fmu' = FinMem-Selection b f sel fmg cg cb bU
            valN-uf = restrictVal G N C u' u-f b le-uf fmu-f fmu' valN-C
            eqt-vf = pet u-f v-f sel-f N valN-uf
            eqt-ef : EqValTy G (subst1 D N) (subst1 D' N) (EvalFun f u')
            eqt-ef = Eq-transport (\ w -> EqValTy G (subst1 D N) (subst1 D' N) w)
                       (Eq-sym eq-ef) eqt-vf
            cev = Coherent-EvalFun f u' (cft-from-cf f cf) cu'
            cv' = Coherent-Selection-val sel cg
        in Val-EqValTy-expr v' (EvalFun f u') cv' cev eqt-ef body
      -- PiAppEq transport from (C, D) to (C', D')
      pae' : PiAppEq G M C' D' b f g
      pae' = \ u' v' sel N1 N2 eqN ->
        let -- Convert domain: EqVal G N1 N2 C' u' b -> EqVal G N1 N2 C u' b
            eqN-C = EqVal-EqValTy-fwd u' b cb (EqValTy-sym b cb eqC) eqN
            -- Apply original
            body = pae-CD u' v' sel N1 N2 eqN-C
            -- Extract Val for pet
            valN1-C = Val-from-EqVal-first u' b eqN-C
            -- Get EqValTy at EvalFun f u' via selectionBelow
            cu' = Coherent-Selection sel cg
            sb  = selectionBelow f u' cf cu'
            u-f = fst sb
            v-f = fst (snd sb)
            sel-f = fst (snd (snd sb))
            le-uf = fst (snd (snd (snd sb)))
            eq-ef = snd (snd (snd (snd sb)))
            fmu-f = FinMemAllU-Selection b sel-f fmU cf cb bU
            fmu' = FinMem-Selection b f sel fmg cg cb bU
            valN1-uf = restrictVal G N1 C u' u-f b le-uf fmu-f fmu' valN1-C
            eqt-vf = pet u-f v-f sel-f N1 valN1-uf
            eqt-ef : EqValTy G (subst1 D N1) (subst1 D' N1) (EvalFun f u')
            eqt-ef = Eq-transport (\ w -> EqValTy G (subst1 D N1) (subst1 D' N1) w)
                       (Eq-sym eq-ef) eqt-vf
            cev = Coherent-EvalFun f u' (cft-from-cf f cf) cu'
            cv' = Coherent-Selection-val sel cg
        in EqVal-EqValTy-expr v' (EvalFun f u') cv' cev eqt-ef body
      -- Build output ValPi G M B g b f
      vpi' = mkSigma C' (mkSigma D' (mkSigma rB (mkSigma cg
               (mkSigma fmg (mkSigma pav' pae')))))
  in mkSigma vtyB vpi'

------------------------------------------------------------------------
-- EqVal-EqValTy-expr: case split on a, then u at PiCode
------------------------------------------------------------------------

-- a = Bot/UCode/FunEl: A does not appear in EqVal (or doesn't affect it)
EqVal-EqValTy-expr u Bot cu ca eqv ev = tt
EqVal-EqValTy-expr u UCode cu ca eqv ev = ev
EqVal-EqValTy-expr u (FunEl h) cu ca eqv ev = tt
-- a = PiCode, u = Bot/UCode/PiCode: EqVal = Top
EqVal-EqValTy-expr Bot (PiCode b f) cu ca eqv ev = tt
EqVal-EqValTy-expr UCode (PiCode b f) cu ca eqv ev = tt
EqVal-EqValTy-expr (PiCode a' ff) (PiCode b f) cu ca eqv ev = tt
-- a = PiCode b f, u = FunEl g: transport ValTy, ValPi (M and N), EqValPi
EqVal-EqValTy-expr {G = G} {A = A} {B = B} {M = M} {N = N}
  (FunEl g) (PiCode b f) cu ca eqv ev =
  let -- EqValTy components
      vtyA  = fst eqv
      vtyB  = fst (snd eqv)
      core  = snd (snd eqv)
      C   = fst core
      D   = fst (snd core)
      C'  = fst (snd (snd core))
      D'  = fst (snd (snd (snd core)))
      rA  = fst (snd (snd (snd (snd core))))
      rB  = fst (snd (snd (snd (snd (snd core)))))
      cf  = fst (snd (snd (snd (snd (snd (snd core))))))
      fmU = fst (snd (snd (snd (snd (snd (snd (snd core)))))))
      tail8 = snd (snd (snd (snd (snd (snd (snd (snd core)))))))
      eqC = fst tail8
      pet = snd tail8
      cb = fst ca
      bU = bU-from-cf-fmU f b cf fmU
      -- EqVal components: Pair (ValTy G A ...) (Pair (ValPi M) (Pair (ValPi N) (EqValPi)))
      vpiM = fst (snd ev)
      vpiN = fst (snd (snd ev))
      epi  = snd (snd (snd ev))
      -- EqValPi G M N A g b f
      A0   = fst epi
      B0   = fst (snd epi)
      redA = fst (snd (snd epi))
      cg   = fst (snd (snd (snd epi)))
      fmg  = fst (snd (snd (snd (snd epi))))
      paev = snd (snd (snd (snd (snd epi))))
      -- Red-unique-Pi
      uniq = Red-unique-Pi redA rA
      eqA0C : Eq A0 C
      eqA0C = fst uniq
      eqB0D : Eq B0 D
      eqB0D = snd uniq
      -- Transport PiAppEqVal from (A0, B0) = (C, D) to (C', D')
      paev-CD : PiAppEqVal G M N C D b f g
      paev-CD = Eq-transport (\ X -> PiAppEqVal G M N X D b f g) eqA0C
                  (Eq-transport (\ Y -> PiAppEqVal G M N A0 Y b f g) eqB0D paev)
      paev' : PiAppEqVal G M N C' D' b f g
      paev' = \ u' v' sel P valP ->
        let -- Convert domain: Val G P C' u' b -> Val G P C u' b
            valP-C = Val-EqValTy-fwd u' b cb (EqValTy-sym b cb eqC) valP
            -- Apply original
            body = paev-CD u' v' sel P valP-C
            -- Get EqValTy at EvalFun f u' via selectionBelow
            cu' = Coherent-Selection sel cg
            sb  = selectionBelow f u' cf cu'
            u-f = fst sb
            v-f = fst (snd sb)
            sel-f = fst (snd (snd sb))
            le-uf = fst (snd (snd (snd sb)))
            eq-ef = snd (snd (snd (snd sb)))
            fmu-f = FinMemAllU-Selection b sel-f fmU cf cb bU
            fmu' = FinMem-Selection b f sel fmg cg cb bU
            valP-uf = restrictVal G P C u' u-f b le-uf fmu-f fmu' valP-C
            eqt-vf = pet u-f v-f sel-f P valP-uf
            eqt-ef : EqValTy G (subst1 D P) (subst1 D' P) (EvalFun f u')
            eqt-ef = Eq-transport (\ w -> EqValTy G (subst1 D P) (subst1 D' P) w)
                       (Eq-sym eq-ef) eqt-vf
            cev = Coherent-EvalFun f u' (cft-from-cf f cf) cu'
            cv' = Coherent-Selection-val sel cg
        in EqVal-EqValTy-expr v' (EvalFun f u') cv' cev eqt-ef body
      -- Transport ValPi for M and N using Val-EqValTy-expr
      valM-B = Val-EqValTy-expr (FunEl g) (PiCode b f) cu ca eqv
                 (mkSigma (fst ev) vpiM)
      valN-B = Val-EqValTy-expr (FunEl g) (PiCode b f) cu ca eqv
                 (mkSigma (fst ev) vpiN)
      epi' = mkSigma C' (mkSigma D' (mkSigma rB (mkSigma cg
               (mkSigma fmg paev'))))
  in mkSigma vtyB (mkSigma (snd valM-B) (mkSigma (snd valN-B) epi'))

------------------------------------------------------------------------
-- EqVal-trans: transitivity of term equality
--
-- EqVal G M1 M2 A u a -> EqVal G M2 M3 A u a -> EqVal G M1 M3 A u a
--
-- Proved by induction on the complexity of a.
-- Recursive call at (v', EvalFun f u') for PiAppEqVal chaining.
------------------------------------------------------------------------

{-# TERMINATING #-}
EqVal-trans : {n : Nat} {G : Ctx n} {M1 M2 M3 A : Expr n}
  (u a : FinEl) -> Coherent u -> Coherent a ->
  EqVal G M1 M2 A u a -> EqVal G M2 M3 A u a -> EqVal G M1 M3 A u a
-- a = Bot: Top
EqVal-trans u Bot cu ca ev1 ev2 = tt
-- a = UCode: chain EqValTy
EqVal-trans u UCode cu ca ev1 ev2 =
  mkSigma (fst ev1) (mkSigma (fst (snd ev2))
    (EqValTy-trans u cu (snd (snd ev1)) (snd (snd ev2))))
-- a = FunEl: Top
EqVal-trans u (FunEl h) cu ca ev1 ev2 = tt
-- a = PiCode, u = Bot/UCode/PiCode: Top
EqVal-trans Bot (PiCode b f) cu ca ev1 ev2 = tt
EqVal-trans UCode (PiCode b f) cu ca ev1 ev2 = tt
EqVal-trans (PiCode a' ff) (PiCode b f) cu ca ev1 ev2 = tt
-- a = PiCode b f, u = FunEl g: chain EqValPi
EqVal-trans {G = G} {M1 = M1} {M2 = M2} {M3 = M3} {A = A}
  (FunEl g) (PiCode b f) cu ca ev1 ev2 =
  let -- From ev1: ValTy, ValPi M1, ValPi M2, EqValPi M1 M2
      vty   = fst ev1
      vpiM1 = fst (snd ev1)
      vpiM3 = fst (snd (snd ev2))
      epi1  = snd (snd (snd ev1))
      epi2  = snd (snd (snd ev2))
      -- EqValPi G M1 M2 A g b f
      Ax   = fst epi1
      Bx   = fst (snd epi1)
      redAx = fst (snd (snd epi1))
      cg     = fst (snd (snd (snd epi1)))
      fmg    = fst (snd (snd (snd (snd epi1))))
      paev1  = snd (snd (snd (snd (snd epi1))))
      -- EqValPi G M2 M3 A g b f
      Ay   = fst epi2
      By   = fst (snd epi2)
      redAy = fst (snd (snd epi2))
      paev2  = snd (snd (snd (snd (snd epi2))))
      -- Red-unique-Pi: Ax = Ay, Bx = By
      uniq = Red-unique-Pi redAx redAy
      eqA0 : Eq Ax Ay
      eqA0 = fst uniq
      eqB0 : Eq Bx By
      eqB0 = snd uniq
      -- Transport paev2 to use Ax, Bx
      paev2' : PiAppEqVal G M2 M3 Ax Bx b f g
      paev2' = Eq-transport (\ X -> PiAppEqVal G M2 M3 X Bx b f g) (Eq-sym eqA0)
                 (Eq-transport (\ Y -> PiAppEqVal G M2 M3 Ay Y b f g) (Eq-sym eqB0) paev2)
      -- CoherentFun f from Coherent (PiCode b f)
      cf = snd ca
      -- Chain PiAppEqVal
      paev' : PiAppEqVal G M1 M3 Ax Bx b f g
      paev' = \ u' v' sel P valP ->
        let body1 = paev1 u' v' sel P valP
            body2 = paev2' u' v' sel P valP
            cv' = Coherent-Selection-val sel cg
            cu' = Coherent-Selection sel cg
            cev = Coherent-EvalFun f u' (cft-from-cf f cf) cu'
        in EqVal-trans v' (EvalFun f u') cv' cev body1 body2
      epi' = mkSigma Ax (mkSigma Bx (mkSigma redAx (mkSigma cg
               (mkSigma fmg paev'))))
  in mkSigma vty (mkSigma vpiM1 (mkSigma vpiM3 epi'))
