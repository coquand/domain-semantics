{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ValiditySigma.agda
--
-- Logical relation (validity) for dependent type theory with
-- U : U, extended with Sigma types.
-- Parallel version of Validity.agda.
--
-- Defines:
--   Val / EqVal  -- term/equality validity, with SigmaCode/PairCode cases
--   ValTy/EqValTy -- type validity (= Val at UCode)
--   ValTyPi/EqValTyPi -- type validity at Pi-code
--   ValTySigma/EqValTySigma -- type validity at Sigma-code
--   PiEdge/SigmaEdge families
--   Val/EqVal at (PairCode, SigmaCode) = Top (simplifies monotonicity)
--
-- 0 postulates.
------------------------------------------------------------------------

module ValiditySigma where

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ;
              SigmaCode ; PairCode ; FinFun ;
              List ; nil ; cons ;
              isPos)
import RawSyntaxSigma as RS
open RS using (Expr ; Var ; U ; Pi ; Lam ; App ;
  MkPair ; Fst ; Snd ;
  wkExpr ; subst1 ; Fin ; fzero ; fsuc ;
  Sub ; substExpr ; liftSub ;
  Ren ; renExpr ; wkRen ; liftRen ; subst-ren ;
  subst-subst ; substExpr-ext ; liftSub-subst-ext ; Eq-trans)
open import TypingRulesSigma using (Ctx ; empty ; extend ; ConvTm ;
  conv-sym ; conv-trans)
open import ReductionSigma using (Red ; mkRed ; HeadRed ; HeadRed-trans ;
  HeadRed-App ; HeadRed-Fst ; HeadRed-Snd ;
  HeadRed-strip-Pi ; HeadRed-unique-Pi ;
  HeadRed-strip-Sigma ; HeadRed-unique-Sigma)
open import PaperSemanticsSigma using (applyEl ; EvalFun ; EvalFun-step ;
  leFinEl ; leFinEl-sound ;
  LeCode ; LeFunCode ; LeCode-Bot ; LeCode-Sup-lub ;
  LeCode-Sup-left ; LeCode-Sup-right ;
  LeCode-refl ; LeCode-trans ;
  Sup ; append ; Comp ; CompStepFun ; Coherent-Sup ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ; CoherentWith ; cft-from-cf ;
  Coherent-EvalFun ; EvalFun-mon ; EvalFun-mon-arg ;
  CoherentFun-append ; CoherentFunTail-append ;
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
  FinMemFun-append ; FinMem-Sup-element ;
  comp-EvalFun ; EvalFun-append-eq ; FinMemAllU-append-Sup ;
  LeFunCode-refl)
open import SelectionSigma public
open import RawSemanticsSigma using (absurd)

------------------------------------------------------------------------
-- FinMem-Coherent
------------------------------------------------------------------------

FinMem-Coherent : (u a : FinEl) -> FinMem u a -> Coherent u
FinMem-Coherent = FinMem-coh-u

------------------------------------------------------------------------
-- EvalFun-FinMem
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
  EvalFun-FinMem ps b f v (snd fmg) (CFTcons.tail-coh cg) cf allU cv mv
EvalFun-FinMem-step (suc n) p ps b f v eq fmg cg cf allU cv mv =
  let le-k = leFinEl-sound (fst p) v (Eq-transport isPos (Eq-sym eq) tt)
      cpv = CFTcons.val-coh cg
      cw = CFTcons.compat cg
      ih = EvalFun-FinMem ps b f v (snd fmg) (CFTcons.tail-coh cg) cf allU cv mv
      c-efp = Coherent-EvalFun f (fst p) cf (CFTcons.key-coh cg)
      c-efv = Coherent-EvalFun f v cf cv
      le-ef = EvalFun-mon-arg f (fst p) v le-k cf (CFTcons.key-coh cg) cv
      efvU = EvalFun-in-UCode f v b cf cv allU
      mem-p = finMem-upward (snd p) (EvalFun f (fst p)) (EvalFun f v)
                le-ef c-efp c-efv (snd (fst fmg)) efvU
      comp-pv = Comp-value-EvalFun p ps v le-k cv cpv cw
                  (coherentWith-to-compStepFun p ps cw)
  in FinMem-Sup-element (snd p) (EvalFun ps v) (EvalFun f v)
       comp-pv c-efv mem-p ih

------------------------------------------------------------------------
-- Validity relations (mutual, by structural recursion on a)
--
-- Extended with SigmaCode and PairCode.
-- Val/EqVal at (PairCode, SigmaCode) = Top (simplifies monotonicity).
-- Val/EqVal at SigmaCode for non-PairCode realizers:
--   Bot -> Top, others -> Top (unreachable when typed).
------------------------------------------------------------------------

-- Termination: by structural recursion on the code parameter `a`,
-- with the iterative-stage RANK in mind (NOT the size measure `rk` in
-- BasicSigma).  The PiCode/SigmaCode cases dispatch to ValTyPi /
-- ValTySigma whose body mentions ValTy at the inner code `b` with
-- RANK b < RANK (PiCode b f).  The syntactic-cons-counting `rk` does
-- NOT serve here (see RankCounterexamplesSigma); the intended RANK
-- does.
{-# TERMINATING #-}

-- Val G M A u a : term M has type A, with realizer u at code a, in context G
Val : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set

-- EqVal G M N A u a : M = N at type A, with realizer u at code a, in context G
EqVal : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
  FinEl -> FinEl -> Set

-- ValTy G M u : type validity (= Val G M U u UCode)
ValTy : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set

-- EqValTy G M N u : type equality validity
EqValTy : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set

-- ValTyPi G M b f : type validity at u = PiCode b f
ValTyPi : {n : Nat} -> Ctx n -> Expr n -> FinEl -> FinFun -> Set

-- EqValTyPi G M N b f
EqValTyPi : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
  FinEl -> FinFun -> Set

-- ValTySigma G M b f : type validity at u = SigmaCode b f
ValTySigma : {n : Nat} -> Ctx n -> Expr n -> FinEl -> FinFun -> Set

-- EqValTySigma G M N b f
EqValTySigma : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
  FinEl -> FinFun -> Set

-- ValPi G M A g b f : term validity at u = FunEl g, a = PiCode b f
ValPi : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
  FinFun -> FinEl -> FinFun -> Set

-- EqValPi G M N A g b f
EqValPi : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
  FinFun -> FinEl -> FinFun -> Set

-- PiEdgeVal G A B b f
PiEdgeVal : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set

-- PiEdgeEq G A B b f
PiEdgeEq : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set

-- PiEdgeEqTy G A B B' b f
PiEdgeEqTy : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> Expr (suc n) ->
  FinEl -> FinFun -> Set

-- PiAppVal G M A0 B0 b f g
PiAppVal : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) ->
  FinEl -> FinFun -> FinFun -> Set

-- PiAppEq G M A0 B0 b f g
PiAppEq : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) ->
  FinEl -> FinFun -> FinFun -> Set

-- PiAppEqVal G M N A0 B0 b f g
PiAppEqVal : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Expr (suc n) ->
  FinEl -> FinFun -> FinFun -> Set

-- SigmaEdgeVal G A B b f : codomain validity for Sigma
SigmaEdgeVal : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set

-- SigmaEdgeEq G A B b f : codomain equality for Sigma
SigmaEdgeEq : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set

-- SigmaEdgeEqTy G A B B' b f : heterogeneous codomain type equality for Sigma
SigmaEdgeEqTy : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> Expr (suc n) ->
  FinEl -> FinFun -> Set

------------------------------------------------------------------------
-- Definitions
------------------------------------------------------------------------

-- Val: case split on a, with u-split at PiCode and SigmaCode
Val G M A u Bot              = Top
Val G M A u UCode            = ValTy G M u
Val G M A u PropCode         = Top
Val G M A u (FunEl h)        = Top
Val G M A Bot            (PiCode b f) = Top
Val G M A UCode          (PiCode b f) = Top
Val G M A PropCode       (PiCode b f) = Top
Val G M A (FunEl g)      (PiCode b f) = Pair (ValTy G A (PiCode b f)) (ValPi G M A g b f)
Val G M A (PiCode a' f') (PiCode b f) = Top
Val G M A (SigmaCode a' f') (PiCode b f) = Top
Val G M A (PairCode u' v') (PiCode b f) = Top
-- SigmaCode: Val at (PairCode, SigmaCode) = Top
Val G M A Bot              (SigmaCode b f) = Top
Val G M A UCode            (SigmaCode b f) = Top
Val G M A PropCode         (SigmaCode b f) = Top
Val G M A (FunEl g)        (SigmaCode b f) = Top
Val G M A (PiCode a' f')  (SigmaCode b f) = Top
Val G M A (SigmaCode a' f') (SigmaCode b f) = Top
Val G M A (PairCode u' v') (SigmaCode b f) = Top
-- PairCode at a: Val always Top (unreachable when typed)
Val G M A u (PairCode x y) = Top

-- EqVal: case split on a, with u-split at PiCode and SigmaCode
EqVal G M N A u Bot              = Top
EqVal G M N A u UCode            = Pair (ValTy G M u) (Pair (ValTy G N u) (EqValTy G M N u))
EqVal G M N A u PropCode         = Top
EqVal G M N A u (FunEl h)        = Top
EqVal G M N A Bot            (PiCode b f) = Top
EqVal G M N A UCode          (PiCode b f) = Top
EqVal G M N A PropCode       (PiCode b f) = Top
EqVal G M N A (FunEl g)      (PiCode b f) =
  Pair (ValTy G A (PiCode b f))
       (Pair (ValPi G M A g b f)
             (Pair (ValPi G N A g b f)
                   (EqValPi G M N A g b f)))
EqVal G M N A (PiCode a' f') (PiCode b f) = Top
EqVal G M N A (SigmaCode a' f') (PiCode b f) = Top
EqVal G M N A (PairCode u' v') (PiCode b f) = Top
-- SigmaCode: EqVal at (PairCode, SigmaCode) = Top
EqVal G M N A Bot              (SigmaCode b f) = Top
EqVal G M N A UCode            (SigmaCode b f) = Top
EqVal G M N A PropCode         (SigmaCode b f) = Top
EqVal G M N A (FunEl g)        (SigmaCode b f) = Top
EqVal G M N A (PiCode a' f')  (SigmaCode b f) = Top
EqVal G M N A (SigmaCode a' f') (SigmaCode b f) = Top
EqVal G M N A (PairCode u' v') (SigmaCode b f) = Top
-- PairCode at a: EqVal always Top
EqVal G M N A u (PairCode x y) = Top

-- ValTy: case split on u (type validity = Val at UCode)
ValTy G M Bot              = Top
ValTy G M UCode            = Top
ValTy G M PropCode         = Top
ValTy G M (FunEl g)        = Top
ValTy G M (PiCode b f)    = ValTyPi G M b f
ValTy G M (SigmaCode b f) = ValTySigma G M b f
ValTy G M (PairCode u v)  = Top

-- EqValTy: case split on u
EqValTy G M N Bot              = Top
EqValTy G M N UCode            = Top
EqValTy G M N PropCode         = Top
EqValTy G M N (FunEl g)        = Top
EqValTy G M N (PiCode b f)    =
  Pair (ValTy G M (PiCode b f))
       (Pair (ValTy G N (PiCode b f))
             (EqValTyPi G M N b f))
EqValTy G M N (SigmaCode b f) =
  Pair (ValTy G M (SigmaCode b f))
       (Pair (ValTy G N (SigmaCode b f))
             (EqValTySigma G M N b f))
EqValTy G M N (PairCode u v)  = Top

-- PiEdgeVal: codomain validity (selection-based on f, uses v)
PiEdgeVal {n} G A B b f =
  (u v : FinEl) -> Selection f u v ->
  (N : Expr n) -> Val G N A u b ->
  ValTy G (subst1 B N) v

-- PiEdgeEq: codomain equality (selection-based on f, uses v)
PiEdgeEq {n} G A B b f =
  (u v : FinEl) -> Selection f u v ->
  (N1 N2 : Expr n) -> EqVal G N1 N2 A u b ->
  EqValTy G (subst1 B N1) (subst1 B N2) v

-- PiEdgeEqTy: heterogeneous codomain type equality
PiEdgeEqTy {n} G A B B' b f =
  (u v : FinEl) -> Selection f u v ->
  (P : Expr n) -> Val G P A u b ->
  EqValTy G (subst1 B P) (subst1 B' P) v

-- SigmaEdgeVal: codomain validity for Sigma (same type as PiEdge)
SigmaEdgeVal {n} G A B b f =
  (u v : FinEl) -> Selection f u v ->
  (N : Expr n) -> Val G N A u b ->
  ValTy G (subst1 B N) v

-- SigmaEdgeEq: codomain equality for Sigma
SigmaEdgeEq {n} G A B b f =
  (u v : FinEl) -> Selection f u v ->
  (N1 N2 : Expr n) -> EqVal G N1 N2 A u b ->
  EqValTy G (subst1 B N1) (subst1 B N2) v

-- SigmaEdgeEqTy: heterogeneous codomain type equality for Sigma
SigmaEdgeEqTy {n} G A B B' b f =
  (u v : FinEl) -> Selection f u v ->
  (P : Expr n) -> Val G P A u b ->
  EqValTy G (subst1 B P) (subst1 B' P) v

-- PiAppVal: function application validity (selection-based on g)
PiAppVal {n} G M A0 B0 b f g =
  (u v : FinEl) -> Selection g u v ->
  (N : Expr n) -> Val G N A0 u b ->
  Val G (App M N) (subst1 B0 N) v (EvalFun f u)

-- PiAppEq: function congruence (selection-based on g)
PiAppEq {n} G M A0 B0 b f g =
  (u v : FinEl) -> Selection g u v ->
  (N1 N2 : Expr n) -> EqVal G N1 N2 A0 u b ->
  EqVal G (App M N1) (App M N2) (subst1 B0 N1)
    v (EvalFun f u)

-- PiAppEqVal: extensional equality (selection-based on g)
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
  Sigma (CoherentFunTail f) \ _ ->
  Sigma (FinMemAllU f b) \ _ ->
  Pair (ValTy G A b)
       (Pair (PiEdgeVal G A B b f)
             (PiEdgeEq G A B b f))

-- EqValTyPi: core equality data at PiCode b f
EqValTyPi {n} G M N b f =
  Sigma (Expr n) \ A ->
  Sigma (Expr (suc n)) \ B ->
  Sigma (Expr n) \ A' ->
  Sigma (Expr (suc n)) \ B' ->
  Sigma (Red G M (Pi A B) U) \ _ ->
  Sigma (Red G N (Pi A' B') U) \ _ ->
  Sigma (CoherentFunTail f) \ _ ->
  Sigma (FinMemAllU f b) \ _ ->
  Pair (EqValTy G A A' b)
       (PiEdgeEqTy G A B B' b f)

-- ValTySigma: M is a type with Sigma-structure at (SigmaCode b f)
ValTySigma {n} G M b f =
  Sigma (Expr n) \ A ->
  Sigma (Expr (suc n)) \ B ->
  Sigma (Red G M (RS.Sigma A B) U) \ _ ->
  Sigma (CoherentFunTail f) \ _ ->
  Sigma (FinMemAllU f b) \ _ ->
  Pair (ValTy G A b)
       (Pair (SigmaEdgeVal G A B b f)
             (SigmaEdgeEq G A B b f))

-- EqValTySigma: core equality data at SigmaCode b f
EqValTySigma {n} G M N b f =
  Sigma (Expr n) \ A ->
  Sigma (Expr (suc n)) \ B ->
  Sigma (Expr n) \ A' ->
  Sigma (Expr (suc n)) \ B' ->
  Sigma (Red G M (RS.Sigma A B) U) \ _ ->
  Sigma (Red G N (RS.Sigma A' B') U) \ _ ->
  Sigma (CoherentFunTail f) \ _ ->
  Sigma (FinMemAllU f b) \ _ ->
  Pair (EqValTy G A A' b)
       (SigmaEdgeEqTy G A B B' b f)

-- ValPi: term M has type A at (FunEl g, PiCode b f)
ValPi {n} G M A g b f =
  Sigma (Expr n) \ A0 ->
  Sigma (Expr (suc n)) \ B0 ->
  Sigma (Red G A (Pi A0 B0) U) \ _ ->
  Sigma (CoherentFun g) \ _ ->
  Sigma (FinMemFun g b f) \ _ ->
  Pair (PiAppVal G M A0 B0 b f g)
       (PiAppEq G M A0 B0 b f g)

-- EqValPi: equality M = N at type A at (FunEl g, PiCode b f)
EqValPi {n} G M N A g b f =
  Sigma (Expr n) \ A0 ->
  Sigma (Expr (suc n)) \ B0 ->
  Sigma (Red G A (Pi A0 B0) U) \ _ ->
  Sigma (CoherentFun g) \ _ ->
  Sigma (FinMemFun g b f) \ _ ->
  PiAppEqVal G M N A0 B0 b f g

------------------------------------------------------------------------
-- Extract Val for first/second term from EqVal
------------------------------------------------------------------------

Val-from-EqVal-first : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u b : FinEl) -> EqVal G M N A u b -> Val G M A u b
Val-from-EqVal-first u Bot ev = tt
Val-from-EqVal-first u UCode ev = fst ev
Val-from-EqVal-first u PropCode ev = tt
Val-from-EqVal-first u (FunEl h) ev = tt
Val-from-EqVal-first Bot (PiCode b f) ev = tt
Val-from-EqVal-first UCode (PiCode b f) ev = tt
Val-from-EqVal-first PropCode (PiCode b f) ev = tt
Val-from-EqVal-first (FunEl g) (PiCode b f) ev =
  mkSigma (fst ev) (fst (snd ev))
Val-from-EqVal-first (PiCode a' f') (PiCode b f) ev = tt
Val-from-EqVal-first (SigmaCode a' f') (PiCode b f) ev = tt
Val-from-EqVal-first (PairCode u' v') (PiCode b f) ev = tt
Val-from-EqVal-first Bot (SigmaCode b f) ev = tt
Val-from-EqVal-first UCode (SigmaCode b f) ev = tt
Val-from-EqVal-first PropCode (SigmaCode b f) ev = tt
Val-from-EqVal-first (FunEl g) (SigmaCode b f) ev = tt
Val-from-EqVal-first (PiCode a' f') (SigmaCode b f) ev = tt
Val-from-EqVal-first (SigmaCode a' f') (SigmaCode b f) ev = tt
Val-from-EqVal-first (PairCode u' v') (SigmaCode b f) ev = tt
Val-from-EqVal-first u (PairCode x y) ev = tt

Val-from-EqVal-second : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u b : FinEl) -> EqVal G M N A u b -> Val G N A u b
Val-from-EqVal-second u Bot ev = tt
Val-from-EqVal-second u UCode ev = fst (snd ev)
Val-from-EqVal-second u PropCode ev = tt
Val-from-EqVal-second u (FunEl h) ev = tt
Val-from-EqVal-second Bot (PiCode b f) ev = tt
Val-from-EqVal-second UCode (PiCode b f) ev = tt
Val-from-EqVal-second PropCode (PiCode b f) ev = tt
Val-from-EqVal-second (FunEl g) (PiCode b f) ev =
  mkSigma (fst ev) (fst (snd (snd ev)))
Val-from-EqVal-second (PiCode a' f') (PiCode b f) ev = tt
Val-from-EqVal-second (SigmaCode a' f') (PiCode b f) ev = tt
Val-from-EqVal-second (PairCode u' v') (PiCode b f) ev = tt
Val-from-EqVal-second Bot (SigmaCode b f) ev = tt
Val-from-EqVal-second UCode (SigmaCode b f) ev = tt
Val-from-EqVal-second PropCode (SigmaCode b f) ev = tt
Val-from-EqVal-second (FunEl g) (SigmaCode b f) ev = tt
Val-from-EqVal-second (PiCode a' f') (SigmaCode b f) ev = tt
Val-from-EqVal-second (SigmaCode a' f') (SigmaCode b f) ev = tt
Val-from-EqVal-second (PairCode u' v') (SigmaCode b f) ev = tt
Val-from-EqVal-second u (PairCode x y) ev = tt

------------------------------------------------------------------------
-- Val-headred-expand / EqVal-headred-expand
------------------------------------------------------------------------

-- Termination: structural on the FinEl code parameter (Bot / UCode /
-- PropCode / FunEl base cases are immediate; PiCode/SigmaCode recurse
-- into the inner ValPi / ValTySigma payload which is well-founded by
-- record-field structure plus inner RANK on `b`).  Same iterative-
-- stage RANK story as the type-definition block at line ~125.
{-# TERMINATING #-}
mutual
  Val-headred-expand : {n : Nat} {G : Ctx n} {M M' T : Expr n}
    (u a : FinEl) -> HeadRed M' M ->
    Val G M T u a -> Val G M' T u a
  Val-headred-expand u Bot hr v = tt
  Val-headred-expand u UCode hr v =
    ValTy-headred-expand u hr v
  Val-headred-expand u PropCode hr v = tt
  Val-headred-expand u (FunEl h) hr v = tt
  Val-headred-expand Bot (PiCode b f) hr v = tt
  Val-headred-expand UCode (PiCode b f) hr v = tt
  Val-headred-expand PropCode (PiCode b f) hr v = tt
  Val-headred-expand (FunEl g) (PiCode b f) hr (mkSigma vty vpi) =
    mkSigma vty (ValPi-headred-expand g b f hr vpi)
  Val-headred-expand (PiCode a' f') (PiCode b f) hr v = tt
  Val-headred-expand (SigmaCode a' f') (PiCode b f) hr v = tt
  Val-headred-expand (PairCode u' v') (PiCode b f) hr v = tt
  Val-headred-expand Bot (SigmaCode b f) hr v = tt
  Val-headred-expand UCode (SigmaCode b f) hr v = tt
  Val-headred-expand PropCode (SigmaCode b f) hr v = tt
  Val-headred-expand (FunEl g) (SigmaCode b f) hr v = tt
  Val-headred-expand (PiCode a' f') (SigmaCode b f) hr v = tt
  Val-headred-expand (SigmaCode a' f') (SigmaCode b f) hr v = tt
  Val-headred-expand (PairCode u' v') (SigmaCode b f) hr v = tt
  Val-headred-expand u (PairCode x y) hr v = tt

  EqVal-headred-expand : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' T : Expr n}
    (u a : FinEl) -> HeadRed M1' M1 -> HeadRed M2' M2 ->
    EqVal G M1 M2 T u a -> EqVal G M1' M2' T u a
  EqVal-headred-expand u Bot hr1 hr2 v = tt
  EqVal-headred-expand u UCode hr1 hr2 (mkSigma vt1 (mkSigma vt2 eqvt)) =
    mkSigma (ValTy-headred-expand u hr1 vt1)
      (mkSigma (ValTy-headred-expand u hr2 vt2)
        (EqValTy-headred-expand u hr1 hr2 eqvt))
  EqVal-headred-expand u PropCode hr1 hr2 v = tt
  EqVal-headred-expand u (FunEl h) hr1 hr2 v = tt
  EqVal-headred-expand Bot (PiCode b f) hr1 hr2 v = tt
  EqVal-headred-expand UCode (PiCode b f) hr1 hr2 v = tt
  EqVal-headred-expand PropCode (PiCode b f) hr1 hr2 v = tt
  EqVal-headred-expand (FunEl g) (PiCode b f) hr1 hr2
    (mkSigma vty (mkSigma vp1 (mkSigma vp2 eqvp))) =
    mkSigma vty
      (mkSigma (ValPi-headred-expand g b f hr1 vp1)
        (mkSigma (ValPi-headred-expand g b f hr2 vp2)
          (EqValPi-headred-expand g b f hr1 hr2 eqvp)))
  EqVal-headred-expand (PiCode a' f') (PiCode b f) hr1 hr2 v = tt
  EqVal-headred-expand (SigmaCode a' f') (PiCode b f) hr1 hr2 v = tt
  EqVal-headred-expand (PairCode u' v') (PiCode b f) hr1 hr2 v = tt
  EqVal-headred-expand Bot (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-expand UCode (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-expand PropCode (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-expand (FunEl g) (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-expand (PiCode a' f') (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-expand (SigmaCode a' f') (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-expand (PairCode u' v') (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-expand u (PairCode x y) hr1 hr2 v = tt

  ValTy-headred-expand : {n : Nat} {G : Ctx n} {M M' : Expr n}
    (u : FinEl) -> HeadRed M' M ->
    ValTy G M u -> ValTy G M' u
  ValTy-headred-expand Bot hr v = tt
  ValTy-headred-expand UCode hr v = tt
  ValTy-headred-expand PropCode hr v = tt
  ValTy-headred-expand (FunEl g) hr v = tt
  ValTy-headred-expand (PiCode b f) hr
    (mkSigma A (mkSigma B (mkSigma (mkRed red) rest))) =
    mkSigma A (mkSigma B (mkSigma (mkRed (HeadRed-trans hr red)) rest))
  ValTy-headred-expand (SigmaCode b f) hr
    (mkSigma A (mkSigma B (mkSigma (mkRed red) rest))) =
    mkSigma A (mkSigma B (mkSigma (mkRed (HeadRed-trans hr red)) rest))
  ValTy-headred-expand (PairCode u v) hr val = tt

  EqValTy-headred-expand : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' : Expr n}
    (u : FinEl) -> HeadRed M1' M1 -> HeadRed M2' M2 ->
    EqValTy G M1 M2 u -> EqValTy G M1' M2' u
  EqValTy-headred-expand Bot hr1 hr2 v = tt
  EqValTy-headred-expand UCode hr1 hr2 v = tt
  EqValTy-headred-expand PropCode hr1 hr2 v = tt
  EqValTy-headred-expand (FunEl g) hr1 hr2 v = tt
  EqValTy-headred-expand (PiCode b f) hr1 hr2
    (mkSigma vt1 (mkSigma vt2
      (mkSigma A (mkSigma B (mkSigma A' (mkSigma B'
        (mkSigma (mkRed red1) (mkSigma (mkRed red2) rest)))))))) =
    mkSigma (ValTy-headred-expand (PiCode b f) hr1 vt1)
      (mkSigma (ValTy-headred-expand (PiCode b f) hr2 vt2)
        (mkSigma A (mkSigma B (mkSigma A' (mkSigma B'
          (mkSigma (mkRed (HeadRed-trans hr1 red1))
            (mkSigma (mkRed (HeadRed-trans hr2 red2)) rest)))))))
  EqValTy-headred-expand (SigmaCode b f) hr1 hr2
    (mkSigma vt1 (mkSigma vt2
      (mkSigma A (mkSigma B (mkSigma A' (mkSigma B'
        (mkSigma (mkRed red1) (mkSigma (mkRed red2) rest)))))))) =
    mkSigma (ValTy-headred-expand (SigmaCode b f) hr1 vt1)
      (mkSigma (ValTy-headred-expand (SigmaCode b f) hr2 vt2)
        (mkSigma A (mkSigma B (mkSigma A' (mkSigma B'
          (mkSigma (mkRed (HeadRed-trans hr1 red1))
            (mkSigma (mkRed (HeadRed-trans hr2 red2)) rest)))))))
  EqValTy-headred-expand (PairCode u v) hr1 hr2 val = tt

  ValPi-headred-expand : {n : Nat} {G : Ctx n} {M M' T : Expr n}
    (g0 : FinFun) (b : FinEl) (f : FinFun) ->
    HeadRed M' M -> ValPi G M T g0 b f -> ValPi G M' T g0 b f
  ValPi-headred-expand g0 b f hr
    (mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg
      (mkSigma pav pae)))))) =
    mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg
      (mkSigma (\ u v sel N valN ->
        Val-headred-expand v (EvalFun f u) (HeadRed-App hr)
          (pav u v sel N valN))
      (\ u v sel N1 N2 eqN ->
        EqVal-headred-expand v (EvalFun f u) (HeadRed-App hr) (HeadRed-App hr)
          (pae u v sel N1 N2 eqN)))))))

  EqValPi-headred-expand : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' T : Expr n}
    (g0 : FinFun) (b : FinEl) (f : FinFun) ->
    HeadRed M1' M1 -> HeadRed M2' M2 ->
    EqValPi G M1 M2 T g0 b f -> EqValPi G M1' M2' T g0 b f
  EqValPi-headred-expand g0 b f hr1 hr2
    (mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg peqv))))) =
    mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg
      (\ u v sel P valP ->
        EqVal-headred-expand v (EvalFun f u) (HeadRed-App hr1) (HeadRed-App hr2)
          (peqv u v sel P valP))))))

------------------------------------------------------------------------
-- Val-beta-expand / EqVal-beta-expand (derived)
------------------------------------------------------------------------

Val-beta-expand : {n : Nat} {G : Ctx n} {A : Expr n}
  {M : Expr (suc n)} {N T : Expr n}
  (u a : FinEl) ->
  Val G (subst1 M N) T u a -> Val G (App (Lam A M) N) T u a
Val-beta-expand u a = Val-headred-expand u a (ReductionSigma.headred-step ReductionSigma.headred-beta ReductionSigma.headred-refl)

EqVal-beta-expand : {n : Nat} {G : Ctx n} {A : Expr n}
  {M : Expr (suc n)} {N T : Expr n}
  (u a : FinEl) ->
  EqVal G (subst1 M N) (subst1 M N) T u a ->
  EqVal G (App (Lam A M) N) (App (Lam A M) N) T u a
EqVal-beta-expand u a =
  EqVal-headred-expand u a (ReductionSigma.headred-step ReductionSigma.headred-beta ReductionSigma.headred-refl)
                            (ReductionSigma.headred-step ReductionSigma.headred-beta ReductionSigma.headred-refl)

------------------------------------------------------------------------
-- Val-headred-contract / EqVal-headred-contract
------------------------------------------------------------------------

-- Termination: same shape as Val-headred-expand above -- structural on
-- the FinEl code parameter, with iterative-stage RANK on the inner
-- `b` in the PiCode/SigmaCode cases.
{-# TERMINATING #-}
mutual
  Val-headred-contract : {n : Nat} {G : Ctx n} {M M' T : Expr n}
    (u a : FinEl) -> HeadRed M M' ->
    Val G M T u a -> Val G M' T u a
  Val-headred-contract u Bot hr v = tt
  Val-headred-contract u UCode hr v =
    ValTy-headred-contract u hr v
  Val-headred-contract u PropCode hr v = tt
  Val-headred-contract u (FunEl h) hr v = tt
  Val-headred-contract Bot (PiCode b f) hr v = tt
  Val-headred-contract UCode (PiCode b f) hr v = tt
  Val-headred-contract PropCode (PiCode b f) hr v = tt
  Val-headred-contract (FunEl g) (PiCode b f) hr (mkSigma vty vpi) =
    mkSigma vty (ValPi-headred-contract g b f hr vpi)
  Val-headred-contract (PiCode a' f') (PiCode b f) hr v = tt
  Val-headred-contract (SigmaCode a' f') (PiCode b f) hr v = tt
  Val-headred-contract (PairCode u' v') (PiCode b f) hr v = tt
  Val-headred-contract Bot (SigmaCode b f) hr v = tt
  Val-headred-contract UCode (SigmaCode b f) hr v = tt
  Val-headred-contract PropCode (SigmaCode b f) hr v = tt
  Val-headred-contract (FunEl g) (SigmaCode b f) hr v = tt
  Val-headred-contract (PiCode a' f') (SigmaCode b f) hr v = tt
  Val-headred-contract (SigmaCode a' f') (SigmaCode b f) hr v = tt
  Val-headred-contract (PairCode u' v') (SigmaCode b f) hr v = tt
  Val-headred-contract u (PairCode x y) hr v = tt

  EqVal-headred-contract : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' T : Expr n}
    (u a : FinEl) -> HeadRed M1 M1' -> HeadRed M2 M2' ->
    EqVal G M1 M2 T u a -> EqVal G M1' M2' T u a
  EqVal-headred-contract u Bot hr1 hr2 v = tt
  EqVal-headred-contract u UCode hr1 hr2 (mkSigma vt1 (mkSigma vt2 eqvt)) =
    mkSigma (ValTy-headred-contract u hr1 vt1)
      (mkSigma (ValTy-headred-contract u hr2 vt2)
        (EqValTy-headred-contract u hr1 hr2 eqvt))
  EqVal-headred-contract u PropCode hr1 hr2 v = tt
  EqVal-headred-contract u (FunEl h) hr1 hr2 v = tt
  EqVal-headred-contract Bot (PiCode b f) hr1 hr2 v = tt
  EqVal-headred-contract UCode (PiCode b f) hr1 hr2 v = tt
  EqVal-headred-contract PropCode (PiCode b f) hr1 hr2 v = tt
  EqVal-headred-contract (FunEl g) (PiCode b f) hr1 hr2
    (mkSigma vty (mkSigma vp1 (mkSigma vp2 eqvp))) =
    mkSigma vty
      (mkSigma (ValPi-headred-contract g b f hr1 vp1)
        (mkSigma (ValPi-headred-contract g b f hr2 vp2)
          (EqValPi-headred-contract g b f hr1 hr2 eqvp)))
  EqVal-headred-contract (PiCode a' f') (PiCode b f) hr1 hr2 v = tt
  EqVal-headred-contract (SigmaCode a' f') (PiCode b f) hr1 hr2 v = tt
  EqVal-headred-contract (PairCode u' v') (PiCode b f) hr1 hr2 v = tt
  EqVal-headred-contract Bot (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-contract UCode (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-contract PropCode (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-contract (FunEl g) (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-contract (PiCode a' f') (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-contract (SigmaCode a' f') (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-contract (PairCode u' v') (SigmaCode b f) hr1 hr2 v = tt
  EqVal-headred-contract u (PairCode x y) hr1 hr2 v = tt

  ValTy-headred-contract : {n : Nat} {G : Ctx n} {M M' : Expr n}
    (u : FinEl) -> HeadRed M M' ->
    ValTy G M u -> ValTy G M' u
  ValTy-headred-contract Bot hr v = tt
  ValTy-headred-contract UCode hr v = tt
  ValTy-headred-contract PropCode hr v = tt
  ValTy-headred-contract (FunEl g) hr v = tt
  ValTy-headred-contract (PiCode b f) hr
    (mkSigma A (mkSigma B (mkSigma (mkRed red) rest))) =
    mkSigma A (mkSigma B (mkSigma (mkRed (HeadRed-strip-Pi hr red)) rest))
  ValTy-headred-contract (SigmaCode b f) hr
    (mkSigma A (mkSigma B (mkSigma (mkRed red) rest))) =
    mkSigma A (mkSigma B (mkSigma (mkRed (HeadRed-strip-Sigma hr red)) rest))
  ValTy-headred-contract (PairCode u v) hr val = tt

  EqValTy-headred-contract : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' : Expr n}
    (u : FinEl) -> HeadRed M1 M1' -> HeadRed M2 M2' ->
    EqValTy G M1 M2 u -> EqValTy G M1' M2' u
  EqValTy-headred-contract Bot hr1 hr2 v = tt
  EqValTy-headred-contract UCode hr1 hr2 v = tt
  EqValTy-headred-contract PropCode hr1 hr2 v = tt
  EqValTy-headred-contract (FunEl g) hr1 hr2 v = tt
  EqValTy-headred-contract (PiCode b f) hr1 hr2
    (mkSigma vt1 (mkSigma vt2
      (mkSigma A (mkSigma B (mkSigma A' (mkSigma B'
        (mkSigma (mkRed red1) (mkSigma (mkRed red2) rest)))))))) =
    mkSigma (ValTy-headred-contract (PiCode b f) hr1 vt1)
      (mkSigma (ValTy-headred-contract (PiCode b f) hr2 vt2)
        (mkSigma A (mkSigma B (mkSigma A' (mkSigma B'
          (mkSigma (mkRed (HeadRed-strip-Pi hr1 red1))
            (mkSigma (mkRed (HeadRed-strip-Pi hr2 red2)) rest)))))))
  EqValTy-headred-contract (SigmaCode b f) hr1 hr2
    (mkSigma vt1 (mkSigma vt2
      (mkSigma A (mkSigma B (mkSigma A' (mkSigma B'
        (mkSigma (mkRed red1) (mkSigma (mkRed red2) rest)))))))) =
    mkSigma (ValTy-headred-contract (SigmaCode b f) hr1 vt1)
      (mkSigma (ValTy-headred-contract (SigmaCode b f) hr2 vt2)
        (mkSigma A (mkSigma B (mkSigma A' (mkSigma B'
          (mkSigma (mkRed (HeadRed-strip-Sigma hr1 red1))
            (mkSigma (mkRed (HeadRed-strip-Sigma hr2 red2)) rest)))))))
  EqValTy-headred-contract (PairCode u v) hr1 hr2 val = tt

  ValPi-headred-contract : {n : Nat} {G : Ctx n} {M M' T : Expr n}
    (g0 : FinFun) (b : FinEl) (f : FinFun) ->
    HeadRed M M' -> ValPi G M T g0 b f -> ValPi G M' T g0 b f
  ValPi-headred-contract g0 b f hr
    (mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg
      (mkSigma pav pae)))))) =
    mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg
      (mkSigma (\ u v sel N valN ->
        Val-headred-contract v (EvalFun f u) (HeadRed-App hr)
          (pav u v sel N valN))
      (\ u v sel N1 N2 eqN ->
        EqVal-headred-contract v (EvalFun f u) (HeadRed-App hr) (HeadRed-App hr)
          (pae u v sel N1 N2 eqN)))))))

  EqValPi-headred-contract : {n : Nat} {G : Ctx n} {M1 M2 M1' M2' T : Expr n}
    (g0 : FinFun) (b : FinEl) (f : FinFun) ->
    HeadRed M1 M1' -> HeadRed M2 M2' ->
    EqValPi G M1 M2 T g0 b f -> EqValPi G M1' M2' T g0 b f
  EqValPi-headred-contract g0 b f hr1 hr2
    (mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg peqv))))) =
    mkSigma A0 (mkSigma B0 (mkSigma red (mkSigma cg (mkSigma fmg
      (\ u v sel P valP ->
        EqVal-headred-contract v (EvalFun f u) (HeadRed-App hr1) (HeadRed-App hr2)
          (peqv u v sel P valP))))))

------------------------------------------------------------------------
-- Val-Bot / EqVal-Bot
------------------------------------------------------------------------

Val-Bot : {n : Nat} (G : Ctx n) (M A : Expr n) (a : FinEl) -> Val G M A Bot a
Val-Bot G M A Bot              = tt
Val-Bot G M A UCode            = tt
Val-Bot G M A PropCode         = tt
Val-Bot G M A (FunEl g)        = tt
Val-Bot G M A (PiCode b f)    = tt
Val-Bot G M A (SigmaCode b f) = tt
Val-Bot G M A (PairCode x y) = tt

EqVal-Bot : {n : Nat} (G : Ctx n) (M N A : Expr n) (a : FinEl) -> EqVal G M N A Bot a
EqVal-Bot G M N A Bot              = tt
EqVal-Bot G M N A UCode            = mkSigma tt (mkSigma tt tt)
EqVal-Bot G M N A PropCode         = tt
EqVal-Bot G M N A (FunEl g)        = tt
EqVal-Bot G M N A (PiCode b f)    = tt
EqVal-Bot G M N A (SigmaCode b f) = tt
EqVal-Bot G M N A (PairCode x y) = tt

------------------------------------------------------------------------
-- Red-unique-Pi / Red-unique-Sigma
------------------------------------------------------------------------

Red-unique-Pi : {n : Nat} {G : Ctx n} {A B B' : Expr n}
  {F : Expr (suc n)} {F' : Expr (suc n)} ->
  Red G A (Pi B F) U -> Red G A (Pi B' F') U ->
  Pair (Eq B B') (Eq F F')
Red-unique-Pi (mkRed r1) (mkRed r2) = HeadRed-unique-Pi r1 r2

Red-unique-Sigma : {n : Nat} {G : Ctx n} {A B B' : Expr n}
  {F : Expr (suc n)} {F' : Expr (suc n)} ->
  Red G A (RS.Sigma B F) U -> Red G A (RS.Sigma B' F') U ->
  Pair (Eq B B') (Eq F F')
Red-unique-Sigma (mkRed r1) (mkRed r2) = HeadRed-unique-Sigma r1 r2

-- Derive FinMem b UCode from CoherentFun f and FinMemAllU f b
bU-from-cf-fmU : (f : FinFun) (b : FinEl) -> CoherentFun f -> FinMemAllU f b -> FinMem b UCode
bU-from-cf-fmU nil         b ()
bU-from-cf-fmU (cons p ps) b cf fmU = FinMem-a-in-U (fst p) b (fst (fst fmU))

-- Derive FinMem b UCode from CoherentFun g and FinMemFun g b f
bU-from-cf-fmFun : (g : FinFun) (b : FinEl) (f : FinFun) -> CoherentFun g -> FinMemFun g b f -> FinMem b UCode
bU-from-cf-fmFun nil         b f ()
bU-from-cf-fmFun (cons p ps) b f cg fmFun = FinMem-a-in-U (fst p) b (fst (fst fmFun))

