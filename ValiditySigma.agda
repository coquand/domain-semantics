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
