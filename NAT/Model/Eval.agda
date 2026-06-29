{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- RawSemanticsSigma.agda
--
-- Relational semantics extended with Sigma types.
-- Parallel version of RawSemantics.agda.
--
-- New EvalRel cases:
--   Sigma A B → SigmaCode (like Pi → PiCode)
--   MkPair M N → PairCode (like Lam → FunEl)
--   Fst M → fstEl result (projection)
--   Snd M → sndEl result (projection)
--
-- 0 postulates.
------------------------------------------------------------------------

module NAT.Model.Eval where

import NAT.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ;
              Pair ; List ; nil ; cons ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; FinFun)
open import NAT.Domain.Kernel using (LeCode ; LeCode-refl ; LeCode-trans ; LeCode-Bot ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ; cft-from-cf ;
  NotBot ; Coherent-singleton-key ; Coherent-singleton-val ;
  FinMem ; FinMemAllU ; FinMem-coh-u ; FinMem-a-in-U ; Sup ; Sup-Bot-r ; Sup-Bot-l ;
  Comp ; CompFun ; CompStepFun ; CompStepStep ;
  comp-Bot-r ; comp-Bot-l ; Comp-down ; Comp-sym ; NotBot-Sup-Comp ;
  Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub ;
  LeCode-Comp ;
  EvalFun ; EvalFun-mon ; EvalFun-mon-arg ; comp-EvalFun ; Coherent-EvalFun ;
  EvalFun-append-eq ;
  CoherentFun-append ; CoherentFunTail-append ; FinMem-Sup-element ;
  finMem-Sup-left ; finMem-Sup-right ;
  finMem-upward ; LeFunCode ; LeFunCode-refl ; append)
open import NAT.Model.Selection using (Selection ; Edge ; EdgeIn ; here ; there ;
  sel-nil ; sel-take ; sel-skip ; sel-skip-all ;
  Coherent-Selection ; Coherent-Selection-val ;
  singleton-selection ; Selection-le-EvalFun ; selectionBelow ;
  FinMemAllU-Selection)
open import NAT.Syntax.Raw

------------------------------------------------------------------------
-- Part 1: Finite environments
------------------------------------------------------------------------

data EnvApprox : Nat -> Set where
  emptyEnv  : EnvApprox zero
  extendEnv : {n : Nat} -> EnvApprox n -> FinEl -> EnvApprox (suc n)

lookupEnv : {n : Nat} -> Fin n -> EnvApprox n -> FinEl
lookupEnv fzero    (extendEnv rho v) = v
lookupEnv (fsuc i) (extendEnv rho v) = lookupEnv i rho

------------------------------------------------------------------------
-- Part 1b: Approx — Kleene approximant combinator for Y (fixpoint).
--
-- STANDALONE, structural recursion on the Nat index n.  Not mutual with
-- EvalRel.  `step p u` is supplied at the use-site as
--   \ p u -> EvalRel g rho (FunEl (cons (mkSigma p u) nil))
-- i.e. "g maps p to u".  Y_0 = Bot, Y_{n+1} = g (Y_n).
-- This is the rank/stage-stratification trick (cf. Validity.Stratified)
-- applied to the fixpoint: the union over the explicit Kleene index n
-- replaces a TERMINATING pragma.
------------------------------------------------------------------------

Approx : (FinEl -> FinEl -> Set) -> Nat -> FinEl -> Set
Approx step zero    u = Pair (Coherent u) (LeCode u Bot)
Approx step (suc k) u = Sigma FinEl (\ p -> Pair (Approx step k p) (step p u))

-- Coherence: induction on the index, using the step's value-coherence.
Approx-coh : (step : FinEl -> FinEl -> Set)
  -> ((p w : FinEl) -> step p w -> Coherent w)
  -> (k : Nat) (u : FinEl) -> Approx step k u -> Coherent u
Approx-coh step sc zero    u ev = fst ev
Approx-coh step sc (suc k) u ev = sc (fst ev) u (snd (snd ev))

-- Step relabelling: transport along a pointwise implication of steps.
Approx-mon : (step step' : FinEl -> FinEl -> Set)
  -> ((p w : FinEl) -> step p w -> step' p w)
  -> (k : Nat) (u : FinEl) -> Approx step k u -> Approx step' k u
Approx-mon step step' sm zero    u ev = ev
Approx-mon step step' sm (suc k) u ev =
  mkSigma (fst ev) (mkSigma (Approx-mon step step' sm k (fst ev) (fst (snd ev)))
                            (sm (fst ev) u (snd (snd ev))))

-- Downward closure at a non-Bot target, preserving the index.
Approx-down : (step : FinEl -> FinEl -> Set)
  -> ((p w w' : FinEl) -> Coherent w' -> NotBot w' -> step p w -> LeCode w' w -> step p w')
  -> (k : Nat) (u u' : FinEl) -> Coherent u' -> NotBot u' ->
     Approx step k u -> LeCode u' u -> Approx step k u'
Approx-down step sd zero    u u' cu' nb ev le =
  mkSigma cu' (LeCode-trans u' u Bot cu' (fst ev) tt le (snd ev))
Approx-down step sd (suc k) u u' cu' nb ev le =
  mkSigma (fst ev) (mkSigma (fst (snd ev))
                            (sd (fst ev) u u' cu' nb (snd (snd ev)) le))

-- Compatibility: induction on both indices, using the step's Comp law.
Approx-Comp : (step : FinEl -> FinEl -> Set)
  -> ((p1 w1 p2 w2 : FinEl) -> Comp p1 p2 -> step p1 w1 -> step p2 w2 -> Comp w1 w2)
  -> (k1 k2 : Nat) (u v : FinEl) -> Approx step k1 u -> Approx step k2 v -> Comp u v
Approx-Comp step sC zero     k2       u v ev1 ev2 =
  Comp-down u Bot v (snd ev1) (comp-Bot-l v)
Approx-Comp step sC (suc k1) zero     u v ev1 ev2 =
  Comp-sym v u (Comp-down v Bot u (snd ev2) (comp-Bot-l u))
Approx-Comp step sC (suc k1) (suc k2) u v ev1 ev2 =
  sC (fst ev1) u (fst ev2) v
     (Approx-Comp step sC k1 k2 (fst ev1) (fst ev2) (fst (snd ev1)) (fst (snd ev2)))
     (snd (snd ev1)) (snd (snd ev2))

------------------------------------------------------------------------
-- Part 2: EvalRel
------------------------------------------------------------------------

EvalRel : {n : Nat} -> Expr n -> EnvApprox n -> FinEl -> Set

-- CaseBranch a b rho c w : "c is below (caseNat-of w with zero-branch a, succ-branch b)".
-- Mirrors how App applies a singleton function: for w = SucEl v, the succ-branch b
-- (a function value) is applied to the predecessor v.
CaseBranch : {n : Nat} -> Expr n -> Expr n -> EnvApprox n -> FinEl -> FinEl -> Set

-- Variables
EvalRel (Var i) rho b = Pair (Coherent b) (LeCode b (lookupEnv i rho))

-- Universe
EvalRel U rho b = Pair (Coherent b) (LeCode b UCode)

-- Application
EvalRel (App M N) rho Bot = Top
EvalRel (App M N) rho UCode =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v UCode) nil))))
EvalRel (App M N) rho (FunEl g') =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v (FunEl g')) nil))))
EvalRel (App M N) rho (PiCode a' f') =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v (PiCode a' f')) nil))))

-- Lambda
EvalRel (Lam A M) rho Bot = Top
EvalRel (Lam A M) rho (FunEl g) =
  Sigma FinEl (\ a ->
    Pair (CoherentFun g)
      (Pair (FinMem a UCode)
        (Pair (EvalRel A rho a)
          ((u v : FinEl) ->
            Selection g u v ->
            Sigma FinEl (\ x ->
              Pair (LeCode x u)
                   (Pair (FinMem x a)
                         (EvalRel M (extendEnv rho x) v)))))))
EvalRel (Lam A M) rho UCode         = Empty
EvalRel (Lam A M) rho (PiCode a f)  = Empty

-- Pi
EvalRel (Pi A B) rho Bot = Top
EvalRel (Pi A B) rho (PiCode a f) =
  Pair (Coherent (PiCode a f))
    (Pair (EvalRel A rho a)
      (Sigma FinEl (\ a' ->
        Pair (EvalRel A rho a')
          ((u v : FinEl) ->
            Selection f u v ->
            Sigma FinEl (\ x ->
              Pair (LeCode x u)
                   (Pair (FinMem x a')
                         (EvalRel B (extendEnv rho x) v)))))))
EvalRel (Pi A B) rho UCode          = Empty
EvalRel (Pi A B) rho (FunEl g)      = Empty

-- Y g : fixpoint.  Union over the Kleene index of the approximants
-- Y_0 = Bot, Y_{n+1} = g (Y_n).  The "step" is single-edge application of g.
EvalRel (Y g) rho u =
  Sigma Nat (\ k ->
    Approx (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil))) k u)

-- App at Nat-value result codes (same shape as the other App clauses)
EvalRel (App M N) rho NatCode =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v NatCode) nil))))
EvalRel (App M N) rho ZeroEl =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v ZeroEl) nil))))
EvalRel (App M N) rho (SucEl w) =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v (SucEl w)) nil))))
-- Lam / Pi are never Nat values
EvalRel (Lam A M) rho NatCode    = Empty
EvalRel (Lam A M) rho ZeroEl     = Empty
EvalRel (Lam A M) rho (SucEl w)  = Empty
EvalRel (Pi A B) rho NatCode     = Empty
EvalRel (Pi A B) rho ZeroEl      = Empty
EvalRel (Pi A B) rho (SucEl w)   = Empty

-- Nat type : atom code NatCode (like U at UCode)
EvalRel NatT rho b = Pair (Coherent b) (LeCode b NatCode)

-- Zero : atom value ZeroEl
EvalRel Zero rho b = Pair (Coherent b) (LeCode b ZeroEl)

-- Suc m : SucEl of m's value; b <= SucEl v for some approximant v of m
EvalRel (Suc m) rho b =
  Pair (Coherent b) (Sigma FinEl (\ v -> Pair (EvalRel m rho v) (LeCode b (SucEl v))))

-- caseNat M a b : some value w of M, with c below the corresponding branch
EvalRel (Case M a b) rho c =
  Sigma FinEl (\ w -> Pair (EvalRel M rho w) (CaseBranch a b rho c w))

CaseBranch a b rho c Bot          = Pair (Coherent c) (LeCode c Bot)
CaseBranch a b rho c UCode        = Empty
CaseBranch a b rho c (FunEl g)    = Empty
CaseBranch a b rho c (PiCode d f) = Empty
CaseBranch a b rho c NatCode      = Empty
CaseBranch a b rho c ZeroEl       = EvalRel a rho c
CaseBranch a b rho c (SucEl v)    = EvalRel b rho (FunEl (cons (mkSigma v c) nil))

------------------------------------------------------------------------
-- CoherentFun-LeBot-absurd
------------------------------------------------------------------------

mutual
  absurd : {A : Set} -> Empty -> A
  absurd ()

  CoherentFun-LeBot-absurd : (g : FinFun) -> CoherentFun g -> LeFunCode g nil -> Empty
  CoherentFun-LeBot-absurd nil cf lf = cf
  CoherentFun-LeBot-absurd (cons p ps) cf lf =
    Coherent-val-LeBot-absurd (snd p) (mkSigma (CFTcons.val-coh cf) (CFTcons.val-nbot cf)) (fst lf)

  Coherent-val-LeBot-absurd : (v : FinEl) -> Pair (Coherent v) (NotBot v) -> LeCode v Bot -> Empty
  Coherent-val-LeBot-absurd Bot cnb le = snd cnb
  Coherent-val-LeBot-absurd UCode cnb ()
  Coherent-val-LeBot-absurd (PiCode a f) cnb ()
  Coherent-val-LeBot-absurd (FunEl h) cnb ()

------------------------------------------------------------------------
-- Part 3: Coherence extraction
------------------------------------------------------------------------

EvalRel-coh : {n : Nat} (M : Expr n) (rho : EnvApprox n) (u : FinEl) ->
  EvalRel M rho u -> Coherent u

CaseBranch-coh : {n : Nat} (a b : Expr n) (rho : EnvApprox n) (c w : FinEl) ->
  CaseBranch a b rho c w -> Coherent c
CaseBranch-coh a b rho c Bot          cb = fst cb
CaseBranch-coh a b rho c UCode        ()
CaseBranch-coh a b rho c (FunEl g)    ()
CaseBranch-coh a b rho c (PiCode d f) ()
CaseBranch-coh a b rho c NatCode      ()
CaseBranch-coh a b rho c ZeroEl       cb = EvalRel-coh a rho c cb
CaseBranch-coh a b rho c (SucEl v)    cb =
  Coherent-singleton-val v c
    (EvalRel-coh b rho (FunEl (cons (mkSigma v c) nil)) cb)

EvalRel-coh (Var i) rho u ev = fst ev
EvalRel-coh U rho u ev = fst ev
-- App
EvalRel-coh (App M N) rho Bot ev = tt
EvalRel-coh (App M N) rho UCode ev = tt
EvalRel-coh (App M N) rho (FunEl g') ev =
  Coherent-singleton-val (fst ev) (FunEl g')
    (EvalRel-coh M rho (FunEl (cons (mkSigma (fst ev) (FunEl g')) nil)) (snd (snd ev)))
EvalRel-coh (App M N) rho (PiCode a' f') ev =
  Coherent-singleton-val (fst ev) (PiCode a' f')
    (EvalRel-coh M rho (FunEl (cons (mkSigma (fst ev) (PiCode a' f')) nil)) (snd (snd ev)))
-- Lam
EvalRel-coh (Lam A M) rho Bot ev = tt
EvalRel-coh (Lam A M) rho (FunEl g) ev = fst (snd ev)
EvalRel-coh (Lam A M) rho UCode ()
EvalRel-coh (Lam A M) rho (PiCode a f) ()
-- Pi
EvalRel-coh (Pi A B) rho Bot ev = tt
EvalRel-coh (Pi A B) rho (PiCode a f) ev = fst ev
EvalRel-coh (Pi A B) rho UCode ()
EvalRel-coh (Pi A B) rho (FunEl g) ()
EvalRel-coh (Y g) rho u ev =
  Approx-coh (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil)))
    (\ p w sw -> Coherent-singleton-val p w
       (EvalRel-coh g rho (FunEl (cons (mkSigma p w) nil)) sw))
    (fst ev) u (snd ev)
-- App at Nat-value result codes
EvalRel-coh (App M N) rho NatCode ev =
  Coherent-singleton-val (fst ev) NatCode
    (EvalRel-coh M rho (FunEl (cons (mkSigma (fst ev) NatCode) nil)) (snd (snd ev)))
EvalRel-coh (App M N) rho ZeroEl ev =
  Coherent-singleton-val (fst ev) ZeroEl
    (EvalRel-coh M rho (FunEl (cons (mkSigma (fst ev) ZeroEl) nil)) (snd (snd ev)))
EvalRel-coh (App M N) rho (SucEl w) ev =
  Coherent-singleton-val (fst ev) (SucEl w)
    (EvalRel-coh M rho (FunEl (cons (mkSigma (fst ev) (SucEl w)) nil)) (snd (snd ev)))
EvalRel-coh (Lam A M) rho NatCode   ()
EvalRel-coh (Lam A M) rho ZeroEl    ()
EvalRel-coh (Lam A M) rho (SucEl w) ()
EvalRel-coh (Pi A B) rho NatCode    ()
EvalRel-coh (Pi A B) rho ZeroEl     ()
EvalRel-coh (Pi A B) rho (SucEl w)  ()
-- Nat / Zero / Suc / Case
EvalRel-coh NatT rho u ev = fst ev
EvalRel-coh Zero rho u ev = fst ev
EvalRel-coh (Suc m) rho u ev = fst ev
EvalRel-coh (Case M a b) rho c ev =
  CaseBranch-coh a b rho c (fst ev) (snd (snd ev))

------------------------------------------------------------------------
-- Environment infrastructure (unchanged from original)
------------------------------------------------------------------------

CoherentEnv : {n : Nat} -> EnvApprox n -> Set
CoherentEnv emptyEnv = Top
CoherentEnv (extendEnv rho u) = Pair (CoherentEnv rho) (Coherent u)

lookupEnv-coh : {n : Nat} (i : Fin n) (rho : EnvApprox n) ->
  CoherentEnv rho -> Coherent (lookupEnv i rho)
lookupEnv-coh fzero    (extendEnv rho u) crho = snd crho
lookupEnv-coh (fsuc i) (extendEnv rho u) crho = lookupEnv-coh i rho (fst crho)

EnvLe : {n : Nat} -> EnvApprox n -> EnvApprox n -> Set
EnvLe emptyEnv emptyEnv = Top
EnvLe (extendEnv rho u) (extendEnv rho' u') =
  Pair (EnvLe rho rho')
       (Pair (Coherent u) (Pair (Coherent u') (LeCode u u')))

lookupEnv-coh-left : {n : Nat} (i : Fin n) (rho rho' : EnvApprox n) ->
  EnvLe rho rho' -> Coherent (lookupEnv i rho)
lookupEnv-coh-left fzero    (extendEnv rho u) (extendEnv rho' u') envle =
  fst (snd envle)
lookupEnv-coh-left (fsuc i) (extendEnv rho u) (extendEnv rho' u') envle =
  lookupEnv-coh-left i rho rho' (fst envle)

lookupEnv-coh-right : {n : Nat} (i : Fin n) (rho rho' : EnvApprox n) ->
  EnvLe rho rho' -> Coherent (lookupEnv i rho')
lookupEnv-coh-right fzero    (extendEnv rho u) (extendEnv rho' u') envle =
  fst (snd (snd envle))
lookupEnv-coh-right (fsuc i) (extendEnv rho u) (extendEnv rho' u') envle =
  lookupEnv-coh-right i rho rho' (fst envle)

lookupEnv-mon : {n : Nat} (i : Fin n) (rho rho' : EnvApprox n) ->
  EnvLe rho rho' -> LeCode (lookupEnv i rho) (lookupEnv i rho')
lookupEnv-mon fzero    (extendEnv rho u) (extendEnv rho' u') envle =
  snd (snd (snd envle))
lookupEnv-mon (fsuc i) (extendEnv rho u) (extendEnv rho' u') envle =
  lookupEnv-mon i rho rho' (fst envle)

EnvLe-extend : {n : Nat} (rho rho' : EnvApprox n) (x : FinEl) ->
  EnvLe rho rho' -> Coherent x ->
  EnvLe (extendEnv rho x) (extendEnv rho' x)
EnvLe-extend rho rho' x envle cx =
  mkSigma envle (mkSigma cx (mkSigma cx (LeCode-refl x cx)))

EnvLe-refl : {n : Nat} (rho : EnvApprox n) -> CoherentEnv rho -> EnvLe rho rho
EnvLe-refl emptyEnv crho = tt
EnvLe-refl (extendEnv rho u) crho =
  mkSigma (EnvLe-refl rho (fst crho))
          (mkSigma (snd crho) (mkSigma (snd crho) (LeCode-refl u (snd crho))))

EnvLe-extend-left : {n : Nat} (rho : EnvApprox n) (x y : FinEl) ->
  CoherentEnv rho -> Comp x y -> Coherent x -> Coherent y ->
  EnvLe (extendEnv rho x) (extendEnv rho (Sup x y))
EnvLe-extend-left rho x y crho comp cx cy =
  mkSigma (EnvLe-refl rho crho)
          (mkSigma cx (mkSigma (Coherent-Sup x y comp cx cy)
                               (LeCode-Sup-left x y comp cx cy)))

EnvLe-extend-right : {n : Nat} (rho : EnvApprox n) (x y : FinEl) ->
  CoherentEnv rho -> Comp x y -> Coherent x -> Coherent y ->
  EnvLe (extendEnv rho y) (extendEnv rho (Sup x y))
EnvLe-extend-right rho x y crho comp cx cy =
  mkSigma (EnvLe-refl rho crho)
          (mkSigma cy (mkSigma (Coherent-Sup x y comp cx cy)
                               (LeCode-Sup-right x y comp cx cy)))

------------------------------------------------------------------------
-- EvalRel-Bot
------------------------------------------------------------------------

EvalRel-Bot : {n : Nat} (M : Expr n) (rho : EnvApprox n) ->
  EvalRel M rho Bot
EvalRel-Bot (Var i) rho = mkSigma tt tt
EvalRel-Bot U rho = mkSigma tt tt
EvalRel-Bot (App M N) rho = tt
EvalRel-Bot (Lam A M) rho = tt
EvalRel-Bot (Pi A B) rho = tt
EvalRel-Bot (Y g) rho = mkSigma zero (mkSigma tt (LeCode-Bot Bot))
EvalRel-Bot NatT rho = mkSigma tt tt
EvalRel-Bot Zero rho = mkSigma tt tt
EvalRel-Bot (Suc m) rho = mkSigma tt (mkSigma Bot (mkSigma (EvalRel-Bot m rho) tt))
EvalRel-Bot (Case M a b) rho =
  mkSigma Bot (mkSigma (EvalRel-Bot M rho) (mkSigma tt tt))

------------------------------------------------------------------------
-- EvalRel-mon-env
------------------------------------------------------------------------

EvalRel-mon-env : {n : Nat} (M : Expr n) (rho rho' : EnvApprox n) (u : FinEl) ->
  EvalRel M rho u -> EnvLe rho rho' -> EvalRel M rho' u

CaseBranch-mon-env : {n : Nat} (a b : Expr n) (rho rho' : EnvApprox n) (c w : FinEl) ->
  CaseBranch a b rho c w -> EnvLe rho rho' -> CaseBranch a b rho' c w
CaseBranch-mon-env a b rho rho' c Bot          cb envle = cb
CaseBranch-mon-env a b rho rho' c UCode        () envle
CaseBranch-mon-env a b rho rho' c (FunEl g)    () envle
CaseBranch-mon-env a b rho rho' c (PiCode d f) () envle
CaseBranch-mon-env a b rho rho' c NatCode      () envle
CaseBranch-mon-env a b rho rho' c ZeroEl       cb envle =
  EvalRel-mon-env a rho rho' c cb envle
CaseBranch-mon-env a b rho rho' c (SucEl v)    cb envle =
  EvalRel-mon-env b rho rho' (FunEl (cons (mkSigma v c) nil)) cb envle

EvalRel-mon-env (Var i) rho rho' u ev envle =
  mkSigma (fst ev) (LeCode-trans u (lookupEnv i rho) (lookupEnv i rho')
    (fst ev) (lookupEnv-coh-left i rho rho' envle)
    (lookupEnv-coh-right i rho rho' envle) (snd ev) (lookupEnv-mon i rho rho' envle))
EvalRel-mon-env U rho rho' u ev envle = ev
-- App
EvalRel-mon-env (App M N) rho rho' Bot ev envle = tt
EvalRel-mon-env (App M N) rho rho' UCode ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
EvalRel-mon-env (App M N) rho rho' (FunEl g') ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
EvalRel-mon-env (App M N) rho rho' (PiCode a' f') ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
EvalRel-mon-env (App M N) rho rho' NatCode ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
EvalRel-mon-env (App M N) rho rho' ZeroEl ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
EvalRel-mon-env (App M N) rho rho' (SucEl w) ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
EvalRel-mon-env (Lam A M) rho rho' NatCode   () envle
EvalRel-mon-env (Lam A M) rho rho' ZeroEl     () envle
EvalRel-mon-env (Lam A M) rho rho' (SucEl w)  () envle
EvalRel-mon-env (Pi A B) rho rho' NatCode    () envle
EvalRel-mon-env (Pi A B) rho rho' ZeroEl      () envle
EvalRel-mon-env (Pi A B) rho rho' (SucEl w)   () envle
-- Lam
EvalRel-mon-env (Lam A M) rho rho' Bot ev envle = tt
EvalRel-mon-env (Lam A M) rho rho' (FunEl g) ev envle =
  let a    = fst ev
      cg   = fst (snd ev)
      aU   = fst (snd (snd ev))
      evA  = fst (snd (snd (snd ev)))
      body = snd (snd (snd (snd ev)))
  in mkSigma a (mkSigma cg (mkSigma aU
       (mkSigma (EvalRel-mon-env A rho rho' a evA envle)
         (\ u v sel ->
            let w      = body u v sel
                x      = fst w
                le-x-u = fst (snd w)
                mem    = fst (snd (snd w))
                evM    = snd (snd (snd w))
                cx     = FinMem-coh-u x a mem
                envle' = EnvLe-extend rho rho' x envle cx
            in mkSigma x (mkSigma le-x-u (mkSigma mem
                 (EvalRel-mon-env M (extendEnv rho x) (extendEnv rho' x)
                    v evM envle')))))))
EvalRel-mon-env (Lam A M) rho rho' UCode () envle
EvalRel-mon-env (Lam A M) rho rho' (PiCode a f) () envle
-- Pi
EvalRel-mon-env (Pi A B) rho rho' Bot ev envle = tt
EvalRel-mon-env (Pi A B) rho rho' (PiCode a f) ev envle =
  let caf  = fst ev
      evA  = fst (snd ev)
      a'   = fst (snd (snd ev))
      evA' = fst (snd (snd (snd ev)))
      body = snd (snd (snd (snd ev)))
  in mkSigma caf (mkSigma (EvalRel-mon-env A rho rho' a evA envle)
       (mkSigma a' (mkSigma (EvalRel-mon-env A rho rho' a' evA' envle)
       (\ u v sel ->
          let w      = body u v sel
              x      = fst w
              le-x-u = fst (snd w)
              mem    = fst (snd (snd w))
              evB    = snd (snd (snd w))
              cx     = FinMem-coh-u x a' mem
              envle' = EnvLe-extend rho rho' x envle cx
          in mkSigma x (mkSigma le-x-u (mkSigma mem
               (EvalRel-mon-env B (extendEnv rho x) (extendEnv rho' x)
                  v evB envle')))))))
EvalRel-mon-env (Pi A B) rho rho' UCode () envle
EvalRel-mon-env (Pi A B) rho rho' (FunEl g) () envle
EvalRel-mon-env (Y g) rho rho' u ev envle =
  mkSigma (fst ev)
    (Approx-mon (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil)))
                (\ p w -> EvalRel g rho' (FunEl (cons (mkSigma p w) nil)))
       (\ p w sw -> EvalRel-mon-env g rho rho' (FunEl (cons (mkSigma p w) nil)) sw envle)
       (fst ev) u (snd ev))
-- Nat / Zero / Suc / Case
EvalRel-mon-env NatT rho rho' u ev envle = ev
EvalRel-mon-env Zero rho rho' u ev envle = ev
EvalRel-mon-env (Suc m) rho rho' u ev envle =
  mkSigma (fst ev)
    (mkSigma (fst (snd ev))
      (mkSigma (EvalRel-mon-env m rho rho' (fst (snd ev)) (fst (snd (snd ev))) envle)
               (snd (snd (snd ev)))))
EvalRel-mon-env (Case M a b) rho rho' c ev envle =
  mkSigma (fst ev)
    (mkSigma (EvalRel-mon-env M rho rho' (fst ev) (fst (snd ev)) envle)
             (CaseBranch-mon-env a b rho rho' c (fst ev) (snd (snd ev)) envle))

------------------------------------------------------------------------
-- App-decompose
------------------------------------------------------------------------

App-decompose : {n : Nat} (M N : Expr n) (rho : EnvApprox n)
  (u : FinEl) -> NotBot u ->
  EvalRel (App M N) rho u ->
  S.Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v u) nil))))
App-decompose M N rho UCode        nb ev = ev
App-decompose M N rho (FunEl g')   nb ev = ev
App-decompose M N rho (PiCode a f) nb ev = ev
App-decompose M N rho NatCode      nb ev = ev
App-decompose M N rho ZeroEl       nb ev = ev
App-decompose M N rho (SucEl w)    nb ev = ev

------------------------------------------------------------------------
-- Edgewise lemmas
------------------------------------------------------------------------

Lam-edgewise : {n : Nat} (A : Expr n) (M : Expr (suc n))
  (rho : EnvApprox n) (g : FinFun) ->
  EvalRel (Lam A M) rho (FunEl g) ->
  S.Sigma FinEl (\ a ->
    Pair (CoherentFun g)
      (Pair (FinMem a UCode)
        (Pair (EvalRel A rho a)
          ((p : Edge) -> EdgeIn p g ->
            S.Sigma FinEl (\ x ->
              Pair (LeCode x (fst p))
                   (Pair (FinMem x a)
                         (EvalRel M (extendEnv rho x) (snd p))))))))
Lam-edgewise A M rho g ev =
  let a    = fst ev
      cg   = fst (snd ev)
      aU   = fst (snd (snd ev))
      evA  = fst (snd (snd (snd ev)))
      body = snd (snd (snd (snd ev)))
  in mkSigma a (mkSigma cg (mkSigma aU (mkSigma evA
       (\ p ein ->
          let sel = singleton-selection p g ein
              w   = body (Sup (fst p) Bot) (Sup (snd p) Bot) sel
              x   = fst w
              lxu = Eq-transport (LeCode x) (Sup-Bot-r (fst p)) (fst (snd w))
              mem = fst (snd (snd w))
              evM = Eq-transport (EvalRel M (extendEnv rho x)) (Sup-Bot-r (snd p)) (snd (snd (snd w)))
          in mkSigma x (mkSigma lxu (mkSigma mem evM))))))

Pi-edgewise : {n : Nat} (A : Expr n) (B : Expr (suc n))
  (rho : EnvApprox n) (a : FinEl) (f : FinFun) ->
  EvalRel (Pi A B) rho (PiCode a f) ->
  Pair (Coherent (PiCode a f))
    (Pair (EvalRel A rho a)
      (S.Sigma FinEl (\ a' ->
        Pair (EvalRel A rho a')
          ((p : Edge) -> EdgeIn p f ->
            S.Sigma FinEl (\ x ->
              Pair (LeCode x (fst p))
                   (Pair (FinMem x a')
                         (EvalRel B (extendEnv rho x) (snd p))))))))
Pi-edgewise A B rho a f ev =
  let caf  = fst ev
      evA  = fst (snd ev)
      a'   = fst (snd (snd ev))
      evA' = fst (snd (snd (snd ev)))
      body = snd (snd (snd (snd ev)))
  in mkSigma caf (mkSigma evA (mkSigma a' (mkSigma evA'
       (\ p ein ->
          let sel = singleton-selection p f ein
              w   = body (Sup (fst p) Bot) (Sup (snd p) Bot) sel
              x   = fst w
              lxu = Eq-transport (LeCode x) (Sup-Bot-r (fst p)) (fst (snd w))
              mem = fst (snd (snd w))
              evB = Eq-transport (EvalRel B (extendEnv rho x)) (Sup-Bot-r (snd p)) (snd (snd (snd w)))
          in mkSigma x (mkSigma lxu (mkSigma mem evB))))))

------------------------------------------------------------------------
-- Helpers for EvalRel-Comp
------------------------------------------------------------------------

App-Comp-helper : {n : Nat} (M N : Expr n) (rho : EnvApprox n) ->
  (IH-M : (u v : FinEl) -> EvalRel M rho u -> EvalRel M rho v -> Comp u v) ->
  (IH-N : (u v : FinEl) -> EvalRel N rho u -> EvalRel N rho v -> Comp u v) ->
  (u1 u2 : FinEl) ->
  (v1 : FinEl) -> EvalRel N rho v1 ->
  EvalRel M rho (FunEl (cons (mkSigma v1 u1) nil)) ->
  (v2 : FinEl) -> EvalRel N rho v2 ->
  EvalRel M rho (FunEl (cons (mkSigma v2 u2) nil)) ->
  Comp u1 u2
App-Comp-helper M N rho ihm ihn u1 u2 v1 evN1 evM1 v2 evN2 evM2 =
  let comp-fg = ihm (FunEl (cons (mkSigma v1 u1) nil))
                    (FunEl (cons (mkSigma v2 u2) nil)) evM1 evM2
      step = fst (fst comp-fg)
      comp-v = ihn v1 v2 evN1 evN2
  in step comp-v

Comp-via-body : {n : Nat} (M : Expr (suc n)) (rho : EnvApprox n)
  (x1 x2 : FinEl) (v1 v2 : FinEl) ->
  CoherentEnv rho -> Comp x1 x2 -> Coherent x1 -> Coherent x2 ->
  EvalRel M (extendEnv rho x1) v1 ->
  EvalRel M (extendEnv rho x2) v2 ->
  ((rho' : EnvApprox (suc n)) -> CoherentEnv rho' ->
    EvalRel M rho' v1 -> EvalRel M rho' v2 -> Comp v1 v2) ->
  Comp v1 v2
Comp-via-body M rho x1 x2 v1 v2 crho comp cx1 cx2 ev1 ev2 ih =
  let c-sup = Coherent-Sup x1 x2 comp cx1 cx2
      envle1 = EnvLe-extend-left rho x1 x2 crho comp cx1 cx2
      envle2 = EnvLe-extend-right rho x1 x2 crho comp cx1 cx2
      ev1' = EvalRel-mon-env M (extendEnv rho x1) (extendEnv rho (Sup x1 x2)) v1 ev1 envle1
      ev2' = EvalRel-mon-env M (extendEnv rho x2) (extendEnv rho (Sup x1 x2)) v2 ev2 envle2
      crho' = mkSigma crho c-sup
  in ih (extendEnv rho (Sup x1 x2)) crho' ev1' ev2'

Lam-CompStepFun : {n : Nat} (M : Expr (suc n)) (rho : EnvApprox n)
  (a1 a2 : FinEl)
  (s : Edge) (g2 : FinFun) ->
  CoherentEnv rho -> CoherentFunTail g2 ->
  S.Sigma FinEl (\ xs ->
    Pair (LeCode xs (fst s)) (Pair (FinMem xs a1) (EvalRel M (extendEnv rho xs) (snd s)))) ->
  ((t : Edge) -> EdgeIn t g2 ->
    S.Sigma FinEl (\ xt ->
      Pair (LeCode xt (fst t)) (Pair (FinMem xt a2) (EvalRel M (extendEnv rho xt) (snd t))))) ->
  ((rho' : EnvApprox (suc n)) -> CoherentEnv rho' ->
    (u v : FinEl) -> EvalRel M rho' u -> EvalRel M rho' v -> Comp u v) ->
  CompStepFun s g2
Lam-CompStepFun M rho a1 a2 s nil crho cg2 ws wf ih = tt
Lam-CompStepFun M rho a1 a2 s (cons t rest) crho cg2 ws wf ih =
  let xs    = fst ws
      le-xs = fst (snd ws)
      mem-s = fst (snd (snd ws))
      ev-s  = snd (snd (snd ws))
      wt    = wf t here
      xt    = fst wt
      le-xt = fst (snd wt)
      mem-t = fst (snd (snd wt))
      ev-t  = snd (snd (snd wt))
      step : CompStepStep s t
      step comp-keys =
        let cxs    = FinMem-coh-u xs a1 mem-s
            cxt    = FinMem-coh-u xt a2 mem-t
            step-a = Comp-down xs (fst s) (fst t) le-xs comp-keys
            step-b = Comp-down xt (fst t) xs le-xt (Comp-sym xs (fst t) step-a)
            comp-x = Comp-sym xt xs step-b
        in Comp-via-body M rho xs xt (snd s) (snd t) crho comp-x cxs cxt ev-s ev-t
             (\ rho' crho' ev1 ev2 -> ih rho' crho' (snd s) (snd t) ev1 ev2)
      tail = Lam-CompStepFun M rho a1 a2 s rest crho (CFTcons.tail-coh cg2)
               ws (\ t' ein -> wf t' (there ein)) ih
  in mkSigma step tail

Lam-CompFun : {n : Nat} (M : Expr (suc n)) (rho : EnvApprox n)
  (a1 a2 : FinEl)
  (g1 g2 : FinFun) ->
  CoherentEnv rho -> CoherentFunTail g1 -> CoherentFunTail g2 ->
  ((s : Edge) -> EdgeIn s g1 ->
    S.Sigma FinEl (\ xs ->
      Pair (LeCode xs (fst s)) (Pair (FinMem xs a1) (EvalRel M (extendEnv rho xs) (snd s))))) ->
  ((t : Edge) -> EdgeIn t g2 ->
    S.Sigma FinEl (\ xt ->
      Pair (LeCode xt (fst t)) (Pair (FinMem xt a2) (EvalRel M (extendEnv rho xt) (snd t))))) ->
  ((rho' : EnvApprox (suc n)) -> CoherentEnv rho' ->
    (u v : FinEl) -> EvalRel M rho' u -> EvalRel M rho' v -> Comp u v) ->
  CompFun g1 g2
Lam-CompFun M rho a1 a2 nil g2 crho cg1 cg2 wf1 wf2 ih = tt
Lam-CompFun M rho a1 a2 (cons s rest) g2 crho cg1 cg2 wf1 wf2 ih =
  mkSigma (Lam-CompStepFun M rho a1 a2 s g2 crho cg2
             (wf1 s here) wf2 ih)
          (Lam-CompFun M rho a1 a2 rest g2 crho (CFTcons.tail-coh cg1) cg2
             (\ s' ein -> wf1 s' (there ein)) wf2 ih)

LeFunCode-Sup-pair :
  (v1 u1 v2 u2 : FinEl) ->
  Comp v1 v2 -> Comp u1 u2 ->
  CoherentFun (cons (mkSigma v1 u1) (cons (mkSigma v2 u2) nil)) ->
  Coherent (Sup v1 v2) ->
  LeFunCode (cons (mkSigma (Sup v1 v2) (Sup u1 u2)) nil)
            (cons (mkSigma v1 u1) (cons (mkSigma v2 u2) nil))
LeFunCode-Sup-pair v1 u1 v2 u2 comp-v comp-u cf c-supv =
  let sel-inner = sel-take (comp-Bot-r v2) (comp-Bot-r u2) (sel-skip-all nil)
      cv2  = CFTcons.key-coh (CFTcons.tail-coh cf)
      cu2  = CFTcons.val-coh (CFTcons.tail-coh cf)
      comp-v1-sv2 = Eq-transport (Comp v1) (Eq-sym (Sup-Bot-r v2)) comp-v
      comp-u1-su2 = Eq-transport (Comp u1) (Eq-sym (Sup-Bot-r u2)) comp-u
      sel-both = sel-take comp-v1-sv2 comp-u1-su2 sel-inner
      eq-key = Eq-transport (\ z -> Eq (Sup v1 (Sup v2 Bot)) (Sup v1 z)) (Sup-Bot-r v2) refl
      eq-val = Eq-transport (\ z -> Eq (Sup u1 (Sup u2 Bot)) (Sup u1 z)) (Sup-Bot-r u2) refl
      g2 = cons (mkSigma v1 u1) (cons (mkSigma v2 u2) nil)
      ctf = cft-from-cf g2 cf
      lf-refl = LeFunCode-refl g2 ctf
      c-key = Eq-transport Coherent (Eq-sym eq-key) c-supv
      le-raw = Selection-le-EvalFun g2 sel-both lf-refl cf cf c-key
      c-sup-u = Eq-transport Coherent (Eq-sym eq-val) (Coherent-Sup u1 u2 comp-u (CFTcons.val-coh cf) cu2)
      c-ef = Coherent-EvalFun g2 (Sup v1 (Sup v2 Bot)) ctf c-key
      c-ef' = Eq-transport (\ z -> Coherent (EvalFun g2 z)) eq-key c-ef
      le-trans = Eq-transport (\ z -> LeCode z (EvalFun g2 (Sup v1 (Sup v2 Bot)))) eq-val le-raw
      le-result = Eq-transport (\ z -> LeCode (Sup u1 u2) (EvalFun g2 z)) eq-key le-trans
  in mkSigma le-result tt

-- Comp-mono : if u <= w1, v <= w2 and w1, w2 are compatible, then u, v
-- are compatible (both sit below Sup w1 w2).
Comp-mono : (u v w1 w2 : FinEl) ->
  Coherent u -> Coherent v -> Coherent w1 -> Coherent w2 ->
  LeCode u w1 -> LeCode v w2 -> Comp w1 w2 -> Comp u v
Comp-mono u v w1 w2 cu cv cw1 cw2 le1 le2 comp =
  let c-sup = Coherent-Sup w1 w2 comp cw1 cw2
      le-w1 = LeCode-Sup-left w1 w2 comp cw1 cw2
      le-w2 = LeCode-Sup-right w1 w2 comp cw1 cw2
      le-u  = LeCode-trans u w1 (Sup w1 w2) cu cw1 c-sup le1 le-w1
      le-v  = LeCode-trans v w2 (Sup w1 w2) cv cw2 c-sup le2 le-w2
  in LeCode-Comp u v (Sup w1 w2) c-sup le-u le-v

------------------------------------------------------------------------
-- EvalRel-Comp
------------------------------------------------------------------------

EvalRel-Comp : {n : Nat} (M : Expr n) (rho : EnvApprox n) ->
  CoherentEnv rho -> (u v : FinEl) ->
  EvalRel M rho u -> EvalRel M rho v -> Comp u v

-- CaseBranch-Comp : compatibility of two case-branch witnesses at
-- compatible scrutinee values w1, w2.
CaseBranch-Comp : {n : Nat} (a b : Expr n) (rho : EnvApprox n) ->
  CoherentEnv rho ->
  ((x y : FinEl) -> EvalRel a rho x -> EvalRel a rho y -> Comp x y) ->
  ((x y : FinEl) -> EvalRel b rho x -> EvalRel b rho y -> Comp x y) ->
  (u v w1 w2 : FinEl) -> Comp w1 w2 ->
  CaseBranch a b rho u w1 -> CaseBranch a b rho v w2 -> Comp u v
CaseBranch-Comp a b rho crho iha ihb u v Bot w2 cw cb1 cb2 =
  Comp-down u Bot v (snd cb1) (comp-Bot-l v)
CaseBranch-Comp a b rho crho iha ihb u v UCode w2 cw () cb2
CaseBranch-Comp a b rho crho iha ihb u v (FunEl g) w2 cw () cb2
CaseBranch-Comp a b rho crho iha ihb u v (PiCode d f) w2 cw () cb2
CaseBranch-Comp a b rho crho iha ihb u v NatCode w2 cw () cb2
CaseBranch-Comp a b rho crho iha ihb u v ZeroEl Bot cw cb1 cb2 =
  Comp-sym v u (Comp-down v Bot u (snd cb2) (comp-Bot-l u))
CaseBranch-Comp a b rho crho iha ihb u v ZeroEl UCode () cb1 cb2
CaseBranch-Comp a b rho crho iha ihb u v ZeroEl (FunEl g) () cb1 cb2
CaseBranch-Comp a b rho crho iha ihb u v ZeroEl (PiCode d f) () cb1 cb2
CaseBranch-Comp a b rho crho iha ihb u v ZeroEl NatCode () cb1 cb2
CaseBranch-Comp a b rho crho iha ihb u v ZeroEl ZeroEl cw cb1 cb2 =
  iha u v cb1 cb2
CaseBranch-Comp a b rho crho iha ihb u v ZeroEl (SucEl p2) () cb1 cb2
CaseBranch-Comp a b rho crho iha ihb u v (SucEl p1) Bot cw cb1 cb2 =
  Comp-sym v u (Comp-down v Bot u (snd cb2) (comp-Bot-l u))
CaseBranch-Comp a b rho crho iha ihb u v (SucEl p1) UCode () cb1 cb2
CaseBranch-Comp a b rho crho iha ihb u v (SucEl p1) (FunEl g) () cb1 cb2
CaseBranch-Comp a b rho crho iha ihb u v (SucEl p1) (PiCode d f) () cb1 cb2
CaseBranch-Comp a b rho crho iha ihb u v (SucEl p1) NatCode () cb1 cb2
CaseBranch-Comp a b rho crho iha ihb u v (SucEl p1) ZeroEl () cb1 cb2
CaseBranch-Comp a b rho crho iha ihb u v (SucEl p1) (SucEl p2) cw cb1 cb2 =
  let comp-fg = ihb (FunEl (cons (mkSigma p1 u) nil))
                    (FunEl (cons (mkSigma p2 v) nil)) cb1 cb2
  in fst (fst comp-fg) cw

EvalRel-Comp (Var i) rho crho u v ev1 ev2 =
  LeCode-Comp u v (lookupEnv i rho) (lookupEnv-coh i rho crho) (snd ev1) (snd ev2)
EvalRel-Comp U rho crho u v ev1 ev2 = LeCode-Comp u v UCode tt (snd ev1) (snd ev2)

-- App: Bot trivial, non-Bot×non-Bot via App-Comp-helper
EvalRel-Comp (App M N) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (App M N) rho crho UCode Bot ev1 ev2 = comp-Bot-r UCode
EvalRel-Comp (App M N) rho crho (FunEl g1') Bot ev1 ev2 = comp-Bot-r (FunEl g1')
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') Bot ev1 ev2 = comp-Bot-r (PiCode a1' f1')
-- All non-Bot × non-Bot App cases: use App-Comp-helper
EvalRel-Comp (App M N) rho crho UCode UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho UCode (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho UCode (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))

-- App at Nat-value result codes (App-Comp-helper is generic in the codes)
EvalRel-Comp (App M N) rho crho UCode NatCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode NatCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho UCode ZeroEl ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode ZeroEl (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho UCode (SucEl w2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode (SucEl w2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') NatCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') NatCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') ZeroEl ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') ZeroEl (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') (SucEl w2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') (SucEl w2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') NatCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') NatCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') ZeroEl ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') ZeroEl (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') (SucEl w2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') (SucEl w2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
-- NatCode row
EvalRel-Comp (App M N) rho crho NatCode Bot ev1 ev2 = comp-Bot-r NatCode
EvalRel-Comp (App M N) rho crho NatCode UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    NatCode UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho NatCode (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    NatCode (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho NatCode (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    NatCode (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho NatCode NatCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    NatCode NatCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho NatCode ZeroEl ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    NatCode ZeroEl (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho NatCode (SucEl w2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    NatCode (SucEl w2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
-- ZeroEl row
EvalRel-Comp (App M N) rho crho ZeroEl Bot ev1 ev2 = comp-Bot-r ZeroEl
EvalRel-Comp (App M N) rho crho ZeroEl UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    ZeroEl UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho ZeroEl (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    ZeroEl (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho ZeroEl (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    ZeroEl (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho ZeroEl NatCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    ZeroEl NatCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho ZeroEl ZeroEl ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    ZeroEl ZeroEl (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho ZeroEl (SucEl w2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    ZeroEl (SucEl w2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
-- SucEl row
EvalRel-Comp (App M N) rho crho (SucEl w1) Bot ev1 ev2 = comp-Bot-r (SucEl w1)
EvalRel-Comp (App M N) rho crho (SucEl w1) UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (SucEl w1) UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (SucEl w1) (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (SucEl w1) (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (SucEl w1) (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (SucEl w1) (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (SucEl w1) NatCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (SucEl w1) NatCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (SucEl w1) ZeroEl ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (SucEl w1) ZeroEl (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (SucEl w1) (SucEl w2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (SucEl w1) (SucEl w2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))

-- Nat / Zero / Suc / Case
EvalRel-Comp NatT rho crho u v ev1 ev2 =
  LeCode-Comp u v NatCode tt (snd ev1) (snd ev2)
EvalRel-Comp Zero rho crho u v ev1 ev2 =
  LeCode-Comp u v ZeroEl tt (snd ev1) (snd ev2)
EvalRel-Comp (Suc m) rho crho u v ev1 ev2 =
  let v1   = fst (snd ev1)
      evm1 = fst (snd (snd ev1))
      le1  = snd (snd (snd ev1))
      v2   = fst (snd ev2)
      evm2 = fst (snd (snd ev2))
      le2  = snd (snd (snd ev2))
      cv1  = EvalRel-coh m rho v1 evm1
      cv2  = EvalRel-coh m rho v2 evm2
      comp-v = EvalRel-Comp m rho crho v1 v2 evm1 evm2
  in Comp-mono u v (SucEl v1) (SucEl v2) (fst ev1) (fst ev2) cv1 cv2 le1 le2 comp-v
EvalRel-Comp (Case M a b) rho crho u v ev1 ev2 =
  let w1   = fst ev1
      evM1 = fst (snd ev1)
      cb1  = snd (snd ev1)
      w2   = fst ev2
      evM2 = fst (snd ev2)
      cb2  = snd (snd ev2)
      comp-w = EvalRel-Comp M rho crho w1 w2 evM1 evM2
  in CaseBranch-Comp a b rho crho
       (\ x y ex ey -> EvalRel-Comp a rho crho x y ex ey)
       (\ x y ex ey -> EvalRel-Comp b rho crho x y ex ey)
       u v w1 w2 comp-w cb1 cb2

-- Lam
EvalRel-Comp (Lam A M) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (Lam A M) rho crho (FunEl g1) Bot ev1 ev2 = comp-Bot-r (FunEl g1)
EvalRel-Comp (Lam A M) rho crho UCode v () ev2
EvalRel-Comp (Lam A M) rho crho (PiCode a1 f1) v () ev2
EvalRel-Comp (Lam A M) rho crho (FunEl g1) UCode ev1 ()
EvalRel-Comp (Lam A M) rho crho (FunEl g1) (PiCode a2 f2) ev1 ()
EvalRel-Comp (Lam A M) rho crho (FunEl g1) (FunEl g2) ev1 ev2 =
  let ew1 = Lam-edgewise A M rho g1 ev1
      ew2 = Lam-edgewise A M rho g2 ev2
      a1  = fst ew1
      cg1 = fst (snd ew1)
      wf1 = snd (snd (snd (snd ew1)))
      a2  = fst ew2
      cg2 = fst (snd ew2)
      wf2 = snd (snd (snd (snd ew2)))
  in Lam-CompFun M rho a1 a2 g1 g2 crho (cft-from-cf g1 cg1) (cft-from-cf g2 cg2) wf1 wf2
       (\ rho' crho' u v eu ev -> EvalRel-Comp M rho' crho' u v eu ev)

-- Pi
EvalRel-Comp (Pi A B) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) Bot ev1 ev2 = comp-Bot-r (PiCode a1 f1)
EvalRel-Comp (Pi A B) rho crho UCode v () ev2
EvalRel-Comp (Pi A B) rho crho (FunEl g1) v () ev2
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) UCode ev1 ()
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) (FunEl g2) ev1 ()
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) (PiCode a2 f2) ev1 ev2 =
  let pew1 = Pi-edgewise A B rho a1 f1 ev1
      pew2 = Pi-edgewise A B rho a2 f2 ev2
      a1'  = fst (snd (snd pew1))
      wf1  = snd (snd (snd (snd pew1)))
      a2'  = fst (snd (snd pew2))
      wf2  = snd (snd (snd (snd pew2)))
      comp-a = EvalRel-Comp A rho crho a1 a2 (fst (snd ev1)) (fst (snd ev2))
      cf1 = snd (fst ev1)
      cf2 = snd (fst ev2)
      comp-f = Lam-CompFun B rho a1' a2' f1 f2 crho cf1 cf2 wf1 wf2
                 (\ rho' crho' u v eu ev -> EvalRel-Comp B rho' crho' u v eu ev)
  in mkSigma comp-a comp-f
EvalRel-Comp (Y g) rho crho u v ev1 ev2 =
  Approx-Comp (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil)))
    (\ p1 w1 p2 w2 cp s1 s2 ->
       fst (fst (EvalRel-Comp g rho crho
                   (FunEl (cons (mkSigma p1 w1) nil))
                   (FunEl (cons (mkSigma p2 w2) nil)) s1 s2)) cp)
    (fst ev1) (fst ev2) u v (snd ev1) (snd ev2)

------------------------------------------------------------------------
-- EvalRel-down: downward closure of the evaluation relation.
--
-- If M evaluates to u and u' <= u with Coherent u', then M evaluates
-- to u'. By structural induction on M.
------------------------------------------------------------------------

EvalRel-down : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (u u' : FinEl) -> CoherentEnv rho -> Coherent u' ->
  EvalRel M rho u -> LeCode u' u -> EvalRel M rho u'

-- CaseBranch-down : downward closure of a case-branch witness in the
-- output c (the scrutinee value w is fixed).  Requires NotBot u' so the
-- succ-branch singleton graph (cons (mkSigma p u') nil) stays coherent;
-- the EvalRel-down (Case ...) clause handles u' = Bot separately.
CaseBranch-down : {n : Nat} (a b : Expr n) (rho : EnvApprox n) ->
  CoherentEnv rho -> (u u' : FinEl) -> Coherent u' -> NotBot u' ->
  (w : FinEl) -> CaseBranch a b rho u w -> LeCode u' u ->
  CaseBranch a b rho u' w
CaseBranch-down a b rho crho u u' cu' nb Bot cb le =
  absurd (Coherent-val-LeBot-absurd u' (mkSigma cu' nb)
            (LeCode-trans u' u Bot cu' (fst cb) tt le (snd cb)))
CaseBranch-down a b rho crho u u' cu' nb UCode () le
CaseBranch-down a b rho crho u u' cu' nb (FunEl g) () le
CaseBranch-down a b rho crho u u' cu' nb (PiCode d f) () le
CaseBranch-down a b rho crho u u' cu' nb NatCode () le
CaseBranch-down a b rho crho u u' cu' nb ZeroEl cb le =
  EvalRel-down a rho u u' crho cu' cb le
CaseBranch-down a b rho crho u u' cu' nb (SucEl p) cb le =
  let c-pu = EvalRel-coh b rho (FunEl (cons (mkSigma p u) nil)) cb
      cp   = Coherent-singleton-key p u c-pu
      cu   = Coherent-singleton-val p u c-pu
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma p u) nil)) c-pu)
      c-ef = Coherent-EvalFun (cons (mkSigma p u) nil) p c-pu cp
      le-u'-ef = LeCode-trans u' u (EvalFun (cons (mkSigma p u) nil) p)
                   cu' cu c-ef le le-refl
      c-pu' = mkCFT cp cu' nb tt tt
  in EvalRel-down b rho
       (FunEl (cons (mkSigma p u) nil))
       (FunEl (cons (mkSigma p u') nil))
       crho c-pu' cb (mkSigma le-u'-ef tt)

-- Var: compose LeCode
EvalRel-down (Var i) rho u u' crho cu' ev le =
  mkSigma cu' (LeCode-trans u' u (lookupEnv i rho)
    cu' (fst ev) (lookupEnv-coh i rho crho) le (snd ev))

-- U: compose LeCode
EvalRel-down U rho u u' crho cu' ev le =
  mkSigma cu' (LeCode-trans u' u UCode cu' (fst ev) tt le (snd ev))

-- App: u' = Bot trivial
EvalRel-down (App M N) rho u Bot crho cu' ev le = tt
-- App: u = Bot forces non-Bot u' absurd
EvalRel-down (App M N) rho Bot UCode crho cu' ev ()
EvalRel-down (App M N) rho Bot (FunEl g') crho cu' ev ()
EvalRel-down (App M N) rho Bot (PiCode a' f') crho cu' ev ()
-- App: UCode -> UCode
EvalRel-down (App M N) rho UCode UCode crho cu' ev le =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
      c-vu = EvalRel-coh M rho (FunEl (cons (mkSigma v UCode) nil)) evM
      cv   = Coherent-singleton-key v UCode c-vu
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma v UCode) nil)) c-vu)
      c-ef = Coherent-EvalFun (cons (mkSigma v UCode) nil) v c-vu cv
      le-u'-ef = LeCode-trans UCode UCode (EvalFun (cons (mkSigma v UCode) nil) v)
                   cu' tt c-ef le le-refl
      c-vu' = mkCFT cv tt tt tt tt
      evM' = EvalRel-down M rho
               (FunEl (cons (mkSigma v UCode) nil))
               (FunEl (cons (mkSigma v UCode) nil))
               crho c-vu' evM (mkSigma le-u'-ef tt)
  in mkSigma v (mkSigma evN evM')
-- App: UCode -> cross-constructor absurd
EvalRel-down (App M N) rho UCode (FunEl g') crho cu' ev ()
EvalRel-down (App M N) rho UCode (PiCode a' f') crho cu' ev ()
-- App: FunEl -> cross-constructor absurd
EvalRel-down (App M N) rho (FunEl g0) UCode crho cu' ev ()
EvalRel-down (App M N) rho (FunEl g0) (PiCode a' f') crho cu' ev ()
-- App: FunEl -> FunEl
EvalRel-down (App M N) rho (FunEl g0) (FunEl g') crho cu' ev le =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
      c-vu = EvalRel-coh M rho (FunEl (cons (mkSigma v (FunEl g0)) nil)) evM
      cv   = Coherent-singleton-key v (FunEl g0) c-vu
      cu   = Coherent-singleton-val v (FunEl g0) c-vu
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma v (FunEl g0)) nil)) c-vu)
      c-ef = Coherent-EvalFun (cons (mkSigma v (FunEl g0)) nil) v c-vu cv
      le-u'-ef = LeCode-trans (FunEl g') (FunEl g0) (EvalFun (cons (mkSigma v (FunEl g0)) nil) v)
                   cu' cu c-ef le le-refl
      c-vu' = mkCFT cv cu' tt tt tt
      evM' = EvalRel-down M rho
               (FunEl (cons (mkSigma v (FunEl g0)) nil))
               (FunEl (cons (mkSigma v (FunEl g')) nil))
               crho c-vu' evM (mkSigma le-u'-ef tt)
  in mkSigma v (mkSigma evN evM')
-- App: PiCode -> cross-constructor absurd
EvalRel-down (App M N) rho (PiCode a0 f0) UCode crho cu' ev ()
EvalRel-down (App M N) rho (PiCode a0 f0) (FunEl g') crho cu' ev ()
-- App: PiCode -> PiCode
EvalRel-down (App M N) rho (PiCode a0 f0) (PiCode a' f') crho cu' ev le =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
      c-vu = EvalRel-coh M rho (FunEl (cons (mkSigma v (PiCode a0 f0)) nil)) evM
      cv   = Coherent-singleton-key v (PiCode a0 f0) c-vu
      cu   = Coherent-singleton-val v (PiCode a0 f0) c-vu
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma v (PiCode a0 f0)) nil)) c-vu)
      c-ef = Coherent-EvalFun (cons (mkSigma v (PiCode a0 f0)) nil) v c-vu cv
      le-u'-ef = LeCode-trans (PiCode a' f') (PiCode a0 f0)
                   (EvalFun (cons (mkSigma v (PiCode a0 f0)) nil) v)
                   cu' cu c-ef le le-refl
      c-vu' = mkCFT cv cu' tt tt tt
      evM' = EvalRel-down M rho
               (FunEl (cons (mkSigma v (PiCode a0 f0)) nil))
               (FunEl (cons (mkSigma v (PiCode a' f')) nil))
               crho c-vu' evM (mkSigma le-u'-ef tt)
  in mkSigma v (mkSigma evN evM')

-- Lam: absurd cases for non-FunEl outputs
EvalRel-down (Lam A M) rho UCode u' crho cu' () le
EvalRel-down (Lam A M) rho (PiCode a f) u' crho cu' () le
-- Lam Bot
EvalRel-down (Lam A M) rho Bot Bot crho cu' ev le = tt
EvalRel-down (Lam A M) rho Bot UCode crho cu' ev ()
EvalRel-down (Lam A M) rho Bot (FunEl g') crho cu' ev ()
EvalRel-down (Lam A M) rho Bot (PiCode a' f') crho cu' ev ()
-- Lam (FunEl g) Bot: trivial
EvalRel-down (Lam A M) rho (FunEl g) Bot crho cu' ev le = tt
-- Lam (FunEl g) absurd cross-constructors
EvalRel-down (Lam A M) rho (FunEl g) UCode crho cu' ev ()
EvalRel-down (Lam A M) rho (FunEl g) (PiCode a' f') crho cu' ev ()
-- Lam (FunEl g) (FunEl g'): the key case
EvalRel-down (Lam A M) rho (FunEl g) (FunEl g') crho cu' ev le =
  let a    = fst ev
      cg   = fst (snd ev)
      aU   = fst (snd (snd ev))
      evA  = fst (snd (snd (snd ev)))
      body = snd (snd (snd (snd ev)))
      cg'  = cu'
      ctg' = cft-from-cf g' cg'
      ctg  = cft-from-cf g cg
  in mkSigma a (mkSigma cg' (mkSigma aU (mkSigma evA
       (\ u v sel ->
          let cu  = Coherent-Selection sel ctg'
              cv  = Coherent-Selection-val sel ctg'
              lf-g' = LeCode-refl (FunEl g') cg'
              le-v-efg' = Selection-le-EvalFun g' sel lf-g' ctg' ctg' cu
              le-efg'-efg = EvalFun-mon g' g u ctg' ctg cu le
              c-efg'u = Coherent-EvalFun g' u ctg' cu
              c-efgu  = Coherent-EvalFun g u ctg cu
              le-v-efgu = LeCode-trans v (EvalFun g' u) (EvalFun g u)
                            cv c-efg'u c-efgu le-v-efg' le-efg'-efg
              sb     = selectionBelow g u ctg cu
              u0     = fst sb
              v0     = fst (snd sb)
              sel-g  = fst (snd (snd sb))
              le-u0  = fst (snd (snd (snd sb)))
              eq-v0  = snd (snd (snd (snd sb)))
              w      = body u0 v0 sel-g
              x      = fst w
              le-x-u0 = fst (snd w)
              mem-x  = fst (snd (snd w))
              evM-v0 = snd (snd (snd w))
              cx     = FinMem-coh-u x a mem-x
              le-x-u = LeCode-trans x u0 u cx
                         (Coherent-Selection sel-g ctg) cu le-x-u0 le-u0
              le-v-v0 = Eq-transport (LeCode v) eq-v0 le-v-efgu
              cx-env = mkSigma crho cx
              evM-v  = EvalRel-down M (extendEnv rho x) v0 v cx-env cv evM-v0 le-v-v0
          in mkSigma x (mkSigma le-x-u (mkSigma mem-x evM-v))))))

-- Pi: absurd cases for non-PiCode outputs
EvalRel-down (Pi A B) rho UCode u' crho cu' () le
EvalRel-down (Pi A B) rho (FunEl g) u' crho cu' () le
-- Pi Bot
EvalRel-down (Pi A B) rho Bot Bot crho cu' ev le = tt
EvalRel-down (Pi A B) rho Bot UCode crho cu' ev ()
EvalRel-down (Pi A B) rho Bot (FunEl g') crho cu' ev ()
EvalRel-down (Pi A B) rho Bot (PiCode a' f') crho cu' ev ()
-- Pi (PiCode a f) Bot: trivial
EvalRel-down (Pi A B) rho (PiCode a f) Bot crho cu' ev le = tt
-- Pi (PiCode a f) absurd cross-constructors
EvalRel-down (Pi A B) rho (PiCode a f) UCode crho cu' ev ()
EvalRel-down (Pi A B) rho (PiCode a f) (FunEl g') crho cu' ev ()
-- Pi (PiCode a f) (PiCode a' f')
EvalRel-down (Pi A B) rho (PiCode a f) (PiCode a' f') crho cu' ev le =
  let caf  = fst ev
      evA  = fst (snd ev)
      a0   = fst (snd (snd ev))
      evA0 = fst (snd (snd (snd ev)))
      body = snd (snd (snd (snd ev)))
      le-a = fst le
      le-f = snd le
      ca'  = fst cu'
      cf'  = snd cu'
      cf-orig = snd caf
  in mkSigma cu' (mkSigma
       (EvalRel-down A rho a a' crho ca' evA le-a)
       (mkSigma a0 (mkSigma evA0
       (\ u v sel ->
          let cu  = Coherent-Selection sel cf'
              cv  = Coherent-Selection-val sel cf'
              lf-f' = LeFunCode-refl f' cf'
              le-v-eff' = Selection-le-EvalFun f' sel lf-f' cf' cf' cu
              le-eff'-eff = EvalFun-mon f' f u cf' cf-orig cu le-f
              c-eff'u = Coherent-EvalFun f' u cf' cu
              c-effu  = Coherent-EvalFun f u cf-orig cu
              le-v-effu = LeCode-trans v (EvalFun f' u) (EvalFun f u)
                            cv c-eff'u c-effu le-v-eff' le-eff'-eff
              sb     = selectionBelow f u cf-orig cu
              u0     = fst sb
              v0     = fst (snd sb)
              sel-f  = fst (snd (snd sb))
              le-u0  = fst (snd (snd (snd sb)))
              eq-v0  = snd (snd (snd (snd sb)))
              w      = body u0 v0 sel-f
              x      = fst w
              le-x-u0 = fst (snd w)
              mem-x-a0 = fst (snd (snd w))
              evB-v0 = snd (snd (snd w))
              cx     = FinMem-coh-u x a0 mem-x-a0
              le-x-u = LeCode-trans x u0 u cx
                         (Coherent-Selection sel-f cf-orig) cu le-x-u0 le-u0
              le-v-v0 = Eq-transport (LeCode v) eq-v0 le-v-effu
              cx-env = mkSigma crho cx
              evB-x-v = EvalRel-down B (extendEnv rho x) v0 v cx-env cv evB-v0 le-v-v0
          in mkSigma x (mkSigma le-x-u (mkSigma mem-x-a0 evB-x-v))))))

-- Y : Bot target is the zero approximant; every non-Bot target uses the
-- index-preserving Approx-down (same body for all non-Bot codes).
EvalRel-down (Y g) rho u Bot crho cu' ev le =
  mkSigma zero (mkSigma tt (LeCode-Bot Bot))
EvalRel-down (Y g) rho u UCode crho cu' ev le =
  mkSigma (fst ev) (Approx-down (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil)))
    (\ p w w' cw' nbw' sw le' ->
        let c-pw = EvalRel-coh g rho (FunEl (cons (mkSigma p w) nil)) sw
            cp   = Coherent-singleton-key p w c-pw
            cw   = Coherent-singleton-val p w c-pw
            le-rf = fst (LeCode-refl (FunEl (cons (mkSigma p w) nil)) c-pw)
            c-ef  = Coherent-EvalFun (cons (mkSigma p w) nil) p c-pw cp
            le-w' = LeCode-trans w' w (EvalFun (cons (mkSigma p w) nil) p) cw' cw c-ef le' le-rf
            c-pw' = mkCFT cp cw' nbw' tt tt
        in EvalRel-down g rho (FunEl (cons (mkSigma p w) nil)) (FunEl (cons (mkSigma p w') nil))
             crho c-pw' sw (mkSigma le-w' tt)) (fst ev) u UCode cu' tt (snd ev) le)
EvalRel-down (Y g) rho u (FunEl g0) crho cu' ev le =
  mkSigma (fst ev) (Approx-down (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil)))
    (\ p w w' cw' nbw' sw le' ->
        let c-pw = EvalRel-coh g rho (FunEl (cons (mkSigma p w) nil)) sw
            cp   = Coherent-singleton-key p w c-pw
            cw   = Coherent-singleton-val p w c-pw
            le-rf = fst (LeCode-refl (FunEl (cons (mkSigma p w) nil)) c-pw)
            c-ef  = Coherent-EvalFun (cons (mkSigma p w) nil) p c-pw cp
            le-w' = LeCode-trans w' w (EvalFun (cons (mkSigma p w) nil) p) cw' cw c-ef le' le-rf
            c-pw' = mkCFT cp cw' nbw' tt tt
        in EvalRel-down g rho (FunEl (cons (mkSigma p w) nil)) (FunEl (cons (mkSigma p w') nil))
             crho c-pw' sw (mkSigma le-w' tt)) (fst ev) u (FunEl g0) cu' tt (snd ev) le)
EvalRel-down (Y g) rho u (PiCode a0 f0) crho cu' ev le =
  mkSigma (fst ev) (Approx-down (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil)))
    (\ p w w' cw' nbw' sw le' ->
        let c-pw = EvalRel-coh g rho (FunEl (cons (mkSigma p w) nil)) sw
            cp   = Coherent-singleton-key p w c-pw
            cw   = Coherent-singleton-val p w c-pw
            le-rf = fst (LeCode-refl (FunEl (cons (mkSigma p w) nil)) c-pw)
            c-ef  = Coherent-EvalFun (cons (mkSigma p w) nil) p c-pw cp
            le-w' = LeCode-trans w' w (EvalFun (cons (mkSigma p w) nil) p) cw' cw c-ef le' le-rf
            c-pw' = mkCFT cp cw' nbw' tt tt
        in EvalRel-down g rho (FunEl (cons (mkSigma p w) nil)) (FunEl (cons (mkSigma p w') nil))
             crho c-pw' sw (mkSigma le-w' tt)) (fst ev) u (PiCode a0 f0) cu' tt (snd ev) le)
EvalRel-down (Y g) rho u NatCode crho cu' ev le =
  mkSigma (fst ev) (Approx-down (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil)))
    (\ p w w' cw' nbw' sw le' ->
        let c-pw = EvalRel-coh g rho (FunEl (cons (mkSigma p w) nil)) sw
            cp   = Coherent-singleton-key p w c-pw
            cw   = Coherent-singleton-val p w c-pw
            le-rf = fst (LeCode-refl (FunEl (cons (mkSigma p w) nil)) c-pw)
            c-ef  = Coherent-EvalFun (cons (mkSigma p w) nil) p c-pw cp
            le-w' = LeCode-trans w' w (EvalFun (cons (mkSigma p w) nil) p) cw' cw c-ef le' le-rf
            c-pw' = mkCFT cp cw' nbw' tt tt
        in EvalRel-down g rho (FunEl (cons (mkSigma p w) nil)) (FunEl (cons (mkSigma p w') nil))
             crho c-pw' sw (mkSigma le-w' tt)) (fst ev) u NatCode cu' tt (snd ev) le)
EvalRel-down (Y g) rho u ZeroEl crho cu' ev le =
  mkSigma (fst ev) (Approx-down (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil)))
    (\ p w w' cw' nbw' sw le' ->
        let c-pw = EvalRel-coh g rho (FunEl (cons (mkSigma p w) nil)) sw
            cp   = Coherent-singleton-key p w c-pw
            cw   = Coherent-singleton-val p w c-pw
            le-rf = fst (LeCode-refl (FunEl (cons (mkSigma p w) nil)) c-pw)
            c-ef  = Coherent-EvalFun (cons (mkSigma p w) nil) p c-pw cp
            le-w' = LeCode-trans w' w (EvalFun (cons (mkSigma p w) nil) p) cw' cw c-ef le' le-rf
            c-pw' = mkCFT cp cw' nbw' tt tt
        in EvalRel-down g rho (FunEl (cons (mkSigma p w) nil)) (FunEl (cons (mkSigma p w') nil))
             crho c-pw' sw (mkSigma le-w' tt)) (fst ev) u ZeroEl cu' tt (snd ev) le)
EvalRel-down (Y g) rho u (SucEl w0) crho cu' ev le =
  mkSigma (fst ev) (Approx-down (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil)))
    (\ p w w' cw' nbw' sw le' ->
        let c-pw = EvalRel-coh g rho (FunEl (cons (mkSigma p w) nil)) sw
            cp   = Coherent-singleton-key p w c-pw
            cw   = Coherent-singleton-val p w c-pw
            le-rf = fst (LeCode-refl (FunEl (cons (mkSigma p w) nil)) c-pw)
            c-ef  = Coherent-EvalFun (cons (mkSigma p w) nil) p c-pw cp
            le-w' = LeCode-trans w' w (EvalFun (cons (mkSigma p w) nil) p) cw' cw c-ef le' le-rf
            c-pw' = mkCFT cp cw' nbw' tt tt
        in EvalRel-down g rho (FunEl (cons (mkSigma p w) nil)) (FunEl (cons (mkSigma p w') nil))
             crho c-pw' sw (mkSigma le-w' tt)) (fst ev) u (SucEl w0) cu' tt (snd ev) le)

-- App at Nat-value result codes.  u' = NatCode/ZeroEl only when u matches
-- (LeCode forces it); the atom-atom cases are identity.
EvalRel-down (App M N) rho Bot NatCode crho cu' ev ()
EvalRel-down (App M N) rho UCode NatCode crho cu' ev ()
EvalRel-down (App M N) rho (FunEl g0) NatCode crho cu' ev ()
EvalRel-down (App M N) rho (PiCode a0 f0) NatCode crho cu' ev ()
EvalRel-down (App M N) rho NatCode NatCode crho cu' ev le = ev
EvalRel-down (App M N) rho ZeroEl NatCode crho cu' ev ()
EvalRel-down (App M N) rho (SucEl w0) NatCode crho cu' ev ()
EvalRel-down (App M N) rho Bot ZeroEl crho cu' ev ()
EvalRel-down (App M N) rho UCode ZeroEl crho cu' ev ()
EvalRel-down (App M N) rho (FunEl g0) ZeroEl crho cu' ev ()
EvalRel-down (App M N) rho (PiCode a0 f0) ZeroEl crho cu' ev ()
EvalRel-down (App M N) rho NatCode ZeroEl crho cu' ev ()
EvalRel-down (App M N) rho ZeroEl ZeroEl crho cu' ev le = ev
EvalRel-down (App M N) rho (SucEl w0) ZeroEl crho cu' ev ()
EvalRel-down (App M N) rho Bot (SucEl w') crho cu' ev ()
EvalRel-down (App M N) rho UCode (SucEl w') crho cu' ev ()
EvalRel-down (App M N) rho (FunEl g0) (SucEl w') crho cu' ev ()
EvalRel-down (App M N) rho (PiCode a0 f0) (SucEl w') crho cu' ev ()
EvalRel-down (App M N) rho NatCode (SucEl w') crho cu' ev ()
EvalRel-down (App M N) rho ZeroEl (SucEl w') crho cu' ev ()
EvalRel-down (App M N) rho (SucEl w0) (SucEl w') crho cu' ev le =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
      c-vu = EvalRel-coh M rho (FunEl (cons (mkSigma v (SucEl w0)) nil)) evM
      cv   = Coherent-singleton-key v (SucEl w0) c-vu
      cu   = Coherent-singleton-val v (SucEl w0) c-vu
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma v (SucEl w0)) nil)) c-vu)
      c-ef = Coherent-EvalFun (cons (mkSigma v (SucEl w0)) nil) v c-vu cv
      le-u'-ef = LeCode-trans (SucEl w') (SucEl w0)
                   (EvalFun (cons (mkSigma v (SucEl w0)) nil) v)
                   cu' cu c-ef le le-refl
      c-vu' = mkCFT cv cu' tt tt tt
      evM' = EvalRel-down M rho
               (FunEl (cons (mkSigma v (SucEl w0)) nil))
               (FunEl (cons (mkSigma v (SucEl w')) nil))
               crho c-vu' evM (mkSigma le-u'-ef tt)
  in mkSigma v (mkSigma evN evM')

-- Nat / Zero / Suc / Case
EvalRel-down NatT rho u u' crho cu' ev le =
  mkSigma cu' (LeCode-trans u' u NatCode cu' (fst ev) tt le (snd ev))
EvalRel-down Zero rho u u' crho cu' ev le =
  mkSigma cu' (LeCode-trans u' u ZeroEl cu' (fst ev) tt le (snd ev))
EvalRel-down (Suc m) rho u u' crho cu' ev le =
  let v0  = fst (snd ev)
      evm = fst (snd (snd ev))
      le-u-sv = snd (snd (snd ev))
      cv0 = EvalRel-coh m rho v0 evm
      le-u'-sv = LeCode-trans u' u (SucEl v0) cu' (fst ev) cv0 le le-u-sv
  in mkSigma cu' (mkSigma v0 (mkSigma evm le-u'-sv))
EvalRel-down (Case M a b) rho u Bot crho cu' ev le = EvalRel-Bot (Case M a b) rho
EvalRel-down (Case M a b) rho u UCode crho cu' ev le =
  mkSigma (fst ev) (mkSigma (fst (snd ev))
    (CaseBranch-down a b rho crho u UCode cu' tt (fst ev) (snd (snd ev)) le))
EvalRel-down (Case M a b) rho u (FunEl g) crho cu' ev le =
  mkSigma (fst ev) (mkSigma (fst (snd ev))
    (CaseBranch-down a b rho crho u (FunEl g) cu' tt (fst ev) (snd (snd ev)) le))
EvalRel-down (Case M a b) rho u (PiCode d f) crho cu' ev le =
  mkSigma (fst ev) (mkSigma (fst (snd ev))
    (CaseBranch-down a b rho crho u (PiCode d f) cu' tt (fst ev) (snd (snd ev)) le))
EvalRel-down (Case M a b) rho u NatCode crho cu' ev le =
  mkSigma (fst ev) (mkSigma (fst (snd ev))
    (CaseBranch-down a b rho crho u NatCode cu' tt (fst ev) (snd (snd ev)) le))
EvalRel-down (Case M a b) rho u ZeroEl crho cu' ev le =
  mkSigma (fst ev) (mkSigma (fst (snd ev))
    (CaseBranch-down a b rho crho u ZeroEl cu' tt (fst ev) (snd (snd ev)) le))
EvalRel-down (Case M a b) rho u (SucEl p) crho cu' ev le =
  mkSigma (fst ev) (mkSigma (fst (snd ev))
    (CaseBranch-down a b rho crho u (SucEl p) cu' tt (fst ev) (snd (snd ev)) le))

------------------------------------------------------------------------
-- EvalRel-Sup: supremum closure of the evaluation relation.
--
-- If M evaluates to both u and v in rho, with rho coherent and
-- u, v coherent and compatible, then M evaluates to Sup u v.
------------------------------------------------------------------------

EvalRel-Sup : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (u v : FinEl) -> CoherentEnv rho -> Coherent u -> Coherent v ->
  Comp u v ->
  EvalRel M rho u -> EvalRel M rho v -> EvalRel M rho (Sup u v)

-- Sup-closure for Y, by induction on the PAIR of Kleene indices.
-- No Bot-tolerance / chain-monotonicity needed: a real edge step p w =
-- EvalRel g (FunEl [p|->w]) forces NotBot w (CFTcons.val-nbot), so the
-- Bot edge is never constructed; whenever a value <= Bot appears its
-- index is 0 (Sup Bot x = x definitionally) or it is discharged absurdly.
YSup : {n : Nat} (g : Expr n) (rho : EnvApprox n) (n1 n2 : Nat) (u v : FinEl) ->
  CoherentEnv rho -> Coherent u -> Coherent v -> Comp u v ->
  Approx (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil))) n1 u ->
  Approx (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil))) n2 v ->
  EvalRel (Y g) rho (Sup u v)

-- The single-edge merge:  g[p1|->w1] , g[p2|->w2]  ==>  g[Sup p1 p2 |-> Sup w1 w2].
singletonSup : {n : Nat} (g : Expr n) (rho : EnvApprox n) (p1 w1 p2 w2 : FinEl) ->
  CoherentEnv rho -> Comp p1 p2 -> Comp w1 w2 ->
  Coherent w1 -> Coherent w2 -> NotBot w1 -> NotBot w2 ->
  EvalRel g rho (FunEl (cons (mkSigma p1 w1) nil)) ->
  EvalRel g rho (FunEl (cons (mkSigma p2 w2) nil)) ->
  EvalRel g rho (FunEl (cons (mkSigma (Sup p1 p2) (Sup w1 w2)) nil))

-- LeBot-is-Bot : a coherent element below Bot is Bot.
LeBot-is-Bot : (u : FinEl) -> LeCode u Bot -> Eq u Bot
LeBot-is-Bot Bot          le = refl
LeBot-is-Bot UCode        ()
LeBot-is-Bot (FunEl g)    ()
LeBot-is-Bot (PiCode a f) ()
LeBot-is-Bot NatCode      ()
LeBot-is-Bot ZeroEl       ()
LeBot-is-Bot (SucEl a)    ()

-- App-Sup-helper : generic supremum of two App witnesses at compatible
-- non-Bot result codes u1, u2.  Returns the Sigma underlying
-- EvalRel (App M N) rho (Sup u1 u2).
App-Sup-helper : {n : Nat} (M N : Expr n) (rho : EnvApprox n) ->
  CoherentEnv rho -> (u1 u2 : FinEl) ->
  Coherent u1 -> Coherent u2 -> NotBot u1 -> NotBot u2 -> Comp u1 u2 ->
  EvalRel (App M N) rho u1 -> EvalRel (App M N) rho u2 ->
  S.Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                          (EvalRel M rho (FunEl (cons (mkSigma v (Sup u1 u2)) nil))))

-- CaseBranch-Sup : supremum of two case-branch witnesses at compatible
-- scrutinee values w1, w2 (the subtle one: case commutes with the join).
CaseBranch-Sup : {n : Nat} (a b : Expr n) (rho : EnvApprox n) ->
  CoherentEnv rho -> (u v : FinEl) -> Coherent u -> Coherent v -> Comp u v ->
  (w1 w2 : FinEl) -> Comp w1 w2 ->
  CaseBranch a b rho u w1 -> CaseBranch a b rho v w2 ->
  CaseBranch a b rho (Sup u v) (Sup w1 w2)

App-Sup-helper M N rho crho u1 u2 cu cv nbu1 nbu2 comp eu ev =
  let d1   = App-decompose M N rho u1 nbu1 eu
      v1   = fst d1
      evN1 = fst (snd d1)
      evM1 = snd (snd d1)
      d2   = App-decompose M N rho u2 nbu2 ev
      v2   = fst d2
      evN2 = fst (snd d2)
      evM2 = snd (snd d2)
      cv1  = EvalRel-coh N rho v1 evN1
      cv2  = EvalRel-coh N rho v2 evN2
      cM1  = EvalRel-coh M rho (FunEl (cons (mkSigma v1 u1) nil)) evM1
      cM2  = EvalRel-coh M rho (FunEl (cons (mkSigma v2 u2) nil)) evM2
      comp-v = EvalRel-Comp N rho crho v1 v2 evN1 evN2
      comp-M = EvalRel-Comp M rho crho
                 (FunEl (cons (mkSigma v1 u1) nil))
                 (FunEl (cons (mkSigma v2 u2) nil)) evM1 evM2
      evN-sup = EvalRel-Sup N rho v1 v2 crho cv1 cv2 comp-v evN1 evN2
      evM-2 = EvalRel-Sup M rho
                (FunEl (cons (mkSigma v1 u1) nil))
                (FunEl (cons (mkSigma v2 u2) nil))
                crho cM1 cM2 comp-M evM1 evM2
      c-2graph = Coherent-Sup
                   (FunEl (cons (mkSigma v1 u1) nil))
                   (FunEl (cons (mkSigma v2 u2) nil)) comp-M cM1 cM2
      c-supv = Coherent-Sup v1 v2 comp-v cv1 cv2
      c-result-val = Coherent-Sup u1 u2 comp cu cv
      nb-sup = NotBot-Sup-Comp u1 u2 nbu1 comp
      le-down = LeFunCode-Sup-pair v1 u1 v2 u2 comp-v comp c-2graph c-supv
      c-singleton = mkCFT c-supv c-result-val nb-sup tt tt
      evM-result = EvalRel-down M rho
                     (FunEl (cons (mkSigma v1 u1) (cons (mkSigma v2 u2) nil)))
                     (FunEl (cons (mkSigma (Sup v1 v2) (Sup u1 u2)) nil))
                     crho c-singleton evM-2 le-down
  in mkSigma (Sup v1 v2) (mkSigma evN-sup evM-result)

CaseBranch-Sup a b rho crho u v cu cv comp Bot w2 cw cb1 cb2 =
  let eq-u   = LeBot-is-Bot u (snd cb1)
      eq-suv = Eq-transport (\ z -> Eq (Sup z v) v) (Eq-sym eq-u) (Sup-Bot-l v)
  in Eq-transport (\ c -> CaseBranch a b rho c w2) (Eq-sym eq-suv) cb2
CaseBranch-Sup a b rho crho u v cu cv comp UCode w2 cw () cb2
CaseBranch-Sup a b rho crho u v cu cv comp (FunEl g) w2 cw () cb2
CaseBranch-Sup a b rho crho u v cu cv comp (PiCode d f) w2 cw () cb2
CaseBranch-Sup a b rho crho u v cu cv comp NatCode w2 cw () cb2
CaseBranch-Sup a b rho crho u v cu cv comp ZeroEl Bot cw cb1 cb2 =
  let eq-v   = LeBot-is-Bot v (snd cb2)
      eq-suv = Eq-transport (\ z -> Eq (Sup u z) u) (Eq-sym eq-v) (Sup-Bot-r u)
  in Eq-transport (\ c -> CaseBranch a b rho c ZeroEl) (Eq-sym eq-suv) cb1
CaseBranch-Sup a b rho crho u v cu cv comp ZeroEl UCode () cb1 cb2
CaseBranch-Sup a b rho crho u v cu cv comp ZeroEl (FunEl g) () cb1 cb2
CaseBranch-Sup a b rho crho u v cu cv comp ZeroEl (PiCode d f) () cb1 cb2
CaseBranch-Sup a b rho crho u v cu cv comp ZeroEl NatCode () cb1 cb2
CaseBranch-Sup a b rho crho u v cu cv comp ZeroEl ZeroEl cw cb1 cb2 =
  EvalRel-Sup a rho u v crho cu cv comp cb1 cb2
CaseBranch-Sup a b rho crho u v cu cv comp ZeroEl (SucEl p2) () cb1 cb2
CaseBranch-Sup a b rho crho u v cu cv comp (SucEl p1) Bot cw cb1 cb2 =
  let eq-v   = LeBot-is-Bot v (snd cb2)
      eq-suv = Eq-transport (\ z -> Eq (Sup u z) u) (Eq-sym eq-v) (Sup-Bot-r u)
  in Eq-transport (\ c -> CaseBranch a b rho c (SucEl p1)) (Eq-sym eq-suv) cb1
CaseBranch-Sup a b rho crho u v cu cv comp (SucEl p1) UCode () cb1 cb2
CaseBranch-Sup a b rho crho u v cu cv comp (SucEl p1) (FunEl g) () cb1 cb2
CaseBranch-Sup a b rho crho u v cu cv comp (SucEl p1) (PiCode d f) () cb1 cb2
CaseBranch-Sup a b rho crho u v cu cv comp (SucEl p1) NatCode () cb1 cb2
CaseBranch-Sup a b rho crho u v cu cv comp (SucEl p1) ZeroEl () cb1 cb2
CaseBranch-Sup a b rho crho u v cu cv comp (SucEl p1) (SucEl p2) cw cb1 cb2 =
  let cM1 = EvalRel-coh b rho (FunEl (cons (mkSigma p1 u) nil)) cb1
      cM2 = EvalRel-coh b rho (FunEl (cons (mkSigma p2 v) nil)) cb2
      cp1 = Coherent-singleton-key p1 u cM1
      cp2 = Coherent-singleton-key p2 v cM2
      nbu = CFTcons.val-nbot cM1
      comp-M = EvalRel-Comp b rho crho
                 (FunEl (cons (mkSigma p1 u) nil))
                 (FunEl (cons (mkSigma p2 v) nil)) cb1 cb2
      evM-2 = EvalRel-Sup b rho
                (FunEl (cons (mkSigma p1 u) nil))
                (FunEl (cons (mkSigma p2 v) nil))
                crho cM1 cM2 comp-M cb1 cb2
      c-2graph = Coherent-Sup
                   (FunEl (cons (mkSigma p1 u) nil))
                   (FunEl (cons (mkSigma p2 v) nil)) comp-M cM1 cM2
      c-supp = Coherent-Sup p1 p2 cw cp1 cp2
      c-result-val = Coherent-Sup u v comp cu cv
      nb-sup = NotBot-Sup-Comp u v nbu comp
      le-down = LeFunCode-Sup-pair p1 u p2 v cw comp c-2graph c-supp
      c-singleton = mkCFT c-supp c-result-val nb-sup tt tt
  in EvalRel-down b rho
       (FunEl (cons (mkSigma p1 u) (cons (mkSigma p2 v) nil)))
       (FunEl (cons (mkSigma (Sup p1 p2) (Sup u v)) nil))
       crho c-singleton evM-2 le-down

-- Var: LeCode-Sup-lub
EvalRel-Sup (Var i) rho u v crho cu cv comp eu ev =
  mkSigma (Coherent-Sup u v comp cu cv)
          (LeCode-Sup-lub u v (lookupEnv i rho) (snd eu) (snd ev))

-- U: LeCode-Sup-lub
EvalRel-Sup U rho u v crho cu cv comp eu ev =
  mkSigma (Coherent-Sup u v comp cu cv) (LeCode-Sup-lub u v UCode (snd eu) (snd ev))

-- App: Bot cases
EvalRel-Sup (App M N) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (App M N) rho UCode Bot crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho (FunEl g1') Bot crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho (PiCode a1' f1') Bot crho cu cv comp eu ev = eu

-- App: Cross-constructor non-Bot: Comp = Empty
EvalRel-Sup (App M N) rho UCode (FunEl g2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho UCode (PiCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (FunEl g1') UCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (FunEl g1') (PiCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') UCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') (FunEl g2') crho cu cv () eu ev

-- App: same-constructor non-Bot
EvalRel-Sup (App M N) rho UCode UCode crho cu cv comp eu ev = eu

-- App: FunEl-FunEl
EvalRel-Sup (App M N) rho (FunEl g1') (FunEl g2') crho cu cv comp eu ev =
  let v1   = fst eu
      evN1 = fst (snd eu)
      evM1 = snd (snd eu)
      v2   = fst ev
      evN2 = fst (snd ev)
      evM2 = snd (snd ev)
      cv1  = EvalRel-coh N rho v1 evN1
      cv2  = EvalRel-coh N rho v2 evN2
      cM1  = EvalRel-coh M rho (FunEl (cons (mkSigma v1 (FunEl g1')) nil)) evM1
      cM2  = EvalRel-coh M rho (FunEl (cons (mkSigma v2 (FunEl g2')) nil)) evM2
      comp-v = EvalRel-Comp N rho crho v1 v2 evN1 evN2
      comp-M = EvalRel-Comp M rho crho
                 (FunEl (cons (mkSigma v1 (FunEl g1')) nil))
                 (FunEl (cons (mkSigma v2 (FunEl g2')) nil))
                 evM1 evM2
      evN-sup = EvalRel-Sup N rho v1 v2 crho cv1 cv2 comp-v evN1 evN2
      evM-2 = EvalRel-Sup M rho
                (FunEl (cons (mkSigma v1 (FunEl g1')) nil))
                (FunEl (cons (mkSigma v2 (FunEl g2')) nil))
                crho cM1 cM2 comp-M evM1 evM2
      c-2graph = Coherent-Sup
                   (FunEl (cons (mkSigma v1 (FunEl g1')) nil))
                   (FunEl (cons (mkSigma v2 (FunEl g2')) nil))
                   comp-M cM1 cM2
      c-supv = Coherent-Sup v1 v2 comp-v cv1 cv2
      c-result-val = Coherent-Sup (FunEl g1') (FunEl g2') comp cu cv
      le-down = LeFunCode-Sup-pair v1 (FunEl g1') v2 (FunEl g2') comp-v comp c-2graph c-supv
      c-singleton = mkCFT c-supv c-result-val tt tt tt
      evM-result = EvalRel-down M rho
                     (FunEl (cons (mkSigma v1 (FunEl g1')) (cons (mkSigma v2 (FunEl g2')) nil)))
                     (FunEl (cons (mkSigma (Sup v1 v2) (FunEl (append g1' g2'))) nil))
                     crho c-singleton evM-2 le-down
  in mkSigma (Sup v1 v2) (mkSigma evN-sup evM-result)

-- App: PiCode-PiCode
EvalRel-Sup (App M N) rho (PiCode a1' f1') (PiCode a2' f2') crho cu cv comp eu ev =
  let v1   = fst eu
      evN1 = fst (snd eu)
      evM1 = snd (snd eu)
      v2   = fst ev
      evN2 = fst (snd ev)
      evM2 = snd (snd ev)
      cv1  = EvalRel-coh N rho v1 evN1
      cv2  = EvalRel-coh N rho v2 evN2
      cM1  = EvalRel-coh M rho (FunEl (cons (mkSigma v1 (PiCode a1' f1')) nil)) evM1
      cM2  = EvalRel-coh M rho (FunEl (cons (mkSigma v2 (PiCode a2' f2')) nil)) evM2
      comp-v = EvalRel-Comp N rho crho v1 v2 evN1 evN2
      comp-M = EvalRel-Comp M rho crho
                 (FunEl (cons (mkSigma v1 (PiCode a1' f1')) nil))
                 (FunEl (cons (mkSigma v2 (PiCode a2' f2')) nil))
                 evM1 evM2
      evN-sup = EvalRel-Sup N rho v1 v2 crho cv1 cv2 comp-v evN1 evN2
      evM-2 = EvalRel-Sup M rho
                (FunEl (cons (mkSigma v1 (PiCode a1' f1')) nil))
                (FunEl (cons (mkSigma v2 (PiCode a2' f2')) nil))
                crho cM1 cM2 comp-M evM1 evM2
      c-2graph = Coherent-Sup
                   (FunEl (cons (mkSigma v1 (PiCode a1' f1')) nil))
                   (FunEl (cons (mkSigma v2 (PiCode a2' f2')) nil))
                   comp-M cM1 cM2
      c-supv = Coherent-Sup v1 v2 comp-v cv1 cv2
      c-result-val = Coherent-Sup (PiCode a1' f1') (PiCode a2' f2') comp cu cv
      le-down = LeFunCode-Sup-pair v1 (PiCode a1' f1') v2 (PiCode a2' f2') comp-v comp c-2graph c-supv
      c-singleton = mkCFT c-supv c-result-val tt tt tt
      evM-result = EvalRel-down M rho
                     (FunEl (cons (mkSigma v1 (PiCode a1' f1')) (cons (mkSigma v2 (PiCode a2' f2')) nil)))
                     (FunEl (cons (mkSigma (Sup v1 v2) (PiCode (Sup a1' a2') (append f1' f2'))) nil))
                     crho c-singleton evM-2 le-down
  in mkSigma (Sup v1 v2) (mkSigma evN-sup evM-result)

-- App at Nat-value result codes.
-- Bot on the right
EvalRel-Sup (App M N) rho NatCode Bot crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho ZeroEl Bot crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho (SucEl w1) Bot crho cu cv comp eu ev = eu
-- Cross-constructor with new codes: Comp = Empty
EvalRel-Sup (App M N) rho UCode NatCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho UCode ZeroEl crho cu cv () eu ev
EvalRel-Sup (App M N) rho UCode (SucEl w2) crho cu cv () eu ev
EvalRel-Sup (App M N) rho (FunEl g1') NatCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (FunEl g1') ZeroEl crho cu cv () eu ev
EvalRel-Sup (App M N) rho (FunEl g1') (SucEl w2) crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') NatCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') ZeroEl crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') (SucEl w2) crho cu cv () eu ev
EvalRel-Sup (App M N) rho NatCode UCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho NatCode (FunEl g2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho NatCode (PiCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho NatCode ZeroEl crho cu cv () eu ev
EvalRel-Sup (App M N) rho NatCode (SucEl w2) crho cu cv () eu ev
EvalRel-Sup (App M N) rho ZeroEl UCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho ZeroEl (FunEl g2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho ZeroEl (PiCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho ZeroEl NatCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho ZeroEl (SucEl w2) crho cu cv () eu ev
EvalRel-Sup (App M N) rho (SucEl w1) UCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (SucEl w1) (FunEl g2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (SucEl w1) (PiCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (SucEl w1) NatCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (SucEl w1) ZeroEl crho cu cv () eu ev
-- Same-constructor new codes: via App-Sup-helper
EvalRel-Sup (App M N) rho NatCode NatCode crho cu cv comp eu ev =
  App-Sup-helper M N rho crho NatCode NatCode cu cv tt tt comp eu ev
EvalRel-Sup (App M N) rho ZeroEl ZeroEl crho cu cv comp eu ev =
  App-Sup-helper M N rho crho ZeroEl ZeroEl cu cv tt tt comp eu ev
EvalRel-Sup (App M N) rho (SucEl w1) (SucEl w2) crho cu cv comp eu ev =
  App-Sup-helper M N rho crho (SucEl w1) (SucEl w2) cu cv tt tt comp eu ev

-- Nat / Zero / Suc / Case
EvalRel-Sup NatT rho u v crho cu cv comp eu ev =
  mkSigma (Coherent-Sup u v comp cu cv) (LeCode-Sup-lub u v NatCode (snd eu) (snd ev))
EvalRel-Sup Zero rho u v crho cu cv comp eu ev =
  mkSigma (Coherent-Sup u v comp cu cv) (LeCode-Sup-lub u v ZeroEl (snd eu) (snd ev))
EvalRel-Sup (Suc m) rho u v crho cu cv comp eu ev =
  let w1 = fst (snd eu)
      evm1 = fst (snd (snd eu))
      le-u-sw1 = snd (snd (snd eu))
      w2 = fst (snd ev)
      evm2 = fst (snd (snd ev))
      le-v-sw2 = snd (snd (snd ev))
      cw1 = EvalRel-coh m rho w1 evm1
      cw2 = EvalRel-coh m rho w2 evm2
      comp-w = EvalRel-Comp m rho crho w1 w2 evm1 evm2
      evm-sup = EvalRel-Sup m rho w1 w2 crho cw1 cw2 comp-w evm1 evm2
      c-sw-sup = Coherent-Sup (SucEl w1) (SucEl w2) comp-w cw1 cw2
      le-sw1 = LeCode-Sup-left (SucEl w1) (SucEl w2) comp-w cw1 cw2
      le-sw2 = LeCode-Sup-right (SucEl w1) (SucEl w2) comp-w cw1 cw2
      le-u' = LeCode-trans u (SucEl w1) (Sup (SucEl w1) (SucEl w2)) cu cw1 c-sw-sup le-u-sw1 le-sw1
      le-v' = LeCode-trans v (SucEl w2) (Sup (SucEl w1) (SucEl w2)) cv cw2 c-sw-sup le-v-sw2 le-sw2
      le-sup = LeCode-Sup-lub u v (Sup (SucEl w1) (SucEl w2)) le-u' le-v'
  in mkSigma (Coherent-Sup u v comp cu cv)
       (mkSigma (Sup w1 w2) (mkSigma evm-sup le-sup))
EvalRel-Sup (Case M a b) rho u v crho cu cv comp eu ev =
  let w1   = fst eu
      evM1 = fst (snd eu)
      cb1  = snd (snd eu)
      w2   = fst ev
      evM2 = fst (snd ev)
      cb2  = snd (snd ev)
      cw1  = EvalRel-coh M rho w1 evM1
      cw2  = EvalRel-coh M rho w2 evM2
      comp-w = EvalRel-Comp M rho crho w1 w2 evM1 evM2
      evM-sup = EvalRel-Sup M rho w1 w2 crho cw1 cw2 comp-w evM1 evM2
      cbS = CaseBranch-Sup a b rho crho u v cu cv comp w1 w2 comp-w cb1 cb2
  in mkSigma (Sup w1 w2) (mkSigma evM-sup cbS)

-- Lam: Bot cases
EvalRel-Sup (Lam A M) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (Lam A M) rho (FunEl g1) Bot crho cu cv comp eu ev = eu

-- Lam: Absurd cases
EvalRel-Sup (Lam A M) rho UCode v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho (PiCode a1 f1) v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho (FunEl g1) UCode crho cu cv comp eu ()
EvalRel-Sup (Lam A M) rho (FunEl g1) (PiCode a2 f2) crho cu cv comp eu ()

-- Lam: FunEl-FunEl
EvalRel-Sup (Lam A M) rho (FunEl g1) (FunEl g2) crho cu cv comp eu ev =
  let a1    = fst eu
      cg1   = fst (snd eu)
      a1U   = fst (snd (snd eu))
      evA1  = fst (snd (snd (snd eu)))
      body1 = snd (snd (snd (snd eu)))
      a2    = fst ev
      cg2   = fst (snd ev)
      a2U   = fst (snd (snd ev))
      evA2  = fst (snd (snd (snd ev)))
      body2 = snd (snd (snd (snd ev)))
      ca1   = EvalRel-coh A rho a1 evA1
      ca2   = EvalRel-coh A rho a2 evA2
      comp-a = EvalRel-Comp A rho crho a1 a2 evA1 evA2
      evA-sup = EvalRel-Sup A rho a1 a2 crho ca1 ca2 comp-a evA1 evA2
      c-sup-a = Coherent-Sup a1 a2 comp-a ca1 ca2
      supU = FinMem-Sup-element a1 a2 UCode comp-a tt a1U a2U
      c-gab = CoherentFun-append g1 g2 cg1 cg2 comp
      ct-gab = cft-from-cf (append g1 g2) c-gab
  in mkSigma (Sup a1 a2) (mkSigma c-gab (mkSigma supU (mkSigma evA-sup
       (\ u v sel ->
          let cu-sel = Coherent-Selection sel ct-gab
              cv-sel = Coherent-Selection-val sel ct-gab
              sb1    = selectionBelow g1 u (cft-from-cf g1 cg1) cu-sel
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow g2 u (cft-from-cf g2 cg2) cu-sel
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              w1     = body1 u1 v1 sel1
              x1     = fst w1
              le-x1  = fst (snd w1)
              mem-x1 = fst (snd (snd w1))
              evM-x1 = snd (snd (snd w1))
              w2     = body2 u2 v2 sel2
              x2     = fst w2
              le-x2  = fst (snd w2)
              mem-x2 = fst (snd (snd w2))
              evM-x2 = snd (snd (snd w2))
              cx1    = FinMem-coh-u x1 a1 mem-x1
              cx2    = FinMem-coh-u x2 a2 mem-x2
              le-x1-u = LeCode-trans x1 u1 u cx1 (Coherent-Selection sel1 (cft-from-cf g1 cg1)) cu-sel le-x1 le-u1
              le-x2-u = LeCode-trans x2 u2 u cx2 (Coherent-Selection sel2 (cft-from-cf g2 cg2)) cu-sel le-x2 le-u2
              comp-x  = LeCode-Comp x1 x2 u cu-sel le-x1-u le-x2-u
              c-supx  = Coherent-Sup x1 x2 comp-x cx1 cx2
              le-supx-u = LeCode-Sup-lub x1 x2 u le-x1-u le-x2-u
              le-a1-sup = LeCode-Sup-left a1 a2 comp-a ca1 ca2
              le-a2-sup = LeCode-Sup-right a1 a2 comp-a ca1 ca2
              mem-x1-sup = finMem-upward x1 a1 (Sup a1 a2) le-a1-sup ca1 c-sup-a mem-x1 supU
              mem-x2-sup = finMem-upward x2 a2 (Sup a1 a2) le-a2-sup ca2 c-sup-a mem-x2 supU
              mem-supx   = FinMem-Sup-element x1 x2 (Sup a1 a2) comp-x c-sup-a mem-x1-sup mem-x2-sup
              envle1 = EnvLe-extend-left rho x1 x2 crho comp-x cx1 cx2
              envle2 = EnvLe-extend-right rho x1 x2 crho comp-x cx1 cx2
              evM-sup1 = EvalRel-mon-env M (extendEnv rho x1) (extendEnv rho (Sup x1 x2)) v1 evM-x1 envle1
              evM-sup2 = EvalRel-mon-env M (extendEnv rho x2) (extendEnv rho (Sup x1 x2)) v2 evM-x2 envle2
              crho-sup = mkSigma crho c-supx
              comp-v = EvalRel-Comp M (extendEnv rho (Sup x1 x2)) crho-sup v1 v2 evM-sup1 evM-sup2
              cv1    = EvalRel-coh M (extendEnv rho x1) v1 evM-x1
              cv2    = EvalRel-coh M (extendEnv rho x2) v2 evM-x2
              evM-supv = EvalRel-Sup M (extendEnv rho (Sup x1 x2)) v1 v2 crho-sup cv1 cv2 comp-v evM-sup1 evM-sup2
              lf-gab = LeFunCode-refl (append g1 g2) ct-gab
              le-v-ef = Selection-le-EvalFun (append g1 g2) sel lf-gab ct-gab ct-gab cu-sel
              ctg1   = cft-from-cf g1 cg1
              eq-ef  = EvalFun-append-eq g1 g2 u comp ctg1 cu-sel
              le-v-supef = Eq-transport (LeCode v) eq-ef le-v-ef
              eq-sup = Eq-transport (\ z -> Eq (Sup z (EvalFun g2 u)) (Sup v1 v2))
                         (Eq-sym eq-v1)
                         (Eq-transport (\ z -> Eq (Sup v1 z) (Sup v1 v2))
                           (Eq-sym eq-v2) refl)
              le-v-supv = Eq-transport (LeCode v) eq-sup le-v-supef
              c-supv = Coherent-Sup v1 v2 comp-v cv1 cv2
              evM-v  = EvalRel-down M (extendEnv rho (Sup x1 x2)) (Sup v1 v2) v crho-sup cv-sel evM-supv le-v-supv
          in mkSigma (Sup x1 x2) (mkSigma le-supx-u (mkSigma mem-supx evM-v))))))

-- Pi: Bot cases
EvalRel-Sup (Pi A B) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) Bot crho cu cv comp eu ev = eu

-- Pi: Absurd cases
EvalRel-Sup (Pi A B) rho UCode v crho cu cv comp () ev
EvalRel-Sup (Pi A B) rho (FunEl g1) v crho cu cv comp () ev
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) UCode crho cu cv comp eu ()
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) (FunEl g2) crho cu cv comp eu ()

-- Pi: PiCode-PiCode
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) (PiCode a2 f2) crho cu cv comp eu ev =
  let cu1   = fst eu
      evA1  = fst (snd eu)
      a1'   = fst (snd (snd eu))
      evA1' = fst (snd (snd (snd eu)))
      body1 = snd (snd (snd (snd eu)))
      cu2   = fst ev
      evA2  = fst (snd ev)
      a2'   = fst (snd (snd ev))
      evA2' = fst (snd (snd (snd ev)))
      body2 = snd (snd (snd (snd ev)))
      ca1   = EvalRel-coh A rho a1 evA1
      ca2   = EvalRel-coh A rho a2 evA2
      ca1'  = EvalRel-coh A rho a1' evA1'
      ca2'  = EvalRel-coh A rho a2' evA2'
      comp-a = fst comp
      comp-f = snd comp
      comp-a' = EvalRel-Comp A rho crho a1' a2' evA1' evA2'
      evA-sup = EvalRel-Sup A rho a1 a2 crho ca1 ca2 comp-a evA1 evA2
      evA'-sup = EvalRel-Sup A rho a1' a2' crho ca1' ca2' comp-a' evA1' evA2'
      c-sup-a' = Coherent-Sup a1' a2' comp-a' ca1' ca2'
      c-result = Coherent-Sup (PiCode a1 f1) (PiCode a2 f2) comp cu cv
      cf1   = snd cu1
      cf2   = snd cu2
      c-fab = CoherentFunTail-append f1 f2 cf1 cf2 comp-f
  in mkSigma c-result (mkSigma evA-sup
       (mkSigma (Sup a1' a2') (mkSigma evA'-sup
       (\ u v sel ->
          let cu-sel = Coherent-Selection sel c-fab
              cv-sel = Coherent-Selection-val sel c-fab
              sb1    = selectionBelow f1 u cf1 cu-sel
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow f2 u cf2 cu-sel
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              w1     = body1 u1 v1 sel1
              x1     = fst w1
              le-x1  = fst (snd w1)
              mem-x1 = fst (snd (snd w1))
              evB-x1 = snd (snd (snd w1))
              w2     = body2 u2 v2 sel2
              x2     = fst w2
              le-x2  = fst (snd w2)
              mem-x2 = fst (snd (snd w2))
              evB-x2 = snd (snd (snd w2))
              cx1    = FinMem-coh-u x1 a1' mem-x1
              cx2    = FinMem-coh-u x2 a2' mem-x2
              le-x1-u = LeCode-trans x1 u1 u cx1 (Coherent-Selection sel1 cf1) cu-sel le-x1 le-u1
              le-x2-u = LeCode-trans x2 u2 u cx2 (Coherent-Selection sel2 cf2) cu-sel le-x2 le-u2
              comp-x  = LeCode-Comp x1 x2 u cu-sel le-x1-u le-x2-u
              c-supx  = Coherent-Sup x1 x2 comp-x cx1 cx2
              le-supx-u = LeCode-Sup-lub x1 x2 u le-x1-u le-x2-u
              le-a1'-sup = LeCode-Sup-left a1' a2' comp-a' ca1' ca2'
              le-a2'-sup = LeCode-Sup-right a1' a2' comp-a' ca1' ca2'
              supU-a' = FinMem-a-in-U x1 a1' mem-x1
              supU-a'' = FinMem-a-in-U x2 a2' mem-x2
              supU-result = FinMem-Sup-element a1' a2' UCode comp-a' tt supU-a' supU-a''
              mem-x1-sup = finMem-upward x1 a1' (Sup a1' a2') le-a1'-sup ca1' c-sup-a' mem-x1 supU-result
              mem-x2-sup = finMem-upward x2 a2' (Sup a1' a2') le-a2'-sup ca2' c-sup-a' mem-x2 supU-result
              mem-supx   = FinMem-Sup-element x1 x2 (Sup a1' a2') comp-x c-sup-a' mem-x1-sup mem-x2-sup
              envle1 = EnvLe-extend-left rho x1 x2 crho comp-x cx1 cx2
              envle2 = EnvLe-extend-right rho x1 x2 crho comp-x cx1 cx2
              evB-sup1 = EvalRel-mon-env B (extendEnv rho x1) (extendEnv rho (Sup x1 x2)) v1 evB-x1 envle1
              evB-sup2 = EvalRel-mon-env B (extendEnv rho x2) (extendEnv rho (Sup x1 x2)) v2 evB-x2 envle2
              crho-sup = mkSigma crho c-supx
              comp-v = EvalRel-Comp B (extendEnv rho (Sup x1 x2)) crho-sup v1 v2 evB-sup1 evB-sup2
              cv1    = EvalRel-coh B (extendEnv rho x1) v1 evB-x1
              cv2    = EvalRel-coh B (extendEnv rho x2) v2 evB-x2
              evB-supv = EvalRel-Sup B (extendEnv rho (Sup x1 x2)) v1 v2 crho-sup cv1 cv2 comp-v evB-sup1 evB-sup2
              lf-fab = LeFunCode-refl (append f1 f2) c-fab
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-fab c-fab c-fab cu-sel
              ctf1   = cf1
              eq-ef  = EvalFun-append-eq f1 f2 u comp-f ctf1 cu-sel
              le-v-supef = Eq-transport (LeCode v) eq-ef le-v-ef
              eq-sup = Eq-transport (\ z -> Eq (Sup z (EvalFun f2 u)) (Sup v1 v2))
                         (Eq-sym eq-v1)
                         (Eq-transport (\ z -> Eq (Sup v1 z) (Sup v1 v2))
                           (Eq-sym eq-v2) refl)
              le-v-supv = Eq-transport (LeCode v) eq-sup le-v-supef
              c-supv = Coherent-Sup v1 v2 comp-v cv1 cv2
              evB-v  = EvalRel-down B (extendEnv rho (Sup x1 x2)) (Sup v1 v2) v crho-sup cv-sel evB-supv le-v-supv
          in mkSigma (Sup x1 x2) (mkSigma le-supx-u (mkSigma mem-supx evB-v))))))
-- Y : Bot cases (Sup Bot v = v, Sup u Bot = u definitionally)
EvalRel-Sup (Y g) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (Y g) rho UCode Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Y g) rho (FunEl g1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Y g) rho (PiCode a1 f1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Y g) rho NatCode Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Y g) rho ZeroEl Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Y g) rho (SucEl w1) Bot crho cu cv comp eu ev = eu
-- Y : cross-constructor non-Bot (Comp empty)
EvalRel-Sup (Y g) rho UCode (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho UCode (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho UCode NatCode crho cu cv () eu ev
EvalRel-Sup (Y g) rho UCode ZeroEl crho cu cv () eu ev
EvalRel-Sup (Y g) rho UCode (SucEl w2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho (FunEl g1) UCode crho cu cv () eu ev
EvalRel-Sup (Y g) rho (FunEl g1) (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho (FunEl g1) NatCode crho cu cv () eu ev
EvalRel-Sup (Y g) rho (FunEl g1) ZeroEl crho cu cv () eu ev
EvalRel-Sup (Y g) rho (FunEl g1) (SucEl w2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho (PiCode a1 f1) UCode crho cu cv () eu ev
EvalRel-Sup (Y g) rho (PiCode a1 f1) (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho (PiCode a1 f1) NatCode crho cu cv () eu ev
EvalRel-Sup (Y g) rho (PiCode a1 f1) ZeroEl crho cu cv () eu ev
EvalRel-Sup (Y g) rho (PiCode a1 f1) (SucEl w2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho NatCode UCode crho cu cv () eu ev
EvalRel-Sup (Y g) rho NatCode (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho NatCode (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho NatCode ZeroEl crho cu cv () eu ev
EvalRel-Sup (Y g) rho NatCode (SucEl w2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho ZeroEl UCode crho cu cv () eu ev
EvalRel-Sup (Y g) rho ZeroEl (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho ZeroEl (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho ZeroEl NatCode crho cu cv () eu ev
EvalRel-Sup (Y g) rho ZeroEl (SucEl w2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho (SucEl w1) UCode crho cu cv () eu ev
EvalRel-Sup (Y g) rho (SucEl w1) (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho (SucEl w1) (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Y g) rho (SucEl w1) NatCode crho cu cv () eu ev
EvalRel-Sup (Y g) rho (SucEl w1) ZeroEl crho cu cv () eu ev
-- Y : same-constructor
EvalRel-Sup (Y g) rho UCode UCode crho cu cv comp eu ev = eu
EvalRel-Sup (Y g) rho NatCode NatCode crho cu cv comp eu ev = eu
EvalRel-Sup (Y g) rho ZeroEl ZeroEl crho cu cv comp eu ev = eu
EvalRel-Sup (Y g) rho (FunEl g1) (FunEl g2) crho cu cv comp eu ev =
  YSup g rho (fst eu) (fst ev) (FunEl g1) (FunEl g2) crho cu cv comp (snd eu) (snd ev)
EvalRel-Sup (Y g) rho (PiCode a1 f1) (PiCode a2 f2) crho cu cv comp eu ev =
  YSup g rho (fst eu) (fst ev) (PiCode a1 f1) (PiCode a2 f2) crho cu cv comp (snd eu) (snd ev)
EvalRel-Sup (Y g) rho (SucEl w1) (SucEl w2) crho cu cv comp eu ev =
  YSup g rho (fst eu) (fst ev) (SucEl w1) (SucEl w2) crho cu cv comp (snd eu) (snd ev)

------------------------------------------------------------------------
-- EvalRel-Comp-ext: compatibility of evaluation results at
-- compatible environment extensions.
------------------------------------------------------------------------

EvalRel-Comp-ext : {n : Nat} (M : Expr (suc n)) (rho : EnvApprox n)
  (x1 x2 y1 y2 : FinEl) ->
  CoherentEnv rho -> Comp x1 x2 -> Coherent x1 -> Coherent x2 ->
  EvalRel M (extendEnv rho x1) y1 ->
  EvalRel M (extendEnv rho x2) y2 ->
  Comp y1 y2
EvalRel-Comp-ext M rho x1 x2 y1 y2 crho comp cx1 cx2 ev1 ev2 =
  let envle1 = EnvLe-extend-left rho x1 x2 crho comp cx1 cx2
      envle2 = EnvLe-extend-right rho x1 x2 crho comp cx1 cx2
      ev1'   = EvalRel-mon-env M (extendEnv rho x1) (extendEnv rho (Sup x1 x2))
                 y1 ev1 envle1
      ev2'   = EvalRel-mon-env M (extendEnv rho x2) (extendEnv rho (Sup x1 x2))
                 y2 ev2 envle2
      c-sup  = Coherent-Sup x1 x2 comp cx1 cx2
      crho'  = mkSigma crho c-sup
  in EvalRel-Comp M (extendEnv rho (Sup x1 x2)) crho' y1 y2 ev1' ev2'

------------------------------------------------------------------------
-- EvalRel-ideal-Comp: Sup-closure of evaluation at compatible
-- environment extensions.
------------------------------------------------------------------------

EvalRel-ideal-Comp : {n : Nat} (M : Expr (suc n)) (rho : EnvApprox n)
  (x1 x2 y1 y2 : FinEl) ->
  CoherentEnv rho -> Comp x1 x2 -> Coherent x1 -> Coherent x2 ->
  EvalRel M (extendEnv rho x1) y1 ->
  EvalRel M (extendEnv rho x2) y2 ->
  EvalRel M (extendEnv rho (Sup x1 x2)) (Sup y1 y2)
EvalRel-ideal-Comp M rho x1 x2 y1 y2 crho comp cx1 cx2 ev1 ev2 =
  let envle1 = EnvLe-extend-left rho x1 x2 crho comp cx1 cx2
      envle2 = EnvLe-extend-right rho x1 x2 crho comp cx1 cx2
      ev1'   = EvalRel-mon-env M (extendEnv rho x1) (extendEnv rho (Sup x1 x2))
                 y1 ev1 envle1
      ev2'   = EvalRel-mon-env M (extendEnv rho x2) (extendEnv rho (Sup x1 x2))
                 y2 ev2 envle2
      c-sup  = Coherent-Sup x1 x2 comp cx1 cx2
      crho'  = mkSigma crho c-sup
      cy1    = EvalRel-coh M (extendEnv rho (Sup x1 x2)) y1 ev1'
      cy2    = EvalRel-coh M (extendEnv rho (Sup x1 x2)) y2 ev2'
      comp-y = EvalRel-Comp M (extendEnv rho (Sup x1 x2)) crho' y1 y2 ev1' ev2'
  in EvalRel-Sup M (extendEnv rho (Sup x1 x2)) y1 y2 crho' cy1 cy2 comp-y ev1' ev2'


------------------------------------------------------------------------
-- YSup / singletonSup clauses
------------------------------------------------------------------------

-- n1 = 0 : u <= Bot, so Sup u v = v (Sup Bot v = v definitionally when u = Bot).
YSup g rho zero n2 Bot          v crho cu cv comp eu ev = mkSigma n2 ev
YSup g rho zero n2 UCode        v crho cu cv comp eu ev =
  absurd (Coherent-val-LeBot-absurd UCode (mkSigma tt tt) (snd eu))
YSup g rho zero n2 (FunEl g0)   v crho cu cv comp eu ev =
  absurd (Coherent-val-LeBot-absurd (FunEl g0) (mkSigma cu tt) (snd eu))
YSup g rho zero n2 (PiCode a0 f0) v crho cu cv comp eu ev =
  absurd (Coherent-val-LeBot-absurd (PiCode a0 f0) (mkSigma cu tt) (snd eu))
YSup g rho zero n2 NatCode      v crho cu cv comp eu ev =
  absurd (Coherent-val-LeBot-absurd NatCode (mkSigma tt tt) (snd eu))
YSup g rho zero n2 ZeroEl       v crho cu cv comp eu ev =
  absurd (Coherent-val-LeBot-absurd ZeroEl (mkSigma tt tt) (snd eu))
YSup g rho zero n2 (SucEl w0)   v crho cu cv comp eu ev =
  absurd (Coherent-val-LeBot-absurd (SucEl w0) (mkSigma cu tt) (snd eu))
-- n1 = suc, n2 = 0 : v <= Bot, so Sup u Bot = u (match u for the reduction).
YSup g rho (suc k1) zero u Bot          crho cu cv comp eu ev =
  Eq-transport (\ w -> EvalRel (Y g) rho w) (Eq-sym (Sup-Bot-r u)) (mkSigma (suc k1) eu)
YSup g rho (suc k1) zero u UCode        crho cu cv comp eu ev =
  absurd (Coherent-val-LeBot-absurd UCode (mkSigma tt tt) (snd ev))
YSup g rho (suc k1) zero u (FunEl g0)   crho cu cv comp eu ev =
  absurd (Coherent-val-LeBot-absurd (FunEl g0) (mkSigma cv tt) (snd ev))
YSup g rho (suc k1) zero u (PiCode a0 f0) crho cu cv comp eu ev =
  absurd (Coherent-val-LeBot-absurd (PiCode a0 f0) (mkSigma cv tt) (snd ev))
YSup g rho (suc k1) zero u NatCode      crho cu cv comp eu ev =
  absurd (Coherent-val-LeBot-absurd NatCode (mkSigma tt tt) (snd ev))
YSup g rho (suc k1) zero u ZeroEl       crho cu cv comp eu ev =
  absurd (Coherent-val-LeBot-absurd ZeroEl (mkSigma tt tt) (snd ev))
YSup g rho (suc k1) zero u (SucEl w0)   crho cu cv comp eu ev =
  absurd (Coherent-val-LeBot-absurd (SucEl w0) (mkSigma cv tt) (snd ev))
-- n1 = suc, n2 = suc : both have a real edge; recurse on the inner approximants.
YSup g rho (suc k1) (suc k2) u v crho cu cv comp eu ev =
  let p1 = fst eu ; A1 = fst (snd eu) ; s1 = snd (snd eu)
      p2 = fst ev ; A2 = fst (snd ev) ; s2 = snd (snd ev)
      cF1 = EvalRel-coh g rho (FunEl (cons (mkSigma p1 u) nil)) s1
      cF2 = EvalRel-coh g rho (FunEl (cons (mkSigma p2 v) nil)) s2
      cp1 = Coherent-singleton-key p1 u cF1
      cp2 = Coherent-singleton-key p2 v cF2
      nbu = CFTcons.val-nbot cF1
      nbv = CFTcons.val-nbot cF2
      comp-p = Approx-Comp (\ p w -> EvalRel g rho (FunEl (cons (mkSigma p w) nil)))
                 (\ q1 x1 q2 x2 cq t1 t2 ->
                    fst (fst (EvalRel-Comp g rho crho
                              (FunEl (cons (mkSigma q1 x1) nil))
                              (FunEl (cons (mkSigma q2 x2) nil)) t1 t2)) cq)
                 k1 k2 p1 p2 A1 A2
      inner = YSup g rho k1 k2 p1 p2 crho cp1 cp2 comp-p A1 A2
      edgeR = singletonSup g rho p1 u p2 v crho comp-p comp cu cv nbu nbv s1 s2
  in mkSigma (suc (fst inner)) (mkSigma (Sup p1 p2) (mkSigma (snd inner) edgeR))

singletonSup g rho p1 w1 p2 w2 crho comp-p comp-w cw1 cw2 nbw1 nbw2 ev1 ev2 =
  let cF1 = EvalRel-coh g rho (FunEl (cons (mkSigma p1 w1) nil)) ev1
      cF2 = EvalRel-coh g rho (FunEl (cons (mkSigma p2 w2) nil)) ev2
      cp1 = Coherent-singleton-key p1 w1 cF1
      cp2 = Coherent-singleton-key p2 w2 cF2
      comp-M = EvalRel-Comp g rho crho (FunEl (cons (mkSigma p1 w1) nil)) (FunEl (cons (mkSigma p2 w2) nil)) ev1 ev2
      ev-2 = EvalRel-Sup g rho (FunEl (cons (mkSigma p1 w1) nil)) (FunEl (cons (mkSigma p2 w2) nil)) crho cF1 cF2 comp-M ev1 ev2
      c-2graph = Coherent-Sup (FunEl (cons (mkSigma p1 w1) nil)) (FunEl (cons (mkSigma p2 w2) nil)) comp-M cF1 cF2
      c-supp   = Coherent-Sup p1 p2 comp-p cp1 cp2
      c-supw   = Coherent-Sup w1 w2 comp-w cw1 cw2
      le-down  = LeFunCode-Sup-pair p1 w1 p2 w2 comp-p comp-w c-2graph c-supp
      c-single = mkCFT c-supp c-supw (NotBot-Sup-Comp w1 w2 nbw1 comp-w) tt tt
  in EvalRel-down g rho
       (FunEl (cons (mkSigma p1 w1) (cons (mkSigma p2 w2) nil)))
       (FunEl (cons (mkSigma (Sup p1 p2) (Sup w1 w2)) nil))
       crho c-single ev-2 le-down
