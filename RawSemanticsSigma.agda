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

module RawSemanticsSigma where

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ;
              Pair ; List ; nil ; cons ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; SigmaCode ; PairCode ; FinFun)
open import PaperSemanticsSigma using (LeCode ; LeCode-refl ; LeCode-trans ; LeCode-Bot ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ; cft-from-cf ;
  NotBot ; Coherent-singleton-key ; Coherent-singleton-val ;
  FinMem ; FinMemAllU ; FinMem-coh-u ; FinMem-a-in-U ; Sup ; Sup-Bot-r ; Sup-Bot-l ;
  Comp ; CompFun ; CompStepFun ; CompStepStep ;
  comp-Bot-r ; comp-Bot-l ; Comp-down ; Comp-sym ;
  Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub ;
  LeCode-Comp ;
  EvalFun ; EvalFun-mon ; EvalFun-mon-arg ; comp-EvalFun ; Coherent-EvalFun ;
  EvalFun-append-eq ;
  CoherentFun-append ; CoherentFunTail-append ; FinMem-Sup-element ;
  finMem-Sup-left ; finMem-Sup-right ;
  finMem-upward ; LeFunCode ; LeFunCode-refl ; append ;
  Or ; inl ; inr ;
  fstEl ; sndEl ;
  NotBot-Sup-Comp ; Or-NotBot-Sup)
open import SelectionSigma using (Selection ; Edge ; EdgeIn ; here ; there ;
  sel-nil ; sel-take ; sel-skip ; sel-skip-all ;
  Coherent-Selection ; Coherent-Selection-val ;
  singleton-selection ; Selection-le-EvalFun ; selectionBelow ;
  FinMemAllU-Selection)
open import RawSyntaxSigma hiding (Sigma)

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
-- Part 2: EvalRel
------------------------------------------------------------------------

EvalRel : {n : Nat} -> Expr n -> EnvApprox n -> FinEl -> Set

-- Variables
EvalRel (Var i) rho b = Pair (Coherent b) (LeCode b (lookupEnv i rho))

-- Universe
EvalRel U rho b = Pair (Coherent b) (LeCode b UCode)

-- Prop
EvalRel Prop rho b = Pair (Coherent b) (LeCode b PropCode)

-- Application
EvalRel (App M N) rho Bot = Top
EvalRel (App M N) rho UCode =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v UCode) nil))))
EvalRel (App M N) rho PropCode =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v PropCode) nil))))
EvalRel (App M N) rho (FunEl g') =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v (FunEl g')) nil))))
EvalRel (App M N) rho (PiCode a' f') =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v (PiCode a' f')) nil))))
EvalRel (App M N) rho (SigmaCode a' f') =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v (SigmaCode a' f')) nil))))
EvalRel (App M N) rho (PairCode u' v') =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v (PairCode u' v')) nil))))

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
EvalRel (Lam A M) rho PropCode      = Empty
EvalRel (Lam A M) rho (PiCode a f)  = Empty
EvalRel (Lam A M) rho (SigmaCode a f) = Empty
EvalRel (Lam A M) rho (PairCode u v)  = Empty

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
EvalRel (Pi A B) rho PropCode       = Empty
EvalRel (Pi A B) rho (FunEl g)      = Empty
EvalRel (Pi A B) rho (SigmaCode a f) = Empty
EvalRel (Pi A B) rho (PairCode u v)  = Empty

-- Sigma (mirrors Pi)
EvalRel (RawSyntaxSigma.Sigma A B) rho Bot = Top
EvalRel (RawSyntaxSigma.Sigma A B) rho (SigmaCode a f) =
  Pair (Coherent (SigmaCode a f))
    (Pair (EvalRel A rho a)
      (Sigma FinEl (\ a' ->
        Pair (EvalRel A rho a')
          ((u v : FinEl) ->
            Selection f u v ->
            Sigma FinEl (\ x ->
              Pair (LeCode x u)
                   (Pair (FinMem x a')
                         (EvalRel B (extendEnv rho x) v)))))))
EvalRel (RawSyntaxSigma.Sigma A B) rho UCode          = Empty
EvalRel (RawSyntaxSigma.Sigma A B) rho PropCode       = Empty
EvalRel (RawSyntaxSigma.Sigma A B) rho (FunEl g)      = Empty
EvalRel (RawSyntaxSigma.Sigma A B) rho (PiCode a f)   = Empty
EvalRel (RawSyntaxSigma.Sigma A B) rho (PairCode u v)  = Empty

-- MkPair: PairCode u v bundles Coherent (PairCode u v)
-- and domain/codomain membership evidence
EvalRel (MkPair M N) rho Bot = Top
EvalRel (MkPair M N) rho (PairCode u v) =
  Pair (Coherent (PairCode u v))
    (Pair (EvalRel M rho u) (EvalRel N rho v))
EvalRel (MkPair M N) rho UCode          = Empty
EvalRel (MkPair M N) rho PropCode       = Empty
EvalRel (MkPair M N) rho (FunEl g)      = Empty
EvalRel (MkPair M N) rho (PiCode a f)   = Empty
EvalRel (MkPair M N) rho (SigmaCode a f) = Empty

-- Fst: project first component
EvalRel (Fst M) rho Bot = Top
EvalRel (Fst M) rho UCode =
  S.Sigma FinEl (\ v -> EvalRel M rho (PairCode UCode v))
EvalRel (Fst M) rho PropCode =
  S.Sigma FinEl (\ v -> EvalRel M rho (PairCode PropCode v))
EvalRel (Fst M) rho (FunEl g) =
  S.Sigma FinEl (\ v -> EvalRel M rho (PairCode (FunEl g) v))
EvalRel (Fst M) rho (PiCode a f) =
  S.Sigma FinEl (\ v -> EvalRel M rho (PairCode (PiCode a f) v))
EvalRel (Fst M) rho (SigmaCode a f) =
  S.Sigma FinEl (\ v -> EvalRel M rho (PairCode (SigmaCode a f) v))
EvalRel (Fst M) rho (PairCode u' v') =
  S.Sigma FinEl (\ v -> EvalRel M rho (PairCode (PairCode u' v') v))

-- Snd: project second component
EvalRel (Snd M) rho Bot = Top
EvalRel (Snd M) rho UCode =
  S.Sigma FinEl (\ u -> EvalRel M rho (PairCode u UCode))
EvalRel (Snd M) rho PropCode =
  S.Sigma FinEl (\ u -> EvalRel M rho (PairCode u PropCode))
EvalRel (Snd M) rho (FunEl g) =
  S.Sigma FinEl (\ u -> EvalRel M rho (PairCode u (FunEl g)))
EvalRel (Snd M) rho (PiCode a f) =
  S.Sigma FinEl (\ u -> EvalRel M rho (PairCode u (PiCode a f)))
EvalRel (Snd M) rho (SigmaCode a f) =
  S.Sigma FinEl (\ u -> EvalRel M rho (PairCode u (SigmaCode a f)))
EvalRel (Snd M) rho (PairCode u' v') =
  S.Sigma FinEl (\ u -> EvalRel M rho (PairCode u (PairCode u' v')))

------------------------------------------------------------------------
-- CoherentFun-LeBot-absurd
------------------------------------------------------------------------

{-# TERMINATING #-}
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
  Coherent-val-LeBot-absurd PropCode cnb ()
  Coherent-val-LeBot-absurd (PiCode a f) cnb ()
  Coherent-val-LeBot-absurd (FunEl h) cnb ()
  Coherent-val-LeBot-absurd (SigmaCode a f) cnb ()
  Coherent-val-LeBot-absurd (PairCode u v) cnb ()

------------------------------------------------------------------------
-- Part 3: Coherence extraction
------------------------------------------------------------------------

EvalRel-coh : {n : Nat} (M : Expr n) (rho : EnvApprox n) (u : FinEl) ->
  EvalRel M rho u -> Coherent u

EvalRel-coh (Var i) rho u ev = fst ev
EvalRel-coh U rho u ev = fst ev
EvalRel-coh Prop rho u ev = fst ev
-- App
EvalRel-coh (App M N) rho Bot ev = tt
EvalRel-coh (App M N) rho UCode ev = tt
EvalRel-coh (App M N) rho PropCode ev = tt
EvalRel-coh (App M N) rho (FunEl g') ev =
  Coherent-singleton-val (fst ev) (FunEl g')
    (EvalRel-coh M rho (FunEl (cons (mkSigma (fst ev) (FunEl g')) nil)) (snd (snd ev)))
EvalRel-coh (App M N) rho (PiCode a' f') ev =
  Coherent-singleton-val (fst ev) (PiCode a' f')
    (EvalRel-coh M rho (FunEl (cons (mkSigma (fst ev) (PiCode a' f')) nil)) (snd (snd ev)))
EvalRel-coh (App M N) rho (SigmaCode a' f') ev =
  Coherent-singleton-val (fst ev) (SigmaCode a' f')
    (EvalRel-coh M rho (FunEl (cons (mkSigma (fst ev) (SigmaCode a' f')) nil)) (snd (snd ev)))
EvalRel-coh (App M N) rho (PairCode u' v') ev =
  Coherent-singleton-val (fst ev) (PairCode u' v')
    (EvalRel-coh M rho (FunEl (cons (mkSigma (fst ev) (PairCode u' v')) nil)) (snd (snd ev)))
-- Lam
EvalRel-coh (Lam A M) rho Bot ev = tt
EvalRel-coh (Lam A M) rho (FunEl g) ev = fst (snd ev)
EvalRel-coh (Lam A M) rho UCode ()
EvalRel-coh (Lam A M) rho PropCode ()
EvalRel-coh (Lam A M) rho (PiCode a f) ()
EvalRel-coh (Lam A M) rho (SigmaCode a f) ()
EvalRel-coh (Lam A M) rho (PairCode u v) ()
-- Pi
EvalRel-coh (Pi A B) rho Bot ev = tt
EvalRel-coh (Pi A B) rho (PiCode a f) ev = fst ev
EvalRel-coh (Pi A B) rho UCode ()
EvalRel-coh (Pi A B) rho PropCode ()
EvalRel-coh (Pi A B) rho (FunEl g) ()
EvalRel-coh (Pi A B) rho (SigmaCode a f) ()
EvalRel-coh (Pi A B) rho (PairCode u v) ()
-- Sigma
EvalRel-coh (RawSyntaxSigma.Sigma A B) rho Bot ev = tt
EvalRel-coh (RawSyntaxSigma.Sigma A B) rho (SigmaCode a f) ev = fst ev
EvalRel-coh (RawSyntaxSigma.Sigma A B) rho UCode ()
EvalRel-coh (RawSyntaxSigma.Sigma A B) rho PropCode ()
EvalRel-coh (RawSyntaxSigma.Sigma A B) rho (FunEl g) ()
EvalRel-coh (RawSyntaxSigma.Sigma A B) rho (PiCode a f) ()
EvalRel-coh (RawSyntaxSigma.Sigma A B) rho (PairCode u v) ()
-- MkPair
EvalRel-coh (MkPair M N) rho Bot ev = tt
EvalRel-coh (MkPair M N) rho (PairCode u v) ev = fst ev
EvalRel-coh (MkPair M N) rho UCode ()
EvalRel-coh (MkPair M N) rho PropCode ()
EvalRel-coh (MkPair M N) rho (FunEl g) ()
EvalRel-coh (MkPair M N) rho (PiCode a f) ()
EvalRel-coh (MkPair M N) rho (SigmaCode a f) ()
-- Fst
EvalRel-coh (Fst M) rho Bot ev = tt
EvalRel-coh (Fst M) rho UCode ev =
  fst (fst (EvalRel-coh M rho (PairCode UCode (fst ev)) (snd ev)))
EvalRel-coh (Fst M) rho PropCode ev =
  fst (fst (EvalRel-coh M rho (PairCode PropCode (fst ev)) (snd ev)))
EvalRel-coh (Fst M) rho (FunEl g) ev =
  fst (fst (EvalRel-coh M rho (PairCode (FunEl g) (fst ev)) (snd ev)))
EvalRel-coh (Fst M) rho (PiCode a f) ev =
  fst (fst (EvalRel-coh M rho (PairCode (PiCode a f) (fst ev)) (snd ev)))
EvalRel-coh (Fst M) rho (SigmaCode a f) ev =
  fst (fst (EvalRel-coh M rho (PairCode (SigmaCode a f) (fst ev)) (snd ev)))
EvalRel-coh (Fst M) rho (PairCode u' v') ev =
  fst (fst (EvalRel-coh M rho (PairCode (PairCode u' v') (fst ev)) (snd ev)))
-- Snd
EvalRel-coh (Snd M) rho Bot ev = tt
EvalRel-coh (Snd M) rho UCode ev =
  snd (fst (EvalRel-coh M rho (PairCode (fst ev) UCode) (snd ev)))
EvalRel-coh (Snd M) rho PropCode ev =
  snd (fst (EvalRel-coh M rho (PairCode (fst ev) PropCode) (snd ev)))
EvalRel-coh (Snd M) rho (FunEl g) ev =
  snd (fst (EvalRel-coh M rho (PairCode (fst ev) (FunEl g)) (snd ev)))
EvalRel-coh (Snd M) rho (PiCode a f) ev =
  snd (fst (EvalRel-coh M rho (PairCode (fst ev) (PiCode a f)) (snd ev)))
EvalRel-coh (Snd M) rho (SigmaCode a f) ev =
  snd (fst (EvalRel-coh M rho (PairCode (fst ev) (SigmaCode a f)) (snd ev)))
EvalRel-coh (Snd M) rho (PairCode u' v') ev =
  snd (fst (EvalRel-coh M rho (PairCode (fst ev) (PairCode u' v')) (snd ev)))

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
EvalRel-Bot Prop rho = mkSigma tt tt
EvalRel-Bot (App M N) rho = tt
EvalRel-Bot (Lam A M) rho = tt
EvalRel-Bot (Pi A B) rho = tt
EvalRel-Bot (RawSyntaxSigma.Sigma A B) rho = tt
EvalRel-Bot (MkPair M N) rho = tt
EvalRel-Bot (Fst M) rho = tt
EvalRel-Bot (Snd M) rho = tt

------------------------------------------------------------------------
-- EvalRel-mon-env
------------------------------------------------------------------------

EvalRel-mon-env : {n : Nat} (M : Expr n) (rho rho' : EnvApprox n) (u : FinEl) ->
  EvalRel M rho u -> EnvLe rho rho' -> EvalRel M rho' u

EvalRel-mon-env (Var i) rho rho' u ev envle =
  mkSigma (fst ev) (LeCode-trans u (lookupEnv i rho) (lookupEnv i rho')
    (fst ev) (lookupEnv-coh-left i rho rho' envle)
    (lookupEnv-coh-right i rho rho' envle) (snd ev) (lookupEnv-mon i rho rho' envle))
EvalRel-mon-env U rho rho' u ev envle = ev
EvalRel-mon-env Prop rho rho' u ev envle = ev
-- App
EvalRel-mon-env (App M N) rho rho' Bot ev envle = tt
EvalRel-mon-env (App M N) rho rho' UCode ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
EvalRel-mon-env (App M N) rho rho' PropCode ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
EvalRel-mon-env (App M N) rho rho' (FunEl g') ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
EvalRel-mon-env (App M N) rho rho' (PiCode a' f') ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
EvalRel-mon-env (App M N) rho rho' (SigmaCode a' f') ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
EvalRel-mon-env (App M N) rho rho' (PairCode u' v') ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
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
EvalRel-mon-env (Lam A M) rho rho' PropCode () envle
EvalRel-mon-env (Lam A M) rho rho' (PiCode a f) () envle
EvalRel-mon-env (Lam A M) rho rho' (SigmaCode a f) () envle
EvalRel-mon-env (Lam A M) rho rho' (PairCode u v) () envle
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
EvalRel-mon-env (Pi A B) rho rho' PropCode () envle
EvalRel-mon-env (Pi A B) rho rho' (FunEl g) () envle
EvalRel-mon-env (Pi A B) rho rho' (SigmaCode a f) () envle
EvalRel-mon-env (Pi A B) rho rho' (PairCode u v) () envle
-- Sigma (mirrors Pi)
EvalRel-mon-env (RawSyntaxSigma.Sigma A B) rho rho' Bot ev envle = tt
EvalRel-mon-env (RawSyntaxSigma.Sigma A B) rho rho' (SigmaCode a f) ev envle =
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
EvalRel-mon-env (RawSyntaxSigma.Sigma A B) rho rho' UCode () envle
EvalRel-mon-env (RawSyntaxSigma.Sigma A B) rho rho' PropCode () envle
EvalRel-mon-env (RawSyntaxSigma.Sigma A B) rho rho' (FunEl g) () envle
EvalRel-mon-env (RawSyntaxSigma.Sigma A B) rho rho' (PiCode a f) () envle
EvalRel-mon-env (RawSyntaxSigma.Sigma A B) rho rho' (PairCode u v) () envle
-- MkPair
EvalRel-mon-env (MkPair M N) rho rho' Bot ev envle = tt
EvalRel-mon-env (MkPair M N) rho rho' (PairCode u v) ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env M rho rho' u (fst (snd ev)) envle)
                             (EvalRel-mon-env N rho rho' v (snd (snd ev)) envle))
EvalRel-mon-env (MkPair M N) rho rho' UCode () envle
EvalRel-mon-env (MkPair M N) rho rho' PropCode () envle
EvalRel-mon-env (MkPair M N) rho rho' (FunEl g) () envle
EvalRel-mon-env (MkPair M N) rho rho' (PiCode a f) () envle
EvalRel-mon-env (MkPair M N) rho rho' (SigmaCode a f) () envle
-- Fst
EvalRel-mon-env (Fst M) rho rho' Bot ev envle = tt
EvalRel-mon-env (Fst M) rho rho' UCode ev envle =
  mkSigma (fst ev) (EvalRel-mon-env M rho rho' (PairCode UCode (fst ev)) (snd ev) envle)
EvalRel-mon-env (Fst M) rho rho' PropCode ev envle =
  mkSigma (fst ev) (EvalRel-mon-env M rho rho' (PairCode PropCode (fst ev)) (snd ev) envle)
EvalRel-mon-env (Fst M) rho rho' (FunEl g) ev envle =
  mkSigma (fst ev) (EvalRel-mon-env M rho rho' (PairCode (FunEl g) (fst ev)) (snd ev) envle)
EvalRel-mon-env (Fst M) rho rho' (PiCode a f) ev envle =
  mkSigma (fst ev) (EvalRel-mon-env M rho rho' (PairCode (PiCode a f) (fst ev)) (snd ev) envle)
EvalRel-mon-env (Fst M) rho rho' (SigmaCode a f) ev envle =
  mkSigma (fst ev) (EvalRel-mon-env M rho rho' (PairCode (SigmaCode a f) (fst ev)) (snd ev) envle)
EvalRel-mon-env (Fst M) rho rho' (PairCode u' v') ev envle =
  mkSigma (fst ev) (EvalRel-mon-env M rho rho' (PairCode (PairCode u' v') (fst ev)) (snd ev) envle)
-- Snd
EvalRel-mon-env (Snd M) rho rho' Bot ev envle = tt
EvalRel-mon-env (Snd M) rho rho' UCode ev envle =
  mkSigma (fst ev) (EvalRel-mon-env M rho rho' (PairCode (fst ev) UCode) (snd ev) envle)
EvalRel-mon-env (Snd M) rho rho' PropCode ev envle =
  mkSigma (fst ev) (EvalRel-mon-env M rho rho' (PairCode (fst ev) PropCode) (snd ev) envle)
EvalRel-mon-env (Snd M) rho rho' (FunEl g) ev envle =
  mkSigma (fst ev) (EvalRel-mon-env M rho rho' (PairCode (fst ev) (FunEl g)) (snd ev) envle)
EvalRel-mon-env (Snd M) rho rho' (PiCode a f) ev envle =
  mkSigma (fst ev) (EvalRel-mon-env M rho rho' (PairCode (fst ev) (PiCode a f)) (snd ev) envle)
EvalRel-mon-env (Snd M) rho rho' (SigmaCode a f) ev envle =
  mkSigma (fst ev) (EvalRel-mon-env M rho rho' (PairCode (fst ev) (SigmaCode a f)) (snd ev) envle)
EvalRel-mon-env (Snd M) rho rho' (PairCode u' v') ev envle =
  mkSigma (fst ev) (EvalRel-mon-env M rho rho' (PairCode (fst ev) (PairCode u' v')) (snd ev) envle)

------------------------------------------------------------------------
-- App-decompose
------------------------------------------------------------------------

App-decompose : {n : Nat} (M N : Expr n) (rho : EnvApprox n)
  (u : FinEl) -> NotBot u ->
  EvalRel (App M N) rho u ->
  S.Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v u) nil))))
App-decompose M N rho UCode        nb ev = ev
App-decompose M N rho PropCode     nb ev = ev
App-decompose M N rho (FunEl g')   nb ev = ev
App-decompose M N rho (PiCode a f) nb ev = ev
App-decompose M N rho (SigmaCode a f) nb ev = ev
App-decompose M N rho (PairCode u v) nb ev = ev

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

Sigma-edgewise : {n : Nat} (A : Expr n) (B : Expr (suc n))
  (rho : EnvApprox n) (a : FinEl) (f : FinFun) ->
  EvalRel (RawSyntaxSigma.Sigma A B) rho (SigmaCode a f) ->
  Pair (Coherent (SigmaCode a f))
    (Pair (EvalRel A rho a)
      (S.Sigma FinEl (\ a' ->
        Pair (EvalRel A rho a')
          ((p : Edge) -> EdgeIn p f ->
            S.Sigma FinEl (\ x ->
              Pair (LeCode x (fst p))
                   (Pair (FinMem x a')
                         (EvalRel B (extendEnv rho x) (snd p))))))))
Sigma-edgewise A B rho a f ev =
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

------------------------------------------------------------------------
-- EvalRel-Comp
------------------------------------------------------------------------

EvalRel-Comp : {n : Nat} (M : Expr n) (rho : EnvApprox n) ->
  CoherentEnv rho -> (u v : FinEl) ->
  EvalRel M rho u -> EvalRel M rho v -> Comp u v

EvalRel-Comp (Var i) rho crho u v ev1 ev2 =
  LeCode-Comp u v (lookupEnv i rho) (lookupEnv-coh i rho crho) (snd ev1) (snd ev2)
EvalRel-Comp U rho crho u v ev1 ev2 = LeCode-Comp u v UCode tt (snd ev1) (snd ev2)
EvalRel-Comp Prop rho crho u v ev1 ev2 = LeCode-Comp u v PropCode tt (snd ev1) (snd ev2)

-- App: Bot trivial, non-Bot×non-Bot via App-Comp-helper
EvalRel-Comp (App M N) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (App M N) rho crho UCode Bot ev1 ev2 = comp-Bot-r UCode
EvalRel-Comp (App M N) rho crho PropCode Bot ev1 ev2 = comp-Bot-r PropCode
EvalRel-Comp (App M N) rho crho (FunEl g1') Bot ev1 ev2 = comp-Bot-r (FunEl g1')
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') Bot ev1 ev2 = comp-Bot-r (PiCode a1' f1')
EvalRel-Comp (App M N) rho crho (SigmaCode a1' f1') Bot ev1 ev2 = comp-Bot-r (SigmaCode a1' f1')
EvalRel-Comp (App M N) rho crho (PairCode u1' v1') Bot ev1 ev2 = comp-Bot-r (PairCode u1' v1')
-- All non-Bot × non-Bot App cases: use App-Comp-helper
EvalRel-Comp (App M N) rho crho UCode UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho UCode PropCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode PropCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho UCode (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho UCode (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho UCode (SigmaCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode (SigmaCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho UCode (PairCode u2' v2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode (PairCode u2' v2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho PropCode UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    PropCode UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho PropCode PropCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    PropCode PropCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho PropCode (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    PropCode (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho PropCode (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    PropCode (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho PropCode (SigmaCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    PropCode (SigmaCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho PropCode (PairCode u2' v2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    PropCode (PairCode u2' v2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') PropCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') PropCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') (SigmaCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') (SigmaCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') (PairCode u2' v2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') (PairCode u2' v2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') PropCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') PropCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') (SigmaCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') (SigmaCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') (PairCode u2' v2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') (PairCode u2' v2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (SigmaCode a1' f1') UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (SigmaCode a1' f1') UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (SigmaCode a1' f1') PropCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (SigmaCode a1' f1') PropCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (SigmaCode a1' f1') (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (SigmaCode a1' f1') (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (SigmaCode a1' f1') (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (SigmaCode a1' f1') (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (SigmaCode a1' f1') (SigmaCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (SigmaCode a1' f1') (SigmaCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (SigmaCode a1' f1') (PairCode u2' v2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (SigmaCode a1' f1') (PairCode u2' v2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PairCode u1' v1') UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PairCode u1' v1') UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PairCode u1' v1') PropCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PairCode u1' v1') PropCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PairCode u1' v1') (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PairCode u1' v1') (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PairCode u1' v1') (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PairCode u1' v1') (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PairCode u1' v1') (SigmaCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PairCode u1' v1') (SigmaCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PairCode u1' v1') (PairCode u2' v2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PairCode u1' v1') (PairCode u2' v2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))

-- Lam
EvalRel-Comp (Lam A M) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (Lam A M) rho crho (FunEl g1) Bot ev1 ev2 = comp-Bot-r (FunEl g1)
EvalRel-Comp (Lam A M) rho crho UCode v () ev2
EvalRel-Comp (Lam A M) rho crho PropCode v () ev2
EvalRel-Comp (Lam A M) rho crho (PiCode a1 f1) v () ev2
EvalRel-Comp (Lam A M) rho crho (SigmaCode a1 f1) v () ev2
EvalRel-Comp (Lam A M) rho crho (PairCode u1 v1) v () ev2
EvalRel-Comp (Lam A M) rho crho (FunEl g1) UCode ev1 ()
EvalRel-Comp (Lam A M) rho crho (FunEl g1) PropCode ev1 ()
EvalRel-Comp (Lam A M) rho crho (FunEl g1) (PiCode a2 f2) ev1 ()
EvalRel-Comp (Lam A M) rho crho (FunEl g1) (SigmaCode a2 f2) ev1 ()
EvalRel-Comp (Lam A M) rho crho (FunEl g1) (PairCode u2 v2) ev1 ()
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
EvalRel-Comp (Pi A B) rho crho PropCode v () ev2
EvalRel-Comp (Pi A B) rho crho (FunEl g1) v () ev2
EvalRel-Comp (Pi A B) rho crho (SigmaCode a1 f1) v () ev2
EvalRel-Comp (Pi A B) rho crho (PairCode u1 v1) v () ev2
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) UCode ev1 ()
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) PropCode ev1 ()
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) (FunEl g2) ev1 ()
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) (SigmaCode a2 f2) ev1 ()
EvalRel-Comp (Pi A B) rho crho (PiCode a1 f1) (PairCode u2 v2) ev1 ()
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

-- Sigma (mirrors Pi)
EvalRel-Comp (RawSyntaxSigma.Sigma A B) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (RawSyntaxSigma.Sigma A B) rho crho (SigmaCode a1 f1) Bot ev1 ev2 = comp-Bot-r (SigmaCode a1 f1)
EvalRel-Comp (RawSyntaxSigma.Sigma A B) rho crho UCode v () ev2
EvalRel-Comp (RawSyntaxSigma.Sigma A B) rho crho PropCode v () ev2
EvalRel-Comp (RawSyntaxSigma.Sigma A B) rho crho (FunEl g1) v () ev2
EvalRel-Comp (RawSyntaxSigma.Sigma A B) rho crho (PiCode a1 f1) v () ev2
EvalRel-Comp (RawSyntaxSigma.Sigma A B) rho crho (PairCode u1 v1) v () ev2
EvalRel-Comp (RawSyntaxSigma.Sigma A B) rho crho (SigmaCode a1 f1) UCode ev1 ()
EvalRel-Comp (RawSyntaxSigma.Sigma A B) rho crho (SigmaCode a1 f1) PropCode ev1 ()
EvalRel-Comp (RawSyntaxSigma.Sigma A B) rho crho (SigmaCode a1 f1) (FunEl g2) ev1 ()
EvalRel-Comp (RawSyntaxSigma.Sigma A B) rho crho (SigmaCode a1 f1) (PiCode a2 f2) ev1 ()
EvalRel-Comp (RawSyntaxSigma.Sigma A B) rho crho (SigmaCode a1 f1) (PairCode u2 v2) ev1 ()
EvalRel-Comp (RawSyntaxSigma.Sigma A B) rho crho (SigmaCode a1 f1) (SigmaCode a2 f2) ev1 ev2 =
  let sew1 = Sigma-edgewise A B rho a1 f1 ev1
      sew2 = Sigma-edgewise A B rho a2 f2 ev2
      a1'  = fst (snd (snd sew1))
      wf1  = snd (snd (snd (snd sew1)))
      a2'  = fst (snd (snd sew2))
      wf2  = snd (snd (snd (snd sew2)))
      comp-a = EvalRel-Comp A rho crho a1 a2 (fst (snd ev1)) (fst (snd ev2))
      cf1 = snd (fst ev1)
      cf2 = snd (fst ev2)
      comp-f = Lam-CompFun B rho a1' a2' f1 f2 crho cf1 cf2 wf1 wf2
                 (\ rho' crho' u v eu ev -> EvalRel-Comp B rho' crho' u v eu ev)
  in mkSigma comp-a comp-f

-- MkPair
EvalRel-Comp (MkPair M N) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (MkPair M N) rho crho (PairCode u1 v1) Bot ev1 ev2 = comp-Bot-r (PairCode u1 v1)
EvalRel-Comp (MkPair M N) rho crho UCode v () ev2
EvalRel-Comp (MkPair M N) rho crho PropCode v () ev2
EvalRel-Comp (MkPair M N) rho crho (FunEl g1) v () ev2
EvalRel-Comp (MkPair M N) rho crho (PiCode a1 f1) v () ev2
EvalRel-Comp (MkPair M N) rho crho (SigmaCode a1 f1) v () ev2
EvalRel-Comp (MkPair M N) rho crho (PairCode u1 v1) UCode ev1 ()
EvalRel-Comp (MkPair M N) rho crho (PairCode u1 v1) PropCode ev1 ()
EvalRel-Comp (MkPair M N) rho crho (PairCode u1 v1) (FunEl g2) ev1 ()
EvalRel-Comp (MkPair M N) rho crho (PairCode u1 v1) (PiCode a2 f2) ev1 ()
EvalRel-Comp (MkPair M N) rho crho (PairCode u1 v1) (SigmaCode a2 f2) ev1 ()
EvalRel-Comp (MkPair M N) rho crho (PairCode u1 v1) (PairCode u2 v2) ev1 ev2 =
  mkSigma (EvalRel-Comp M rho crho u1 u2 (fst (snd ev1)) (fst (snd ev2)))
          (EvalRel-Comp N rho crho v1 v2 (snd (snd ev1)) (snd (snd ev2)))

-- Fst
EvalRel-Comp (Fst M) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (Fst M) rho crho UCode Bot ev1 ev2 = comp-Bot-r UCode
EvalRel-Comp (Fst M) rho crho PropCode Bot ev1 ev2 = comp-Bot-r PropCode
EvalRel-Comp (Fst M) rho crho (FunEl g1) Bot ev1 ev2 = comp-Bot-r (FunEl g1)
EvalRel-Comp (Fst M) rho crho (PiCode a1 f1) Bot ev1 ev2 = comp-Bot-r (PiCode a1 f1)
EvalRel-Comp (Fst M) rho crho (SigmaCode a1 f1) Bot ev1 ev2 = comp-Bot-r (SigmaCode a1 f1)
EvalRel-Comp (Fst M) rho crho (PairCode u1' v1') Bot ev1 ev2 = comp-Bot-r (PairCode u1' v1')
EvalRel-Comp (Fst M) rho crho UCode UCode ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode UCode (fst ev1)) (PairCode UCode (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho UCode PropCode ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode UCode (fst ev1)) (PairCode PropCode (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho UCode (FunEl g2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode UCode (fst ev1)) (PairCode (FunEl g2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho UCode (PiCode a2 f2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode UCode (fst ev1)) (PairCode (PiCode a2 f2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho UCode (SigmaCode a2 f2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode UCode (fst ev1)) (PairCode (SigmaCode a2 f2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho UCode (PairCode u2' v2') ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode UCode (fst ev1)) (PairCode (PairCode u2' v2') (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho PropCode UCode ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode PropCode (fst ev1)) (PairCode UCode (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho PropCode PropCode ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode PropCode (fst ev1)) (PairCode PropCode (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho PropCode (FunEl g2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode PropCode (fst ev1)) (PairCode (FunEl g2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho PropCode (PiCode a2 f2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode PropCode (fst ev1)) (PairCode (PiCode a2 f2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho PropCode (SigmaCode a2 f2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode PropCode (fst ev1)) (PairCode (SigmaCode a2 f2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho PropCode (PairCode u2' v2') ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode PropCode (fst ev1)) (PairCode (PairCode u2' v2') (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (FunEl g1) UCode ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (FunEl g1) (fst ev1)) (PairCode UCode (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (FunEl g1) PropCode ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (FunEl g1) (fst ev1)) (PairCode PropCode (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (FunEl g1) (FunEl g2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (FunEl g1) (fst ev1)) (PairCode (FunEl g2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (FunEl g1) (PiCode a2 f2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (FunEl g1) (fst ev1)) (PairCode (PiCode a2 f2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (FunEl g1) (SigmaCode a2 f2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (FunEl g1) (fst ev1)) (PairCode (SigmaCode a2 f2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (FunEl g1) (PairCode u2' v2') ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (FunEl g1) (fst ev1)) (PairCode (PairCode u2' v2') (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (PiCode a1 f1) UCode ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (PiCode a1 f1) (fst ev1)) (PairCode UCode (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (PiCode a1 f1) PropCode ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (PiCode a1 f1) (fst ev1)) (PairCode PropCode (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (PiCode a1 f1) (FunEl g2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (PiCode a1 f1) (fst ev1)) (PairCode (FunEl g2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (PiCode a1 f1) (PiCode a2 f2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (PiCode a1 f1) (fst ev1)) (PairCode (PiCode a2 f2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (PiCode a1 f1) (SigmaCode a2 f2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (PiCode a1 f1) (fst ev1)) (PairCode (SigmaCode a2 f2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (PiCode a1 f1) (PairCode u2' v2') ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (PiCode a1 f1) (fst ev1)) (PairCode (PairCode u2' v2') (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (SigmaCode a1 f1) UCode ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (SigmaCode a1 f1) (fst ev1)) (PairCode UCode (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (SigmaCode a1 f1) PropCode ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (SigmaCode a1 f1) (fst ev1)) (PairCode PropCode (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (SigmaCode a1 f1) (FunEl g2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (SigmaCode a1 f1) (fst ev1)) (PairCode (FunEl g2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (SigmaCode a1 f1) (PiCode a2 f2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (SigmaCode a1 f1) (fst ev1)) (PairCode (PiCode a2 f2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (SigmaCode a1 f1) (SigmaCode a2 f2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (SigmaCode a1 f1) (fst ev1)) (PairCode (SigmaCode a2 f2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (SigmaCode a1 f1) (PairCode u2' v2') ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (SigmaCode a1 f1) (fst ev1)) (PairCode (PairCode u2' v2') (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (PairCode u1' v1') UCode ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (PairCode u1' v1') (fst ev1)) (PairCode UCode (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (PairCode u1' v1') PropCode ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (PairCode u1' v1') (fst ev1)) (PairCode PropCode (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (PairCode u1' v1') (FunEl g2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (PairCode u1' v1') (fst ev1)) (PairCode (FunEl g2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (PairCode u1' v1') (PiCode a2 f2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (PairCode u1' v1') (fst ev1)) (PairCode (PiCode a2 f2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (PairCode u1' v1') (SigmaCode a2 f2) ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (PairCode u1' v1') (fst ev1)) (PairCode (SigmaCode a2 f2) (fst ev2)) (snd ev1) (snd ev2))
EvalRel-Comp (Fst M) rho crho (PairCode u1' v1') (PairCode u2' v2') ev1 ev2 =
  fst (EvalRel-Comp M rho crho (PairCode (PairCode u1' v1') (fst ev1)) (PairCode (PairCode u2' v2') (fst ev2)) (snd ev1) (snd ev2))

-- Snd (same pattern as Fst but extract snd)
EvalRel-Comp (Snd M) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (Snd M) rho crho UCode Bot ev1 ev2 = comp-Bot-r UCode
EvalRel-Comp (Snd M) rho crho PropCode Bot ev1 ev2 = comp-Bot-r PropCode
EvalRel-Comp (Snd M) rho crho (FunEl g1) Bot ev1 ev2 = comp-Bot-r (FunEl g1)
EvalRel-Comp (Snd M) rho crho (PiCode a1 f1) Bot ev1 ev2 = comp-Bot-r (PiCode a1 f1)
EvalRel-Comp (Snd M) rho crho (SigmaCode a1 f1) Bot ev1 ev2 = comp-Bot-r (SigmaCode a1 f1)
EvalRel-Comp (Snd M) rho crho (PairCode u1' v1') Bot ev1 ev2 = comp-Bot-r (PairCode u1' v1')
EvalRel-Comp (Snd M) rho crho UCode UCode ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) UCode) (PairCode (fst ev2) UCode) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho UCode PropCode ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) UCode) (PairCode (fst ev2) PropCode) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho UCode (FunEl g2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) UCode) (PairCode (fst ev2) (FunEl g2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho UCode (PiCode a2 f2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) UCode) (PairCode (fst ev2) (PiCode a2 f2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho UCode (SigmaCode a2 f2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) UCode) (PairCode (fst ev2) (SigmaCode a2 f2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho UCode (PairCode u2' v2') ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) UCode) (PairCode (fst ev2) (PairCode u2' v2')) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho PropCode UCode ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) PropCode) (PairCode (fst ev2) UCode) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho PropCode PropCode ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) PropCode) (PairCode (fst ev2) PropCode) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho PropCode (FunEl g2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) PropCode) (PairCode (fst ev2) (FunEl g2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho PropCode (PiCode a2 f2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) PropCode) (PairCode (fst ev2) (PiCode a2 f2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho PropCode (SigmaCode a2 f2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) PropCode) (PairCode (fst ev2) (SigmaCode a2 f2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho PropCode (PairCode u2' v2') ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) PropCode) (PairCode (fst ev2) (PairCode u2' v2')) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (FunEl g1) UCode ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (FunEl g1)) (PairCode (fst ev2) UCode) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (FunEl g1) PropCode ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (FunEl g1)) (PairCode (fst ev2) PropCode) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (FunEl g1) (FunEl g2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (FunEl g1)) (PairCode (fst ev2) (FunEl g2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (FunEl g1) (PiCode a2 f2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (FunEl g1)) (PairCode (fst ev2) (PiCode a2 f2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (FunEl g1) (SigmaCode a2 f2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (FunEl g1)) (PairCode (fst ev2) (SigmaCode a2 f2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (FunEl g1) (PairCode u2' v2') ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (FunEl g1)) (PairCode (fst ev2) (PairCode u2' v2')) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (PiCode a1 f1) UCode ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (PiCode a1 f1)) (PairCode (fst ev2) UCode) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (PiCode a1 f1) PropCode ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (PiCode a1 f1)) (PairCode (fst ev2) PropCode) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (PiCode a1 f1) (FunEl g2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (PiCode a1 f1)) (PairCode (fst ev2) (FunEl g2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (PiCode a1 f1) (PiCode a2 f2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (PiCode a1 f1)) (PairCode (fst ev2) (PiCode a2 f2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (PiCode a1 f1) (SigmaCode a2 f2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (PiCode a1 f1)) (PairCode (fst ev2) (SigmaCode a2 f2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (PiCode a1 f1) (PairCode u2' v2') ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (PiCode a1 f1)) (PairCode (fst ev2) (PairCode u2' v2')) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (SigmaCode a1 f1) UCode ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (SigmaCode a1 f1)) (PairCode (fst ev2) UCode) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (SigmaCode a1 f1) PropCode ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (SigmaCode a1 f1)) (PairCode (fst ev2) PropCode) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (SigmaCode a1 f1) (FunEl g2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (SigmaCode a1 f1)) (PairCode (fst ev2) (FunEl g2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (SigmaCode a1 f1) (PiCode a2 f2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (SigmaCode a1 f1)) (PairCode (fst ev2) (PiCode a2 f2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (SigmaCode a1 f1) (SigmaCode a2 f2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (SigmaCode a1 f1)) (PairCode (fst ev2) (SigmaCode a2 f2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (SigmaCode a1 f1) (PairCode u2' v2') ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (SigmaCode a1 f1)) (PairCode (fst ev2) (PairCode u2' v2')) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (PairCode u1' v1') UCode ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (PairCode u1' v1')) (PairCode (fst ev2) UCode) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (PairCode u1' v1') PropCode ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (PairCode u1' v1')) (PairCode (fst ev2) PropCode) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (PairCode u1' v1') (FunEl g2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (PairCode u1' v1')) (PairCode (fst ev2) (FunEl g2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (PairCode u1' v1') (PiCode a2 f2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (PairCode u1' v1')) (PairCode (fst ev2) (PiCode a2 f2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (PairCode u1' v1') (SigmaCode a2 f2) ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (PairCode u1' v1')) (PairCode (fst ev2) (SigmaCode a2 f2)) (snd ev1) (snd ev2))
EvalRel-Comp (Snd M) rho crho (PairCode u1' v1') (PairCode u2' v2') ev1 ev2 =
  snd (EvalRel-Comp M rho crho (PairCode (fst ev1) (PairCode u1' v1')) (PairCode (fst ev2) (PairCode u2' v2')) (snd ev1) (snd ev2))

------------------------------------------------------------------------
-- EvalRel-down: downward closure of the evaluation relation.
--
-- If M evaluates to u and u' <= u with Coherent u', then M evaluates
-- to u'. By structural induction on M.
------------------------------------------------------------------------

EvalRel-down : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (u u' : FinEl) -> CoherentEnv rho -> Coherent u' ->
  EvalRel M rho u -> LeCode u' u -> EvalRel M rho u'

-- Var: compose LeCode
EvalRel-down (Var i) rho u u' crho cu' ev le =
  mkSigma cu' (LeCode-trans u' u (lookupEnv i rho)
    cu' (fst ev) (lookupEnv-coh i rho crho) le (snd ev))

-- U: compose LeCode
EvalRel-down U rho u u' crho cu' ev le =
  mkSigma cu' (LeCode-trans u' u UCode cu' (fst ev) tt le (snd ev))

-- Prop: compose LeCode
EvalRel-down Prop rho u u' crho cu' ev le =
  mkSigma cu' (LeCode-trans u' u PropCode cu' (fst ev) tt le (snd ev))

-- App: u' = Bot trivial
EvalRel-down (App M N) rho u Bot crho cu' ev le = tt
-- App: u = Bot forces non-Bot u' absurd
EvalRel-down (App M N) rho Bot UCode crho cu' ev ()
EvalRel-down (App M N) rho Bot PropCode crho cu' ev ()
EvalRel-down (App M N) rho Bot (FunEl g') crho cu' ev ()
EvalRel-down (App M N) rho Bot (PiCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho Bot (SigmaCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho Bot (PairCode u' v') crho cu' ev ()
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
EvalRel-down (App M N) rho UCode PropCode crho cu' ev ()
EvalRel-down (App M N) rho UCode (FunEl g') crho cu' ev ()
EvalRel-down (App M N) rho UCode (PiCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho UCode (SigmaCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho UCode (PairCode u' v') crho cu' ev ()
-- App: PropCode -> PropCode
EvalRel-down (App M N) rho PropCode PropCode crho cu' ev le =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
      c-vu = EvalRel-coh M rho (FunEl (cons (mkSigma v PropCode) nil)) evM
      cv   = Coherent-singleton-key v PropCode c-vu
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma v PropCode) nil)) c-vu)
      c-ef = Coherent-EvalFun (cons (mkSigma v PropCode) nil) v c-vu cv
      le-u'-ef = LeCode-trans PropCode PropCode (EvalFun (cons (mkSigma v PropCode) nil) v)
                   cu' tt c-ef le le-refl
      c-vu' = mkCFT cv tt tt tt tt
      evM' = EvalRel-down M rho
               (FunEl (cons (mkSigma v PropCode) nil))
               (FunEl (cons (mkSigma v PropCode) nil))
               crho c-vu' evM (mkSigma le-u'-ef tt)
  in mkSigma v (mkSigma evN evM')
-- App: PropCode -> cross-constructor absurd
EvalRel-down (App M N) rho PropCode UCode crho cu' ev ()
EvalRel-down (App M N) rho PropCode (FunEl g') crho cu' ev ()
EvalRel-down (App M N) rho PropCode (PiCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho PropCode (SigmaCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho PropCode (PairCode u' v') crho cu' ev ()
-- App: FunEl -> cross-constructor absurd
EvalRel-down (App M N) rho (FunEl g0) UCode crho cu' ev ()
EvalRel-down (App M N) rho (FunEl g0) PropCode crho cu' ev ()
EvalRel-down (App M N) rho (FunEl g0) (PiCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho (FunEl g0) (SigmaCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho (FunEl g0) (PairCode u' v') crho cu' ev ()
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
EvalRel-down (App M N) rho (PiCode a0 f0) PropCode crho cu' ev ()
EvalRel-down (App M N) rho (PiCode a0 f0) (FunEl g') crho cu' ev ()
EvalRel-down (App M N) rho (PiCode a0 f0) (SigmaCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho (PiCode a0 f0) (PairCode u' v') crho cu' ev ()
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
-- App: SigmaCode -> cross-constructor absurd
EvalRel-down (App M N) rho (SigmaCode a0 f0) UCode crho cu' ev ()
EvalRel-down (App M N) rho (SigmaCode a0 f0) PropCode crho cu' ev ()
EvalRel-down (App M N) rho (SigmaCode a0 f0) (FunEl g') crho cu' ev ()
EvalRel-down (App M N) rho (SigmaCode a0 f0) (PiCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho (SigmaCode a0 f0) (PairCode u' v') crho cu' ev ()
-- App: SigmaCode -> SigmaCode
EvalRel-down (App M N) rho (SigmaCode a0 f0) (SigmaCode a' f') crho cu' ev le =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
      c-vu = EvalRel-coh M rho (FunEl (cons (mkSigma v (SigmaCode a0 f0)) nil)) evM
      cv   = Coherent-singleton-key v (SigmaCode a0 f0) c-vu
      cu   = Coherent-singleton-val v (SigmaCode a0 f0) c-vu
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma v (SigmaCode a0 f0)) nil)) c-vu)
      c-ef = Coherent-EvalFun (cons (mkSigma v (SigmaCode a0 f0)) nil) v c-vu cv
      le-u'-ef = LeCode-trans (SigmaCode a' f') (SigmaCode a0 f0)
                   (EvalFun (cons (mkSigma v (SigmaCode a0 f0)) nil) v)
                   cu' cu c-ef le le-refl
      c-vu' = mkCFT cv cu' tt tt tt
      evM' = EvalRel-down M rho
               (FunEl (cons (mkSigma v (SigmaCode a0 f0)) nil))
               (FunEl (cons (mkSigma v (SigmaCode a' f')) nil))
               crho c-vu' evM (mkSigma le-u'-ef tt)
  in mkSigma v (mkSigma evN evM')
-- App: PairCode -> cross-constructor absurd
EvalRel-down (App M N) rho (PairCode u0 v0) UCode crho cu' ev ()
EvalRel-down (App M N) rho (PairCode u0 v0) PropCode crho cu' ev ()
EvalRel-down (App M N) rho (PairCode u0 v0) (FunEl g') crho cu' ev ()
EvalRel-down (App M N) rho (PairCode u0 v0) (PiCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho (PairCode u0 v0) (SigmaCode a' f') crho cu' ev ()
-- App: PairCode -> PairCode
EvalRel-down (App M N) rho (PairCode u0 v0) (PairCode u' v') crho cu' ev le =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
      c-vu = EvalRel-coh M rho (FunEl (cons (mkSigma v (PairCode u0 v0)) nil)) evM
      cv   = Coherent-singleton-key v (PairCode u0 v0) c-vu
      cu   = Coherent-singleton-val v (PairCode u0 v0) c-vu
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma v (PairCode u0 v0)) nil)) c-vu)
      c-ef = Coherent-EvalFun (cons (mkSigma v (PairCode u0 v0)) nil) v c-vu cv
      le-u'-ef = LeCode-trans (PairCode u' v') (PairCode u0 v0)
                   (EvalFun (cons (mkSigma v (PairCode u0 v0)) nil) v)
                   cu' cu c-ef le le-refl
      c-vu' = mkCFT cv cu' tt tt tt
      evM' = EvalRel-down M rho
               (FunEl (cons (mkSigma v (PairCode u0 v0)) nil))
               (FunEl (cons (mkSigma v (PairCode u' v')) nil))
               crho c-vu' evM (mkSigma le-u'-ef tt)
  in mkSigma v (mkSigma evN evM')

-- Lam: absurd cases for non-FunEl outputs
EvalRel-down (Lam A M) rho UCode u' crho cu' () le
EvalRel-down (Lam A M) rho PropCode u' crho cu' () le
EvalRel-down (Lam A M) rho (PiCode a f) u' crho cu' () le
EvalRel-down (Lam A M) rho (SigmaCode a f) u' crho cu' () le
EvalRel-down (Lam A M) rho (PairCode u0 v0) u' crho cu' () le
-- Lam Bot
EvalRel-down (Lam A M) rho Bot Bot crho cu' ev le = tt
EvalRel-down (Lam A M) rho Bot UCode crho cu' ev ()
EvalRel-down (Lam A M) rho Bot PropCode crho cu' ev ()
EvalRel-down (Lam A M) rho Bot (FunEl g') crho cu' ev ()
EvalRel-down (Lam A M) rho Bot (PiCode a' f') crho cu' ev ()
EvalRel-down (Lam A M) rho Bot (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Lam A M) rho Bot (PairCode u' v') crho cu' ev ()
-- Lam (FunEl g) Bot: trivial
EvalRel-down (Lam A M) rho (FunEl g) Bot crho cu' ev le = tt
-- Lam (FunEl g) absurd cross-constructors
EvalRel-down (Lam A M) rho (FunEl g) UCode crho cu' ev ()
EvalRel-down (Lam A M) rho (FunEl g) PropCode crho cu' ev ()
EvalRel-down (Lam A M) rho (FunEl g) (PiCode a' f') crho cu' ev ()
EvalRel-down (Lam A M) rho (FunEl g) (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Lam A M) rho (FunEl g) (PairCode u' v') crho cu' ev ()
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
EvalRel-down (Pi A B) rho PropCode u' crho cu' () le
EvalRel-down (Pi A B) rho (FunEl g) u' crho cu' () le
EvalRel-down (Pi A B) rho (SigmaCode a f) u' crho cu' () le
EvalRel-down (Pi A B) rho (PairCode u0 v0) u' crho cu' () le
-- Pi Bot
EvalRel-down (Pi A B) rho Bot Bot crho cu' ev le = tt
EvalRel-down (Pi A B) rho Bot UCode crho cu' ev ()
EvalRel-down (Pi A B) rho Bot PropCode crho cu' ev ()
EvalRel-down (Pi A B) rho Bot (FunEl g') crho cu' ev ()
EvalRel-down (Pi A B) rho Bot (PiCode a' f') crho cu' ev ()
EvalRel-down (Pi A B) rho Bot (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Pi A B) rho Bot (PairCode u' v') crho cu' ev ()
-- Pi (PiCode a f) Bot: trivial
EvalRel-down (Pi A B) rho (PiCode a f) Bot crho cu' ev le = tt
-- Pi (PiCode a f) absurd cross-constructors
EvalRel-down (Pi A B) rho (PiCode a f) UCode crho cu' ev ()
EvalRel-down (Pi A B) rho (PiCode a f) PropCode crho cu' ev ()
EvalRel-down (Pi A B) rho (PiCode a f) (FunEl g') crho cu' ev ()
EvalRel-down (Pi A B) rho (PiCode a f) (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Pi A B) rho (PiCode a f) (PairCode u' v') crho cu' ev ()
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

-- Sigma: mirrors Pi exactly
EvalRel-down (RawSyntaxSigma.Sigma A B) rho UCode u' crho cu' () le
EvalRel-down (RawSyntaxSigma.Sigma A B) rho PropCode u' crho cu' () le
EvalRel-down (RawSyntaxSigma.Sigma A B) rho (FunEl g) u' crho cu' () le
EvalRel-down (RawSyntaxSigma.Sigma A B) rho (PiCode a f) u' crho cu' () le
EvalRel-down (RawSyntaxSigma.Sigma A B) rho (PairCode u0 v0) u' crho cu' () le
-- Sigma Bot
EvalRel-down (RawSyntaxSigma.Sigma A B) rho Bot Bot crho cu' ev le = tt
EvalRel-down (RawSyntaxSigma.Sigma A B) rho Bot UCode crho cu' ev ()
EvalRel-down (RawSyntaxSigma.Sigma A B) rho Bot PropCode crho cu' ev ()
EvalRel-down (RawSyntaxSigma.Sigma A B) rho Bot (FunEl g') crho cu' ev ()
EvalRel-down (RawSyntaxSigma.Sigma A B) rho Bot (PiCode a' f') crho cu' ev ()
EvalRel-down (RawSyntaxSigma.Sigma A B) rho Bot (SigmaCode a' f') crho cu' ev ()
EvalRel-down (RawSyntaxSigma.Sigma A B) rho Bot (PairCode u' v') crho cu' ev ()
-- Sigma (SigmaCode a f) Bot: trivial
EvalRel-down (RawSyntaxSigma.Sigma A B) rho (SigmaCode a f) Bot crho cu' ev le = tt
-- Sigma (SigmaCode a f) absurd cross-constructors
EvalRel-down (RawSyntaxSigma.Sigma A B) rho (SigmaCode a f) UCode crho cu' ev ()
EvalRel-down (RawSyntaxSigma.Sigma A B) rho (SigmaCode a f) PropCode crho cu' ev ()
EvalRel-down (RawSyntaxSigma.Sigma A B) rho (SigmaCode a f) (FunEl g') crho cu' ev ()
EvalRel-down (RawSyntaxSigma.Sigma A B) rho (SigmaCode a f) (PiCode a' f') crho cu' ev ()
EvalRel-down (RawSyntaxSigma.Sigma A B) rho (SigmaCode a f) (PairCode u' v') crho cu' ev ()
-- Sigma (SigmaCode a f) (SigmaCode a' f')
EvalRel-down (RawSyntaxSigma.Sigma A B) rho (SigmaCode a f) (SigmaCode a' f') crho cu' ev le =
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

-- MkPair: absurd cases for non-PairCode outputs
EvalRel-down (MkPair M N) rho UCode u' crho cu' () le
EvalRel-down (MkPair M N) rho PropCode u' crho cu' () le
EvalRel-down (MkPair M N) rho (FunEl g) u' crho cu' () le
EvalRel-down (MkPair M N) rho (PiCode a f) u' crho cu' () le
EvalRel-down (MkPair M N) rho (SigmaCode a f) u' crho cu' () le
-- MkPair Bot
EvalRel-down (MkPair M N) rho Bot Bot crho cu' ev le = tt
EvalRel-down (MkPair M N) rho Bot UCode crho cu' ev ()
EvalRel-down (MkPair M N) rho Bot PropCode crho cu' ev ()
EvalRel-down (MkPair M N) rho Bot (FunEl g') crho cu' ev ()
EvalRel-down (MkPair M N) rho Bot (PiCode a' f') crho cu' ev ()
EvalRel-down (MkPair M N) rho Bot (SigmaCode a' f') crho cu' ev ()
EvalRel-down (MkPair M N) rho Bot (PairCode u' v') crho cu' ev ()
-- MkPair (PairCode u1 v1) Bot: trivial
EvalRel-down (MkPair M N) rho (PairCode u1 v1) Bot crho cu' ev le = tt
-- MkPair (PairCode) absurd cross-constructors
EvalRel-down (MkPair M N) rho (PairCode u1 v1) UCode crho cu' ev ()
EvalRel-down (MkPair M N) rho (PairCode u1 v1) PropCode crho cu' ev ()
EvalRel-down (MkPair M N) rho (PairCode u1 v1) (FunEl g') crho cu' ev ()
EvalRel-down (MkPair M N) rho (PairCode u1 v1) (PiCode a' f') crho cu' ev ()
EvalRel-down (MkPair M N) rho (PairCode u1 v1) (SigmaCode a' f') crho cu' ev ()
-- MkPair (PairCode u1 v1) (PairCode u2 v2)
EvalRel-down (MkPair M N) rho (PairCode u1 v1) (PairCode u2 v2) crho cu' ev le =
  mkSigma cu'
    (mkSigma (EvalRel-down M rho u1 u2 crho (fst (fst cu')) (fst (snd ev)) (fst le))
             (EvalRel-down N rho v1 v2 crho (snd (fst cu')) (snd (snd ev)) (snd le)))

-- Fst: Bot cases
EvalRel-down (Fst M) rho u Bot crho cu' ev le = tt
EvalRel-down (Fst M) rho Bot UCode crho cu' ev ()
EvalRel-down (Fst M) rho Bot PropCode crho cu' ev ()
EvalRel-down (Fst M) rho Bot (FunEl g') crho cu' ev ()
EvalRel-down (Fst M) rho Bot (PiCode a' f') crho cu' ev ()
EvalRel-down (Fst M) rho Bot (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Fst M) rho Bot (PairCode u' v') crho cu' ev ()
-- Fst non-Bot u' (all constructors): use same v witness, EvalRel-down on M
EvalRel-down (Fst M) rho UCode UCode crho cu' ev le =
  let v = fst ev
      evM = snd ev
      cv = snd (fst (EvalRel-coh M rho (PairCode UCode v) evM))
      le-v = LeCode-refl v cv
      c-pair = mkSigma (mkSigma tt cv) (inl tt)
      evM' = EvalRel-down M rho (PairCode UCode v) (PairCode UCode v) crho c-pair evM (mkSigma le le-v)
  in mkSigma v evM'
EvalRel-down (Fst M) rho UCode PropCode crho cu' ev ()
EvalRel-down (Fst M) rho UCode (FunEl g') crho cu' ev ()
EvalRel-down (Fst M) rho UCode (PiCode a' f') crho cu' ev ()
EvalRel-down (Fst M) rho UCode (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Fst M) rho UCode (PairCode u' v') crho cu' ev ()
EvalRel-down (Fst M) rho PropCode PropCode crho cu' ev le =
  let v = fst ev
      evM = snd ev
      cv = snd (fst (EvalRel-coh M rho (PairCode PropCode v) evM))
      le-v = LeCode-refl v cv
      c-pair = mkSigma (mkSigma tt cv) (inl tt)
      evM' = EvalRel-down M rho (PairCode PropCode v) (PairCode PropCode v) crho c-pair evM (mkSigma le le-v)
  in mkSigma v evM'
EvalRel-down (Fst M) rho PropCode UCode crho cu' ev ()
EvalRel-down (Fst M) rho PropCode (FunEl g') crho cu' ev ()
EvalRel-down (Fst M) rho PropCode (PiCode a' f') crho cu' ev ()
EvalRel-down (Fst M) rho PropCode (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Fst M) rho PropCode (PairCode u' v') crho cu' ev ()
EvalRel-down (Fst M) rho (FunEl g0) (FunEl g') crho cu' ev le =
  let v = fst ev
      evM = snd ev
      cv = snd (fst (EvalRel-coh M rho (PairCode (FunEl g0) v) evM))
      le-v = LeCode-refl v cv
      c-pair = mkSigma (mkSigma cu' cv) (inl tt)
      evM' = EvalRel-down M rho (PairCode (FunEl g0) v) (PairCode (FunEl g') v) crho c-pair evM (mkSigma le le-v)
  in mkSigma v evM'
EvalRel-down (Fst M) rho (FunEl g0) UCode crho cu' ev ()
EvalRel-down (Fst M) rho (FunEl g0) PropCode crho cu' ev ()
EvalRel-down (Fst M) rho (FunEl g0) (PiCode a' f') crho cu' ev ()
EvalRel-down (Fst M) rho (FunEl g0) (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Fst M) rho (FunEl g0) (PairCode u' v') crho cu' ev ()
EvalRel-down (Fst M) rho (PiCode a0 f0) (PiCode a' f') crho cu' ev le =
  let v = fst ev
      evM = snd ev
      cv = snd (fst (EvalRel-coh M rho (PairCode (PiCode a0 f0) v) evM))
      le-v = LeCode-refl v cv
      c-pair = mkSigma (mkSigma cu' cv) (inl tt)
      evM' = EvalRel-down M rho (PairCode (PiCode a0 f0) v) (PairCode (PiCode a' f') v) crho c-pair evM (mkSigma le le-v)
  in mkSigma v evM'
EvalRel-down (Fst M) rho (PiCode a0 f0) UCode crho cu' ev ()
EvalRel-down (Fst M) rho (PiCode a0 f0) PropCode crho cu' ev ()
EvalRel-down (Fst M) rho (PiCode a0 f0) (FunEl g') crho cu' ev ()
EvalRel-down (Fst M) rho (PiCode a0 f0) (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Fst M) rho (PiCode a0 f0) (PairCode u' v') crho cu' ev ()
EvalRel-down (Fst M) rho (SigmaCode a0 f0) (SigmaCode a' f') crho cu' ev le =
  let v = fst ev
      evM = snd ev
      cv = snd (fst (EvalRel-coh M rho (PairCode (SigmaCode a0 f0) v) evM))
      le-v = LeCode-refl v cv
      c-pair = mkSigma (mkSigma cu' cv) (inl tt)
      evM' = EvalRel-down M rho (PairCode (SigmaCode a0 f0) v) (PairCode (SigmaCode a' f') v) crho c-pair evM (mkSigma le le-v)
  in mkSigma v evM'
EvalRel-down (Fst M) rho (SigmaCode a0 f0) UCode crho cu' ev ()
EvalRel-down (Fst M) rho (SigmaCode a0 f0) PropCode crho cu' ev ()
EvalRel-down (Fst M) rho (SigmaCode a0 f0) (FunEl g') crho cu' ev ()
EvalRel-down (Fst M) rho (SigmaCode a0 f0) (PiCode a' f') crho cu' ev ()
EvalRel-down (Fst M) rho (SigmaCode a0 f0) (PairCode u' v') crho cu' ev ()
EvalRel-down (Fst M) rho (PairCode u0 v0) (PairCode u' v') crho cu' ev le =
  let v = fst ev
      evM = snd ev
      cv = snd (fst (EvalRel-coh M rho (PairCode (PairCode u0 v0) v) evM))
      le-v = LeCode-refl v cv
      c-pair = mkSigma (mkSigma cu' cv) (inl tt)
      evM' = EvalRel-down M rho (PairCode (PairCode u0 v0) v) (PairCode (PairCode u' v') v) crho c-pair evM (mkSigma le le-v)
  in mkSigma v evM'
EvalRel-down (Fst M) rho (PairCode u0 v0) UCode crho cu' ev ()
EvalRel-down (Fst M) rho (PairCode u0 v0) PropCode crho cu' ev ()
EvalRel-down (Fst M) rho (PairCode u0 v0) (FunEl g') crho cu' ev ()
EvalRel-down (Fst M) rho (PairCode u0 v0) (PiCode a' f') crho cu' ev ()
EvalRel-down (Fst M) rho (PairCode u0 v0) (SigmaCode a' f') crho cu' ev ()

-- Snd: symmetric to Fst
EvalRel-down (Snd M) rho u Bot crho cu' ev le = tt
EvalRel-down (Snd M) rho Bot UCode crho cu' ev ()
EvalRel-down (Snd M) rho Bot PropCode crho cu' ev ()
EvalRel-down (Snd M) rho Bot (FunEl g') crho cu' ev ()
EvalRel-down (Snd M) rho Bot (PiCode a' f') crho cu' ev ()
EvalRel-down (Snd M) rho Bot (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Snd M) rho Bot (PairCode u' v') crho cu' ev ()
-- Snd non-Bot u' (all constructors): use same u witness, EvalRel-down on M
EvalRel-down (Snd M) rho UCode UCode crho cu' ev le =
  let u = fst ev
      evM = snd ev
      cu = fst (fst (EvalRel-coh M rho (PairCode u UCode) evM))
      le-u = LeCode-refl u cu
      c-pair = mkSigma (mkSigma cu tt) (inr tt)
      evM' = EvalRel-down M rho (PairCode u UCode) (PairCode u UCode) crho c-pair evM (mkSigma le-u le)
  in mkSigma u evM'
EvalRel-down (Snd M) rho UCode PropCode crho cu' ev ()
EvalRel-down (Snd M) rho UCode (FunEl g') crho cu' ev ()
EvalRel-down (Snd M) rho UCode (PiCode a' f') crho cu' ev ()
EvalRel-down (Snd M) rho UCode (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Snd M) rho UCode (PairCode u' v') crho cu' ev ()
EvalRel-down (Snd M) rho PropCode PropCode crho cu' ev le =
  let u = fst ev
      evM = snd ev
      cu = fst (fst (EvalRel-coh M rho (PairCode u PropCode) evM))
      le-u = LeCode-refl u cu
      c-pair = mkSigma (mkSigma cu tt) (inr tt)
      evM' = EvalRel-down M rho (PairCode u PropCode) (PairCode u PropCode) crho c-pair evM (mkSigma le-u le)
  in mkSigma u evM'
EvalRel-down (Snd M) rho PropCode UCode crho cu' ev ()
EvalRel-down (Snd M) rho PropCode (FunEl g') crho cu' ev ()
EvalRel-down (Snd M) rho PropCode (PiCode a' f') crho cu' ev ()
EvalRel-down (Snd M) rho PropCode (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Snd M) rho PropCode (PairCode u' v') crho cu' ev ()
EvalRel-down (Snd M) rho (FunEl g0) (FunEl g') crho cu' ev le =
  let u = fst ev
      evM = snd ev
      cu = fst (fst (EvalRel-coh M rho (PairCode u (FunEl g0)) evM))
      le-u = LeCode-refl u cu
      c-pair = mkSigma (mkSigma cu cu') (inr tt)
      evM' = EvalRel-down M rho (PairCode u (FunEl g0)) (PairCode u (FunEl g')) crho c-pair evM (mkSigma le-u le)
  in mkSigma u evM'
EvalRel-down (Snd M) rho (FunEl g0) UCode crho cu' ev ()
EvalRel-down (Snd M) rho (FunEl g0) PropCode crho cu' ev ()
EvalRel-down (Snd M) rho (FunEl g0) (PiCode a' f') crho cu' ev ()
EvalRel-down (Snd M) rho (FunEl g0) (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Snd M) rho (FunEl g0) (PairCode u' v') crho cu' ev ()
EvalRel-down (Snd M) rho (PiCode a0 f0) (PiCode a' f') crho cu' ev le =
  let u = fst ev
      evM = snd ev
      cu = fst (fst (EvalRel-coh M rho (PairCode u (PiCode a0 f0)) evM))
      le-u = LeCode-refl u cu
      c-pair = mkSigma (mkSigma cu cu') (inr tt)
      evM' = EvalRel-down M rho (PairCode u (PiCode a0 f0)) (PairCode u (PiCode a' f')) crho c-pair evM (mkSigma le-u le)
  in mkSigma u evM'
EvalRel-down (Snd M) rho (PiCode a0 f0) UCode crho cu' ev ()
EvalRel-down (Snd M) rho (PiCode a0 f0) PropCode crho cu' ev ()
EvalRel-down (Snd M) rho (PiCode a0 f0) (FunEl g') crho cu' ev ()
EvalRel-down (Snd M) rho (PiCode a0 f0) (SigmaCode a' f') crho cu' ev ()
EvalRel-down (Snd M) rho (PiCode a0 f0) (PairCode u' v') crho cu' ev ()
EvalRel-down (Snd M) rho (SigmaCode a0 f0) (SigmaCode a' f') crho cu' ev le =
  let u = fst ev
      evM = snd ev
      cu = fst (fst (EvalRel-coh M rho (PairCode u (SigmaCode a0 f0)) evM))
      le-u = LeCode-refl u cu
      c-pair = mkSigma (mkSigma cu cu') (inr tt)
      evM' = EvalRel-down M rho (PairCode u (SigmaCode a0 f0)) (PairCode u (SigmaCode a' f')) crho c-pair evM (mkSigma le-u le)
  in mkSigma u evM'
EvalRel-down (Snd M) rho (SigmaCode a0 f0) UCode crho cu' ev ()
EvalRel-down (Snd M) rho (SigmaCode a0 f0) PropCode crho cu' ev ()
EvalRel-down (Snd M) rho (SigmaCode a0 f0) (FunEl g') crho cu' ev ()
EvalRel-down (Snd M) rho (SigmaCode a0 f0) (PiCode a' f') crho cu' ev ()
EvalRel-down (Snd M) rho (SigmaCode a0 f0) (PairCode u' v') crho cu' ev ()
EvalRel-down (Snd M) rho (PairCode u0 v0) (PairCode u' v') crho cu' ev le =
  let u = fst ev
      evM = snd ev
      cu = fst (fst (EvalRel-coh M rho (PairCode u (PairCode u0 v0)) evM))
      le-u = LeCode-refl u cu
      c-pair = mkSigma (mkSigma cu cu') (inr tt)
      evM' = EvalRel-down M rho (PairCode u (PairCode u0 v0)) (PairCode u (PairCode u' v')) crho c-pair evM (mkSigma le-u le)
  in mkSigma u evM'
EvalRel-down (Snd M) rho (PairCode u0 v0) UCode crho cu' ev ()
EvalRel-down (Snd M) rho (PairCode u0 v0) PropCode crho cu' ev ()
EvalRel-down (Snd M) rho (PairCode u0 v0) (FunEl g') crho cu' ev ()
EvalRel-down (Snd M) rho (PairCode u0 v0) (PiCode a' f') crho cu' ev ()
EvalRel-down (Snd M) rho (PairCode u0 v0) (SigmaCode a' f') crho cu' ev ()

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

-- Var: LeCode-Sup-lub
EvalRel-Sup (Var i) rho u v crho cu cv comp eu ev =
  mkSigma (Coherent-Sup u v comp cu cv)
          (LeCode-Sup-lub u v (lookupEnv i rho) (snd eu) (snd ev))

-- U: LeCode-Sup-lub
EvalRel-Sup U rho u v crho cu cv comp eu ev =
  mkSigma (Coherent-Sup u v comp cu cv) (LeCode-Sup-lub u v UCode (snd eu) (snd ev))

-- Prop: LeCode-Sup-lub
EvalRel-Sup Prop rho u v crho cu cv comp eu ev =
  mkSigma (Coherent-Sup u v comp cu cv) (LeCode-Sup-lub u v PropCode (snd eu) (snd ev))

-- App: Bot cases
EvalRel-Sup (App M N) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (App M N) rho UCode Bot crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho PropCode Bot crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho (FunEl g1') Bot crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho (PiCode a1' f1') Bot crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho (SigmaCode a1' f1') Bot crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho (PairCode u1' v1') Bot crho cu cv comp eu ev = eu

-- App: Cross-constructor non-Bot: Comp = Empty
EvalRel-Sup (App M N) rho UCode (FunEl g2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho UCode (PiCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho UCode PropCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho UCode (SigmaCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho UCode (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (FunEl g1') UCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (FunEl g1') (PiCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (FunEl g1') PropCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (FunEl g1') (SigmaCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (FunEl g1') (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') UCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') (FunEl g2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') PropCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') (SigmaCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho PropCode UCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho PropCode (FunEl g2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho PropCode (PiCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho PropCode (SigmaCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho PropCode (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (SigmaCode a1' f1') UCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (SigmaCode a1' f1') PropCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (SigmaCode a1' f1') (FunEl g2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (SigmaCode a1' f1') (PiCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (SigmaCode a1' f1') (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PairCode u1' v1') UCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PairCode u1' v1') PropCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PairCode u1' v1') (FunEl g2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PairCode u1' v1') (PiCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PairCode u1' v1') (SigmaCode a2' f2') crho cu cv () eu ev

-- App: same-constructor non-Bot
EvalRel-Sup (App M N) rho UCode UCode crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho PropCode PropCode crho cu cv comp eu ev = eu

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

-- App: SigmaCode-SigmaCode
EvalRel-Sup (App M N) rho (SigmaCode a1' f1') (SigmaCode a2' f2') crho cu cv comp eu ev =
  let v1   = fst eu
      evN1 = fst (snd eu)
      evM1 = snd (snd eu)
      v2   = fst ev
      evN2 = fst (snd ev)
      evM2 = snd (snd ev)
      cv1  = EvalRel-coh N rho v1 evN1
      cv2  = EvalRel-coh N rho v2 evN2
      cM1  = EvalRel-coh M rho (FunEl (cons (mkSigma v1 (SigmaCode a1' f1')) nil)) evM1
      cM2  = EvalRel-coh M rho (FunEl (cons (mkSigma v2 (SigmaCode a2' f2')) nil)) evM2
      comp-v = EvalRel-Comp N rho crho v1 v2 evN1 evN2
      comp-M = EvalRel-Comp M rho crho
                 (FunEl (cons (mkSigma v1 (SigmaCode a1' f1')) nil))
                 (FunEl (cons (mkSigma v2 (SigmaCode a2' f2')) nil))
                 evM1 evM2
      evN-sup = EvalRel-Sup N rho v1 v2 crho cv1 cv2 comp-v evN1 evN2
      evM-2 = EvalRel-Sup M rho
                (FunEl (cons (mkSigma v1 (SigmaCode a1' f1')) nil))
                (FunEl (cons (mkSigma v2 (SigmaCode a2' f2')) nil))
                crho cM1 cM2 comp-M evM1 evM2
      c-2graph = Coherent-Sup
                   (FunEl (cons (mkSigma v1 (SigmaCode a1' f1')) nil))
                   (FunEl (cons (mkSigma v2 (SigmaCode a2' f2')) nil))
                   comp-M cM1 cM2
      c-supv = Coherent-Sup v1 v2 comp-v cv1 cv2
      c-result-val = Coherent-Sup (SigmaCode a1' f1') (SigmaCode a2' f2') comp cu cv
      le-down = LeFunCode-Sup-pair v1 (SigmaCode a1' f1') v2 (SigmaCode a2' f2') comp-v comp c-2graph c-supv
      c-singleton = mkCFT c-supv c-result-val tt tt tt
      evM-result = EvalRel-down M rho
                     (FunEl (cons (mkSigma v1 (SigmaCode a1' f1')) (cons (mkSigma v2 (SigmaCode a2' f2')) nil)))
                     (FunEl (cons (mkSigma (Sup v1 v2) (SigmaCode (Sup a1' a2') (append f1' f2'))) nil))
                     crho c-singleton evM-2 le-down
  in mkSigma (Sup v1 v2) (mkSigma evN-sup evM-result)

-- App: PairCode-PairCode
EvalRel-Sup (App M N) rho (PairCode u1' v1') (PairCode u2' v2') crho cu cv comp eu ev =
  let v1   = fst eu
      evN1 = fst (snd eu)
      evM1 = snd (snd eu)
      v2   = fst ev
      evN2 = fst (snd ev)
      evM2 = snd (snd ev)
      cv1  = EvalRel-coh N rho v1 evN1
      cv2  = EvalRel-coh N rho v2 evN2
      cM1  = EvalRel-coh M rho (FunEl (cons (mkSigma v1 (PairCode u1' v1')) nil)) evM1
      cM2  = EvalRel-coh M rho (FunEl (cons (mkSigma v2 (PairCode u2' v2')) nil)) evM2
      comp-v = EvalRel-Comp N rho crho v1 v2 evN1 evN2
      comp-M = EvalRel-Comp M rho crho
                 (FunEl (cons (mkSigma v1 (PairCode u1' v1')) nil))
                 (FunEl (cons (mkSigma v2 (PairCode u2' v2')) nil))
                 evM1 evM2
      evN-sup = EvalRel-Sup N rho v1 v2 crho cv1 cv2 comp-v evN1 evN2
      evM-2 = EvalRel-Sup M rho
                (FunEl (cons (mkSigma v1 (PairCode u1' v1')) nil))
                (FunEl (cons (mkSigma v2 (PairCode u2' v2')) nil))
                crho cM1 cM2 comp-M evM1 evM2
      c-2graph = Coherent-Sup
                   (FunEl (cons (mkSigma v1 (PairCode u1' v1')) nil))
                   (FunEl (cons (mkSigma v2 (PairCode u2' v2')) nil))
                   comp-M cM1 cM2
      c-supv = Coherent-Sup v1 v2 comp-v cv1 cv2
      c-result-val = Coherent-Sup (PairCode u1' v1') (PairCode u2' v2') comp cu cv
      le-down = LeFunCode-Sup-pair v1 (PairCode u1' v1') v2 (PairCode u2' v2') comp-v comp c-2graph c-supv
      c-singleton = mkCFT c-supv c-result-val tt tt tt
      evM-result = EvalRel-down M rho
                     (FunEl (cons (mkSigma v1 (PairCode u1' v1')) (cons (mkSigma v2 (PairCode u2' v2')) nil)))
                     (FunEl (cons (mkSigma (Sup v1 v2) (PairCode (Sup u1' u2') (Sup v1' v2'))) nil))
                     crho c-singleton evM-2 le-down
  in mkSigma (Sup v1 v2) (mkSigma evN-sup evM-result)

-- Lam: Bot cases
EvalRel-Sup (Lam A M) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (Lam A M) rho (FunEl g1) Bot crho cu cv comp eu ev = eu

-- Lam: Absurd cases
EvalRel-Sup (Lam A M) rho UCode v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho PropCode v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho (PiCode a1 f1) v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho (SigmaCode a1 f1) v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho (PairCode u1 v1) v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho (FunEl g1) UCode crho cu cv comp eu ()
EvalRel-Sup (Lam A M) rho (FunEl g1) PropCode crho cu cv comp eu ()
EvalRel-Sup (Lam A M) rho (FunEl g1) (PiCode a2 f2) crho cu cv comp eu ()
EvalRel-Sup (Lam A M) rho (FunEl g1) (SigmaCode a2 f2) crho cu cv comp eu ()
EvalRel-Sup (Lam A M) rho (FunEl g1) (PairCode u2 v2) crho cu cv comp eu ()

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
EvalRel-Sup (Pi A B) rho PropCode v crho cu cv comp () ev
EvalRel-Sup (Pi A B) rho (FunEl g1) v crho cu cv comp () ev
EvalRel-Sup (Pi A B) rho (SigmaCode a1 f1) v crho cu cv comp () ev
EvalRel-Sup (Pi A B) rho (PairCode u1 v1) v crho cu cv comp () ev
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) UCode crho cu cv comp eu ()
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) PropCode crho cu cv comp eu ()
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) (FunEl g2) crho cu cv comp eu ()
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) (SigmaCode a2 f2) crho cu cv comp eu ()
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) (PairCode u2 v2) crho cu cv comp eu ()

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

-- Sigma: mirrors Pi exactly
EvalRel-Sup (RawSyntaxSigma.Sigma A B) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (RawSyntaxSigma.Sigma A B) rho (SigmaCode a1 f1) Bot crho cu cv comp eu ev = eu

-- Sigma: Absurd cases
EvalRel-Sup (RawSyntaxSigma.Sigma A B) rho UCode v crho cu cv comp () ev
EvalRel-Sup (RawSyntaxSigma.Sigma A B) rho PropCode v crho cu cv comp () ev
EvalRel-Sup (RawSyntaxSigma.Sigma A B) rho (FunEl g1) v crho cu cv comp () ev
EvalRel-Sup (RawSyntaxSigma.Sigma A B) rho (PiCode a1 f1) v crho cu cv comp () ev
EvalRel-Sup (RawSyntaxSigma.Sigma A B) rho (PairCode u1 v1) v crho cu cv comp () ev
EvalRel-Sup (RawSyntaxSigma.Sigma A B) rho (SigmaCode a1 f1) UCode crho cu cv comp eu ()
EvalRel-Sup (RawSyntaxSigma.Sigma A B) rho (SigmaCode a1 f1) PropCode crho cu cv comp eu ()
EvalRel-Sup (RawSyntaxSigma.Sigma A B) rho (SigmaCode a1 f1) (FunEl g2) crho cu cv comp eu ()
EvalRel-Sup (RawSyntaxSigma.Sigma A B) rho (SigmaCode a1 f1) (PiCode a2 f2) crho cu cv comp eu ()
EvalRel-Sup (RawSyntaxSigma.Sigma A B) rho (SigmaCode a1 f1) (PairCode u2 v2) crho cu cv comp eu ()

-- Sigma: SigmaCode-SigmaCode
EvalRel-Sup (RawSyntaxSigma.Sigma A B) rho (SigmaCode a1 f1) (SigmaCode a2 f2) crho cu cv comp eu ev =
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
      c-result = Coherent-Sup (SigmaCode a1 f1) (SigmaCode a2 f2) comp cu cv
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

-- MkPair: Bot cases
EvalRel-Sup (MkPair M N) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (MkPair M N) rho (PairCode u1 v1) Bot crho cu cv comp eu ev = eu

-- MkPair: Absurd cases
EvalRel-Sup (MkPair M N) rho UCode v crho cu cv comp () ev
EvalRel-Sup (MkPair M N) rho PropCode v crho cu cv comp () ev
EvalRel-Sup (MkPair M N) rho (FunEl g1) v crho cu cv comp () ev
EvalRel-Sup (MkPair M N) rho (PiCode a1 f1) v crho cu cv comp () ev
EvalRel-Sup (MkPair M N) rho (SigmaCode a1 f1) v crho cu cv comp () ev
EvalRel-Sup (MkPair M N) rho (PairCode u1 v1) UCode crho cu cv comp eu ()
EvalRel-Sup (MkPair M N) rho (PairCode u1 v1) PropCode crho cu cv comp eu ()
EvalRel-Sup (MkPair M N) rho (PairCode u1 v1) (FunEl g2) crho cu cv comp eu ()
EvalRel-Sup (MkPair M N) rho (PairCode u1 v1) (PiCode a2 f2) crho cu cv comp eu ()
EvalRel-Sup (MkPair M N) rho (PairCode u1 v1) (SigmaCode a2 f2) crho cu cv comp eu ()

-- MkPair: PairCode-PairCode
EvalRel-Sup (MkPair M N) rho (PairCode u1 v1) (PairCode u2 v2) crho cu cv comp eu ev =
  let cu1   = fst (fst cu)
      cv1   = snd (fst cu)
      cu2   = fst (fst cv)
      cv2   = snd (fst cv)
      comp-u = fst comp
      comp-v = snd comp
      c-result = Coherent-Sup (PairCode u1 v1) (PairCode u2 v2) comp cu cv
      evM-sup = EvalRel-Sup M rho u1 u2 crho cu1 cu2 comp-u (fst (snd eu)) (fst (snd ev))
      evN-sup = EvalRel-Sup N rho v1 v2 crho cv1 cv2 comp-v (snd (snd eu)) (snd (snd ev))
  in mkSigma c-result (mkSigma evM-sup evN-sup)

-- Fst: Bot cases
EvalRel-Sup (Fst M) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (Fst M) rho UCode Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Fst M) rho PropCode Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Fst M) rho (FunEl g1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Fst M) rho (PiCode a1 f1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Fst M) rho (SigmaCode a1 f1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Fst M) rho (PairCode u1' v1') Bot crho cu cv comp eu ev = eu

-- Fst: Cross-constructor non-Bot: Comp = Empty
EvalRel-Sup (Fst M) rho UCode (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho UCode PropCode crho cu cv () eu ev
EvalRel-Sup (Fst M) rho UCode (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho UCode (SigmaCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho UCode (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (Fst M) rho PropCode UCode crho cu cv () eu ev
EvalRel-Sup (Fst M) rho PropCode (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho PropCode (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho PropCode (SigmaCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho PropCode (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (FunEl g1) UCode crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (FunEl g1) PropCode crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (FunEl g1) (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (FunEl g1) (SigmaCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (FunEl g1) (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (PiCode a1 f1) UCode crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (PiCode a1 f1) PropCode crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (PiCode a1 f1) (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (PiCode a1 f1) (SigmaCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (PiCode a1 f1) (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (SigmaCode a1 f1) UCode crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (SigmaCode a1 f1) PropCode crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (SigmaCode a1 f1) (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (SigmaCode a1 f1) (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (SigmaCode a1 f1) (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (PairCode u1' v1') UCode crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (PairCode u1' v1') PropCode crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (PairCode u1' v1') (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (PairCode u1' v1') (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Fst M) rho (PairCode u1' v1') (SigmaCode a2 f2) crho cu cv () eu ev

-- Fst: same-constructor non-Bot
EvalRel-Sup (Fst M) rho UCode UCode crho cu cv comp eu ev = eu
EvalRel-Sup (Fst M) rho PropCode PropCode crho cu cv comp eu ev = eu
EvalRel-Sup (Fst M) rho (FunEl g1) (FunEl g2) crho cu cv comp eu ev =
  let w1 = fst eu ; evM1 = snd eu
      w2 = fst ev ; evM2 = snd ev
      comp-w = EvalRel-Comp M rho crho (PairCode (FunEl g1) w1) (PairCode (FunEl g2) w2) evM1 evM2
      c-w1 = snd (fst (EvalRel-coh M rho (PairCode (FunEl g1) w1) evM1))
      c-w2 = snd (fst (EvalRel-coh M rho (PairCode (FunEl g2) w2) evM2))
      comp-w12 = snd comp-w
      evM-sup = EvalRel-Sup M rho (PairCode (FunEl g1) w1) (PairCode (FunEl g2) w2) crho
                  (EvalRel-coh M rho (PairCode (FunEl g1) w1) evM1)
                  (EvalRel-coh M rho (PairCode (FunEl g2) w2) evM2)
                  comp-w evM1 evM2
  in mkSigma (Sup w1 w2) evM-sup
EvalRel-Sup (Fst M) rho (PiCode a1 f1) (PiCode a2 f2) crho cu cv comp eu ev =
  let w1 = fst eu ; evM1 = snd eu
      w2 = fst ev ; evM2 = snd ev
      comp-w = EvalRel-Comp M rho crho (PairCode (PiCode a1 f1) w1) (PairCode (PiCode a2 f2) w2) evM1 evM2
      evM-sup = EvalRel-Sup M rho (PairCode (PiCode a1 f1) w1) (PairCode (PiCode a2 f2) w2) crho
                  (EvalRel-coh M rho (PairCode (PiCode a1 f1) w1) evM1)
                  (EvalRel-coh M rho (PairCode (PiCode a2 f2) w2) evM2)
                  comp-w evM1 evM2
  in mkSigma (Sup w1 w2) evM-sup
EvalRel-Sup (Fst M) rho (SigmaCode a1 f1) (SigmaCode a2 f2) crho cu cv comp eu ev =
  let w1 = fst eu ; evM1 = snd eu
      w2 = fst ev ; evM2 = snd ev
      comp-w = EvalRel-Comp M rho crho (PairCode (SigmaCode a1 f1) w1) (PairCode (SigmaCode a2 f2) w2) evM1 evM2
      evM-sup = EvalRel-Sup M rho (PairCode (SigmaCode a1 f1) w1) (PairCode (SigmaCode a2 f2) w2) crho
                  (EvalRel-coh M rho (PairCode (SigmaCode a1 f1) w1) evM1)
                  (EvalRel-coh M rho (PairCode (SigmaCode a2 f2) w2) evM2)
                  comp-w evM1 evM2
  in mkSigma (Sup w1 w2) evM-sup
EvalRel-Sup (Fst M) rho (PairCode u1' v1') (PairCode u2' v2') crho cu cv comp eu ev =
  let w1 = fst eu ; evM1 = snd eu
      w2 = fst ev ; evM2 = snd ev
      comp-w = EvalRel-Comp M rho crho (PairCode (PairCode u1' v1') w1) (PairCode (PairCode u2' v2') w2) evM1 evM2
      evM-sup = EvalRel-Sup M rho (PairCode (PairCode u1' v1') w1) (PairCode (PairCode u2' v2') w2) crho
                  (EvalRel-coh M rho (PairCode (PairCode u1' v1') w1) evM1)
                  (EvalRel-coh M rho (PairCode (PairCode u2' v2') w2) evM2)
                  comp-w evM1 evM2
  in mkSigma (Sup w1 w2) evM-sup

-- Snd: Bot cases
EvalRel-Sup (Snd M) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (Snd M) rho UCode Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Snd M) rho PropCode Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Snd M) rho (FunEl g1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Snd M) rho (PiCode a1 f1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Snd M) rho (SigmaCode a1 f1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Snd M) rho (PairCode u1' v1') Bot crho cu cv comp eu ev = eu

-- Snd: Cross-constructor non-Bot: Comp = Empty
EvalRel-Sup (Snd M) rho UCode (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho UCode PropCode crho cu cv () eu ev
EvalRel-Sup (Snd M) rho UCode (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho UCode (SigmaCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho UCode (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (Snd M) rho PropCode UCode crho cu cv () eu ev
EvalRel-Sup (Snd M) rho PropCode (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho PropCode (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho PropCode (SigmaCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho PropCode (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (FunEl g1) UCode crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (FunEl g1) PropCode crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (FunEl g1) (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (FunEl g1) (SigmaCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (FunEl g1) (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (PiCode a1 f1) UCode crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (PiCode a1 f1) PropCode crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (PiCode a1 f1) (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (PiCode a1 f1) (SigmaCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (PiCode a1 f1) (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (SigmaCode a1 f1) UCode crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (SigmaCode a1 f1) PropCode crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (SigmaCode a1 f1) (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (SigmaCode a1 f1) (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (SigmaCode a1 f1) (PairCode u2' v2') crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (PairCode u1' v1') UCode crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (PairCode u1' v1') PropCode crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (PairCode u1' v1') (FunEl g2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (PairCode u1' v1') (PiCode a2 f2) crho cu cv () eu ev
EvalRel-Sup (Snd M) rho (PairCode u1' v1') (SigmaCode a2 f2) crho cu cv () eu ev

-- Snd: same-constructor non-Bot
EvalRel-Sup (Snd M) rho UCode UCode crho cu cv comp eu ev = eu
EvalRel-Sup (Snd M) rho PropCode PropCode crho cu cv comp eu ev = eu
EvalRel-Sup (Snd M) rho (FunEl g1) (FunEl g2) crho cu cv comp eu ev =
  let w1 = fst eu ; evM1 = snd eu
      w2 = fst ev ; evM2 = snd ev
      comp-w = EvalRel-Comp M rho crho (PairCode w1 (FunEl g1)) (PairCode w2 (FunEl g2)) evM1 evM2
      evM-sup = EvalRel-Sup M rho (PairCode w1 (FunEl g1)) (PairCode w2 (FunEl g2)) crho
                  (EvalRel-coh M rho (PairCode w1 (FunEl g1)) evM1)
                  (EvalRel-coh M rho (PairCode w2 (FunEl g2)) evM2)
                  comp-w evM1 evM2
  in mkSigma (Sup w1 w2) evM-sup
EvalRel-Sup (Snd M) rho (PiCode a1 f1) (PiCode a2 f2) crho cu cv comp eu ev =
  let w1 = fst eu ; evM1 = snd eu
      w2 = fst ev ; evM2 = snd ev
      comp-w = EvalRel-Comp M rho crho (PairCode w1 (PiCode a1 f1)) (PairCode w2 (PiCode a2 f2)) evM1 evM2
      evM-sup = EvalRel-Sup M rho (PairCode w1 (PiCode a1 f1)) (PairCode w2 (PiCode a2 f2)) crho
                  (EvalRel-coh M rho (PairCode w1 (PiCode a1 f1)) evM1)
                  (EvalRel-coh M rho (PairCode w2 (PiCode a2 f2)) evM2)
                  comp-w evM1 evM2
  in mkSigma (Sup w1 w2) evM-sup
EvalRel-Sup (Snd M) rho (SigmaCode a1 f1) (SigmaCode a2 f2) crho cu cv comp eu ev =
  let w1 = fst eu ; evM1 = snd eu
      w2 = fst ev ; evM2 = snd ev
      comp-w = EvalRel-Comp M rho crho (PairCode w1 (SigmaCode a1 f1)) (PairCode w2 (SigmaCode a2 f2)) evM1 evM2
      evM-sup = EvalRel-Sup M rho (PairCode w1 (SigmaCode a1 f1)) (PairCode w2 (SigmaCode a2 f2)) crho
                  (EvalRel-coh M rho (PairCode w1 (SigmaCode a1 f1)) evM1)
                  (EvalRel-coh M rho (PairCode w2 (SigmaCode a2 f2)) evM2)
                  comp-w evM1 evM2
  in mkSigma (Sup w1 w2) evM-sup
EvalRel-Sup (Snd M) rho (PairCode u1' v1') (PairCode u2' v2') crho cu cv comp eu ev =
  let w1 = fst eu ; evM1 = snd eu
      w2 = fst ev ; evM2 = snd ev
      comp-w = EvalRel-Comp M rho crho (PairCode w1 (PairCode u1' v1')) (PairCode w2 (PairCode u2' v2')) evM1 evM2
      evM-sup = EvalRel-Sup M rho (PairCode w1 (PairCode u1' v1')) (PairCode w2 (PairCode u2' v2')) crho
                  (EvalRel-coh M rho (PairCode w1 (PairCode u1' v1')) evM1)
                  (EvalRel-coh M rho (PairCode w2 (PairCode u2' v2')) evM2)
                  comp-w evM1 evM2
  in mkSigma (Sup w1 w2) evM-sup

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
