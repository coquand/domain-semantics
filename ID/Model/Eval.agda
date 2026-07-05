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

module ID.Model.Eval where

import ID.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ;
              Pair ; List ; nil ; cons ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl ; FinFun)
open import ID.Domain.Kernel using (LeCode ; LeCode-refl ; LeCode-trans ; LeCode-Bot ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ; cft-from-cf ;
  NotBot ; Coherent-singleton-key ; Coherent-singleton-val ;
  FinMem ; FinMemAllU ; FinMem-coh-u ; FinMem-a-in-U ; finMem-Sup-both ; Sup ; Sup-Bot-r ; Sup-Bot-l ;
  Comp ; CompFun ; CompStepFun ; CompStepStep ;
  comp-Bot-r ; comp-Bot-l ; Comp-down ; Comp-sym ; NotBot-Sup-Comp ;
  Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub ;
  LeCode-Comp ;
  EvalFun ; EvalFun-mon ; EvalFun-mon-arg ; comp-EvalFun ; Coherent-EvalFun ;
  EvalFun-append-eq ;
  CoherentFun-append ; CoherentFunTail-append ; FinMem-Sup-element ;
  finMem-Sup-left ; finMem-Sup-right ;
  finMem-upward ; LeFunCode ; LeFunCode-refl ; append)
open import ID.Model.Selection using (Selection ; Edge ; EdgeIn ; here ; there ;
  sel-nil ; sel-take ; sel-skip ; sel-skip-all ;
  Coherent-Selection ; Coherent-Selection-val ;
  singleton-selection ; Selection-le-EvalFun ; selectionBelow ;
  FinMemAllU-Selection)
open import ID.Syntax.Raw

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

-- JBranch C d rho c w : the based-J eliminator dispatch on the proof value w.
-- For w = RefEl _ (a genuine proof), J C d (Ref a) reduces to d, so c must
-- approximate d; the motive C is irrelevant to the VALUE.
JBranch : {n : Nat} (C d : Expr n) (rho : EnvApprox n) (c w : FinEl) -> Set

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
EvalRel (Pi A B) rho (IdCode t u v) = Empty
EvalRel (Pi A B) rho (RefEl w)      = Empty

-- App result codes for the new constructors (mirror FunEl/PiCode)
EvalRel (App M N) rho (IdCode a' b' c') =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v (IdCode a' b' c')) nil))))
EvalRel (App M N) rho (RefEl w') =
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v (RefEl w')) nil))))

-- Lam cross-cells
EvalRel (Lam A M) rho (IdCode t u v) = Empty
EvalRel (Lam A M) rho (RefEl w)      = Empty

-- Id  (a type former, like Pi: evaluates to IdCode t u v)
EvalRel (Id A a b) rho Bot            = Top
EvalRel (Id A a b) rho (IdCode t u v) =
  Pair (Coherent (IdCode t u v))
       (Pair (EvalRel A rho t) (Pair (EvalRel a rho u) (EvalRel b rho v)))
EvalRel (Id A a b) rho UCode          = Empty
EvalRel (Id A a b) rho (FunEl g)      = Empty
EvalRel (Id A a b) rho (PiCode c f)   = Empty
EvalRel (Id A a b) rho (RefEl w)      = Empty

-- Ref  (a proof value, like Lam: evaluates to RefEl w)
EvalRel (Ref a) rho Bot              = Top
EvalRel (Ref a) rho (RefEl w)        = EvalRel a rho w
EvalRel (Ref a) rho UCode            = Empty
EvalRel (Ref a) rho (FunEl g)        = Empty
EvalRel (Ref a) rho (PiCode c f)     = Empty
EvalRel (Ref a) rho (IdCode t u v)   = Empty

-- J  (the based eliminator, like Case: scrutinee p evaluates to a proof,
--     J C d (Ref a) reduces to d, so the VALUE ignores the motive C)
EvalRel (J C d p) rho c =
  Sigma FinEl (\ w -> Pair (EvalRel p rho w) (JBranch C d rho c w))

JBranch C d rho c Bot            = Pair (Coherent c) (LeCode c Bot)
JBranch C d rho c UCode          = Empty
JBranch C d rho c (FunEl g)      = Empty
JBranch C d rho c (PiCode e f)   = Empty
JBranch C d rho c (IdCode t u v) = Empty
-- ML original J: J C d (Ref w) reduces to  App d w, so its value is  ⟦d⟧
-- applied to the proof witness w.  Exactly the App shape (d as a single-edge
-- function w ↦ c): c ≤ ⟦J C d p⟧ iff d maps w to c.  The motive C is ignored
-- by the value (it only constrains the TYPE).
JBranch C d rho c (RefEl w)      =
  EvalRel d rho (FunEl (cons (mkSigma w c) nil))

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

JBranch-coh : {n : Nat} (C d : Expr n) (rho : EnvApprox n) (c w : FinEl) ->
  JBranch C d rho c w -> Coherent c

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
EvalRel-coh (Pi A B) rho (IdCode t u v) ()
EvalRel-coh (Pi A B) rho (RefEl w) ()
-- App new result codes
EvalRel-coh (App M N) rho (IdCode a' b' c') ev =
  Coherent-singleton-val (fst ev) (IdCode a' b' c')
    (EvalRel-coh M rho (FunEl (cons (mkSigma (fst ev) (IdCode a' b' c')) nil)) (snd (snd ev)))
EvalRel-coh (App M N) rho (RefEl w') ev =
  Coherent-singleton-val (fst ev) (RefEl w')
    (EvalRel-coh M rho (FunEl (cons (mkSigma (fst ev) (RefEl w')) nil)) (snd (snd ev)))
-- Lam cross-cells
EvalRel-coh (Lam A M) rho (IdCode t u v) ()
EvalRel-coh (Lam A M) rho (RefEl w) ()
-- Id
EvalRel-coh (Id A a b) rho Bot ev = tt
EvalRel-coh (Id A a b) rho (IdCode t u v) ev = fst ev
EvalRel-coh (Id A a b) rho UCode ()
EvalRel-coh (Id A a b) rho (FunEl g) ()
EvalRel-coh (Id A a b) rho (PiCode c f) ()
EvalRel-coh (Id A a b) rho (RefEl w) ()
-- Ref
EvalRel-coh (Ref a) rho Bot ev = tt
EvalRel-coh (Ref a) rho (RefEl w) ev = EvalRel-coh a rho w ev
EvalRel-coh (Ref a) rho UCode ()
EvalRel-coh (Ref a) rho (FunEl g) ()
EvalRel-coh (Ref a) rho (PiCode c f) ()
EvalRel-coh (Ref a) rho (IdCode t u v) ()
-- J
EvalRel-coh (J C d p) rho c ev = JBranch-coh C d rho c (fst ev) (snd (snd ev))

JBranch-coh C d rho c Bot            jb = fst jb
JBranch-coh C d rho c UCode          ()
JBranch-coh C d rho c (FunEl g)      ()
JBranch-coh C d rho c (PiCode e f)   ()
JBranch-coh C d rho c (IdCode t u v) ()
JBranch-coh C d rho c (RefEl w)      jb =
  Coherent-singleton-val w c (EvalRel-coh d rho (FunEl (cons (mkSigma w c) nil)) jb)

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
EvalRel-Bot (Id A a b) rho = tt
EvalRel-Bot (Ref a) rho = tt
EvalRel-Bot (J C d p) rho = mkSigma Bot (mkSigma (EvalRel-Bot p rho) (mkSigma tt tt))

------------------------------------------------------------------------
-- EvalRel-mon-env
------------------------------------------------------------------------

EvalRel-mon-env : {n : Nat} (M : Expr n) (rho rho' : EnvApprox n) (u : FinEl) ->
  EvalRel M rho u -> EnvLe rho rho' -> EvalRel M rho' u

JBranch-mon-env : {n : Nat} (C d : Expr n) (rho rho' : EnvApprox n) (c w : FinEl) ->
  JBranch C d rho c w -> EnvLe rho rho' -> JBranch C d rho' c w

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
EvalRel-mon-env (Pi A B) rho rho' (IdCode t u v) () envle
EvalRel-mon-env (Pi A B) rho rho' (RefEl w) () envle
-- App new result codes
EvalRel-mon-env (App M N) rho rho' (IdCode a' b' c') ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
EvalRel-mon-env (App M N) rho rho' (RefEl w') ev envle =
  mkSigma (fst ev) (mkSigma (EvalRel-mon-env N rho rho' (fst ev) (fst (snd ev)) envle)
                             (EvalRel-mon-env M rho rho' _ (snd (snd ev)) envle))
-- Lam cross-cells
EvalRel-mon-env (Lam A M) rho rho' (IdCode t u v) () envle
EvalRel-mon-env (Lam A M) rho rho' (RefEl w) () envle
-- Id
EvalRel-mon-env (Id A a b) rho rho' Bot ev envle = tt
EvalRel-mon-env (Id A a b) rho rho' (IdCode t u v) ev envle =
  mkSigma (fst ev)
    (mkSigma (EvalRel-mon-env A rho rho' t (fst (snd ev)) envle)
      (mkSigma (EvalRel-mon-env a rho rho' u (fst (snd (snd ev))) envle)
               (EvalRel-mon-env b rho rho' v (snd (snd (snd ev))) envle)))
EvalRel-mon-env (Id A a b) rho rho' UCode () envle
EvalRel-mon-env (Id A a b) rho rho' (FunEl g) () envle
EvalRel-mon-env (Id A a b) rho rho' (PiCode c f) () envle
EvalRel-mon-env (Id A a b) rho rho' (RefEl w) () envle
-- Ref
EvalRel-mon-env (Ref a) rho rho' Bot ev envle = tt
EvalRel-mon-env (Ref a) rho rho' (RefEl w) ev envle = EvalRel-mon-env a rho rho' w ev envle
EvalRel-mon-env (Ref a) rho rho' UCode () envle
EvalRel-mon-env (Ref a) rho rho' (FunEl g) () envle
EvalRel-mon-env (Ref a) rho rho' (PiCode c f) () envle
EvalRel-mon-env (Ref a) rho rho' (IdCode t u v) () envle
-- J
EvalRel-mon-env (J C d p) rho rho' c ev envle =
  mkSigma (fst ev)
    (mkSigma (EvalRel-mon-env p rho rho' (fst ev) (fst (snd ev)) envle)
             (JBranch-mon-env C d rho rho' c (fst ev) (snd (snd ev)) envle))

JBranch-mon-env C d rho rho' c Bot            jb envle = jb
JBranch-mon-env C d rho rho' c UCode          () envle
JBranch-mon-env C d rho rho' c (FunEl g)      () envle
JBranch-mon-env C d rho rho' c (PiCode e f)   () envle
JBranch-mon-env C d rho rho' c (IdCode t u v) () envle
JBranch-mon-env C d rho rho' c (RefEl w)      jb envle =
  EvalRel-mon-env d rho rho' (FunEl (cons (mkSigma w c) nil)) jb envle

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
App-decompose M N rho (IdCode t u v) nb ev = ev
App-decompose M N rho (RefEl w)    nb ev = ev

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

------------------------------------------------------------------------
-- EvalRel-Comp
------------------------------------------------------------------------

EvalRel-Comp : {n : Nat} (M : Expr n) (rho : EnvApprox n) ->
  CoherentEnv rho -> (u v : FinEl) ->
  EvalRel M rho u -> EvalRel M rho v -> Comp u v

JBranch-Comp : {n : Nat} (C d : Expr n) (rho : EnvApprox n) -> CoherentEnv rho ->
  ((x y : FinEl) -> EvalRel d rho x -> EvalRel d rho y -> Comp x y) ->
  (c c' w1 w2 : FinEl) -> Comp w1 w2 ->
  JBranch C d rho c w1 -> JBranch C d rho c' w2 -> Comp c c'

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

-- App new result codes (mirror FunEl/PiCode via App-Comp-helper)
EvalRel-Comp (App M N) rho crho UCode (IdCode a2 b2 c2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode (IdCode a2 b2 c2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho UCode (RefEl w2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode (RefEl w2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') (IdCode a2 b2 c2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') (IdCode a2 b2 c2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') (RefEl w2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') (RefEl w2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') (IdCode a2 b2 c2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') (IdCode a2 b2 c2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') (RefEl w2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') (RefEl w2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (IdCode a1 b1 c1) Bot ev1 ev2 = comp-Bot-r (IdCode a1 b1 c1)
EvalRel-Comp (App M N) rho crho (IdCode a1 b1 c1) UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (IdCode a1 b1 c1) UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (IdCode a1 b1 c1) (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (IdCode a1 b1 c1) (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (IdCode a1 b1 c1) (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (IdCode a1 b1 c1) (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (IdCode a1 b1 c1) (IdCode a2 b2 c2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (IdCode a1 b1 c1) (IdCode a2 b2 c2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (IdCode a1 b1 c1) (RefEl w2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (IdCode a1 b1 c1) (RefEl w2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (RefEl w1) Bot ev1 ev2 = comp-Bot-r (RefEl w1)
EvalRel-Comp (App M N) rho crho (RefEl w1) UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (RefEl w1) UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (RefEl w1) (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (RefEl w1) (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (RefEl w1) (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (RefEl w1) (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (RefEl w1) (IdCode a2 b2 c2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (RefEl w1) (IdCode a2 b2 c2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (RefEl w1) (RefEl w2) ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (RefEl w1) (RefEl w2) (fst ev1) (fst (snd ev1)) (snd (snd ev1)) (fst ev2) (fst (snd ev2)) (snd (snd ev2))

-- Id (type former; simple componentwise Comp)
EvalRel-Comp (Id A a b) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (Id A a b) rho crho (IdCode t1 u1 w1) Bot ev1 ev2 = comp-Bot-r (IdCode t1 u1 w1)
EvalRel-Comp (Id A a b) rho crho UCode v () ev2
EvalRel-Comp (Id A a b) rho crho (FunEl g) v () ev2
EvalRel-Comp (Id A a b) rho crho (PiCode c f) v () ev2
EvalRel-Comp (Id A a b) rho crho (RefEl w) v () ev2
EvalRel-Comp (Id A a b) rho crho (IdCode t1 u1 w1) UCode ev1 ()
EvalRel-Comp (Id A a b) rho crho (IdCode t1 u1 w1) (FunEl g) ev1 ()
EvalRel-Comp (Id A a b) rho crho (IdCode t1 u1 w1) (PiCode c f) ev1 ()
EvalRel-Comp (Id A a b) rho crho (IdCode t1 u1 w1) (RefEl w) ev1 ()
EvalRel-Comp (Id A a b) rho crho (IdCode t1 u1 w1) (IdCode t2 u2 w2) ev1 ev2 =
  mkSigma (EvalRel-Comp A rho crho t1 t2 (fst (snd ev1)) (fst (snd ev2)))
    (mkSigma (EvalRel-Comp a rho crho u1 u2 (fst (snd (snd ev1))) (fst (snd (snd ev2))))
             (EvalRel-Comp b rho crho w1 w2 (snd (snd (snd ev1))) (snd (snd (snd ev2)))))

-- Ref (value; Comp forwards to a)
EvalRel-Comp (Ref a) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (Ref a) rho crho (RefEl w1) Bot ev1 ev2 = comp-Bot-r (RefEl w1)
EvalRel-Comp (Ref a) rho crho UCode v () ev2
EvalRel-Comp (Ref a) rho crho (FunEl g) v () ev2
EvalRel-Comp (Ref a) rho crho (PiCode c f) v () ev2
EvalRel-Comp (Ref a) rho crho (IdCode t u w) v () ev2
EvalRel-Comp (Ref a) rho crho (RefEl w1) UCode ev1 ()
EvalRel-Comp (Ref a) rho crho (RefEl w1) (FunEl g) ev1 ()
EvalRel-Comp (Ref a) rho crho (RefEl w1) (PiCode c f) ev1 ()
EvalRel-Comp (Ref a) rho crho (RefEl w1) (IdCode t u w) ev1 ()
EvalRel-Comp (Ref a) rho crho (RefEl w1) (RefEl w2) ev1 ev2 =
  EvalRel-Comp a rho crho w1 w2 ev1 ev2

-- J (eliminator; one clause + JBranch-Comp)
EvalRel-Comp (J C d p) rho crho u v ev1 ev2 =
  let w1 = fst ev1 ; evP1 = fst (snd ev1) ; jb1 = snd (snd ev1)
      w2 = fst ev2 ; evP2 = fst (snd ev2) ; jb2 = snd (snd ev2)
      comp-w = EvalRel-Comp p rho crho w1 w2 evP1 evP2
  in JBranch-Comp C d rho crho (\ x y ex ey -> EvalRel-Comp d rho crho x y ex ey)
       u v w1 w2 comp-w jb1 jb2

JBranch-Comp C d rho crho ihd c c' Bot            w2 cw jb1 jb2 =
  Comp-down c Bot c' (snd jb1) (comp-Bot-l c')
JBranch-Comp C d rho crho ihd c c' UCode          w2 cw () jb2
JBranch-Comp C d rho crho ihd c c' (FunEl g)      w2 cw () jb2
JBranch-Comp C d rho crho ihd c c' (PiCode e f)   w2 cw () jb2
JBranch-Comp C d rho crho ihd c c' (IdCode t u v) w2 cw () jb2
JBranch-Comp C d rho crho ihd c c' (RefEl w1) Bot            cw jb1 jb2 =
  Comp-sym c' c (Comp-down c' Bot c (snd jb2) (comp-Bot-l c))
JBranch-Comp C d rho crho ihd c c' (RefEl w1) UCode          cw jb1 ()
JBranch-Comp C d rho crho ihd c c' (RefEl w1) (FunEl g)      cw jb1 ()
JBranch-Comp C d rho crho ihd c c' (RefEl w1) (PiCode e f)   cw jb1 ()
JBranch-Comp C d rho crho ihd c c' (RefEl w1) (IdCode t u v) cw jb1 ()
JBranch-Comp C d rho crho ihd c c' (RefEl w1) (RefEl w2)     cw jb1 jb2 =
  -- jb1/jb2 : d maps w1↦c, w2↦c'.  d coherent + Comp w1 w2 ⇒ Comp c c'
  -- (the App codomain-compatibility core).
  fst (fst (ihd (FunEl (cons (mkSigma w1 c) nil)) (FunEl (cons (mkSigma w2 c') nil)) jb1 jb2)) cw

------------------------------------------------------------------------
-- EvalRel-down: downward closure of the evaluation relation.
--
-- If M evaluates to u and u' <= u with Coherent u', then M evaluates
-- to u'. By structural induction on M.
------------------------------------------------------------------------

EvalRel-down : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (u u' : FinEl) -> CoherentEnv rho -> Coherent u' ->
  EvalRel M rho u -> LeCode u' u -> EvalRel M rho u'

JBranch-down : {n : Nat} (C d : Expr n) (rho : EnvApprox n) -> CoherentEnv rho ->
  (c c' : FinEl) -> Coherent c' -> NotBot c' ->
  (w : FinEl) -> JBranch C d rho c w -> LeCode c' c -> JBranch C d rho c' w

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
-- App: Bot -> IdCode/RefEl absurd
EvalRel-down (App M N) rho Bot (IdCode t' u' w') crho cu' ev ()
EvalRel-down (App M N) rho Bot (RefEl w') crho cu' ev ()
-- App: cross-constructor absurd for IdCode/RefEl outputs
EvalRel-down (App M N) rho UCode (IdCode t' u' w') crho cu' ev ()
EvalRel-down (App M N) rho UCode (RefEl w') crho cu' ev ()
EvalRel-down (App M N) rho (FunEl g0) (IdCode t' u' w') crho cu' ev ()
EvalRel-down (App M N) rho (FunEl g0) (RefEl w') crho cu' ev ()
EvalRel-down (App M N) rho (PiCode a0 f0) (IdCode t' u' w') crho cu' ev ()
EvalRel-down (App M N) rho (PiCode a0 f0) (RefEl w') crho cu' ev ()
EvalRel-down (App M N) rho (IdCode t0 u0 w0) UCode crho cu' ev ()
EvalRel-down (App M N) rho (IdCode t0 u0 w0) (FunEl g') crho cu' ev ()
EvalRel-down (App M N) rho (IdCode t0 u0 w0) (PiCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho (IdCode t0 u0 w0) (RefEl w') crho cu' ev ()
EvalRel-down (App M N) rho (RefEl w0) UCode crho cu' ev ()
EvalRel-down (App M N) rho (RefEl w0) (FunEl g') crho cu' ev ()
EvalRel-down (App M N) rho (RefEl w0) (PiCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho (RefEl w0) (IdCode t' u' w') crho cu' ev ()
-- App: IdCode -> IdCode (mirror PiCode)
EvalRel-down (App M N) rho (IdCode t0 u0 w0) (IdCode t' u' w') crho cu' ev le =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
      c-vu = EvalRel-coh M rho (FunEl (cons (mkSigma v (IdCode t0 u0 w0)) nil)) evM
      cv   = Coherent-singleton-key v (IdCode t0 u0 w0) c-vu
      cu   = Coherent-singleton-val v (IdCode t0 u0 w0) c-vu
      c-ef = Coherent-EvalFun (cons (mkSigma v (IdCode t0 u0 w0)) nil) v c-vu cv
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma v (IdCode t0 u0 w0)) nil)) c-vu)
      le-u'-ef = LeCode-trans (IdCode t' u' w') (IdCode t0 u0 w0)
                   (EvalFun (cons (mkSigma v (IdCode t0 u0 w0)) nil) v)
                   cu' cu c-ef le le-refl
      c-vu' = mkCFT cv cu' tt tt tt
      evM' = EvalRel-down M rho
               (FunEl (cons (mkSigma v (IdCode t0 u0 w0)) nil))
               (FunEl (cons (mkSigma v (IdCode t' u' w')) nil))
               crho c-vu' evM (mkSigma le-u'-ef tt)
  in mkSigma v (mkSigma evN evM')
-- App: RefEl -> RefEl (mirror PiCode)
EvalRel-down (App M N) rho (RefEl w0) (RefEl w') crho cu' ev le =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
      c-vu = EvalRel-coh M rho (FunEl (cons (mkSigma v (RefEl w0)) nil)) evM
      cv   = Coherent-singleton-key v (RefEl w0) c-vu
      cu   = Coherent-singleton-val v (RefEl w0) c-vu
      c-ef = Coherent-EvalFun (cons (mkSigma v (RefEl w0)) nil) v c-vu cv
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma v (RefEl w0)) nil)) c-vu)
      le-u'-ef = LeCode-trans (RefEl w') (RefEl w0)
                   (EvalFun (cons (mkSigma v (RefEl w0)) nil) v)
                   cu' cu c-ef le le-refl
      c-vu' = mkCFT cv cu' tt tt tt
      evM' = EvalRel-down M rho
               (FunEl (cons (mkSigma v (RefEl w0)) nil))
               (FunEl (cons (mkSigma v (RefEl w')) nil))
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

-- Id (type former; componentwise down)
EvalRel-down (Id A a b) rho u Bot crho cu' ev le = tt
EvalRel-down (Id A a b) rho Bot (IdCode t' u' w') crho cu' ev ()
EvalRel-down (Id A a b) rho UCode u' crho cu' () le
EvalRel-down (Id A a b) rho (FunEl g) u' crho cu' () le
EvalRel-down (Id A a b) rho (PiCode c f) u' crho cu' () le
EvalRel-down (Id A a b) rho (RefEl w) u' crho cu' () le
EvalRel-down (Id A a b) rho (IdCode t1 u1 w1) UCode crho cu' ev ()
EvalRel-down (Id A a b) rho (IdCode t1 u1 w1) (FunEl g) crho cu' ev ()
EvalRel-down (Id A a b) rho (IdCode t1 u1 w1) (PiCode c f) crho cu' ev ()
EvalRel-down (Id A a b) rho (IdCode t1 u1 w1) (RefEl w) crho cu' ev ()
EvalRel-down (Id A a b) rho (IdCode t1 u1 w1) (IdCode t2 u2 w2) crho cu' ev le =
  mkSigma cu'
    (mkSigma (EvalRel-down A rho t1 t2 crho (fst cu') (fst (snd ev)) (fst le))
      (mkSigma (EvalRel-down a rho u1 u2 crho (fst (snd cu')) (fst (snd (snd ev))) (fst (snd le)))
               (EvalRel-down b rho w1 w2 crho (snd (snd cu')) (snd (snd (snd ev))) (snd (snd le)))))

-- Ref (value; down forwards to a)
EvalRel-down (Ref a) rho u Bot crho cu' ev le = tt
EvalRel-down (Ref a) rho Bot (RefEl w') crho cu' ev ()
EvalRel-down (Ref a) rho UCode u' crho cu' () le
EvalRel-down (Ref a) rho (FunEl g) u' crho cu' () le
EvalRel-down (Ref a) rho (PiCode c f) u' crho cu' () le
EvalRel-down (Ref a) rho (IdCode t u w) u' crho cu' () le
EvalRel-down (Ref a) rho (RefEl w1) UCode crho cu' ev ()
EvalRel-down (Ref a) rho (RefEl w1) (FunEl g) crho cu' ev ()
EvalRel-down (Ref a) rho (RefEl w1) (PiCode c f) crho cu' ev ()
EvalRel-down (Ref a) rho (RefEl w1) (IdCode t u w) crho cu' ev ()
EvalRel-down (Ref a) rho (RefEl w1) (RefEl w2) crho cu' ev le =
  EvalRel-down a rho w1 w2 crho cu' ev le

-- J (eliminator; one clause per result-code + JBranch-down)
EvalRel-down (J C d p) rho u Bot crho cu' ev le = EvalRel-Bot (J C d p) rho
EvalRel-down (J C d p) rho u UCode crho cu' ev le =
  mkSigma (fst ev) (mkSigma (fst (snd ev)) (JBranch-down C d rho crho u UCode cu' tt (fst ev) (snd (snd ev)) le))
EvalRel-down (J C d p) rho u (FunEl g) crho cu' ev le =
  mkSigma (fst ev) (mkSigma (fst (snd ev)) (JBranch-down C d rho crho u (FunEl g) cu' tt (fst ev) (snd (snd ev)) le))
EvalRel-down (J C d p) rho u (PiCode e f) crho cu' ev le =
  mkSigma (fst ev) (mkSigma (fst (snd ev)) (JBranch-down C d rho crho u (PiCode e f) cu' tt (fst ev) (snd (snd ev)) le))
EvalRel-down (J C d p) rho u (IdCode t x y) crho cu' ev le =
  mkSigma (fst ev) (mkSigma (fst (snd ev)) (JBranch-down C d rho crho u (IdCode t x y) cu' tt (fst ev) (snd (snd ev)) le))
EvalRel-down (J C d p) rho u (RefEl w) crho cu' ev le =
  mkSigma (fst ev) (mkSigma (fst (snd ev)) (JBranch-down C d rho crho u (RefEl w) cu' tt (fst ev) (snd (snd ev)) le))

JBranch-down C d rho crho c c' cc' nb Bot            jb le =
  absurd (Coherent-val-LeBot-absurd c' (mkSigma cc' nb)
            (LeCode-trans c' c Bot cc' (fst jb) tt le (snd jb)))
JBranch-down C d rho crho c c' cc' nb UCode          () le
JBranch-down C d rho crho c c' cc' nb (FunEl g)      () le
JBranch-down C d rho crho c c' cc' nb (PiCode e f)   () le
JBranch-down C d rho crho c c' cc' nb (IdCode t u v) () le
JBranch-down C d rho crho c c' cc' nb (RefEl w)      jb le =
  -- jb : d maps w↦c;  goal: d maps w↦c'  (c'≤c) — down-close d's edge codomain.
  let c-wc = EvalRel-coh d rho (FunEl (cons (mkSigma w c) nil)) jb
      cw   = Coherent-singleton-key w c c-wc
      cc   = Coherent-singleton-val w c c-wc
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma w c) nil)) c-wc)
      c-ef = Coherent-EvalFun (cons (mkSigma w c) nil) w c-wc cw
      le-u'-ef = LeCode-trans c' c (EvalFun (cons (mkSigma w c) nil) w) cc' cc c-ef le le-refl
      c-wc' = mkCFT cw cc' nb tt tt
  in EvalRel-down d rho
       (FunEl (cons (mkSigma w c) nil))
       (FunEl (cons (mkSigma w c') nil))
       crho c-wc' jb (mkSigma le-u'-ef tt)

------------------------------------------------------------------------
-- EvalRel-Sup: supremum closure of the evaluation relation.
--
-- If M evaluates to both u and v in rho, with rho coherent and
-- u, v coherent and compatible, then M evaluates to Sup u v.
------------------------------------------------------------------------

-- LeBot-is-Bot : a coherent element below Bot is Bot.
LeBot-is-Bot : (u : FinEl) -> LeCode u Bot -> Eq u Bot
LeBot-is-Bot Bot            le = refl
LeBot-is-Bot UCode          ()
LeBot-is-Bot (FunEl g)      ()
LeBot-is-Bot (PiCode a f)   ()
LeBot-is-Bot (IdCode t u v) ()
LeBot-is-Bot (RefEl w)      ()

EvalRel-Sup : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (u v : FinEl) -> CoherentEnv rho -> Coherent u -> Coherent v ->
  Comp u v ->
  EvalRel M rho u -> EvalRel M rho v -> EvalRel M rho (Sup u v)

JBranch-Sup : {n : Nat} (C d : Expr n) (rho : EnvApprox n) -> CoherentEnv rho ->
  ((x y : FinEl) -> Coherent x -> Coherent y -> Comp x y ->
     EvalRel d rho x -> EvalRel d rho y -> EvalRel d rho (Sup x y)) ->
  (c c' : FinEl) -> Coherent c -> Coherent c' -> Comp c c' ->
  (w1 w2 : FinEl) -> Comp w1 w2 ->
  JBranch C d rho c w1 -> JBranch C d rho c' w2 -> JBranch C d rho (Sup c c') (Sup w1 w2)
JBranch-Sup C d rho crho ihd c c' cc cc' comp Bot          w2 cw jb1 jb2 =
  let eq-c = LeBot-is-Bot c (snd jb1)
      eq-suv = Eq-transport (\ z -> Eq (Sup z c') c') (Eq-sym eq-c) (Sup-Bot-l c')
  in Eq-transport (\ cc0 -> JBranch C d rho cc0 w2) (Eq-sym eq-suv) jb2
JBranch-Sup C d rho crho ihd c c' cc cc' comp UCode        w2 cw () jb2
JBranch-Sup C d rho crho ihd c c' cc cc' comp (FunEl g)    w2 cw () jb2
JBranch-Sup C d rho crho ihd c c' cc cc' comp (PiCode e f) w2 cw () jb2
JBranch-Sup C d rho crho ihd c c' cc cc' comp (IdCode t u v) w2 cw () jb2
JBranch-Sup C d rho crho ihd c c' cc cc' comp (RefEl r1) Bot          cw jb1 jb2 =
  let eq-c' = LeBot-is-Bot c' (snd jb2)
      eq-suv = Eq-transport (\ z -> Eq (Sup c z) c) (Eq-sym eq-c') (Sup-Bot-r c)
  in Eq-transport (\ cc0 -> JBranch C d rho cc0 (RefEl r1)) (Eq-sym eq-suv) jb1
JBranch-Sup C d rho crho ihd c c' cc cc' comp (RefEl r1) UCode        cw jb1 ()
JBranch-Sup C d rho crho ihd c c' cc cc' comp (RefEl r1) (FunEl g)    cw jb1 ()
JBranch-Sup C d rho crho ihd c c' cc cc' comp (RefEl r1) (PiCode e f) cw jb1 ()
JBranch-Sup C d rho crho ihd c c' cc cc' comp (RefEl r1) (IdCode t u v) cw jb1 ()
JBranch-Sup C d rho crho ihd c c' cc cc' comp (RefEl r1) (RefEl r2)   cw jb1 jb2 =
  -- jb1/jb2 : d maps r1↦c, r2↦c'.  Merge the two edges into d maps (Sup r1 r2)↦(Sup c c')
  -- (exactly the App-value Sup): EvalRel-Sup d gives the 2-edge graph, then down-close
  -- to the single merged edge.  (The motive C plays no role in the VALUE.)
  let cd1     = EvalRel-coh d rho (FunEl (cons (mkSigma r1 c) nil)) jb1
      cd2     = EvalRel-coh d rho (FunEl (cons (mkSigma r2 c') nil)) jb2
      comp-d  = EvalRel-Comp d rho crho (FunEl (cons (mkSigma r1 c) nil))
                  (FunEl (cons (mkSigma r2 c') nil)) jb1 jb2
      evd-2   = ihd (FunEl (cons (mkSigma r1 c) nil)) (FunEl (cons (mkSigma r2 c') nil))
                  cd1 cd2 comp-d jb1 jb2
      c-2graph = Coherent-Sup (FunEl (cons (mkSigma r1 c) nil))
                   (FunEl (cons (mkSigma r2 c') nil)) comp-d cd1 cd2
      cr1     = Coherent-singleton-key r1 c cd1
      cr2     = Coherent-singleton-key r2 c' cd2
      c-supr  = Coherent-Sup r1 r2 cw cr1 cr2
      c-result = Coherent-Sup c c' comp cc cc'
      nbc     = CFTcons.val-nbot cd1
      le-down = LeFunCode-Sup-pair r1 c r2 c' cw comp c-2graph c-supr
      c-single = mkCFT c-supr c-result (NotBot-Sup-Comp c c' nbc comp) tt tt
  in EvalRel-down d rho
       (FunEl (cons (mkSigma r1 c) (cons (mkSigma r2 c') nil)))
       (FunEl (cons (mkSigma (Sup r1 r2) (Sup c c')) nil))
       crho c-single evd-2 le-down

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

-- App: Bot columns for IdCode/RefEl
EvalRel-Sup (App M N) rho (IdCode t1 u1 w1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho (RefEl r1) Bot crho cu cv comp eu ev = eu
-- App: cross-constructor absurd (Comp = Empty)
EvalRel-Sup (App M N) rho UCode (IdCode t2 u2 w2) crho cu cv () eu ev
EvalRel-Sup (App M N) rho UCode (RefEl r2) crho cu cv () eu ev
EvalRel-Sup (App M N) rho (FunEl g1') (IdCode t2 u2 w2) crho cu cv () eu ev
EvalRel-Sup (App M N) rho (FunEl g1') (RefEl r2) crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') (IdCode t2 u2 w2) crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') (RefEl r2) crho cu cv () eu ev
EvalRel-Sup (App M N) rho (IdCode t1 u1 w1) UCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (IdCode t1 u1 w1) (FunEl g2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (IdCode t1 u1 w1) (PiCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (IdCode t1 u1 w1) (RefEl r2) crho cu cv () eu ev
EvalRel-Sup (App M N) rho (RefEl r1) UCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (RefEl r1) (FunEl g2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (RefEl r1) (PiCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (RefEl r1) (IdCode t2 u2 w2) crho cu cv () eu ev
-- App: IdCode-IdCode (mirror PiCode)
EvalRel-Sup (App M N) rho (IdCode t1 u1 w1) (IdCode t2 u2 w2) crho cu cv comp eu ev =
  let v1   = fst eu
      evN1 = fst (snd eu)
      evM1 = snd (snd eu)
      v2   = fst ev
      evN2 = fst (snd ev)
      evM2 = snd (snd ev)
      cv1  = EvalRel-coh N rho v1 evN1
      cv2  = EvalRel-coh N rho v2 evN2
      cM1  = EvalRel-coh M rho (FunEl (cons (mkSigma v1 (IdCode t1 u1 w1)) nil)) evM1
      cM2  = EvalRel-coh M rho (FunEl (cons (mkSigma v2 (IdCode t2 u2 w2)) nil)) evM2
      comp-v = EvalRel-Comp N rho crho v1 v2 evN1 evN2
      comp-M = EvalRel-Comp M rho crho
                 (FunEl (cons (mkSigma v1 (IdCode t1 u1 w1)) nil))
                 (FunEl (cons (mkSigma v2 (IdCode t2 u2 w2)) nil))
                 evM1 evM2
      evN-sup = EvalRel-Sup N rho v1 v2 crho cv1 cv2 comp-v evN1 evN2
      evM-2 = EvalRel-Sup M rho
                (FunEl (cons (mkSigma v1 (IdCode t1 u1 w1)) nil))
                (FunEl (cons (mkSigma v2 (IdCode t2 u2 w2)) nil))
                crho cM1 cM2 comp-M evM1 evM2
      c-2graph = Coherent-Sup
                   (FunEl (cons (mkSigma v1 (IdCode t1 u1 w1)) nil))
                   (FunEl (cons (mkSigma v2 (IdCode t2 u2 w2)) nil))
                   comp-M cM1 cM2
      c-supv = Coherent-Sup v1 v2 comp-v cv1 cv2
      c-result-val = Coherent-Sup (IdCode t1 u1 w1) (IdCode t2 u2 w2) comp cu cv
      le-down = LeFunCode-Sup-pair v1 (IdCode t1 u1 w1) v2 (IdCode t2 u2 w2) comp-v comp c-2graph c-supv
      c-singleton = mkCFT c-supv c-result-val tt tt tt
      evM-result = EvalRel-down M rho
                     (FunEl (cons (mkSigma v1 (IdCode t1 u1 w1)) (cons (mkSigma v2 (IdCode t2 u2 w2)) nil)))
                     (FunEl (cons (mkSigma (Sup v1 v2) (IdCode (Sup t1 t2) (Sup u1 u2) (Sup w1 w2))) nil))
                     crho c-singleton evM-2 le-down
  in mkSigma (Sup v1 v2) (mkSigma evN-sup evM-result)
-- App: RefEl-RefEl (mirror PiCode)
EvalRel-Sup (App M N) rho (RefEl r1) (RefEl r2) crho cu cv comp eu ev =
  let v1   = fst eu
      evN1 = fst (snd eu)
      evM1 = snd (snd eu)
      v2   = fst ev
      evN2 = fst (snd ev)
      evM2 = snd (snd ev)
      cv1  = EvalRel-coh N rho v1 evN1
      cv2  = EvalRel-coh N rho v2 evN2
      cM1  = EvalRel-coh M rho (FunEl (cons (mkSigma v1 (RefEl r1)) nil)) evM1
      cM2  = EvalRel-coh M rho (FunEl (cons (mkSigma v2 (RefEl r2)) nil)) evM2
      comp-v = EvalRel-Comp N rho crho v1 v2 evN1 evN2
      comp-M = EvalRel-Comp M rho crho
                 (FunEl (cons (mkSigma v1 (RefEl r1)) nil))
                 (FunEl (cons (mkSigma v2 (RefEl r2)) nil))
                 evM1 evM2
      evN-sup = EvalRel-Sup N rho v1 v2 crho cv1 cv2 comp-v evN1 evN2
      evM-2 = EvalRel-Sup M rho
                (FunEl (cons (mkSigma v1 (RefEl r1)) nil))
                (FunEl (cons (mkSigma v2 (RefEl r2)) nil))
                crho cM1 cM2 comp-M evM1 evM2
      c-2graph = Coherent-Sup
                   (FunEl (cons (mkSigma v1 (RefEl r1)) nil))
                   (FunEl (cons (mkSigma v2 (RefEl r2)) nil))
                   comp-M cM1 cM2
      c-supv = Coherent-Sup v1 v2 comp-v cv1 cv2
      c-result-val = Coherent-Sup (RefEl r1) (RefEl r2) comp cu cv
      le-down = LeFunCode-Sup-pair v1 (RefEl r1) v2 (RefEl r2) comp-v comp c-2graph c-supv
      c-singleton = mkCFT c-supv c-result-val tt tt tt
      evM-result = EvalRel-down M rho
                     (FunEl (cons (mkSigma v1 (RefEl r1)) (cons (mkSigma v2 (RefEl r2)) nil)))
                     (FunEl (cons (mkSigma (Sup v1 v2) (RefEl (Sup r1 r2))) nil))
                     crho c-singleton evM-2 le-down
  in mkSigma (Sup v1 v2) (mkSigma evN-sup evM-result)

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
-- Id (type former; componentwise Sup)
EvalRel-Sup (Id A a b) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (Id A a b) rho (IdCode t1 u1 w1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Id A a b) rho UCode v crho cu cv comp () ev
EvalRel-Sup (Id A a b) rho (FunEl g) v crho cu cv comp () ev
EvalRel-Sup (Id A a b) rho (PiCode c f) v crho cu cv comp () ev
EvalRel-Sup (Id A a b) rho (RefEl w) v crho cu cv comp () ev
EvalRel-Sup (Id A a b) rho (IdCode t1 u1 w1) UCode crho cu cv comp eu ()
EvalRel-Sup (Id A a b) rho (IdCode t1 u1 w1) (FunEl g) crho cu cv comp eu ()
EvalRel-Sup (Id A a b) rho (IdCode t1 u1 w1) (PiCode c f) crho cu cv comp eu ()
EvalRel-Sup (Id A a b) rho (IdCode t1 u1 w1) (RefEl w) crho cu cv comp eu ()
EvalRel-Sup (Id A a b) rho (IdCode t1 u1 w1) (IdCode t2 u2 w2) crho cu cv comp eu ev =
  mkSigma (Coherent-Sup (IdCode t1 u1 w1) (IdCode t2 u2 w2) comp cu cv)
    (mkSigma (EvalRel-Sup A rho t1 t2 crho (fst cu) (fst cv) (fst comp) (fst (snd eu)) (fst (snd ev)))
      (mkSigma (EvalRel-Sup a rho u1 u2 crho (fst (snd cu)) (fst (snd cv)) (fst (snd comp)) (fst (snd (snd eu))) (fst (snd (snd ev))))
               (EvalRel-Sup b rho w1 w2 crho (snd (snd cu)) (snd (snd cv)) (snd (snd comp)) (snd (snd (snd eu))) (snd (snd (snd ev))))))

-- Ref (value; Sup forwards to a)
EvalRel-Sup (Ref a) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (Ref a) rho (RefEl r1) Bot crho cu cv comp eu ev = eu
EvalRel-Sup (Ref a) rho UCode v crho cu cv comp () ev
EvalRel-Sup (Ref a) rho (FunEl g) v crho cu cv comp () ev
EvalRel-Sup (Ref a) rho (PiCode c f) v crho cu cv comp () ev
EvalRel-Sup (Ref a) rho (IdCode t u w) v crho cu cv comp () ev
EvalRel-Sup (Ref a) rho (RefEl r1) UCode crho cu cv comp eu ()
EvalRel-Sup (Ref a) rho (RefEl r1) (FunEl g) crho cu cv comp eu ()
EvalRel-Sup (Ref a) rho (RefEl r1) (PiCode c f) crho cu cv comp eu ()
EvalRel-Sup (Ref a) rho (RefEl r1) (IdCode t u w) crho cu cv comp eu ()
EvalRel-Sup (Ref a) rho (RefEl r1) (RefEl r2) crho cu cv comp eu ev =
  EvalRel-Sup a rho r1 r2 crho cu cv comp eu ev

-- J (eliminator; one clause + JBranch-Sup)
EvalRel-Sup (J C d p) rho u v crho cu cv comp eu ev =
  let w1 = fst eu ; evP1 = fst (snd eu) ; jb1 = snd (snd eu)
      w2 = fst ev ; evP2 = fst (snd ev) ; jb2 = snd (snd ev)
      cw1 = EvalRel-coh p rho w1 evP1
      cw2 = EvalRel-coh p rho w2 evP2
      comp-w = EvalRel-Comp p rho crho w1 w2 evP1 evP2
      evP-sup = EvalRel-Sup p rho w1 w2 crho cw1 cw2 comp-w evP1 evP2
      jbS = JBranch-Sup C d rho crho
              (\ x y cx cy cxy ex ey -> EvalRel-Sup d rho x y crho cx cy cxy ex ey)
              u v cu cv comp w1 w2 comp-w jb1 jb2
  in mkSigma (Sup w1 w2) (mkSigma evP-sup jbS)


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
