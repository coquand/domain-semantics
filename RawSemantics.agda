{-# OPTIONS --without-K --exact-split --type-in-type #-}

------------------------------------------------------------------------
-- RawSemantics.agda
--
-- Relational semantics of raw syntax on finite approximants.
-- No typing rules, no general-domain semantics.
--
-- Uses Selection-based definitions for Lam, Pi.
-- App uses one-edge form: u <= (App M N) rho iff exists v,
--   FunEl [(v,u)] <= M rho and v <= N rho.
-- Purely finite and relational: no ideal semantic functions.
-- Coherent is formal coherence only (no typing payload).
------------------------------------------------------------------------

module RawSemantics where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ;
              Pair ; List ; nil ; cons ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun)
open import PaperSemantics using (LeCode ; LeCode-refl ; LeCode-trans ; LeCode-Bot ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ; cft-from-cf ;
  NotBot ; Coherent-singleton-key ; Coherent-singleton-val ;
  FinMem ; FinMemAllU ; FinMem-coh-u ; FinMem-a-in-U ; Sup ; Sup-Bot-r ; Sup-Bot-l ;
  Comp ; CompFun ; CompStepFun ; CompStepStep ;
  comp-Bot-r ; comp-Bot-l ; Comp-down ; Comp-sym ;
  Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub ;
  LeCode-Comp ;
  EvalFun ; EvalFun-mon ; EvalFun-mon-arg ; comp-EvalFun ; Coherent-EvalFun ;
  EvalFun-append-eq ;
  CoherentFun-append ; FinMem-Sup-element ;
  finMem-Sup-left ; finMem-Sup-right ;
  finMem-upward ; LeFunCode ; LeFunCode-refl ; append)
open import Selection using (Selection ; Edge ; EdgeIn ; here ; there ;
  sel-nil ; sel-take ; sel-skip ;
  Coherent-Selection ; Coherent-Selection-val ;
  singleton-selection ; Selection-le-EvalFun ; selectionBelow ;
  FinMemAllU-Selection)
open import RawSyntax

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
-- Part 2: EvalRel -- relational semantics on finite approximants
--
-- EvalRel M rho u means: from the finite environment rho,
-- the term M yields at least the finite output information u.
--
-- Lam, Pi, App use the Selection relation for a purely finite,
-- relational semantics. No ideal semantic functions are used.
--
-- Coherence is bundled: Coherent u in App, CoherentFun g in Lam,
-- Coherent (PiCode a f) in Pi.
-- Domain codes carry FinMem a UCode (typehood).
------------------------------------------------------------------------

EvalRel : {n : Nat} -> Expr n -> EnvApprox n -> FinEl -> Set

-- Variables: Coherent b bundled
EvalRel (Var i) rho b = Pair (Coherent b) (LeCode b (lookupEnv i rho))

-- Universe: b <= UCode (with Coherent b bundled)
EvalRel U rho b = Pair (Coherent b) (LeCode b UCode)

-- Application: Bot always approximates.
-- Non-Bot u: one-edge form.
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

-- Lambda: Bot always approximates; FunEl g bundles CoherentFun g
-- and requires a domain code a with FinMem a UCode (typehood).
-- For every selection of g, a typed witness exists.
EvalRel (Lam A M) rho Bot       = Top
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
EvalRel (Lam A M) rho UCode        = Empty
EvalRel (Lam A M) rho (PiCode a f) = Empty

-- Pi: PiCode a f bundles Coherent (PiCode a f) and FinMem a UCode.
-- Domain and codomain evidence via Selection.
EvalRel (Pi A B) rho Bot          = Top
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
EvalRel (Pi A B) rho UCode        = Empty
EvalRel (Pi A B) rho (FunEl g)    = Empty

------------------------------------------------------------------------
-- CoherentFun vs LeFunCode-nil: a coherent graph cannot have all
-- values <= Bot, because CoherentFunTail requires NotBot on values.
-- The FunEl case recurses through the value's graph.
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  absurd : {A : Set} -> Empty -> A
  absurd ()

  CoherentFun-LeBot-absurd : (g : FinFun) -> CoherentFun g -> LeFunCode g nil -> Empty
  CoherentFun-LeBot-absurd nil cf lf = cf  -- CoherentFun nil = Empty
  CoherentFun-LeBot-absurd (cons p ps) cf lf =
    Coherent-val-LeBot-absurd (snd p) (mkSigma (CFTcons.val-coh cf) (CFTcons.val-nbot cf)) (fst lf)

  Coherent-val-LeBot-absurd : (v : FinEl) -> Pair (Coherent v) (NotBot v) -> LeCode v Bot -> Empty
  Coherent-val-LeBot-absurd Bot          cnb le = snd cnb  -- NotBot Bot = Empty
  Coherent-val-LeBot-absurd UCode        cnb ()             -- LeCode UCode Bot = Empty
  Coherent-val-LeBot-absurd (PiCode a f) cnb ()             -- LeCode PiCode Bot = Empty
  Coherent-val-LeBot-absurd (FunEl h)    cnb ()  -- LeCode (FunEl h) Bot = Empty

------------------------------------------------------------------------
-- Part 3: Coherence extraction
------------------------------------------------------------------------

-- Coherent u is trivially extractable from any EvalRel M rho u witness.
EvalRel-coh : {n : Nat} (M : Expr n) (rho : EnvApprox n) (u : FinEl) ->
  EvalRel M rho u -> Coherent u

EvalRel-coh (Var i) rho u ev = fst ev
EvalRel-coh U rho u ev = fst ev
EvalRel-coh (App M N) rho Bot ev = tt
EvalRel-coh (App M N) rho UCode ev = tt
EvalRel-coh (App M N) rho (FunEl g') ev =
  Coherent-singleton-val (fst ev) (FunEl g')
    (EvalRel-coh M rho (FunEl (cons (mkSigma (fst ev) (FunEl g')) nil)) (snd (snd ev)))
EvalRel-coh (App M N) rho (PiCode a' f') ev =
  Coherent-singleton-val (fst ev) (PiCode a' f')
    (EvalRel-coh M rho (FunEl (cons (mkSigma (fst ev) (PiCode a' f')) nil)) (snd (snd ev)))
EvalRel-coh (Lam A M) rho Bot ev = tt
EvalRel-coh (Lam A M) rho (FunEl g) ev = fst (snd ev)
EvalRel-coh (Lam A M) rho UCode ()
EvalRel-coh (Lam A M) rho (PiCode a f) ()
EvalRel-coh (Pi A B) rho Bot ev = tt
EvalRel-coh (Pi A B) rho (PiCode a f) ev = fst ev
EvalRel-coh (Pi A B) rho UCode ()
EvalRel-coh (Pi A B) rho (FunEl g) ()

------------------------------------------------------------------------
-- Part 4: Environment ordering and monotonicity
------------------------------------------------------------------------

-- Coherent environment
CoherentEnv : {n : Nat} -> EnvApprox n -> Set
CoherentEnv emptyEnv = Top
CoherentEnv (extendEnv rho u) = Pair (CoherentEnv rho) (Coherent u)

lookupEnv-coh : {n : Nat} (i : Fin n) (rho : EnvApprox n) ->
  CoherentEnv rho -> Coherent (lookupEnv i rho)
lookupEnv-coh fzero    (extendEnv rho u) crho = snd crho
lookupEnv-coh (fsuc i) (extendEnv rho u) crho = lookupEnv-coh i rho (fst crho)

-- Pointwise order on environments, carrying coherence at each position.
EnvLe : {n : Nat} -> EnvApprox n -> EnvApprox n -> Set
EnvLe emptyEnv emptyEnv = Top
EnvLe (extendEnv rho u) (extendEnv rho' u') =
  Pair (EnvLe rho rho')
       (Pair (Coherent u) (Pair (Coherent u') (LeCode u u')))

-- Lookup is monotone in EnvLe, and both sides are coherent.
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

-- Extending two ordered envs by the same coherent value preserves order.
EnvLe-extend : {n : Nat} (rho rho' : EnvApprox n) (x : FinEl) ->
  EnvLe rho rho' -> Coherent x ->
  EnvLe (extendEnv rho x) (extendEnv rho' x)
EnvLe-extend rho rho' x envle cx =
  mkSigma envle (mkSigma cx (mkSigma cx (LeCode-refl x cx)))

-- EnvLe is reflexive given CoherentEnv
EnvLe-refl : {n : Nat} (rho : EnvApprox n) -> CoherentEnv rho -> EnvLe rho rho
EnvLe-refl emptyEnv crho = tt
EnvLe-refl (extendEnv rho u) crho =
  mkSigma (EnvLe-refl rho (fst crho))
          (mkSigma (snd crho) (mkSigma (snd crho) (LeCode-refl u (snd crho))))

-- Extend two copies of the same env with Sup-ordered values
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
-- EvalRel-mon-env: evaluation is monotone in the environment.
------------------------------------------------------------------------

EvalRel-mon-env : {n : Nat} (M : Expr n) (rho rho' : EnvApprox n) (u : FinEl) ->
  EvalRel M rho u -> EnvLe rho rho' -> EvalRel M rho' u

-- Var: use lookup monotonicity and LeCode-trans
EvalRel-mon-env (Var i) rho rho' u ev envle =
  mkSigma (fst ev) (LeCode-trans u (lookupEnv i rho) (lookupEnv i rho')
    (fst ev) (lookupEnv-coh-left i rho rho' envle)
    (lookupEnv-coh-right i rho rho' envle) (snd ev) (lookupEnv-mon i rho rho' envle))

-- U: no dependence on environment
EvalRel-mon-env U rho rho' u ev envle = ev

-- App Bot: trivial
EvalRel-mon-env (App M N) rho rho' Bot ev envle = tt

-- App non-Bot: reuse same witness v; apply IH to N and M
EvalRel-mon-env (App M N) rho rho' UCode ev envle =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
  in mkSigma v (mkSigma (EvalRel-mon-env N rho rho' v evN envle)
                        (EvalRel-mon-env M rho rho' (FunEl (cons (mkSigma v UCode) nil)) evM envle))
EvalRel-mon-env (App M N) rho rho' (FunEl g') ev envle =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
  in mkSigma v (mkSigma (EvalRel-mon-env N rho rho' v evN envle)
                        (EvalRel-mon-env M rho rho' (FunEl (cons (mkSigma v (FunEl g')) nil)) evM envle))
EvalRel-mon-env (App M N) rho rho' (PiCode a' f') ev envle =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
  in mkSigma v (mkSigma (EvalRel-mon-env N rho rho' v evN envle)
                        (EvalRel-mon-env M rho rho' (FunEl (cons (mkSigma v (PiCode a' f')) nil)) evM envle))

-- Lam Bot: trivial
EvalRel-mon-env (Lam A M) rho rho' Bot ev envle = tt

-- Lam (FunEl g): CoherentFun g and FinMem a UCode pass through;
-- apply IH to A and M
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

-- Lam UCode: absurd
EvalRel-mon-env (Lam A M) rho rho' UCode () envle

-- Lam (PiCode a f): absurd
EvalRel-mon-env (Lam A M) rho rho' (PiCode a f) () envle

-- Pi Bot: trivial
EvalRel-mon-env (Pi A B) rho rho' Bot ev envle = tt

-- Pi (PiCode a f): Coherent (PiCode a f) passes through;
-- apply IH to A and B
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

-- Pi UCode: absurd
EvalRel-mon-env (Pi A B) rho rho' UCode () envle

-- Pi (FunEl g): absurd
EvalRel-mon-env (Pi A B) rho rho' (FunEl g) () envle

------------------------------------------------------------------------
-- (EvalRel-down-App removed: App downward closure is now inlined
-- into EvalRel-down using the structural IH on M.)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- App-decompose: if u <= (App M N) rho and u is not Bot, then
-- there exists v with v <= N rho and Fun [(v,u)] <= M rho.
------------------------------------------------------------------------

App-decompose : {n : Nat} (M N : Expr n) (rho : EnvApprox n)
  (u : FinEl) -> NotBot u ->
  EvalRel (App M N) rho u ->
  Sigma FinEl (\ v -> Pair (EvalRel N rho v)
                           (EvalRel M rho (FunEl (cons (mkSigma v u) nil))))
App-decompose M N rho UCode        nb ev = ev
App-decompose M N rho (FunEl g')   nb ev = ev
App-decompose M N rho (PiCode a f) nb ev = ev

------------------------------------------------------------------------
-- LeFunCode-Sup-pair: the singleton graph [(Sup v1 v2, Sup u1 u2)]
-- is below the 2-element graph [(v1,u1),(v2,u2)], given Comp/Coherent.
--
-- Proof: build a Selection of [(v1,u1),(v2,u2)] that takes both,
-- then use Selection-le-EvalFun with LeFunCode-refl.
------------------------------------------------------------------------

LeFunCode-Sup-pair :
  (v1 u1 v2 u2 : FinEl) ->
  Comp v1 v2 -> Comp u1 u2 ->
  CoherentFun (cons (mkSigma v1 u1) (cons (mkSigma v2 u2) nil)) ->
  Coherent (Sup v1 v2) ->
  LeFunCode (cons (mkSigma (Sup v1 v2) (Sup u1 u2)) nil)
            (cons (mkSigma v1 u1) (cons (mkSigma v2 u2) nil))
LeFunCode-Sup-pair v1 u1 v2 u2 comp-v comp-u cf c-supv =
  let -- Build selection of [(v1,u1),(v2,u2)] taking both entries
      -- Inner: sel-take on (v2,u2) with sel-nil
      sel-inner = sel-take (comp-Bot-r v2) (comp-Bot-r u2) sel-nil
      -- sel-inner : Selection [(v2,u2)] (Sup v2 Bot) (Sup u2 Bot)
      -- Comp v1 with (Sup v2 Bot)
      cv2  = CFTcons.key-coh (CFTcons.tail-coh cf)
      cu2  = CFTcons.val-coh (CFTcons.tail-coh cf)
      comp-v1-sv2 = Eq-transport (Comp v1) (Eq-sym (Sup-Bot-r v2)) comp-v
      comp-u1-su2 = Eq-transport (Comp u1) (Eq-sym (Sup-Bot-r u2)) comp-u
      sel-both = sel-take comp-v1-sv2 comp-u1-su2 sel-inner
      -- sel-both : Selection [(v1,u1),(v2,u2)]
      --              (Sup v1 (Sup v2 Bot)) (Sup u1 (Sup u2 Bot))
      -- Transport to (Sup v1 v2) and (Sup u1 u2)
      eq-key = Eq-transport (\ z -> Eq (Sup v1 (Sup v2 Bot)) (Sup v1 z)) (Sup-Bot-r v2) refl
      eq-val = Eq-transport (\ z -> Eq (Sup u1 (Sup u2 Bot)) (Sup u1 z)) (Sup-Bot-r u2) refl
      -- LeFunCode-refl for the 2-element graph
      g2 = cons (mkSigma v1 u1) (cons (mkSigma v2 u2) nil)
      ctf = cft-from-cf g2 cf
      lf-refl = LeFunCode-refl g2 ctf
      -- Selection-le-EvalFun gives LeCode (Sup u1 (Sup u2 Bot)) (EvalFun g2 (Sup v1 (Sup v2 Bot)))
      c-key = Eq-transport Coherent (Eq-sym eq-key) c-supv
      le-raw = Selection-le-EvalFun g2 sel-both lf-refl cf cf c-key
      -- Transport to the correct types
      c-sup-u = Eq-transport Coherent (Eq-sym eq-val) (Coherent-Sup u1 u2 comp-u (CFTcons.val-coh cf) cu2)
      c-ef = Coherent-EvalFun g2 (Sup v1 (Sup v2 Bot)) ctf c-key
      c-ef' = Eq-transport (\ z -> Coherent (EvalFun g2 z)) eq-key c-ef
      le-trans = Eq-transport (\ z -> LeCode z (EvalFun g2 (Sup v1 (Sup v2 Bot)))) eq-val le-raw
      le-result = Eq-transport (\ z -> LeCode (Sup u1 u2) (EvalFun g2 z)) eq-key le-trans
  in mkSigma le-result tt

------------------------------------------------------------------------
-- Lam-edgewise: edgewise characterization of lambda semantics
--
-- If EvalRel (Lam A M) rho (FunEl g), then for every edge (u,v)
-- in g, there exists a witness x <= u with FinMem x a and
-- EvalRel M (rho, x) v.
--
-- Proved by applying the body to a singleton selection and
-- transporting via Sup-Bot-r.
------------------------------------------------------------------------

Lam-edgewise : {n : Nat} (A : Expr n) (M : Expr (suc n))
  (rho : EnvApprox n) (g : FinFun) ->
  EvalRel (Lam A M) rho (FunEl g) ->
  Sigma FinEl (\ a ->
    Pair (CoherentFun g)
      (Pair (FinMem a UCode)
        (Pair (EvalRel A rho a)
          ((p : Edge) -> EdgeIn p g ->
            Sigma FinEl (\ x ->
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
              lxu = Eq-transport (LeCode x) (Sup-Bot-r (fst p))
                      (fst (snd w))
              mem = fst (snd (snd w))
              evM = Eq-transport (EvalRel M (extendEnv rho x))
                      (Sup-Bot-r (snd p))
                      (snd (snd (snd w)))
          in mkSigma x (mkSigma lxu (mkSigma mem evM))))))

------------------------------------------------------------------------
-- Pi-edgewise: edgewise characterization of Pi semantics
--
-- If EvalRel (Pi A B) rho (PiCode a f), then for every edge (u,v)
-- in f, there exists a witness x <= u with FinMem x a and
-- EvalRel B (rho, x) v.
--
-- Same technique as Lam-edgewise: singleton selection + Sup-Bot-r.
------------------------------------------------------------------------

Pi-edgewise : {n : Nat} (A : Expr n) (B : Expr (suc n))
  (rho : EnvApprox n) (a : FinEl) (f : FinFun) ->
  EvalRel (Pi A B) rho (PiCode a f) ->
  Pair (Coherent (PiCode a f))
    (Pair (EvalRel A rho a)
      (Sigma FinEl (\ a' ->
        Pair (EvalRel A rho a')
          ((p : Edge) -> EdgeIn p f ->
            Sigma FinEl (\ x ->
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
              lxu = Eq-transport (LeCode x) (Sup-Bot-r (fst p))
                      (fst (snd w))
              mem = fst (snd (snd w))
              evB = Eq-transport (EvalRel B (extendEnv rho x))
                      (Sup-Bot-r (snd p))
                      (snd (snd (snd w)))
          in mkSigma x (mkSigma lxu (mkSigma mem evB))))))

------------------------------------------------------------------------
-- EvalRel-Bot: Bot is always an approximation.
--
-- For each expression M and environment rho, EvalRel M rho Bot holds.
-- Var: Coherent Bot = Top, LeCode Bot _ = Top.
-- U: LeCode Bot UCode = Top.
-- App Bot = Top.
-- Lam Bot = Top.
-- Pi Bot = Top.
------------------------------------------------------------------------

EvalRel-Bot : {n : Nat} (M : Expr n) (rho : EnvApprox n) ->
  EvalRel M rho Bot
EvalRel-Bot (Var i) rho = mkSigma tt tt
EvalRel-Bot U rho = mkSigma tt tt
EvalRel-Bot (App M N) rho = tt
EvalRel-Bot (Lam A M) rho = tt
EvalRel-Bot (Pi A B) rho = tt

------------------------------------------------------------------------
-- EvalRel-Comp: compatibility of evaluation results.
--
-- If rho is coherent and M evaluates to both u and v, then Comp u v.
-- By structural induction on M. The Lam/Pi cases use EvalRel-mon-env
-- to unify environment extensions. The App case goes through EvalFun.
------------------------------------------------------------------------

-- Helper: Comp of App results from one-edge evidence, parametrized by IH.
-- With the one-edge form, this is much simpler:
-- IH on M gives CompFun [(v1,u1)] [(v2,u2)] which contains (Comp v1 v2 → Comp u1 u2).
-- IH on N gives Comp v1 v2. Combine to get Comp u1 u2.
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
  let -- IH on M: Comp (FunEl [(v1,u1)]) (FunEl [(v2,u2)])
      -- = Pair (Pair (Comp v1 v2 → Comp u1 u2) Top) Top
      comp-fg = ihm (FunEl (cons (mkSigma v1 u1) nil))
                    (FunEl (cons (mkSigma v2 u2) nil)) evM1 evM2
      -- Extract: Comp v1 v2 → Comp u1 u2
      step = fst (fst comp-fg)
      -- IH on N: Comp v1 v2
      comp-v = ihn v1 v2 evN1 evN2
  in step comp-v

-- Helper: Comp-via-body — use IH on body M to show Comp of results
-- at different env extensions, by monotone extension to common env
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

-- Helper: build CompStepFun from edgewise witnesses
Lam-CompStepFun : {n : Nat} (M : Expr (suc n)) (rho : EnvApprox n)
  (a1 a2 : FinEl)
  (s : Edge) (g2 : FinFun) ->
  CoherentEnv rho -> CoherentFunTail g2 ->
  -- witness for edge s
  Sigma FinEl (\ xs ->
    Pair (LeCode xs (fst s))
         (Pair (FinMem xs a1)
               (EvalRel M (extendEnv rho xs) (snd s)))) ->
  -- edgewise witnesses for g2
  ((t : Edge) -> EdgeIn t g2 ->
    Sigma FinEl (\ xt ->
      Pair (LeCode xt (fst t))
           (Pair (FinMem xt a2)
                 (EvalRel M (extendEnv rho xt) (snd t))))) ->
  -- IH on M
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

-- Helper: build CompFun from edgewise witnesses
Lam-CompFun : {n : Nat} (M : Expr (suc n)) (rho : EnvApprox n)
  (a1 a2 : FinEl)
  (g1 g2 : FinFun) ->
  CoherentEnv rho -> CoherentFunTail g1 -> CoherentFunTail g2 ->
  -- edgewise witnesses for g1
  ((s : Edge) -> EdgeIn s g1 ->
    Sigma FinEl (\ xs ->
      Pair (LeCode xs (fst s))
           (Pair (FinMem xs a1)
                 (EvalRel M (extendEnv rho xs) (snd s))))) ->
  -- edgewise witnesses for g2
  ((t : Edge) -> EdgeIn t g2 ->
    Sigma FinEl (\ xt ->
      Pair (LeCode xt (fst t))
           (Pair (FinMem xt a2)
                 (EvalRel M (extendEnv rho xt) (snd t))))) ->
  -- IH on M
  ((rho' : EnvApprox (suc n)) -> CoherentEnv rho' ->
    (u v : FinEl) -> EvalRel M rho' u -> EvalRel M rho' v -> Comp u v) ->
  CompFun g1 g2
Lam-CompFun M rho a1 a2 nil g2 crho cg1 cg2 wf1 wf2 ih = tt
Lam-CompFun M rho a1 a2 (cons s rest) g2 crho cg1 cg2 wf1 wf2 ih =
  mkSigma (Lam-CompStepFun M rho a1 a2 s g2 crho cg2
             (wf1 s here) wf2 ih)
          (Lam-CompFun M rho a1 a2 rest g2 crho (CFTcons.tail-coh cg1) cg2
             (\ s' ein -> wf1 s' (there ein)) wf2 ih)

-- Main theorem
EvalRel-Comp : {n : Nat} (M : Expr n) (rho : EnvApprox n) ->
  CoherentEnv rho -> (u v : FinEl) ->
  EvalRel M rho u -> EvalRel M rho v -> Comp u v

-- Var: both u,v <= lookupEnv i rho which is coherent
EvalRel-Comp (Var i) rho crho u v ev1 ev2 =
  LeCode-Comp u v (lookupEnv i rho)
    (lookupEnv-coh i rho crho) (snd ev1) (snd ev2)

-- U: both u,v <= UCode
EvalRel-Comp U rho crho u v ev1 ev2 = LeCode-Comp u v UCode tt (snd ev1) (snd ev2)

-- App: Bot cases trivial, non-Bot via App-Comp-helper
-- App: Bot cases trivial, non-Bot via App-Comp-helper
EvalRel-Comp (App M N) rho crho Bot v ev1 ev2 = comp-Bot-l v
EvalRel-Comp (App M N) rho crho UCode Bot ev1 ev2 = comp-Bot-r UCode
EvalRel-Comp (App M N) rho crho (FunEl g1') Bot ev1 ev2 = comp-Bot-r (FunEl g1')
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') Bot ev1 ev2 = comp-Bot-r (PiCode a1' f1')
EvalRel-Comp (App M N) rho crho UCode UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1))
                (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho UCode (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1))
                      (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho UCode (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    UCode (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1))
                           (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1))
                      (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1))
                            (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (FunEl g1') (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (FunEl g1') (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1))
                                 (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') UCode ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') UCode (fst ev1) (fst (snd ev1)) (snd (snd ev1))
                           (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') (FunEl g2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') (FunEl g2') (fst ev1) (fst (snd ev1)) (snd (snd ev1))
                                 (fst ev2) (fst (snd ev2)) (snd (snd ev2))
EvalRel-Comp (App M N) rho crho (PiCode a1' f1') (PiCode a2' f2') ev1 ev2 =
  App-Comp-helper M N rho (EvalRel-Comp M rho crho) (EvalRel-Comp N rho crho)
    (PiCode a1' f1') (PiCode a2' f2') (fst ev1) (fst (snd ev1)) (snd (snd ev1))
                                       (fst ev2) (fst (snd ev2)) (snd (snd ev2))

-- Lam: Bot cases trivial, FunEl-FunEl via Lam-CompFun
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

-- Pi: Bot cases trivial, PiCode-PiCode analogous to Lam via Lam-CompFun
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
      evA1 = fst (snd (snd (snd pew1)))
      wf1  = snd (snd (snd (snd pew1)))
      a2'  = fst (snd (snd pew2))
      evA2 = fst (snd (snd (snd pew2)))
      wf2  = snd (snd (snd (snd pew2)))
      -- IH on A: Comp a1 a2
      comp-a = EvalRel-Comp A rho crho a1 a2 (fst (snd ev1)) (fst (snd ev2))
      -- CompFun f1 f2 via Lam-CompFun on the existential witnesses a1' a2'
      cf1 = snd (fst ev1)
      cf2 = snd (fst ev2)
      comp-f = Lam-CompFun B rho a1' a2' f1 f2 crho (cft-from-cf f1 cf1) (cft-from-cf f2 cf2) wf1 wf2
                 (\ rho' crho' u v eu ev -> EvalRel-Comp B rho' crho' u v eu ev)
  in mkSigma comp-a comp-f

------------------------------------------------------------------------
-- EvalRel-down: downward closure (general).
--
-- If M evaluates to u and u' <= u with Coherent u', then M evaluates
-- to u'. By structural induction on M.
--
-- The Lam FunEl -> FunEl case uses selectionBelow to bridge from
-- the smaller graph g' to the original graph g, then applies the
-- selection-based body from ev directly, then uses the structural
-- IH (EvalRel-down on M) to weaken the output from v' to v.
------------------------------------------------------------------------

EvalRel-down : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (u u' : FinEl) -> CoherentEnv rho -> Coherent u' ->
  EvalRel M rho u -> LeCode u' u -> EvalRel M rho u'

-- Var: compose LeCode u' u and LeCode u (lookupEnv i rho)
EvalRel-down (Var i) rho u u' crho cu' ev le =
  mkSigma cu' (LeCode-trans u' u (lookupEnv i rho)
    cu' (fst ev) (lookupEnv-coh i rho crho) le (snd ev))

-- U: compose LeCode u' u and LeCode u UCode
EvalRel-down U rho u u' crho cu' ev le =
  mkSigma cu' (LeCode-trans u' u UCode cu' (fst ev) tt le (snd ev))

-- App: u' = Bot is trivial; u = Bot forces u' = Bot (absurd for non-Bot)
-- Non-Bot cases delegate to the existing App-down chain
-- App: u' = Bot trivial; u = Bot forces absurd for non-Bot u';
-- non-Bot same-constructor: use same v, EvalRel-down M on singleton graph.
-- Cross-constructor non-Bot: absurd by LeCode.
EvalRel-down (App M N) rho u Bot crho cu' ev le = tt
EvalRel-down (App M N) rho Bot UCode crho cu' ev ()
EvalRel-down (App M N) rho Bot (FunEl g') crho cu' ev ()
EvalRel-down (App M N) rho Bot (PiCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho UCode UCode crho cu' ev le =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
      -- Coherence from M evidence
      c-vu = EvalRel-coh M rho (FunEl (cons (mkSigma v UCode) nil)) evM
      cv   = Coherent-singleton-key v UCode c-vu
      -- LeCode UCode (EvalFun [(v,UCode)] v) from LeCode-refl
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma v UCode) nil)) c-vu)
      c-ef = Coherent-EvalFun (cons (mkSigma v UCode) nil) v c-vu cv
      le-u'-ef = LeCode-trans UCode UCode (EvalFun (cons (mkSigma v UCode) nil) v)
                   cu' tt c-ef le le-refl
      -- Coherent (FunEl [(v,UCode)])
      c-vu' = mkCFT cv tt tt tt tt
      -- EvalRel-down M (structural IH: M < App M N)
      evM' = EvalRel-down M rho
               (FunEl (cons (mkSigma v UCode) nil))
               (FunEl (cons (mkSigma v UCode) nil))
               crho c-vu' evM (mkSigma le-u'-ef tt)
  in mkSigma v (mkSigma evN evM')
EvalRel-down (App M N) rho UCode (FunEl g') crho cu' ev ()
EvalRel-down (App M N) rho UCode (PiCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho (FunEl g0) UCode crho cu' ev ()
EvalRel-down (App M N) rho (FunEl g0) (FunEl g') crho cu' ev le =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
      -- Coherence from M evidence
      c-vu = EvalRel-coh M rho (FunEl (cons (mkSigma v (FunEl g0)) nil)) evM
      cv   = Coherent-singleton-key v (FunEl g0) c-vu
      cu   = Coherent-singleton-val v (FunEl g0) c-vu
      -- LeCode (FunEl g0) (EvalFun [(v,FunEl g0)] v) from LeCode-refl
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma v (FunEl g0)) nil)) c-vu)
      c-ef = Coherent-EvalFun (cons (mkSigma v (FunEl g0)) nil) v c-vu cv
      le-u'-ef = LeCode-trans (FunEl g') (FunEl g0) (EvalFun (cons (mkSigma v (FunEl g0)) nil) v)
                   cu' cu c-ef le le-refl
      -- Coherent (FunEl [(v,FunEl g')])
      c-vu' = mkCFT cv cu' tt tt tt
      -- EvalRel-down M
      evM' = EvalRel-down M rho
               (FunEl (cons (mkSigma v (FunEl g0)) nil))
               (FunEl (cons (mkSigma v (FunEl g')) nil))
               crho c-vu' evM (mkSigma le-u'-ef tt)
  in mkSigma v (mkSigma evN evM')
EvalRel-down (App M N) rho (FunEl g0) (PiCode a' f') crho cu' ev ()
EvalRel-down (App M N) rho (PiCode a0 f0) UCode crho cu' ev ()
EvalRel-down (App M N) rho (PiCode a0 f0) (FunEl g') crho cu' ev ()
EvalRel-down (App M N) rho (PiCode a0 f0) (PiCode a' f') crho cu' ev le =
  let v   = fst ev
      evN = fst (snd ev)
      evM = snd (snd ev)
      -- Coherence from M evidence
      c-vu = EvalRel-coh M rho (FunEl (cons (mkSigma v (PiCode a0 f0)) nil)) evM
      cv   = Coherent-singleton-key v (PiCode a0 f0) c-vu
      cu   = Coherent-singleton-val v (PiCode a0 f0) c-vu
      -- LeCode (PiCode a0 f0) (EvalFun [(v,PiCode a0 f0)] v) from LeCode-refl
      le-refl = fst (LeCode-refl (FunEl (cons (mkSigma v (PiCode a0 f0)) nil)) c-vu)
      c-ef = Coherent-EvalFun (cons (mkSigma v (PiCode a0 f0)) nil) v c-vu cv
      le-u'-ef = LeCode-trans (PiCode a' f') (PiCode a0 f0)
                   (EvalFun (cons (mkSigma v (PiCode a0 f0)) nil) v)
                   cu' cu c-ef le le-refl
      -- Coherent (FunEl [(v,PiCode a' f')])
      c-vu' = mkCFT cv cu' tt tt tt
      -- EvalRel-down M
      evM' = EvalRel-down M rho
               (FunEl (cons (mkSigma v (PiCode a0 f0)) nil))
               (FunEl (cons (mkSigma v (PiCode a' f')) nil))
               crho c-vu' evM (mkSigma le-u'-ef tt)
  in mkSigma v (mkSigma evN evM')

-- Lam: absurd cases for UCode/PiCode outputs
EvalRel-down (Lam A M) rho UCode u' crho cu' () le
EvalRel-down (Lam A M) rho (PiCode a f) u' crho cu' () le
-- Lam Bot: u' <= Bot forces u' = Bot
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
-- Uses selectionBelow + original body + IH on M
EvalRel-down (Lam A M) rho (FunEl g) (FunEl g') crho cu' ev le =
  let a    = fst ev
      cg   = fst (snd ev)
      aU   = fst (snd (snd ev))
      evA  = fst (snd (snd (snd ev)))
      body = snd (snd (snd (snd ev)))
      cg'  = cu'  -- Coherent (FunEl g') = CoherentFun g'
      ctg' = cft-from-cf g' cg'
      ctg  = cft-from-cf g cg
  in mkSigma a (mkSigma cg' (mkSigma aU (mkSigma evA
       (\ u v sel ->
          let cu  = Coherent-Selection sel cg'
              cv  = Coherent-Selection-val sel cg'
              -- v <= EvalFun g' u <= EvalFun g u
              lf-g' = LeCode-refl (FunEl g') cg'
              le-v-efg' = Selection-le-EvalFun g' sel lf-g' cg' cg' cu
              le-efg'-efg = EvalFun-mon g' g u ctg' ctg cu le
              c-efg'u = Coherent-EvalFun g' u ctg' cu
              c-efgu  = Coherent-EvalFun g u ctg cu
              le-v-efgu = LeCode-trans v (EvalFun g' u) (EvalFun g u)
                            cv c-efg'u c-efgu le-v-efg' le-efg'-efg
              -- selectionBelow g at u: genuine selection of g
              sb     = selectionBelow g u cg cu
              u0     = fst sb
              v0     = fst (snd sb)
              sel-g  = fst (snd (snd sb))
              le-u0  = fst (snd (snd (snd sb)))
              eq-v0  = snd (snd (snd (snd sb)))
              -- Feed selection into original body from ev
              w      = body u0 v0 sel-g
              x      = fst w
              le-x-u0 = fst (snd w)
              mem-x  = fst (snd (snd w))
              evM-v0 = snd (snd (snd w))
              -- x <= u0 <= u
              cx     = FinMem-coh-u x a mem-x
              le-x-u = LeCode-trans x u0 u cx
                         (Coherent-Selection sel-g cg) cu le-x-u0 le-u0
              -- v <= v0 (since v <= EvalFun g u = v0)
              le-v-v0 = Eq-transport (LeCode v) eq-v0 le-v-efgu
              -- IH: EvalRel-down M to go from v0 to v
              cx-env = mkSigma crho cx
              evM-v  = EvalRel-down M (extendEnv rho x) v0 v cx-env cv evM-v0 le-v-v0
          in mkSigma x (mkSigma le-x-u (mkSigma mem-x evM-v))))))

-- Pi: absurd cases for UCode/FunEl outputs
EvalRel-down (Pi A B) rho UCode u' crho cu' () le
EvalRel-down (Pi A B) rho (FunEl g) u' crho cu' () le
-- Pi Bot: u' <= Bot forces u' = Bot
EvalRel-down (Pi A B) rho Bot Bot crho cu' ev le = tt
EvalRel-down (Pi A B) rho Bot UCode crho cu' ev ()
EvalRel-down (Pi A B) rho Bot (FunEl g') crho cu' ev ()
EvalRel-down (Pi A B) rho Bot (PiCode a' f') crho cu' ev ()
-- Pi (PiCode a f) Bot: trivial
EvalRel-down (Pi A B) rho (PiCode a f) Bot crho cu' ev le = tt
-- Pi (PiCode a f) absurd cross-constructors
EvalRel-down (Pi A B) rho (PiCode a f) UCode crho cu' ev ()
EvalRel-down (Pi A B) rho (PiCode a f) (FunEl g') crho cu' ev ()
-- Pi (PiCode a f) (PiCode a' f'): harder than Lam because the domain
-- changes from a to a'. The body gives FinMem x a, but target needs
-- FinMem x a'. This requires FinMem downward closure in domain.
-- Same technique as Lam for everything except the FinMem transport.
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
      ctf' = cft-from-cf f' cf'
      ctf  = cft-from-cf f cf-orig
  in mkSigma cu' (mkSigma
       (EvalRel-down A rho a a' crho ca' evA le-a)
       (mkSigma a0 (mkSigma evA0
       (\ u v sel ->
          let cu  = Coherent-Selection sel cf'
              cv  = Coherent-Selection-val sel cf'
              -- v <= EvalFun f' u <= EvalFun f u
              lf-f' = LeCode-refl (FunEl f') cf'
              le-v-eff' = Selection-le-EvalFun f' sel lf-f' cf' cf' cu
              le-eff'-eff = EvalFun-mon f' f u ctf' ctf cu le-f
              c-eff'u = Coherent-EvalFun f' u ctf' cu
              c-effu  = Coherent-EvalFun f u ctf cu
              le-v-effu = LeCode-trans v (EvalFun f' u) (EvalFun f u)
                            cv c-eff'u c-effu le-v-eff' le-eff'-eff
              -- selectionBelow f at u
              sb     = selectionBelow f u cf-orig cu
              u0     = fst sb
              v0     = fst (snd sb)
              sel-f  = fst (snd (snd sb))
              le-u0  = fst (snd (snd (snd sb)))
              eq-v0  = snd (snd (snd (snd sb)))
              -- Feed into original body to get EvalRel B (rho,x) v0
              w      = body u0 v0 sel-f
              x      = fst w
              le-x-u0 = fst (snd w)
              mem-x-a0 = fst (snd (snd w))
              evB-v0 = snd (snd (snd w))
              cx     = FinMem-coh-u x a0 mem-x-a0
              le-x-u = LeCode-trans x u0 u cx
                         (Coherent-Selection sel-f cf-orig) cu le-x-u0 le-u0
              -- Down from v0 to v at (rho,x)
              le-v-v0 = Eq-transport (LeCode v) eq-v0 le-v-effu
              cx-env = mkSigma crho cx
              evB-x-v = EvalRel-down B (extendEnv rho x) v0 v cx-env cv evB-v0 le-v-v0
          in mkSigma x (mkSigma le-x-u (mkSigma mem-x-a0 evB-x-v))))))

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

-- Var i: LeCode-Sup-lub from the two LeCode witnesses
EvalRel-Sup (Var i) rho u v crho cu cv comp eu ev =
  mkSigma (Coherent-Sup u v comp cu cv)
          (LeCode-Sup-lub u v (lookupEnv i rho) (snd eu) (snd ev))

-- U: LeCode-Sup-lub from the two LeCode-to-UCode witnesses
EvalRel-Sup U rho u v crho cu cv comp eu ev =
  mkSigma (Coherent-Sup u v comp cu cv) (LeCode-Sup-lub u v UCode (snd eu) (snd ev))

-- App: case split on both u and v
-- Bot cases: Sup Bot v = v, Sup u Bot = u
EvalRel-Sup (App M N) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (App M N) rho UCode Bot crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho (FunEl g1') Bot crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho (PiCode a1' f1') Bot crho cu cv comp eu ev = eu

-- Cross-constructor non-Bot: Sup collapses
EvalRel-Sup (App M N) rho UCode (FunEl g2') crho cu cv comp eu ev = eu
EvalRel-Sup (App M N) rho UCode (PiCode a2' f2') crho cu cv () eu ev
EvalRel-Sup (App M N) rho (FunEl g1') UCode crho cu cv comp eu ev = ev
EvalRel-Sup (App M N) rho (FunEl g1') (PiCode a2' f2') crho cu cv comp eu ev = ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') UCode crho cu cv () eu ev
EvalRel-Sup (App M N) rho (PiCode a1' f1') (FunEl g2') crho cu cv comp eu ev = eu

-- UCode-UCode: Sup UCode UCode = UCode
EvalRel-Sup (App M N) rho UCode UCode crho cu cv comp eu ev = eu

-- FunEl-FunEl: one-edge Sup
-- eu: v1, evN1, evM1 with evM1 : EvalRel M rho (FunEl [(v1, FunEl g1')])
-- ev: v2, evN2, evM2 with evM2 : EvalRel M rho (FunEl [(v2, FunEl g2')])
-- Result: v, evN, evM with evM : EvalRel M rho (FunEl [(v, FunEl (append g1' g2'))])
-- Strategy: Sup on M's singletons → 2-element graph, then down to singleton with Sup key
EvalRel-Sup (App M N) rho (FunEl g1') (FunEl g2') crho cu cv comp eu ev =
  let -- Extract one-edge evidence
      v1   = fst eu
      evN1 = fst (snd eu)
      evM1 = snd (snd eu)
      v2   = fst ev
      evN2 = fst (snd ev)
      evM2 = snd (snd ev)
      -- Coherence
      cv1  = EvalRel-coh N rho v1 evN1
      cv2  = EvalRel-coh N rho v2 evN2
      cM1  = EvalRel-coh M rho (FunEl (cons (mkSigma v1 (FunEl g1')) nil)) evM1
      cM2  = EvalRel-coh M rho (FunEl (cons (mkSigma v2 (FunEl g2')) nil)) evM2
      -- IH on N: Comp v1 v2
      comp-v = EvalRel-Comp N rho crho v1 v2 evN1 evN2
      -- IH on M: Comp (FunEl [(v1, FunEl g1')]) (FunEl [(v2, FunEl g2')])
      comp-M = EvalRel-Comp M rho crho
                 (FunEl (cons (mkSigma v1 (FunEl g1')) nil))
                 (FunEl (cons (mkSigma v2 (FunEl g2')) nil))
                 evM1 evM2
      -- IH on N: EvalRel N rho (Sup v1 v2)
      evN-sup = EvalRel-Sup N rho v1 v2 crho cv1 cv2 comp-v evN1 evN2
      -- IH on M: EvalRel M rho (FunEl [(v1, FunEl g1'), (v2, FunEl g2')])
      evM-2 = EvalRel-Sup M rho
                (FunEl (cons (mkSigma v1 (FunEl g1')) nil))
                (FunEl (cons (mkSigma v2 (FunEl g2')) nil))
                crho cM1 cM2 comp-M evM1 evM2
      -- Coherence of the 2-element graph
      c-2graph = Coherent-Sup
                   (FunEl (cons (mkSigma v1 (FunEl g1')) nil))
                   (FunEl (cons (mkSigma v2 (FunEl g2')) nil))
                   comp-M cM1 cM2
      -- Sup v1 v2 coherent
      c-supv = Coherent-Sup v1 v2 comp-v cv1 cv2
      -- Need: singleton graph [(Sup v1 v2, FunEl (append g1' g2'))] <= 2-element graph
      -- LeFunCode [(Sup v1 v2, FunEl (append g1' g2'))]
      --           [(v1, FunEl g1'), (v2, FunEl g2')]
      -- = LeCode (FunEl (append g1' g2'))
      --          (EvalFun [(v1, FunEl g1'), (v2, FunEl g2')] (Sup v1 v2))
      -- EvalFun at Sup v1 v2: both keys Comp, so result = Sup (FunEl g1') (FunEl g2')
      --                      = FunEl (append g1' g2')
      -- So we need LeCode-refl (FunEl (append g1' g2'))
      c-result-val = Coherent-Sup (FunEl g1') (FunEl g2') comp cu cv
      le-down = LeFunCode-Sup-pair v1 (FunEl g1') v2 (FunEl g2') comp-v comp c-2graph c-supv
      -- Coherent singleton
      c-singleton = mkCFT c-supv c-result-val tt tt tt
      -- EvalRel-down M: from 2-element graph to singleton
      evM-result = EvalRel-down M rho
                     (FunEl (cons (mkSigma v1 (FunEl g1')) (cons (mkSigma v2 (FunEl g2')) nil)))
                     (FunEl (cons (mkSigma (Sup v1 v2) (FunEl (append g1' g2'))) nil))
                     crho c-singleton evM-2 le-down
  in mkSigma (Sup v1 v2) (mkSigma evN-sup evM-result)

-- PiCode-PiCode: same strategy as FunEl-FunEl
-- Sup (PiCode a1' f1') (PiCode a2' f2') = PiCode (Sup a1' a2') (append f1' f2')
EvalRel-Sup (App M N) rho (PiCode a1' f1') (PiCode a2' f2') crho cu cv comp eu ev =
  let -- Extract one-edge evidence
      v1   = fst eu
      evN1 = fst (snd eu)
      evM1 = snd (snd eu)
      v2   = fst ev
      evN2 = fst (snd ev)
      evM2 = snd (snd ev)
      -- Coherence
      cv1  = EvalRel-coh N rho v1 evN1
      cv2  = EvalRel-coh N rho v2 evN2
      cM1  = EvalRel-coh M rho (FunEl (cons (mkSigma v1 (PiCode a1' f1')) nil)) evM1
      cM2  = EvalRel-coh M rho (FunEl (cons (mkSigma v2 (PiCode a2' f2')) nil)) evM2
      -- IH on N and M
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

-- Lam: case split on u and v
-- Bot cases: trivial
EvalRel-Sup (Lam A M) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (Lam A M) rho (FunEl g1) Bot crho cu cv comp eu ev = eu

-- Absurd cases
EvalRel-Sup (Lam A M) rho UCode v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho (PiCode a1 f1) v crho cu cv comp () ev
EvalRel-Sup (Lam A M) rho (FunEl g1) UCode crho cu cv comp eu ()
EvalRel-Sup (Lam A M) rho (FunEl g1) (PiCode a2 f2) crho cu cv comp eu ()

-- FunEl-FunEl: the hard case for Lam
-- Sup (FunEl g1) (FunEl g2) = FunEl (append g1 g2)
EvalRel-Sup (Lam A M) rho (FunEl g1) (FunEl g2) crho cu cv comp eu ev =
  let -- Extract from eu: (a1, cg1, a1U, evA1, body1)
      a1    = fst eu
      cg1   = fst (snd eu)
      a1U   = fst (snd (snd eu))
      evA1  = fst (snd (snd (snd eu)))
      body1 = snd (snd (snd (snd eu)))
      -- Extract from ev: (a2, cg2, a2U, evA2, body2)
      a2    = fst ev
      cg2   = fst (snd ev)
      a2U   = fst (snd (snd ev))
      evA2  = fst (snd (snd (snd ev)))
      body2 = snd (snd (snd (snd ev)))
      -- IH on A: Comp a1 a2
      ca1   = EvalRel-coh A rho a1 evA1
      ca2   = EvalRel-coh A rho a2 evA2
      comp-a = EvalRel-Comp A rho crho a1 a2 evA1 evA2
      -- IH on A: EvalRel A rho (Sup a1 a2)
      evA-sup = EvalRel-Sup A rho a1 a2 crho ca1 ca2 comp-a evA1 evA2
      -- Coherence
      c-sup-a = Coherent-Sup a1 a2 comp-a ca1 ca2
      -- FinMem (Sup a1 a2) UCode
      supU = FinMem-Sup-element a1 a2 UCode comp-a tt a1U a2U
      -- CoherentFun (append g1 g2)
      c-gab = CoherentFun-append g1 g2 cg1 cg2 comp
      -- Body: for every Selection (append g1 g2) u v, build witness
  in mkSigma (Sup a1 a2) (mkSigma c-gab (mkSigma supU (mkSigma evA-sup
       (\ u v sel ->
          let -- selectionBelow g1 u and g2 u
              cu-sel = Coherent-Selection sel c-gab
              cv-sel = Coherent-Selection-val sel c-gab
              sb1    = selectionBelow g1 u cg1 cu-sel
              u1     = fst sb1
              v1     = fst (snd sb1)
              sel1   = fst (snd (snd sb1))
              le-u1  = fst (snd (snd (snd sb1)))
              eq-v1  = snd (snd (snd (snd sb1)))
              sb2    = selectionBelow g2 u cg2 cu-sel
              u2     = fst sb2
              v2     = fst (snd sb2)
              sel2   = fst (snd (snd sb2))
              le-u2  = fst (snd (snd (snd sb2)))
              eq-v2  = snd (snd (snd (snd sb2)))
              -- body1 with sel1: (x1, le-x1-u1, mem-x1-a1, evM-x1-v1)
              w1     = body1 u1 v1 sel1
              x1     = fst w1
              le-x1  = fst (snd w1)
              mem-x1 = fst (snd (snd w1))
              evM-x1 = snd (snd (snd w1))
              -- body2 with sel2: (x2, le-x2-u2, mem-x2-a2, evM-x2-v2)
              w2     = body2 u2 v2 sel2
              x2     = fst w2
              le-x2  = fst (snd w2)
              mem-x2 = fst (snd (snd w2))
              evM-x2 = snd (snd (snd w2))
              -- Coherence of x1, x2
              cx1    = FinMem-coh-u x1 a1 mem-x1
              cx2    = FinMem-coh-u x2 a2 mem-x2
              -- Comp x1 x2: both <= u via chains, so LeCode-Comp
              le-x1-u = LeCode-trans x1 u1 u cx1 (Coherent-Selection sel1 cg1) cu-sel le-x1 le-u1
              le-x2-u = LeCode-trans x2 u2 u cx2 (Coherent-Selection sel2 cg2) cu-sel le-x2 le-u2
              comp-x  = LeCode-Comp x1 x2 u cu-sel le-x1-u le-x2-u
              -- Sup x1 x2
              c-supx  = Coherent-Sup x1 x2 comp-x cx1 cx2
              -- LeCode (Sup x1 x2) u
              le-supx-u = LeCode-Sup-lub x1 x2 u le-x1-u le-x2-u
              -- FinMem (Sup x1 x2) (Sup a1 a2)
              le-a1-sup = LeCode-Sup-left a1 a2 comp-a ca1 ca2
              le-a2-sup = LeCode-Sup-right a1 a2 comp-a ca1 ca2
              mem-x1-sup = finMem-upward x1 a1 (Sup a1 a2) le-a1-sup ca1 c-sup-a mem-x1 supU
              mem-x2-sup = finMem-upward x2 a2 (Sup a1 a2) le-a2-sup ca2 c-sup-a mem-x2 supU
              mem-supx   = FinMem-Sup-element x1 x2 (Sup a1 a2) comp-x c-sup-a mem-x1-sup mem-x2-sup
              -- Transport evM witnesses to extended env with Sup x1 x2
              envle1 = EnvLe-extend-left rho x1 x2 crho comp-x cx1 cx2
              envle2 = EnvLe-extend-right rho x1 x2 crho comp-x cx1 cx2
              evM-sup1 = EvalRel-mon-env M (extendEnv rho x1) (extendEnv rho (Sup x1 x2)) v1 evM-x1 envle1
              evM-sup2 = EvalRel-mon-env M (extendEnv rho x2) (extendEnv rho (Sup x1 x2)) v2 evM-x2 envle2
              -- Comp v1 v2
              crho-sup = mkSigma crho c-supx
              comp-v = EvalRel-Comp M (extendEnv rho (Sup x1 x2)) crho-sup v1 v2 evM-sup1 evM-sup2
              -- IH on M: EvalRel M (rho, Sup x1 x2) (Sup v1 v2)
              cv1    = EvalRel-coh M (extendEnv rho x1) v1 evM-x1
              cv2    = EvalRel-coh M (extendEnv rho x2) v2 evM-x2
              evM-supv = EvalRel-Sup M (extendEnv rho (Sup x1 x2)) v1 v2 crho-sup cv1 cv2 comp-v evM-sup1 evM-sup2
              -- v <= Sup v1 v2 via Selection-le-EvalFun + EvalFun-append-eq
              -- v <= EvalFun (append g1 g2) u
              ct-gab = cft-from-cf (append g1 g2) c-gab
              lf-gab = LeFunCode-refl (append g1 g2) ct-gab
              le-v-ef = Selection-le-EvalFun (append g1 g2) sel lf-gab c-gab c-gab cu-sel
              -- EvalFun (append g1 g2) u = Sup (EvalFun g1 u) (EvalFun g2 u)
              ctg1   = cft-from-cf g1 cg1
              eq-ef  = EvalFun-append-eq g1 g2 u comp ctg1 cu-sel
              -- v1 = EvalFun g1 u, v2 = EvalFun g2 u
              -- So Sup v1 v2 = Sup (EvalFun g1 u) (EvalFun g2 u) = EvalFun (append g1 g2) u
              -- le-v-ef : LeCode v (EvalFun (append g1 g2) u)
              -- eq-ef : Eq (EvalFun (append g1 g2) u) (Sup (EvalFun g1 u) (EvalFun g2 u))
              le-v-supef = Eq-transport (LeCode v) eq-ef le-v-ef
              -- eq-v1 : Eq (EvalFun g1 u) v1, eq-v2 : Eq (EvalFun g2 u) v2
              -- Need: Eq (Sup (EvalFun g1 u) (EvalFun g2 u)) (Sup v1 v2)
              eq-sup = Eq-transport (\ z -> Eq (Sup z (EvalFun g2 u)) (Sup v1 v2))
                         (Eq-sym eq-v1)
                         (Eq-transport (\ z -> Eq (Sup v1 z) (Sup v1 v2))
                           (Eq-sym eq-v2) refl)
              le-v-supv = Eq-transport (LeCode v) eq-sup le-v-supef
              -- Down from Sup v1 v2 to v
              c-supv = Coherent-Sup v1 v2 comp-v cv1 cv2
              evM-v  = EvalRel-down M (extendEnv rho (Sup x1 x2)) (Sup v1 v2) v crho-sup cv-sel evM-supv le-v-supv
          in mkSigma (Sup x1 x2) (mkSigma le-supx-u (mkSigma mem-supx evM-v))))))

-- Pi: case split on u and v
-- Bot cases: trivial
EvalRel-Sup (Pi A B) rho Bot v crho cu cv comp eu ev = ev
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) Bot crho cu cv comp eu ev = eu

-- Absurd cases
EvalRel-Sup (Pi A B) rho UCode v crho cu cv comp () ev
EvalRel-Sup (Pi A B) rho (FunEl g1) v crho cu cv comp () ev
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) UCode crho cu cv comp eu ()
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) (FunEl g2) crho cu cv comp eu ()

-- PiCode-PiCode: the hard case for Pi
-- Sup (PiCode a1 f1) (PiCode a2 f2) = PiCode (Sup a1 a2) (append f1 f2)
EvalRel-Sup (Pi A B) rho (PiCode a1 f1) (PiCode a2 f2) crho cu cv comp eu ev =
  let -- Extract from eu: (Coherent, EvalRel A rho a1, a1', EvalRel A rho a1', body1)
      cu1   = fst eu
      evA1  = fst (snd eu)
      a1'   = fst (snd (snd eu))
      evA1' = fst (snd (snd (snd eu)))
      body1 = snd (snd (snd (snd eu)))
      -- Extract from ev: (Coherent, EvalRel A rho a2, a2', EvalRel A rho a2', body2)
      cu2   = fst ev
      evA2  = fst (snd ev)
      a2'   = fst (snd (snd ev))
      evA2' = fst (snd (snd (snd ev)))
      body2 = snd (snd (snd (snd ev)))
      -- IH on A
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
      -- Coherent (PiCode (Sup a1 a2) (append f1 f2))
      c-result = Coherent-Sup (PiCode a1 f1) (PiCode a2 f2) comp cu cv
      -- CoherentFun (append f1 f2)
      cf1   = snd cu1
      cf2   = snd cu2
      c-fab = CoherentFun-append f1 f2 cf1 cf2 comp-f
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
              -- body1 with sel1
              w1     = body1 u1 v1 sel1
              x1     = fst w1
              le-x1  = fst (snd w1)
              mem-x1 = fst (snd (snd w1))
              evB-x1 = snd (snd (snd w1))
              -- body2 with sel2
              w2     = body2 u2 v2 sel2
              x2     = fst w2
              le-x2  = fst (snd w2)
              mem-x2 = fst (snd (snd w2))
              evB-x2 = snd (snd (snd w2))
              -- Coherence of x1, x2
              cx1    = FinMem-coh-u x1 a1' mem-x1
              cx2    = FinMem-coh-u x2 a2' mem-x2
              -- Comp x1 x2
              le-x1-u = LeCode-trans x1 u1 u cx1 (Coherent-Selection sel1 cf1) cu-sel le-x1 le-u1
              le-x2-u = LeCode-trans x2 u2 u cx2 (Coherent-Selection sel2 cf2) cu-sel le-x2 le-u2
              comp-x  = LeCode-Comp x1 x2 u cu-sel le-x1-u le-x2-u
              c-supx  = Coherent-Sup x1 x2 comp-x cx1 cx2
              le-supx-u = LeCode-Sup-lub x1 x2 u le-x1-u le-x2-u
              -- FinMem (Sup x1 x2) (Sup a1' a2')
              le-a1'-sup = LeCode-Sup-left a1' a2' comp-a' ca1' ca2'
              le-a2'-sup = LeCode-Sup-right a1' a2' comp-a' ca1' ca2'
              supU-a' = FinMem-a-in-U x1 a1' mem-x1
              supU-a'' = FinMem-a-in-U x2 a2' mem-x2
              supU-result = FinMem-Sup-element a1' a2' UCode comp-a' tt supU-a' supU-a''
              mem-x1-sup = finMem-upward x1 a1' (Sup a1' a2') le-a1'-sup ca1' c-sup-a' mem-x1 supU-result
              mem-x2-sup = finMem-upward x2 a2' (Sup a1' a2') le-a2'-sup ca2' c-sup-a' mem-x2 supU-result
              mem-supx   = FinMem-Sup-element x1 x2 (Sup a1' a2') comp-x c-sup-a' mem-x1-sup mem-x2-sup
              -- Transport evB witnesses to extended env with Sup x1 x2
              envle1 = EnvLe-extend-left rho x1 x2 crho comp-x cx1 cx2
              envle2 = EnvLe-extend-right rho x1 x2 crho comp-x cx1 cx2
              evB-sup1 = EvalRel-mon-env B (extendEnv rho x1) (extendEnv rho (Sup x1 x2)) v1 evB-x1 envle1
              evB-sup2 = EvalRel-mon-env B (extendEnv rho x2) (extendEnv rho (Sup x1 x2)) v2 evB-x2 envle2
              -- Comp v1 v2
              crho-sup = mkSigma crho c-supx
              comp-v = EvalRel-Comp B (extendEnv rho (Sup x1 x2)) crho-sup v1 v2 evB-sup1 evB-sup2
              cv1    = EvalRel-coh B (extendEnv rho x1) v1 evB-x1
              cv2    = EvalRel-coh B (extendEnv rho x2) v2 evB-x2
              -- IH on B
              evB-supv = EvalRel-Sup B (extendEnv rho (Sup x1 x2)) v1 v2 crho-sup cv1 cv2 comp-v evB-sup1 evB-sup2
              -- v <= Sup v1 v2 via same chain as Lam case
              ct-fab = cft-from-cf (append f1 f2) c-fab
              lf-fab = LeFunCode-refl (append f1 f2) ct-fab
              le-v-ef = Selection-le-EvalFun (append f1 f2) sel lf-fab c-fab c-fab cu-sel
              ctf1   = cft-from-cf f1 cf1
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

------------------------------------------------------------------------
-- EvalRel-Comp-ext: compatibility of evaluation results at
-- compatible environment extensions.
--
-- If M evaluates to y1 at (rho, x1) and to y2 at (rho, x2),
-- and x1, x2 are compatible, then y1 and y2 are compatible.
--
-- Proof: lift both evaluations to the common environment
-- (rho, Sup x1 x2) via EvalRel-mon-env, then apply EvalRel-Comp.
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
--
-- If M evaluates to y1 at (rho, x1) and to y2 at (rho, x2),
-- and x1, x2 are compatible, then M evaluates to Sup y1 y2
-- at (rho, Sup x1 x2).
--
-- Proof: lift both evaluations to (rho, Sup x1 x2) via
-- EvalRel-mon-env, derive Comp y1 y2 via EvalRel-Comp,
-- then apply EvalRel-Sup.
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
