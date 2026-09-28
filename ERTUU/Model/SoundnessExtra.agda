{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERTUU.Model.SoundnessExtra
--
-- The soundness lemmas the Russell system needs beyond MIN's
-- (ERTUU.Model.SoundnessLemmas):
--
--   * InvTyp-U-lvl      the type of types may be any universe level
--                       (membership in a universe ignores its level);
--   * InvTyp-equiv      InvTyp transported along semantic equivalence;
--   * InvTyp-var, InvTyp-wk
--                       variables, and weakening of the invariant;
--   * InvConv-Lam-body, InvConv-Lam-dom
--                       congruence of λ in its body and in its domain;
--   * InvConv-eta       the eta rule  c = λx. c x  at a product type.
--
-- 0 postulates.
------------------------------------------------------------------------

module ERTUU.Model.SoundnessExtra where

open import ERTUU.Dom.Basic using (U0 ; EqL-refl)
import ERTUU.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ;
              Pair ; List ; nil ; cons ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun)
open import ERTUU.Dom.Kernel using (LeCode ; LeCode-refl ; LeCode-trans ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ; cft-from-cf ;
  NotBot ; FinMem ; FinMem-coh-u ; coh-from-aU ; finMem-U-lvl ;
  finMem-piU-dom ; finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf ;
  Sup-Bot-r ; LeFunCode ; LeFunCode-refl ; EvalFun)
open CFTcons
open import ERTUU.Model.Selection using (Selection ; Edge ; EdgeIn ; here ; there ;
  Coherent-Selection ; Coherent-Selection-val ; CoherentFun-edge-key ;
  singleton-selection ; Selection-le-EvalFun ; FinMem-Selection)
open import ERTUU.Model.Core using (Expr ; Var ; U ; Pi ; Lam ; App ;
  Fin ; fzero ; fsuc ; liftRen ; renExpr ; wkRen ; wkExpr ; subst1 ; subst1Sub ;
  Sub ; liftSub ; substExpr ; substExpr-ext ; subst-ren ; Eq-trans ; Eq-cong2-Expr ;
  Ctx ; extend ; lookup)
open import ERTUU.Model.Eval
open import ERTUU.Model.EvalSubstitution using (EvalRel-wk ; EvalRel-unwk)
open import ERTUU.Model.SoundnessLemmas using (Fits ; Fits-CoherentEnv ; Fits-var ;
  Typed ; InvTyp ; InvConv ; EvalFun-edge-le)

------------------------------------------------------------------------
-- Two syntactic facts about core terms
------------------------------------------------------------------------

substExpr-id : {n : Nat} (e : Expr n) -> Eq (substExpr Var e) e
substExpr-id (Var i)   = refl
substExpr-id (U l)     = refl
substExpr-id (Pi A B)  =
  Eq-cong2-Expr Pi (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub Var) Var liftVar B) (substExpr-id B))
  where
    liftVar : (i : Fin _) -> Eq (liftSub Var i) (Var i)
    liftVar fzero    = refl
    liftVar (fsuc i) = refl
substExpr-id (Lam A M) =
  Eq-cong2-Expr Lam (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub Var) Var liftVar M) (substExpr-id M))
  where
    liftVar : (i : Fin _) -> Eq (liftSub Var i) (Var i)
    liftVar fzero    = refl
    liftVar (fsuc i) = refl
substExpr-id (App f a) = Eq-cong2-Expr App (substExpr-id f) (substExpr-id a)

-- (B lifted past a fresh variable) applied to that variable is B.
subst1-liftWk-cancel : {n : Nat} (B : Expr (suc n))
  -> Eq (subst1 (renExpr (liftRen wkRen) B) (Var fzero)) B
subst1-liftWk-cancel B =
  Eq-trans (subst-ren (subst1Sub (Var fzero)) (liftRen wkRen) B)
    (Eq-trans (substExpr-ext _ Var ext B) (substExpr-id B))
  where
    ext : (i : Fin _) -> Eq (subst1Sub (Var fzero) (liftRen wkRen i)) (Var i)
    ext fzero    = refl
    ext (fsuc i) = refl

------------------------------------------------------------------------
-- The type of a type may be any universe
------------------------------------------------------------------------

InvTyp-U-lvl : {n : Nat} {G : Ctx n} {M : Expr n} {rho : EnvApprox n}
  (l m : Nat) -> InvTyp G M (U l) rho -> InvTyp G M (U m) rho
InvTyp-U-lvl {rho = rho} l m inv u ev =
  let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evU)))) = inv u ev
      mkSigma a'' (mkSigma fm' evU') = shift u' a' fm evU
  in mkSigma u' (mkSigma a'' (mkSigma le (mkSigma evM (mkSigma fm' evU'))))
  where
    shift : (u' a' : FinEl) -> FinMem u' a' -> EvalRel (U l) rho a'
      -> Sigma FinEl (\ a'' -> Pair (FinMem u' a'') (EvalRel (U m) rho a''))
    shift u' Bot          fm ev = mkSigma Bot (mkSigma fm (mkSigma tt tt))
    shift u' (UCode k)    fm ev =
      mkSigma (UCode m) (mkSigma (finMem-U-lvl u' k m fm) (mkSigma tt (EqL-refl m)))
    shift u' (FunEl g)    fm (mkSigma _ ())
    shift u' (PiCode a f) fm (mkSigma _ ())

------------------------------------------------------------------------
-- InvTyp along a semantic equivalence of terms
------------------------------------------------------------------------

InvTyp-equiv : {n : Nat} {G : Ctx n} {M N T : Expr n} {rho : EnvApprox n}
  -> InvTyp G M T rho
  -> ((u : FinEl) -> EvalRel N rho u -> EvalRel M rho u)
  -> ((u : FinEl) -> EvalRel M rho u -> EvalRel N rho u)
  -> InvTyp G N T rho
InvTyp-equiv inv bwd fwd u ev =
  let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evT)))) = inv u (bwd u ev)
  in mkSigma u' (mkSigma a' (mkSigma le (mkSigma (fwd u' evM) (mkSigma fm evT))))

------------------------------------------------------------------------
-- Variables and weakening
------------------------------------------------------------------------

InvTyp-var : {n : Nat} {G : Ctx n} (rho : EnvApprox n) -> Fits G rho
  -> (i : Fin n) -> InvTyp G (Var i) (lookup G i) rho
InvTyp-var rho fits i u (mkSigma cu le) =
  let mkSigma a' (mkSigma fm evA) = Fits-var rho fits i
      li  = lookupEnv i rho
      cli = FinMem-coh-u li a' fm
  in mkSigma li (mkSigma a'
       (mkSigma le (mkSigma (mkSigma cli (LeCode-refl li cli))
         (mkSigma fm evA))))

InvTyp-wk : {n : Nat} {G : Ctx n} {C M T : Expr n} {rho : EnvApprox n} {x : FinEl}
  -> InvTyp G M T rho -> InvTyp (extend G C) (wkExpr M) (wkExpr T) (extendEnv rho x)
InvTyp-wk {M = M} {T = T} {rho = rho} {x = x} inv u ev =
  let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evT)))) =
        inv u (EvalRel-unwk M rho x u ev)
  in mkSigma u' (mkSigma a' (mkSigma le
       (mkSigma (EvalRel-wk M rho x u' evM)
         (mkSigma fm (EvalRel-wk T rho x a' evT)))))

------------------------------------------------------------------------
-- Congruence of λ
------------------------------------------------------------------------

Lam-map : {n : Nat} {A A' : Expr n} {M M' : Expr (suc n)} {rho : EnvApprox n}
  -> ((a : FinEl) -> EvalRel A rho a -> EvalRel A' rho a)
  -> ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
       (v : FinEl) -> EvalRel M (extendEnv rho x) v -> EvalRel M' (extendEnv rho x) v)
  -> (u : FinEl) -> EvalRel (Lam A M) rho u -> EvalRel (Lam A' M') rho u
Lam-map fA fM Bot          ev = tt
Lam-map fA fM (FunEl g)    (mkSigma a (mkSigma cg (mkSigma aU (mkSigma evA body)))) =
  mkSigma a (mkSigma cg (mkSigma aU (mkSigma (fA a evA)
    (\ u v sel ->
      let mkSigma x (mkSigma le (mkSigma fm evM)) = body u v sel
      in mkSigma x (mkSigma le (mkSigma fm (fM x a fm evA v evM)))))))
Lam-map fA fM (UCode _)    ()
Lam-map fA fM (PiCode _ _) ()

-- λ with convertible bodies.
InvConv-Lam-body : {n : Nat} {G : Ctx n} (A : Expr n) (B M M' : Expr (suc n))
  -> (rho : EnvApprox n) -> Fits G rho
  -> ((rho' : EnvApprox n) (x a : FinEl) -> Fits G rho' -> FinMem x a ->
       EvalRel A rho' a -> InvConv (extend G A) M M' B (extendEnv rho' x))
  -> InvTyp G (Lam A M) (Pi A B) rho
  -> InvTyp G (Lam A M') (Pi A B) rho
  -> InvConv G (Lam A M) (Lam A M') (Pi A B) rho
InvConv-Lam-body A B M M' rho fits bih invL invR =
  mkSigma invL (mkSigma invR
    (mkSigma (Lam-map {A = A} {A' = A} {M = M} {M' = M'} {rho = rho} (\ a e -> e)
               (\ x a fm evA v ev -> fst (snd (snd (bih rho x a fits fm evA))) v ev))
             (Lam-map {A = A} {A' = A} {M = M'} {M' = M} {rho = rho} (\ a e -> e)
               (\ x a fm evA v ev -> snd (snd (snd (bih rho x a fits fm evA))) v ev))))

-- λ with convertible domains (same body).
InvConv-Lam-dom : {n : Nat} {G : Ctx n} (A A' : Expr n) (M : Expr (suc n)) (T : Expr n)
  -> (rho : EnvApprox n)
  -> InvTyp G (Lam A M) T rho
  -> ((a : FinEl) -> EvalRel A rho a -> EvalRel A' rho a)
  -> ((a : FinEl) -> EvalRel A' rho a -> EvalRel A rho a)
  -> InvConv G (Lam A M) (Lam A' M) T rho
InvConv-Lam-dom {G = G} A A' M T rho inv fA bA =
  let fwd = Lam-map {A = A} {A' = A'} {M = M} {M' = M} {rho = rho} fA (\ x a fm evA v ev -> ev)
      bwd = Lam-map {A = A'} {A' = A} {M = M} {M' = M} {rho = rho} bA (\ x a fm evA v ev -> ev)
  in mkSigma inv (mkSigma (InvTyp-equiv {G = G} inv bwd fwd) (mkSigma fwd bwd))

------------------------------------------------------------------------
-- Eta
--
--   c  =  λ(A, c↑ v0)   :  Π A B
--
-- (<=) Each edge (k, v) of a graph of the η-expansion is witnessed by
--      some w <= k with c ∋ (w ↦ v), hence c ∋ (k ↦ v); the graph is
--      rebuilt from its edges.
-- (=>) Pass to the typed enlargement g' of a graph of c: its keys lie
--      in the domain a, hence so does the key u of each selection of
--      g', and c ∋ (u ↦ v); then go back down.
------------------------------------------------------------------------

InvConv-eta : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n)) (c : Expr n)
  -> (rho : EnvApprox n) -> Fits G rho
  -> InvTyp G c (Pi A B) rho
  -> InvTyp G (Lam A (App (wkExpr c) (Var fzero))) (Pi A B) rho
  -> InvConv G c (Lam A (App (wkExpr c) (Var fzero))) (Pi A B) rho
InvConv-eta {G = G} A B c rho fits invc invL =
  mkSigma invc (mkSigma invL (mkSigma fwd bwd))
  where
    etaL : Expr _
    etaL = Lam A (App (wkExpr c) (Var fzero))

    crho = Fits-CoherentEnv rho fits

    Body : FinEl -> FinEl -> Set
    Body x v = EvalRel (App (wkExpr c) (Var fzero)) (extendEnv rho x) v

    sing : FinEl -> FinEl -> FinEl
    sing w v = FunEl (cons (mkSigma w v) nil)

    app-edge : (x w vi : FinEl) -> NotBot vi ->
      EvalRel (Var fzero) (extendEnv rho x) w -> EvalRel c rho (sing w vi) -> Body x vi
    app-edge x w Bot          () evw evc
    app-edge x w (UCode l)    nb evw evc =
      mkSigma w (mkSigma evw (EvalRel-wk c rho x (sing w (UCode l)) evc))
    app-edge x w (FunEl g)    nb evw evc =
      mkSigma w (mkSigma evw (EvalRel-wk c rho x (sing w (FunEl g)) evc))
    app-edge x w (PiCode a f) nb evw evc =
      mkSigma w (mkSigma evw (EvalRel-wk c rho x (sing w (PiCode a f)) evc))

    app-dec : (x vi : FinEl) -> NotBot vi -> Body x vi ->
      Sigma FinEl (\ w -> Pair (Pair (Coherent w) (LeCode w x)) (EvalRel c rho (sing w vi)))
    app-dec x Bot          () ev
    app-dec x (UCode l)    nb (mkSigma w (mkSigma evw evc)) =
      mkSigma w (mkSigma evw (EvalRel-unwk c rho x (sing w (UCode l)) evc))
    app-dec x (FunEl g)    nb (mkSigma w (mkSigma evw evc)) =
      mkSigma w (mkSigma evw (EvalRel-unwk c rho x (sing w (FunEl g)) evc))
    app-dec x (PiCode a f) nb (mkSigma w (mkSigma evw evc)) =
      mkSigma w (mkSigma evw (EvalRel-unwk c rho x (sing w (PiCode a f)) evc))

    edge-val : (e : Edge) (h : FinFun) -> CoherentFunTail h -> EdgeIn e h ->
      Pair (Coherent (snd e)) (NotBot (snd e))
    edge-val e (cons q qs) cft here = mkSigma (val-coh cft) (val-nbot cft)
    edge-val e (cons q (cons r rs)) cft (there ein) =
      edge-val e (cons r rs) (tail-coh cft) ein

    -- (=>) at the typed enlargement
    lamG : (g' : FinFun) (a : FinEl) (f : FinFun) ->
      FinMem (FunEl g') (PiCode a f) -> EvalRel (Pi A B) rho (PiCode a f) ->
      EvalRel c rho (FunEl g') -> EvalRel etaL rho (FunEl g')
    lamG g' a f fm evPi evc =
      mkSigma a (mkSigma cfg (mkSigma aU (mkSigma evA body)))
      where
        cfg = finMem-funel-coh g' a f fm
        cft = cft-from-cf g' cfg
        fmf = finMem-funel-fun g' a f fm
        aU  = finMem-piU-dom a f (finMem-funel-wf g' a f fm)
        ca  = coh-from-aU a aU
        evA = fst (snd evPi)

        edge-nb : (u0 vi : FinEl) -> NotBot vi -> Selection g' u0 vi ->
          Coherent u0 -> Coherent vi -> Body u0 vi
        edge-nb u0 vi nb sel cu0 cvi =
          app-edge u0 u0 vi nb (mkSigma cu0 (LeCode-refl u0 cu0))
            (EvalRel-down c rho (FunEl g') (sing u0 vi) crho
              (mkCFT cu0 cvi nb tt tt) evc
              (mkSigma (Selection-le-EvalFun g' sel (LeFunCode-refl g' cft) cft cft cu0) tt))

        edge : (u0 v0 : FinEl) -> Selection g' u0 v0 -> Coherent u0 -> Coherent v0 ->
          Body u0 v0
        edge u0 Bot sel cu0 cv0 = tt
        edge u0 (UCode l) sel cu0 cv0 = edge-nb u0 (UCode l) tt sel cu0 cv0
        edge u0 (FunEl g) sel cu0 cv0 = edge-nb u0 (FunEl g) tt sel cu0 cv0
        edge u0 (PiCode b h) sel cu0 cv0 = edge-nb u0 (PiCode b h) tt sel cu0 cv0

        body : (u0 v0 : FinEl) -> Selection g' u0 v0 ->
          Sigma FinEl (\ x -> Pair (LeCode x u0) (Pair (FinMem x a) (Body x v0)))
        body u0 v0 sel =
          let cu0 = Coherent-Selection sel cft
              cv0 = Coherent-Selection-val sel cft
          in mkSigma u0 (mkSigma (LeCode-refl u0 cu0)
               (mkSigma (FinMem-Selection a f sel fmf cft ca aU) (edge u0 v0 sel cu0 cv0)))

    fwd-main : (u u' pa : FinEl) -> Coherent u -> LeCode u u' ->
      EvalRel c rho u' -> FinMem u' pa -> EvalRel (Pi A B) rho pa -> EvalRel etaL rho u
    fwd-main Bot          u'             pa           cu le evc fm evPi = EvalRel-Bot etaL rho
    fwd-main (FunEl h)    (FunEl g')     (PiCode a f) cu le evc fm evPi =
      EvalRel-down etaL rho (FunEl g') (FunEl h) crho cu (lamG g' a f fm evPi evc) le
    fwd-main (FunEl h)    (FunEl g')     Bot          cu le evc () evPi
    fwd-main (FunEl h)    (FunEl g')     (UCode _)    cu le evc () evPi
    fwd-main (FunEl h)    (FunEl g')     (FunEl _)    cu le evc () evPi
    fwd-main (FunEl h)    Bot            pa           cu () evc fm evPi
    fwd-main (FunEl h)    (UCode _)      pa           cu () evc fm evPi
    fwd-main (FunEl h)    (PiCode _ _)   pa           cu () evc fm evPi
    fwd-main (UCode _)    (UCode _)      Bot          cu le evc () evPi
    fwd-main (UCode _)    (UCode _)      (UCode _)    cu le evc fm ()
    fwd-main (UCode _)    (UCode _)      (FunEl _)    cu le evc () evPi
    fwd-main (UCode _)    (UCode _)      (PiCode _ _) cu le evc () evPi
    fwd-main (UCode _)    Bot            pa           cu () evc fm evPi
    fwd-main (UCode _)    (FunEl _)      pa           cu () evc fm evPi
    fwd-main (UCode _)    (PiCode _ _)   pa           cu () evc fm evPi
    fwd-main (PiCode _ _) (PiCode _ _)   Bot          cu le evc () evPi
    fwd-main (PiCode _ _) (PiCode _ _)   (UCode _)    cu le evc fm ()
    fwd-main (PiCode _ _) (PiCode _ _)   (FunEl _)    cu le evc () evPi
    fwd-main (PiCode _ _) (PiCode _ _)   (PiCode _ _) cu le evc () evPi
    fwd-main (PiCode _ _) Bot            pa           cu () evc fm evPi
    fwd-main (PiCode _ _) (UCode _)      pa           cu () evc fm evPi
    fwd-main (PiCode _ _) (FunEl _)      pa           cu () evc fm evPi

    fwd : (u : FinEl) -> EvalRel c rho u -> EvalRel etaL rho u
    fwd u ev =
      let mkSigma u' (mkSigma pa (mkSigma le (mkSigma evc (mkSigma fm evPi)))) = invc u ev
      in fwd-main u u' pa (EvalRel-coh c rho u ev) le evc fm evPi

    -- (<=) edge by edge
    build-graph : (g : FinFun) -> CoherentFun g ->
      ((p : Edge) -> EdgeIn p g -> EvalRel c rho (FunEl (cons p nil))) ->
      EvalRel c rho (FunEl g)
    build-graph nil () _
    build-graph (cons p nil) _ f = f p here
    build-graph (cons p (cons q qs)) cfg f =
      let evSing = f p here
          evRest = build-graph (cons q qs) (tail-coh cfg) (\ r rin -> f r (there rin))
          sgl  = FunEl (cons p nil)
          rest = FunEl (cons q qs)
          csing = EvalRel-coh c rho sgl evSing
          crest = EvalRel-coh c rho rest evRest
          comp  = EvalRel-Comp c rho crho sgl rest evSing evRest
      in EvalRel-Sup c rho sgl rest crho csing crest comp evSing evRest

    bwd : (u : FinEl) -> EvalRel etaL rho u -> EvalRel c rho u
    bwd Bot          ev = EvalRel-Bot c rho
    bwd (UCode _)    ()
    bwd (PiCode _ _) ()
    bwd (FunEl h) (mkSigma a (mkSigma cfh (mkSigma aU (mkSigma evA body)))) =
      build-graph h cfh edgeC
      where
        cft = cft-from-cf h cfh
        edgeC : (p : Edge) -> EdgeIn p h -> EvalRel c rho (FunEl (cons p nil))
        edgeC p ein =
          let k   = fst p
              v   = snd p
              ck  = CoherentFun-edge-key p h cft ein
              cv  = fst (edge-val p h cft ein)
              nbv = snd (edge-val p h cft ein)
              sel = singleton-selection p h ein
              mkSigma x (mkSigma le-x0 (mkSigma fmx evApp0)) = body _ _ sel
              le-x : LeCode x k
              le-x = Eq-transport (\ z -> LeCode x z) (Sup-Bot-r k) le-x0
              evApp : Body x v
              evApp = Eq-transport (\ z -> Body x z) (Sup-Bot-r v) evApp0
              cx  = FinMem-coh-u x a fmx
              mkSigma w (mkSigma (mkSigma cw le-wx) evcw) = app-dec x v nbv evApp
              le-wk = LeCode-trans w x k cw cx ck le-wx le-x
              cft-wv = mkCFT cw cv nbv tt tt
          in EvalRel-down c rho (sing w v) (FunEl (cons p nil)) crho
               (mkCFT ck cv nbv tt tt) evcw
               (mkSigma (EvalFun-edge-le (mkSigma w v) (cons (mkSigma w v) nil) k
                          cft-wv here ck le-wk) tt)
