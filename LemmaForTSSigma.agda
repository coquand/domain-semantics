{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- LemmaForTSSigma.agda
--
-- Parallel version of LemmaForTS.agda extended with Sigma types.
--
-- Provides:
-- - replaceKeys and related graph manipulation (unchanged)
-- - Lam-L1 (Lam inversion with typed keys) — with SigmaCode/PairCode absurd
-- - Sigma-L1 (Sigma inversion with typed keys) — mirrors Pi-L1
-- - Fits / Typed / InvTyp / InvConv
-- - InvTyp-Lam / InvTyp-Pi / InvTyp-Sigma / InvTyp-MkPair
-- - InvTyp-App / InvTyp-Fst / InvTyp-Snd
-- - InvConv-beta / InvConv-funext / InvConv-App-fun / InvConv-App-arg
-- - InvConv-MkPair-fst / InvConv-MkPair-snd
-- - InvConv-Fst / InvConv-Snd
-- - InvConv-beta-fst / InvConv-beta-snd
-- - InvConv-pair-eta
--
-- 0 postulates.
------------------------------------------------------------------------

module LemmaForTSSigma where

import BasicSigma as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ;
              Pair ; List ; nil ; cons ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; SigmaCode ; PairCode ; FinFun)
open import PaperSemanticsSigma using (LeCode ; LeCode-refl ; LeCode-trans ; LeCode-Bot ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ; cft-from-cf ;
  CoherentWith ;
  NotBot ; FinMem ; FinMemFun ; FinMemAllU ; FinMem-coh-u ; FinMem-a-in-U ; coh-from-aU ;
  finMem-upward ;
  Sup ; Sup-Bot-r ; Sup-Bot-l ;
  Comp ; comp-Bot-r ; comp-Bot-l ; Comp-down ; Comp-sym ;
  Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub ;
  LeCode-Comp ;
  EvalFun ; EvalFun-mon-arg ; Coherent-EvalFun ;
  FinMem-Sup-element ;
  LeFunCode ; LeFunCode-refl ; append ;
  EvalFun-in-UCode ;
  finMemUCode-Sup ; Comp-refl ;
  FinMemAllProp ; EvalFun-in-PropCode ; finMemPropCode-Sup ; FinMem-Prop-to-U ;
  Or ; inl ; inr)
open CFTcons
open import SelectionSigma using (Selection ; Edge ; EdgeIn ; here ; there ;
  sel-nil ; sel-take ; sel-skip ;
  Coherent-Selection ; Coherent-Selection-val ;
  CoherentFun-edge-key ;
  singleton-selection ; Selection-le-EvalFun ; selectionBelow ;
  FinMem-Selection ; FinMem-Selection-codomain)
open import RawSyntaxSigma using (Expr ; Var ; U ; Prop ; Pi ; Lam ; App ;
  MkPair ; Fst ; Snd ;
  Fin ; fzero ; fsuc ; Ren ; liftRen ; renExpr ; wkRen ; wkExpr ; subst1)
open import RawSemanticsSigma
open import TypingRulesSigma using (Ctx ; empty ; extend ; lookup ;
  HasType ; ty-var ; ty-conv ; ty-U ; ty-Pi ; ty-Lam ; ty-App ;
  ty-Sigma ; ty-MkPair ; ty-Fst ; ty-Snd ;
  WfCtx ; wf-empty ; wf-extend ;
  ConvTm ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg ;
  conv-Sigma ; conv-beta-fst ; conv-beta-snd ; conv-pair-eta ;
  conv-MkPair-fst ; conv-MkPair-snd ; conv-Fst ; conv-Snd)
open import EvalSubstitutionSigma using (EvalRel-ren ; EvalRel-wk ; EvalRel-unwk ;
  EvalRel-subst1-backward ; EvalRel-subst1-forward-bounded ;
  EvalRel-subst1-forward)

------------------------------------------------------------------------
-- Helper: replace keys in a graph using a witness function
------------------------------------------------------------------------

replaceKeys : (g : FinFun) ->
  ((p : Edge) -> EdgeIn p g -> FinEl) ->
  FinFun
replaceKeys nil         f = nil
replaceKeys (cons p ps) f =
  cons (mkSigma (f p here) (snd p))
       (replaceKeys ps (\ q ein -> f q (there ein)))

------------------------------------------------------------------------
-- Helper: correspondence between edges of g and replaceKeys g
------------------------------------------------------------------------

replaceKeys-corr : (g : FinFun) ->
  (f : (p : Edge) -> EdgeIn p g -> FinEl) ->
  (q : Edge) -> (ein : EdgeIn q g) ->
  EdgeIn (mkSigma (f q ein) (snd q)) (replaceKeys g f)
replaceKeys-corr (cons p ps) f .p here = here
replaceKeys-corr (cons p ps) f q (there ein) =
  there (replaceKeys-corr ps (\ r rin -> f r (there rin)) q ein)

------------------------------------------------------------------------
-- Helper: edgewise property of the replacement graph
------------------------------------------------------------------------

replaceKeys-edgewise :
  {n : Nat} (M : Expr (suc n)) (rho : EnvApprox n) (a : FinEl)
  (g : FinFun) ->
  (wf : (p : Edge) -> EdgeIn p g ->
    Sigma FinEl (\ x ->
      Pair (LeCode x (fst p))
           (Pair (FinMem x a)
                 (EvalRel M (extendEnv rho x) (snd p))))) ->
  (e : Edge) -> EdgeIn e (replaceKeys g (\ p ein -> fst (wf p ein))) ->
  Pair (FinMem (fst e) a) (EvalRel M (extendEnv rho (fst e)) (snd e))
replaceKeys-edgewise M rho a (cons p ps) wf .(mkSigma (fst (wf p here)) (snd p)) here =
  let w = wf p here
  in mkSigma (fst (snd (snd w))) (snd (snd (snd w)))
replaceKeys-edgewise M rho a (cons p ps) wf e (there ein) =
  replaceKeys-edgewise M rho a ps (\ q qin -> wf q (there qin)) e ein

------------------------------------------------------------------------
-- Helper: CoherentWith for a replacement edge against the rest
------------------------------------------------------------------------

replaceKeys-CoherentWith :
  {n : Nat} (M : Expr (suc n)) (rho : EnvApprox n) (a : FinEl)
  (s : Edge) (rest : FinFun) ->
  CoherentEnv rho ->
  FinMem (fst s) a -> EvalRel M (extendEnv rho (fst s)) (snd s) ->
  (wf : (p : Edge) -> EdgeIn p rest ->
    Sigma FinEl (\ x ->
      Pair (LeCode x (fst p))
           (Pair (FinMem x a)
                 (EvalRel M (extendEnv rho x) (snd p))))) ->
  CoherentWith s (replaceKeys rest (\ p ein -> fst (wf p ein)))
replaceKeys-CoherentWith M rho a s nil crho ms evs wf = tt
replaceKeys-CoherentWith M rho a s (cons t ts) crho ms evs wf =
  let wt   = wf t here
      xt   = fst wt
      mt   = fst (snd (snd wt))
      evt  = snd (snd (snd wt))
      step : Comp (fst s) xt -> Comp (snd s) (snd t)
      step comp-keys =
        let cs  = FinMem-coh-u (fst s) a ms
            ct  = FinMem-coh-u xt a mt
        in EvalRel-Comp-ext M rho (fst s) xt (snd s) (snd t)
             crho comp-keys cs ct evs evt
      tail = replaceKeys-CoherentWith M rho a s ts crho ms evs
               (\ q qin -> wf q (there qin))
  in mkSigma step tail

------------------------------------------------------------------------
-- Helper: CoherentFunTail for replacement graph
------------------------------------------------------------------------

replaceKeys-CoherentFunTail :
  {n : Nat} (M : Expr (suc n)) (rho : EnvApprox n) (a : FinEl)
  (g : FinFun) ->
  CoherentEnv rho ->
  CoherentFunTail g ->
  (wf : (p : Edge) -> EdgeIn p g ->
    Sigma FinEl (\ x ->
      Pair (LeCode x (fst p))
           (Pair (FinMem x a)
                 (EvalRel M (extendEnv rho x) (snd p))))) ->
  CoherentFunTail (replaceKeys g (\ p ein -> fst (wf p ein)))
replaceKeys-CoherentFunTail M rho a nil crho cg wf = tt
replaceKeys-CoherentFunTail M rho a (cons p ps) crho cg wf =
  let wp  = wf p here
      xp  = fst wp
      mp  = fst (snd (snd wp))
      evp = snd (snd (snd wp))
      cxp = FinMem-coh-u xp a mp
      cw = replaceKeys-CoherentWith M rho a (mkSigma xp (snd p)) ps crho mp evp
             (\ q qin -> wf q (there qin))
      tail-cft = replaceKeys-CoherentFunTail M rho a ps crho
                   (tail-coh cg) (\ q qin -> wf q (there qin))
  in mkCFT cxp (val-coh cg) (val-nbot cg) cw tail-cft

------------------------------------------------------------------------
-- Helper: LeFunCode-lookup
------------------------------------------------------------------------

LeFunCode-lookup : (e : Edge) (g h : FinFun) ->
  LeFunCode g h -> EdgeIn e g -> LeCode (snd e) (EvalFun h (fst e))
LeFunCode-lookup e (cons p ps) h lf here = fst lf
LeFunCode-lookup e (cons p ps) h lf (there ein) =
  LeFunCode-lookup e ps h (snd lf) ein

------------------------------------------------------------------------
-- Helper: EvalFun-edge-le
------------------------------------------------------------------------

EvalFun-edge-le : (e : Edge) (g : FinFun) (u : FinEl) ->
  CoherentFunTail g -> EdgeIn e g -> Coherent u -> LeCode (fst e) u ->
  LeCode (snd e) (EvalFun g u)
EvalFun-edge-le e (cons p ps) u cg ein cu le =
  let cfg  = cg
      ck   = CoherentFun-edge-key e (cons p ps) cfg ein
      cv   = fst (cft-edge-val e (cons p ps) cg ein)
      lr   = LeFunCode-refl (cons p ps) cg
      le-k = LeFunCode-lookup e (cons p ps) (cons p ps) lr ein
      cef  = Coherent-EvalFun (cons p ps) (fst e) (cft-from-cf (cons p ps) cfg) ck
      cefu = Coherent-EvalFun (cons p ps) u (cft-from-cf (cons p ps) cfg) cu
      mon  = EvalFun-mon-arg (cons p ps) (fst e) u le cg ck cu
  in LeCode-trans (snd e) (EvalFun (cons p ps) (fst e)) (EvalFun (cons p ps) u) cv cef cefu le-k mon
  where
    cft-edge-val : (e : Edge) (g : FinFun) ->
      CoherentFunTail g -> EdgeIn e g ->
      Pair (Coherent (snd e)) (NotBot (snd e))
    cft-edge-val e (cons p ps) cg here = mkSigma (val-coh cg) (val-nbot cg)
    cft-edge-val e (cons p nil) cg (there ())
    cft-edge-val e (cons p (cons q qs)) cg (there ein) =
      cft-edge-val e (cons q qs) (tail-coh cg) ein

------------------------------------------------------------------------
-- Helper: LeFunCode from old graph to replacement graph
------------------------------------------------------------------------

replaceKeys-LeFunCode :
  {n : Nat} (M : Expr (suc n)) (rho : EnvApprox n) (a : FinEl)
  (g : FinFun) ->
  CoherentEnv rho ->
  CoherentFunTail g ->
  (wf : (p : Edge) -> EdgeIn p g ->
    Sigma FinEl (\ x ->
      Pair (LeCode x (fst p))
           (Pair (FinMem x a)
                 (EvalRel M (extendEnv rho x) (snd p))))) ->
  let g' = replaceKeys g (\ p ein -> fst (wf p ein))
  in LeFunCode g g'
replaceKeys-LeFunCode M rho a nil crho cg wf = tt
replaceKeys-LeFunCode M rho a (cons p ps) crho cg wf =
  let g'   = replaceKeys (cons p ps) (\ q ein -> fst (wf q ein))
      cft' = replaceKeys-CoherentFunTail M rho a (cons p ps) crho cg wf
      wp   = wf p here
      xp   = fst wp
      le-x = fst (snd wp)
      ck-p = key-coh cg
      head-le = EvalFun-edge-le (mkSigma xp (snd p)) g' (fst p)
                  cft' here ck-p le-x
      tail-le = replaceKeys-LeFunCode-tail ps (cons p ps) cg wf
                  (\ q qin -> there qin)
                  (\ q qin -> replaceKeys-corr (cons p ps) (\ r rin -> fst (wf r rin)) q (there qin))
  in mkSigma head-le tail-le
  where
    cft-edge : {g : FinFun} -> CoherentFunTail g -> {e : Edge} ->
      EdgeIn e g -> CoherentFunTail (cons e nil)
    cft-edge {cons p ps} cg here =
      mkCFT (key-coh cg) (val-coh cg) (val-nbot cg) tt tt
    cft-edge {cons p nil} cg (there ())
    cft-edge {cons p (cons q qs)} cg (there ein) =
      cft-edge (tail-coh cg) ein

    replaceKeys-LeFunCode-tail :
      (ps orig : FinFun) ->
      CoherentFunTail orig ->
      (wf : (p : Edge) -> EdgeIn p orig ->
        Sigma FinEl (\ x ->
          Pair (LeCode x (fst p))
               (Pair (FinMem x a)
                     (EvalRel M (extendEnv rho x) (snd p))))) ->
      let g' = replaceKeys orig (\ q ein -> fst (wf q ein))
          cft' = replaceKeys-CoherentFunTail M rho a orig crho
      in  (ein-shift : (q : Edge) -> EdgeIn q ps ->
             EdgeIn q orig) ->
          ((q : Edge) (ein : EdgeIn q ps) ->
             EdgeIn (mkSigma (fst (wf q (ein-shift q ein))) (snd q)) g') ->
          LeFunCode ps g'
    replaceKeys-LeFunCode-tail nil orig cg wf shift corr = tt
    replaceKeys-LeFunCode-tail (cons q qs) orig cg wf shift corr =
      let wq    = wf q (shift q here)
          xq    = fst wq
          le-xq = fst (snd wq)
          cft'  = replaceKeys-CoherentFunTail M rho a orig crho cg wf
          ck-q  = key-coh (cft-edge cg (shift q here))
          head  = EvalFun-edge-le
                    (mkSigma xq (snd q))
                    (replaceKeys orig (\ r rin -> fst (wf r rin)))
                    (fst q)
                    cft' (corr q here) ck-q le-xq
          tail  = replaceKeys-LeFunCode-tail qs orig cg wf
                    (\ r rin -> shift r (there rin))
                    (\ r rin -> corr r (there rin))
      in mkSigma head tail

------------------------------------------------------------------------
-- Helper: Selection body for replacement graph
------------------------------------------------------------------------

replaceKeys-selection-body :
  {n : Nat} (M : Expr (suc n)) (rho : EnvApprox n) (a : FinEl)
  (g' : FinFun) (u v : FinEl) ->
  CoherentEnv rho -> FinMem a UCode ->
  CoherentFunTail g' ->
  ((e : Edge) -> EdgeIn e g' ->
    Pair (FinMem (fst e) a) (EvalRel M (extendEnv rho (fst e)) (snd e))) ->
  Selection g' u v ->
  Sigma FinEl (\ x ->
    Pair (LeCode x u)
         (Pair (FinMem x a)
               (EvalRel M (extendEnv rho x) v)))
-- sel-nil
replaceKeys-selection-body M rho a g' .Bot .Bot crho aU cg' ew sel-nil =
  mkSigma Bot (mkSigma tt (mkSigma aU (EvalRel-Bot M (extendEnv rho Bot))))
-- sel-skip
replaceKeys-selection-body M rho a (cons p g') u v crho aU cg' ew (sel-skip sel) =
  replaceKeys-selection-body M rho a g' u v crho aU
    (cft-tail g' cg') (\ e ein -> ew e (there ein)) sel
  where
    cft-tail : (g : FinFun) -> CoherentFunTail (cons p g) -> CoherentFunTail g
    cft-tail nil cft = tt
    cft-tail (cons q qs) cft = tail-coh cft
-- sel-take
replaceKeys-selection-body M rho a (cons p g') .(Sup (fst p) u') .(Sup (snd p) v')
    crho aU cg' ew (sel-take {.p} {u'} {v'} comp-k comp-v sel) =
  let -- IH
      cft-g' = cft-tail g' cg'
      ih   = replaceKeys-selection-body M rho a g' u' v' crho aU
               cft-g' (\ e ein -> ew e (there ein)) sel
      x'   = fst ih
      le-x'  = fst (snd ih)
      mem-x' = fst (snd (snd ih))
      ev-x'  = snd (snd (snd ih))
      -- Edge p data
      ep   = ew p here
      mem-p = fst ep
      ev-p  = snd ep
      -- Coherences
      cp   = FinMem-coh-u (fst p) a mem-p
      cx'  = FinMem-coh-u x' a mem-x'
      ca   = coh-from-aU a aU
      -- Comp (fst p) x'
      comp-u'-p = Comp-sym (fst p) u' comp-k
      comp-x'-p = Comp-down x' u' (fst p) le-x' comp-u'-p
      comp-p-x' = Comp-sym x' (fst p) comp-x'-p
      -- FinMem (Sup (fst p) x') a
      mem-sup = FinMem-Sup-element (fst p) x' a comp-p-x' ca mem-p mem-x'
      -- EvalRel M (rho, Sup (fst p) x') (Sup (snd p) v')
      ev-sup = EvalRel-ideal-Comp M rho (fst p) x' (snd p) v'
                 crho comp-p-x' cp cx' ev-p ev-x'
      -- LeCode (Sup (fst p) x') (Sup (fst p) u')
      cu'    = coh-sel-key g' (\ e ein -> ew e (there ein)) sel
      le-p-sup = LeCode-Sup-left (fst p) u' comp-k cp cu'
      le-x'-u' = LeCode-Sup-right (fst p) u' comp-k cp cu'
      csup   = Coherent-Sup (fst p) u' comp-k cp cu'
      le-x'-sup = LeCode-trans x' u' (Sup (fst p) u') cx' cu' csup le-x' le-x'-u'
      le-result = LeCode-Sup-lub (fst p) x' (Sup (fst p) u') le-p-sup le-x'-sup
  in mkSigma (Sup (fst p) x') (mkSigma le-result (mkSigma mem-sup ev-sup))
  where
    cft-tail : (g : FinFun) -> CoherentFunTail (cons p g) -> CoherentFunTail g
    cft-tail nil cft = tt
    cft-tail (cons q qs) cft = tail-coh cft

    coh-sel-key : (h : FinFun) ->
      ((e : Edge) -> EdgeIn e h ->
        Pair (FinMem (fst e) a) (EvalRel M (extendEnv rho (fst e)) (snd e))) ->
      {u' v' : FinEl} -> Selection h u' v' -> Coherent u'
    coh-sel-key h ew sel-nil = tt
    coh-sel-key (cons q qs) ew (sel-skip sel) =
      coh-sel-key qs (\ e ein -> ew e (there ein)) sel
    coh-sel-key (cons q qs) ew (sel-take {.q} {u0} {v0} ck cv sel) =
      let cq = FinMem-coh-u (fst q) a (fst (ew q here))
          cu0 = coh-sel-key qs (\ e ein -> ew e (there ein)) sel
      in Coherent-Sup (fst q) u0 ck cq cu0

------------------------------------------------------------------------
-- Lam-L1: Lam inversion with typed keys
------------------------------------------------------------------------

Lam-L1 : {n : Nat} (A : Expr n) (M : Expr (suc n))
  (rho : EnvApprox n) (u : FinEl) ->
  NotBot u ->
  CoherentEnv rho ->
  EvalRel (Lam A M) rho u ->
  Sigma FinEl (\ a ->
    Sigma FinFun (\ g' ->
      Pair (EvalRel A rho a)
        (Pair (FinMem a UCode)
          (Pair (LeCode u (FunEl g'))
            (Pair (EvalRel (Lam A M) rho (FunEl g'))
              ((p : Edge) -> EdgeIn p g' ->
                Pair (FinMem (fst p) a)
                     (EvalRel M (extendEnv rho (fst p)) (snd p))))))))
Lam-L1 A M rho UCode            nb crho ()
Lam-L1 A M rho PropCode         nb crho ()
Lam-L1 A M rho (PiCode a f)     nb crho ()
Lam-L1 A M rho (SigmaCode a f)  nb crho ()
Lam-L1 A M rho (PairCode u v)   nb crho ()
Lam-L1 A M rho (FunEl g)        nb crho ev =
  Lam-L1-aux A M rho g nb crho ev
  where
    Lam-L1-aux : {n : Nat} (A : Expr n) (M : Expr (suc n))
      (rho : EnvApprox n) (g : FinFun) ->
      NotBot (FunEl g) ->
      CoherentEnv rho ->
      EvalRel (Lam A M) rho (FunEl g) ->
      Sigma FinEl (\ a ->
        Sigma FinFun (\ g' ->
          Pair (EvalRel A rho a)
            (Pair (FinMem a UCode)
              (Pair (LeCode (FunEl g) (FunEl g'))
                (Pair (EvalRel (Lam A M) rho (FunEl g'))
                  ((p : Edge) -> EdgeIn p g' ->
                    Pair (FinMem (fst p) a)
                         (EvalRel M (extendEnv rho (fst p)) (snd p))))))))
    Lam-L1-aux A M rho (cons p0 ps0) nb crho ev =
      let g    = cons p0 ps0
          ew   = Lam-edgewise A M rho g ev
          a    = fst ew
          cg   = fst (snd ew)
          aU   = fst (snd (snd ew))
          evA  = fst (snd (snd (snd ew)))
          wf   = snd (snd (snd (snd ew)))
          g'   = replaceKeys g (\ p ein -> fst (wf p ein))
          cg'  = replaceKeys-CoherentFunTail M rho a g crho (cft-from-cf g cg) wf
          ew'  = replaceKeys-edgewise M rho a g wf
          lf   = replaceKeys-LeFunCode M rho a g crho (cft-from-cf g cg) wf
          selbody : (u' v' : FinEl) -> Selection g' u' v' ->
            Sigma FinEl (\ x ->
              Pair (LeCode x u')
                   (Pair (FinMem x a)
                         (EvalRel M (extendEnv rho x) v')))
          selbody u' v' sel =
            replaceKeys-selection-body M rho a g' u' v' crho aU cg' ew' sel
          evLam : EvalRel (Lam A M) rho (FunEl g')
          evLam = mkSigma a (mkSigma cg' (mkSigma aU (mkSigma evA selbody)))
      in mkSigma a (mkSigma g' (mkSigma evA (mkSigma aU (mkSigma lf (mkSigma evLam ew')))))

------------------------------------------------------------------------
-- Helper: replace values in a graph using a witness function
------------------------------------------------------------------------

replaceVals : (g : FinFun) ->
  ((p : Edge) -> EdgeIn p g -> FinEl) ->
  FinFun
replaceVals nil         f = nil
replaceVals (cons p ps) f =
  cons (mkSigma (fst p) (f p here))
       (replaceVals ps (\ q ein -> f q (there ein)))

replaceVals-corr : (g : FinFun) ->
  (f : (p : Edge) -> EdgeIn p g -> FinEl) ->
  (q : Edge) -> (ein : EdgeIn q g) ->
  EdgeIn (mkSigma (fst q) (f q ein)) (replaceVals g f)
replaceVals-corr (cons p ps) f .p here = here
replaceVals-corr (cons p ps) f q (there ein) =
  there (replaceVals-corr ps (\ r rin -> f r (there rin)) q ein)

------------------------------------------------------------------------
-- Helper: map both keys and values in a graph
------------------------------------------------------------------------

mapEdges : (g : FinFun) ->
  ((p : Edge) -> EdgeIn p g -> Edge) ->
  FinFun
mapEdges nil         f = nil
mapEdges (cons p ps) f =
  cons (f p here)
       (mapEdges ps (\ q ein -> f q (there ein)))

mapEdges-corr : (g : FinFun) ->
  (f : (p : Edge) -> EdgeIn p g -> Edge) ->
  (q : Edge) -> (ein : EdgeIn q g) ->
  EdgeIn (f q ein) (mapEdges g f)
mapEdges-corr (cons p ps) f .p here = here
mapEdges-corr (cons p ps) f q (there ein) =
  there (mapEdges-corr ps (\ r rin -> f r (there rin)) q ein)

------------------------------------------------------------------------
-- Helper: NotBot is preserved upward
------------------------------------------------------------------------

NotBot-from-Le : (u v : FinEl) -> Coherent u -> NotBot u ->
  LeCode u v -> NotBot v
NotBot-from-Le u Bot cu nbu le =
  Coherent-val-LeBot-absurd u (mkSigma cu nbu) le
NotBot-from-Le u UCode cu nbu le = tt
NotBot-from-Le u PropCode cu nbu le = tt
NotBot-from-Le u (FunEl g) cu nbu le = tt
NotBot-from-Le u (PiCode a f) cu nbu le = tt
NotBot-from-Le u (SigmaCode a f) cu nbu le = tt
NotBot-from-Le u (PairCode a b) cu nbu le = tt

NotBot-from-FinMem : (u a : FinEl) -> NotBot u -> FinMem u a -> NotBot a
NotBot-from-FinMem Bot a () fm
NotBot-from-FinMem UCode Bot nbu ()
NotBot-from-FinMem UCode UCode nbu fm = tt
NotBot-from-FinMem UCode PropCode nbu ()
NotBot-from-FinMem UCode (FunEl g) nbu ()
NotBot-from-FinMem UCode (PiCode a f) nbu ()
NotBot-from-FinMem UCode (SigmaCode a f) nbu ()
NotBot-from-FinMem UCode (PairCode u v) nbu ()
NotBot-from-FinMem PropCode UCode nbu fm = tt
NotBot-from-FinMem PropCode Bot nbu ()
NotBot-from-FinMem PropCode PropCode nbu ()
NotBot-from-FinMem PropCode (FunEl g) nbu ()
NotBot-from-FinMem PropCode (PiCode a f) nbu ()
NotBot-from-FinMem PropCode (SigmaCode a f) nbu ()
NotBot-from-FinMem PropCode (PairCode u v) nbu ()
NotBot-from-FinMem (FunEl g) Bot nbu ()
NotBot-from-FinMem (FunEl g) (PiCode a f) nbu fm = tt
NotBot-from-FinMem (FunEl g) PropCode nbu ()
NotBot-from-FinMem (FunEl g) UCode nbu ()
NotBot-from-FinMem (FunEl g) (FunEl h) nbu ()
NotBot-from-FinMem (FunEl g) (SigmaCode a f) nbu ()
NotBot-from-FinMem (FunEl g) (PairCode u v) nbu ()
NotBot-from-FinMem (PiCode a f) Bot nbu ()
NotBot-from-FinMem (PiCode a f) UCode nbu fm = tt
NotBot-from-FinMem (PiCode a f) PropCode nbu fm = tt
NotBot-from-FinMem (PiCode a f) (PiCode c h) nbu ()
NotBot-from-FinMem (PiCode a f) (FunEl h) nbu ()
NotBot-from-FinMem (PiCode a f) (SigmaCode c h) nbu ()
NotBot-from-FinMem (PiCode a f) (PairCode u v) nbu ()
NotBot-from-FinMem (SigmaCode a f) Bot nbu ()
NotBot-from-FinMem (SigmaCode a f) UCode nbu fm = tt
NotBot-from-FinMem (SigmaCode a f) PropCode nbu ()
NotBot-from-FinMem (SigmaCode a f) (FunEl h) nbu ()
NotBot-from-FinMem (SigmaCode a f) (PiCode c h) nbu ()
NotBot-from-FinMem (SigmaCode a f) (SigmaCode c h) nbu ()
NotBot-from-FinMem (SigmaCode a f) (PairCode u v) nbu ()
NotBot-from-FinMem (PairCode u v) Bot nbu ()
NotBot-from-FinMem (PairCode u v) UCode nbu ()
NotBot-from-FinMem (PairCode u v) PropCode nbu ()
NotBot-from-FinMem (PairCode u v) (FunEl h) nbu ()
NotBot-from-FinMem (PairCode u v) (PiCode c h) nbu ()
NotBot-from-FinMem (PairCode u v) (SigmaCode a f) nbu fm = tt
NotBot-from-FinMem (PairCode u v) (PairCode u2 v2) nbu ()

------------------------------------------------------------------------
-- Part 1: Fits — well-typed finite environments
------------------------------------------------------------------------

Fits : {n : Nat} -> Ctx n -> EnvApprox n -> Set
Fits empty emptyEnv = Top
Fits (extend G A) (extendEnv rho u) =
  Pair (Fits G rho)
       (Sigma FinEl (\ a' -> Pair (FinMem u a') (EvalRel A rho a')))

Fits-tail : {n : Nat} {G : Ctx n} {A : Expr n} {rho : EnvApprox n} {u : FinEl} ->
  Fits (extend G A) (extendEnv rho u) -> Fits G rho
Fits-tail (mkSigma fits_G _) = fits_G

Fits-CoherentEnv : {n : Nat} {G : Ctx n} (rho : EnvApprox n) ->
  Fits G rho -> CoherentEnv rho
Fits-CoherentEnv {zero} {empty} emptyEnv fits = tt
Fits-CoherentEnv {suc n} {extend G A} (extendEnv rho v)
  (mkSigma fits_G (mkSigma a' (mkSigma fm _))) =
  mkSigma (Fits-CoherentEnv rho fits_G) (FinMem-coh-u v a' fm)

Fits-var : {n : Nat} {G : Ctx n} (rho : EnvApprox n) ->
  Fits G rho -> (i : Fin n) ->
  Sigma FinEl (\ a' ->
    Pair (FinMem (lookupEnv i rho) a') (EvalRel (lookup G i) rho a'))
Fits-var {suc n} {extend G A} (extendEnv rho v)
  (mkSigma fits_G (mkSigma a' (mkSigma fm evA))) fzero =
  mkSigma a' (mkSigma fm (EvalRel-wk A rho v a' evA))
Fits-var {suc n} {extend G A} (extendEnv rho v)
  (mkSigma fits_G _) (fsuc i) =
  let ih = Fits-var rho fits_G i
      a' = fst ih
      fm = fst (snd ih)
      evLk = snd (snd ih)
  in mkSigma a' (mkSigma fm (EvalRel-wk (lookup G i) rho v a' evLk))

------------------------------------------------------------------------
-- Part 2: Named invariants
------------------------------------------------------------------------

Typed : {n : Nat} -> Expr n -> Expr n -> EnvApprox n -> FinEl -> Set
Typed {n} M A rho u =
  Sigma FinEl (\ u' -> Sigma FinEl (\ a' ->
    Pair (LeCode u u') (Pair (EvalRel M rho u') (Pair (FinMem u' a') (EvalRel A rho a')))))

InvTyp : {n : Nat} -> Ctx n -> Expr n -> Expr n -> EnvApprox n -> Set
InvTyp G M A rho =
  (u : FinEl) -> EvalRel M rho u -> Typed M A rho u

InvConv : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
  EnvApprox n -> Set
InvConv G M N A rho =
  Pair (InvTyp G M A rho)
  (Pair (InvTyp G N A rho)
  (Pair ((u : FinEl) -> EvalRel M rho u -> EvalRel N rho u)
        ((u : FinEl) -> EvalRel N rho u -> EvalRel M rho u)))

------------------------------------------------------------------------
-- InvTyp-Lam
------------------------------------------------------------------------

InvTyp-Lam : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M : Expr (suc n)) ->
  ((rho : EnvApprox n) (x a : FinEl) ->
    Fits G rho -> FinMem x a -> EvalRel A rho a ->
    InvTyp (extend G A) M B (extendEnv rho x)) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G (Lam A M) (Pi A B) rho
InvTyp-Lam A B M body-ih rho fits Bot ev =
  mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt))))
InvTyp-Lam A B M body-ih rho fits UCode ()
InvTyp-Lam A B M body-ih rho fits PropCode ()
InvTyp-Lam A B M body-ih rho fits (PiCode a0 f0) ()
InvTyp-Lam A B M body-ih rho fits (SigmaCode a0 f0) ()
InvTyp-Lam A B M body-ih rho fits (PairCode u0 v0) ()
InvTyp-Lam A B M body-ih rho fits (FunEl g) ev =
  let crho = Fits-CoherentEnv rho fits
      l1   = Lam-L1 A M rho (FunEl g) tt crho ev
      ac   = fst l1
      g'   = fst (snd l1)
      evA  = fst (snd (snd l1))
      aU   = fst (snd (snd (snd l1)))
      le-u = fst (snd (snd (snd (snd l1))))
      evLam-g' = fst (snd (snd (snd (snd (snd l1)))))
      ew'  = snd (snd (snd (snd (snd (snd l1)))))
      cg'  = fst (snd evLam-g')
      wf : (p : Edge) -> EdgeIn p g' ->
        Sigma FinEl (\ yi -> Sigma FinEl (\ bi ->
          Pair (LeCode (snd p) yi)
            (Pair (EvalRel M (extendEnv rho (fst p)) yi)
              (Pair (FinMem yi bi) (EvalRel B (extendEnv rho (fst p)) bi)))))
      wf p ein =
        let ep = ew' p ein
            inv = body-ih rho (fst p) ac fits (fst ep) evA (snd p) (snd ep)
        in mkSigma (fst inv) (mkSigma (fst (snd inv))
             (mkSigma (fst (snd (snd inv)))
               (mkSigma (fst (snd (snd (snd inv))))
                 (mkSigma (fst (snd (snd (snd (snd inv)))))
                          (snd (snd (snd (snd (snd inv)))))))))
      yi-of = \ (p : Edge) (ein : EdgeIn p g') -> fst (wf p ein)
      bi-of = \ (p : Edge) (ein : EdgeIn p g') -> fst (snd (wf p ein))
      h  = replaceVals g' yi-of
      f  = replaceVals g' bi-of
      cft-h = rv-cft M g' crho (cft-from-cf g' cg') wf
      cft-f = rv-cft-f g' crho (cft-from-cf g' cg') wf
      cf-h  = rv-cf g' cg' yi-of cft-h
      cf-f  = rv-cf g' cg' bi-of cft-f
      ew-h : (e : Edge) -> EdgeIn e h ->
        Pair (FinMem (fst e) ac) (EvalRel M (extendEnv rho (fst e)) (snd e))
      ew-h = rv-ew M ac g' ew' wf
      ew-f : (e : Edge) -> EdgeIn e f ->
        Pair (FinMem (fst e) ac) (EvalRel B (extendEnv rho (fst e)) (snd e))
      ew-f = rv-ew-f ac g' ew' wf
      lf-g'-h = rv-lf g' (cft-from-cf g' cg') wf cft-h
      cu   = EvalRel-coh (Lam A M) rho (FunEl g) ev
      cu-g' = EvalRel-coh (Lam A M) rho (FunEl g') evLam-g'
      cu-h  = rv-cf g' cg' yi-of cft-h
      le-u-h = LeCode-trans (FunEl g) (FunEl g') (FunEl h) cu cu-g' cu-h le-u lf-g'-h
      selbody-h : (u' v' : FinEl) -> Selection h u' v' ->
        Sigma FinEl (\ x -> Pair (LeCode x u')
          (Pair (FinMem x ac) (EvalRel M (extendEnv rho x) v')))
      selbody-h u' v' sel =
        replaceKeys-selection-body M rho ac h u' v' crho aU cft-h ew-h sel
      selbody-f : (u' v' : FinEl) -> Selection f u' v' ->
        Sigma FinEl (\ x -> Pair (LeCode x u')
          (Pair (FinMem x ac) (EvalRel B (extendEnv rho x) v')))
      selbody-f u' v' sel =
        replaceKeys-selection-body B rho ac f u' v' crho aU cft-f ew-f sel
      evLam-h = mkSigma ac (mkSigma cf-h (mkSigma aU (mkSigma evA selbody-h)))
      ca = coh-from-aU ac aU
      evPi = mkSigma (mkSigma ca cft-f)
               (mkSigma evA (mkSigma ac (mkSigma evA selbody-f)))
      fmAllU = rv-fmAllU ac g' ew' wf
      fm-pi-U : FinMem (PiCode ac f) UCode
      fm-pi-U = mkSigma aU (mkSigma fmAllU cft-f)
      fmFun  = rv-fmFun ac g' ew' wf f cft-f fmAllU
                  (\ p ein -> replaceVals-corr g' (\ q qin -> fst (snd (wf q qin))) p ein)
      fm-h-pi = mkSigma fmFun (mkSigma cf-h fm-pi-U)
  in mkSigma (FunEl h) (mkSigma (PiCode ac f)
       (mkSigma le-u-h (mkSigma evLam-h (mkSigma fm-h-pi evPi))))
  where
    WF : Expr (suc _) -> FinFun -> Set
    WF E g = (p : Edge) -> EdgeIn p g ->
      Sigma FinEl (\ yi -> Sigma FinEl (\ bi ->
        Pair (LeCode (snd p) yi)
          (Pair (EvalRel E (extendEnv rho (fst p)) yi)
            (Pair (FinMem yi bi) (EvalRel B (extendEnv rho (fst p)) bi)))))

    rv-cf : (g : FinFun) -> CoherentFun g ->
      (f : (p : Edge) -> EdgeIn p g -> FinEl) ->
      CoherentFunTail (replaceVals g f) ->
      CoherentFun (replaceVals g f)
    rv-cf (cons p ps) _ f cft = cft

    cft-edge : {g : FinFun} -> CoherentFunTail g -> {e : Edge} ->
      EdgeIn e g -> CoherentFunTail (cons e nil)
    cft-edge {cons p ps} cg here = mkCFT (key-coh cg) (val-coh cg) (val-nbot cg) tt tt
    cft-edge {cons p nil} cg (there ())
    cft-edge {cons p (cons q qs)} cg (there ein) =
      cft-edge (tail-coh cg) ein

    rv-cw : (E : Expr (suc _)) ->
      (sk sv : FinEl) -> (rest : FinFun) ->
      CoherentEnv rho -> Coherent sk -> CoherentFunTail rest ->
      EvalRel E (extendEnv rho sk) sv ->
      (wf0 : (q : Edge) -> EdgeIn q rest ->
        Sigma FinEl (\ yi -> Sigma FinEl (\ bi ->
          Pair (LeCode (snd q) yi)
            (Pair (EvalRel E (extendEnv rho (fst q)) yi)
              (Pair (FinMem yi bi) (EvalRel B (extendEnv rho (fst q)) bi)))))) ->
      CoherentWith (mkSigma sk sv)
                   (replaceVals rest (\ q ein -> fst (wf0 q ein)))
    rv-cw E sk sv nil crho0 csk crest evs wf0 = tt
    rv-cw E sk sv (cons t ts) crho0 csk crest evs wf0 =
      let wt = wf0 t here
          yt = fst wt
          evE-yt = fst (snd (snd (snd wt)))
          ct = key-coh crest
          step : Comp sk (fst t) -> Comp sv yt
          step ck = EvalRel-Comp-ext E rho sk (fst t) sv yt
                      crho0 ck csk ct evs evE-yt
          tail = rv-cw E sk sv ts crho0 csk (tail-coh crest) evs
                   (\ q qin -> wf0 q (there qin))
      in mkSigma step tail

    rv-cft : (E : Expr (suc _)) ->
      (g : FinFun) -> CoherentEnv rho -> CoherentFunTail g ->
      (wf0 : (p : Edge) -> EdgeIn p g ->
        Sigma FinEl (\ yi -> Sigma FinEl (\ bi ->
          Pair (LeCode (snd p) yi)
            (Pair (EvalRel E (extendEnv rho (fst p)) yi)
              (Pair (FinMem yi bi) (EvalRel B (extendEnv rho (fst p)) bi)))))) ->
      CoherentFunTail (replaceVals g (\ p ein -> fst (wf0 p ein)))
    rv-cft E nil crho0 cg wf0 = tt
    rv-cft E (cons p ps) crho0 cg wf0 =
      let wp  = wf0 p here
          yp  = fst wp ; bp = fst (snd wp)
          le-vp = fst (snd (snd wp))
          evE-yp = fst (snd (snd (snd wp)))
          fm-yp = fst (snd (snd (snd (snd wp))))
          ck  = key-coh cg
          cv  = val-coh cg
          nb  = val-nbot cg
          cyp = FinMem-coh-u yp bp fm-yp
          nbyp = NotBot-from-Le (snd p) yp cv nb le-vp
          cw  = rv-cw E (fst p) yp ps crho0 ck (tail-coh cg) evE-yp
                  (\ q qin -> wf0 q (there qin))
          tail = rv-cft E ps crho0 (tail-coh cg)
                   (\ q qin -> wf0 q (there qin))
      in mkCFT ck cyp nbyp cw tail

    rv-ew : (E : Expr (suc _)) -> (a0 : FinEl) ->
      (g : FinFun) ->
      ((p : Edge) -> EdgeIn p g ->
        Pair (FinMem (fst p) a0) (EvalRel E (extendEnv rho (fst p)) (snd p))) ->
      (wf0 : (p : Edge) -> EdgeIn p g ->
        Sigma FinEl (\ yi -> Sigma FinEl (\ bi ->
          Pair (LeCode (snd p) yi)
            (Pair (EvalRel E (extendEnv rho (fst p)) yi)
              (Pair (FinMem yi bi) (EvalRel B (extendEnv rho (fst p)) bi)))))) ->
      (e : Edge) -> EdgeIn e (replaceVals g (\ p ein -> fst (wf0 p ein))) ->
      Pair (FinMem (fst e) a0) (EvalRel E (extendEnv rho (fst e)) (snd e))
    rv-ew E a0 (cons p ps) ew0 wf0 .(mkSigma (fst p) (fst (wf0 p here))) here =
      mkSigma (fst (ew0 p here)) (fst (snd (snd (snd (wf0 p here)))))
    rv-ew E a0 (cons p ps) ew0 wf0 e (there ein) =
      rv-ew E a0 ps (\ q qin -> ew0 q (there qin))
        (\ q qin -> wf0 q (there qin)) e ein

    rv-ew-f : (a0 : FinEl) -> (g : FinFun) ->
      ((p : Edge) -> EdgeIn p g ->
        Pair (FinMem (fst p) a0) (EvalRel M (extendEnv rho (fst p)) (snd p))) ->
      (wf0 : WF M g) ->
      (e : Edge) -> EdgeIn e (replaceVals g (\ p ein -> fst (snd (wf0 p ein)))) ->
      Pair (FinMem (fst e) a0) (EvalRel B (extendEnv rho (fst e)) (snd e))
    rv-ew-f a0 (cons p ps) ew0 wf0 .(mkSigma (fst p) (fst (snd (wf0 p here)))) here =
      mkSigma (fst (ew0 p here)) (snd (snd (snd (snd (snd (wf0 p here))))))
    rv-ew-f a0 (cons p ps) ew0 wf0 e (there ein) =
      rv-ew-f a0 ps (\ q qin -> ew0 q (there qin))
        (\ q qin -> wf0 q (there qin)) e ein

    rv-cw-f : (sk : FinEl) (bk : FinEl) -> (rest : FinFun) ->
      CoherentEnv rho -> Coherent sk -> CoherentFunTail rest ->
      EvalRel B (extendEnv rho sk) bk ->
      (wf0 : (q : Edge) -> EdgeIn q rest ->
        Sigma FinEl (\ yi -> Sigma FinEl (\ bi ->
          Pair (LeCode (snd q) yi)
            (Pair (EvalRel M (extendEnv rho (fst q)) yi)
              (Pair (FinMem yi bi) (EvalRel B (extendEnv rho (fst q)) bi)))))) ->
      CoherentWith (mkSigma sk bk)
                   (replaceVals rest (\ q ein -> fst (snd (wf0 q ein))))
    rv-cw-f sk bk nil crho0 csk crest evs wf0 = tt
    rv-cw-f sk bk (cons t ts) crho0 csk crest evs wf0 =
      let wt = wf0 t here
          bt = fst (snd wt)
          evB-bt = snd (snd (snd (snd (snd wt))))
          ct = key-coh crest
          step : Comp sk (fst t) -> Comp bk bt
          step ck = EvalRel-Comp-ext B rho sk (fst t) bk bt
                      crho0 ck csk ct evs evB-bt
          tail = rv-cw-f sk bk ts crho0 csk (tail-coh crest) evs
                   (\ q qin -> wf0 q (there qin))
      in mkSigma step tail

    rv-cft-f : (g : FinFun) -> CoherentEnv rho -> CoherentFunTail g ->
      (wf0 : WF M g) ->
      CoherentFunTail (replaceVals g (\ p ein -> fst (snd (wf0 p ein))))
    rv-cft-f nil crho0 cg wf0 = tt
    rv-cft-f (cons p ps) crho0 cg wf0 =
      let wp  = wf0 p here
          yp  = fst wp ; bp = fst (snd wp)
          le-vp = fst (snd (snd wp))
          fm-yp = fst (snd (snd (snd (snd wp))))
          evB-bp = snd (snd (snd (snd (snd wp))))
          ck  = key-coh cg
          cv  = val-coh cg
          nb  = val-nbot cg
          cbp = EvalRel-coh B (extendEnv rho (fst p)) bp evB-bp
          nbyp = NotBot-from-Le (snd p) yp cv nb le-vp
          nbbp = NotBot-from-FinMem yp bp nbyp fm-yp
          cw  = rv-cw-f (fst p) bp ps crho0 ck (tail-coh cg) evB-bp
                  (\ q qin -> wf0 q (there qin))
          tail = rv-cft-f ps crho0 (tail-coh cg)
                   (\ q qin -> wf0 q (there qin))
      in mkCFT ck cbp nbbp cw tail

    rv-lf-tail : (ps orig : FinFun) -> CoherentFunTail orig ->
      (wf0 : WF M orig) ->
      let h = replaceVals orig (\ q ein -> fst (wf0 q ein))
      in CoherentFunTail h ->
         (shift : (q : Edge) -> EdgeIn q ps -> EdgeIn q orig) ->
         ((q : Edge) (ein : EdgeIn q ps) ->
            EdgeIn (mkSigma (fst q) (fst (wf0 q (shift q ein)))) h) ->
         LeFunCode ps h
    rv-lf-tail nil orig cg wf0 cft-h shift corr = tt
    rv-lf-tail (cons q qs) orig cg wf0 cft-h shift corr =
      let h    = replaceVals orig (\ r rin -> fst (wf0 r rin))
          wq   = wf0 q (shift q here)
          yq   = fst wq ; bq = fst (snd wq)
          le-vq = fst (snd (snd wq))
          fm-yq = fst (snd (snd (snd (snd wq))))
          cft-e = cft-edge cg (shift q here)
          ck-q  = key-coh cft-e
          cv-q  = val-coh cft-e
          cyq   = FinMem-coh-u yq bq fm-yq
          head-le = EvalFun-edge-le (mkSigma (fst q) yq) h (fst q)
                      cft-h (corr q here) ck-q (LeCode-refl (fst q) ck-q)
          cefh  = Coherent-EvalFun h (fst q) cft-h ck-q
          head  = LeCode-trans (snd q) yq (EvalFun h (fst q))
                    cv-q cyq cefh le-vq head-le
          tail  = rv-lf-tail qs orig cg wf0 cft-h
                    (\ r rin -> shift r (there rin))
                    (\ r rin -> corr r (there rin))
      in mkSigma head tail

    rv-lf : (g : FinFun) -> CoherentFunTail g ->
      (wf0 : WF M g) ->
      CoherentFunTail (replaceVals g (\ p ein -> fst (wf0 p ein))) ->
      LeFunCode g (replaceVals g (\ p ein -> fst (wf0 p ein)))
    rv-lf nil cg wf0 cft-h = tt
    rv-lf (cons p ps) cg wf0 cft-h =
      let h    = replaceVals (cons p ps) (\ q ein -> fst (wf0 q ein))
          wp   = wf0 p here
          yp   = fst wp ; bp = fst (snd wp)
          le-vp = fst (snd (snd wp))
          fm-yp = fst (snd (snd (snd (snd wp))))
          ck-p = key-coh cg
          cv-p = val-coh cg
          cyp  = FinMem-coh-u yp bp fm-yp
          head-le = EvalFun-edge-le (mkSigma (fst p) yp) h (fst p)
                      cft-h here ck-p (LeCode-refl (fst p) ck-p)
          cefh = Coherent-EvalFun h (fst p) cft-h ck-p
          head = LeCode-trans (snd p) yp (EvalFun h (fst p))
                   cv-p cyp cefh le-vp head-le
          tail = rv-lf-tail ps (cons p ps) cg wf0 cft-h
                   (\ q qin -> there qin)
                   (\ q qin -> replaceVals-corr (cons p ps)
                      (\ r rin -> fst (wf0 r rin)) q (there qin))
      in mkSigma head tail

    rv-fmFun : (a0 : FinEl) ->
      (g : FinFun) ->
      ((p : Edge) -> EdgeIn p g ->
        Pair (FinMem (fst p) a0) (EvalRel M (extendEnv rho (fst p)) (snd p))) ->
      (wf0 : WF M g) ->
      (ff : FinFun) -> CoherentFunTail ff -> FinMemAllU ff a0 ->
      ((p : Edge) (ein : EdgeIn p g) ->
        EdgeIn (mkSigma (fst p) (fst (snd (wf0 p ein)))) ff) ->
      FinMemFun (replaceVals g (\ p ein -> fst (wf0 p ein))) a0 ff
    rv-fmFun a0 nil ew0 wf0 ff cft-ff fmAllU-ff corr = tt
    rv-fmFun a0 (cons p ps) ew0 wf0 ff cft-ff fmAllU-ff corr =
      let ep   = ew0 p here
          fm-k = fst ep
          wp   = wf0 p here
          yp   = fst wp ; bp = fst (snd wp)
          fm-yp = fst (snd (snd (snd (snd wp))))
          ck-p = FinMem-coh-u (fst p) a0 fm-k
          cbp  = coh-from-aU bp (FinMem-a-in-U yp bp fm-yp)
          cef  = Coherent-EvalFun ff (fst p) cft-ff ck-p
          efU  = EvalFun-in-UCode ff (fst p) a0 cft-ff ck-p fmAllU-ff
          le-bp-ef = EvalFun-edge-le (mkSigma (fst p) bp) ff (fst p)
                       cft-ff (corr p here) ck-p (LeCode-refl (fst p) ck-p)
          fm-yp-ef = finMem-upward yp bp (EvalFun ff (fst p))
                       le-bp-ef cbp cef fm-yp efU
          tail = rv-fmFun a0 ps (\ q qin -> ew0 q (there qin))
                   (\ q qin -> wf0 q (there qin))
                   ff cft-ff fmAllU-ff (\ q qin -> corr q (there qin))
      in mkSigma (mkSigma fm-k fm-yp-ef) tail

    rv-fmAllU : (a0 : FinEl) ->
      (g : FinFun) ->
      ((p : Edge) -> EdgeIn p g ->
        Pair (FinMem (fst p) a0) (EvalRel M (extendEnv rho (fst p)) (snd p))) ->
      (wf0 : WF M g) ->
      FinMemAllU (replaceVals g (\ p ein -> fst (snd (wf0 p ein)))) a0
    rv-fmAllU a0 nil ew0 wf0 = tt
    rv-fmAllU a0 (cons p ps) ew0 wf0 =
      let ep   = ew0 p here
          fm-k = fst ep
          wp   = wf0 p here
          yp   = fst wp ; bp = fst (snd wp)
          fm-yp = fst (snd (snd (snd (snd wp))))
          bU   = FinMem-a-in-U yp bp fm-yp
          tail = rv-fmAllU a0 ps (\ q qin -> ew0 q (there qin))
                   (\ q qin -> wf0 q (there qin))
      in mkSigma (mkSigma fm-k bU) tail

------------------------------------------------------------------------
-- InvTyp-App
------------------------------------------------------------------------

InvTyp-App : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M N : Expr n) (rho : EnvApprox n) ->
  Fits G rho ->
  InvTyp G M (Pi A B) rho ->
  InvTyp G N A rho ->
  InvTyp G (App M N) (subst1 B N) rho
InvTyp-App A B M N rho fits invM invN = invTyp-App-aux
  where
    crho = Fits-CoherentEnv rho fits

    mkEvalApp : (v0 : FinEl) -> NotBot v0 ->
      (w : FinEl) -> EvalRel N rho w ->
      EvalRel M rho (FunEl (cons (mkSigma w v0) nil)) ->
      EvalRel (App M N) rho v0
    mkEvalApp Bot () w evN evM-sing
    mkEvalApp UCode nbv0 w evN evM-sing = mkSigma w (mkSigma evN evM-sing)
    mkEvalApp PropCode nbv0 w evN evM-sing = mkSigma w (mkSigma evN evM-sing)
    mkEvalApp (FunEl g) nbv0 w evN evM-sing = mkSigma w (mkSigma evN evM-sing)
    mkEvalApp (PiCode a0 f0) nbv0 w evN evM-sing = mkSigma w (mkSigma evN evM-sing)
    mkEvalApp (SigmaCode a0 f0) nbv0 w evN evM-sing = mkSigma w (mkSigma evN evM-sing)
    mkEvalApp (PairCode u0 v0') nbv0 w evN evM-sing = mkSigma w (mkSigma evN evM-sing)

    app-h-case :
      (w v : FinEl) -> NotBot v -> Coherent v ->
      EvalRel N rho w ->
      EvalRel M rho (FunEl (cons (mkSigma w v) nil)) ->
      (h piaf : FinEl) ->
      LeCode (FunEl (cons (mkSigma w v) nil)) h ->
      EvalRel M rho h ->
      FinMem h piaf ->
      EvalRel (Pi A B) rho piaf ->
      Typed (App M N) (subst1 B N) rho v
    app-h-case w v nbv cv evN evM-sing Bot piaf () evM-h fm-h evPi
    app-h-case w v nbv cv evN evM-sing UCode piaf () evPi
    app-h-case w v nbv cv evN evM-sing PropCode piaf () evPi
    app-h-case w v nbv cv evN evM-sing (PiCode _ _) piaf () evPi
    app-h-case w v nbv cv evN evM-sing (SigmaCode _ _) piaf () evPi
    app-h-case w v nbv cv evN evM-sing (PairCode _ _) piaf () evPi
    app-h-case w v nbv cv evN evM-sing (FunEl g') Bot le-g' evM-g' () evPi
    app-h-case w v nbv cv evN evM-sing (FunEl g') UCode le-g' evM-g' () evPi
    app-h-case w v nbv cv evN evM-sing (FunEl g') PropCode le-g' evM-g' () evPi
    app-h-case w v nbv cv evN evM-sing (FunEl g') (FunEl _) le-g' evM-g' () evPi
    app-h-case w v nbv cv evN evM-sing (FunEl g') (SigmaCode _ _) le-g' evM-g' () evPi
    app-h-case w v nbv cv evN evM-sing (FunEl g') (PairCode _ _) le-g' evM-g' () evPi
    app-h-case w v nbv cv evN evM-sing (FunEl g') (PiCode a f) le-g' evM-g' fm-g' evPi =
      let fmFun-g' = fst fm-g'
          cf-g'    = fst (snd fm-g')
          piU      = snd (snd fm-g')
          aU       = fst piU
          fmAllU-f = fst (snd piU)
          cf-f     = snd (snd piU)
          ca       = coh-from-aU a aU
          le-v-ef  = fst le-g'
          cw       = EvalRel-coh N rho w evN
          ctg'     = cft-from-cf g' cf-g'
          sb       = selectionBelow g' w ctg' cw
          u0       = fst sb
          v0       = fst (snd sb)
          sel-g'   = fst (snd (snd sb))
          le-u0-w  = fst (snd (snd (snd sb)))
          eq-v0    = snd (snd (snd (snd sb)))
          le-v-v0  : LeCode v v0
          le-v-v0  = Eq-transport (LeCode v) eq-v0 le-v-ef
          cu0      = Coherent-Selection sel-g' ctg'
          cv0      = Coherent-Selection-val sel-g' ctg'
          fm-u0-a  = FinMem-Selection a f sel-g' fmFun-g' ctg' ca aU
          fm-v0-fu0 = FinMem-Selection-codomain a f sel-g' fmFun-g' ctg' cf-f fmAllU-f
          fu0      = EvalFun f u0
          fu0-U    = EvalFun-in-UCode f u0 a cf-f cu0 fmAllU-f
          selbody-f = snd (snd (snd (snd evPi)))
          sb-f     = selectionBelow f u0 cf-f cu0
          x-f      = fst sb-f
          w-f      = fst (snd sb-f)
          sel-f    = fst (snd (snd sb-f))
          le-xf    = fst (snd (snd (snd sb-f)))
          eq-wf    = snd (snd (snd (snd sb-f)))
          sb-result = selbody-f x-f w-f sel-f
          z        = fst sb-result
          le-z-xf  = fst (snd sb-result)
          fm-z-a'  = fst (snd (snd sb-result))
          evB-z-wf = snd (snd (snd sb-result))
          cz       = FinMem-coh-u z (fst (snd (snd evPi))) fm-z-a'
          cx-f     = Coherent-Selection sel-f cf-f
          le-z-u0  = LeCode-trans z x-f u0 cz cx-f cu0 le-z-xf le-xf
          le-z-w   = LeCode-trans z u0 w cz cu0 cw le-z-u0 le-u0-w
          evB-z-fu0 : EvalRel B (extendEnv rho z) fu0
          evB-z-fu0 = Eq-transport (\ x -> EvalRel B (extendEnv rho z) x)
                        (Eq-sym eq-wf) evB-z-wf
          envle    = mkSigma (EnvLe-refl rho crho)
                       (mkSigma cz (mkSigma cw le-z-w))
          evB-w-fu0 = EvalRel-mon-env B (extendEnv rho z)
                        (extendEnv rho w) fu0 evB-z-fu0 envle
          evBN-fu0 = EvalRel-subst1-backward B N rho w fu0 crho evN evB-w-fu0
          lf-v0    : LeFunCode (cons (mkSigma w v0) nil) g'
          lf-v0    = mkSigma (Eq-transport (\ x -> LeCode x (EvalFun g' w)) eq-v0
                       (LeCode-refl (EvalFun g' w)
                         (Coherent-EvalFun g' w (cft-from-cf g' cf-g') cw))) tt
          nbv0     = NotBot-from-Le v v0 cv nbv le-v-v0
          cf-v0-sing : Coherent (FunEl (cons (mkSigma w v0) nil))
          cf-v0-sing = mkCFT cw cv0 nbv0 tt tt
          evM-v0-sing = EvalRel-down M rho (FunEl g')
                          (FunEl (cons (mkSigma w v0) nil))
                          crho cf-v0-sing evM-g' lf-v0
          evApp-v0 = mkEvalApp v0 nbv0 w evN evM-v0-sing
      in mkSigma v0 (mkSigma fu0
           (mkSigma le-v-v0 (mkSigma evApp-v0 (mkSigma fm-v0-fu0 evBN-fu0))))

    app-main :
      (w v : FinEl) -> NotBot v -> Coherent v ->
      EvalRel N rho w ->
      EvalRel M rho (FunEl (cons (mkSigma w v) nil)) ->
      Typed (App M N) (subst1 B N) rho v
    app-main w v nbv cv evN evM-sing =
      let invM-sing = invM (FunEl (cons (mkSigma w v) nil)) evM-sing
          h     = fst invM-sing
          piaf  = fst (snd invM-sing)
          le-sing-h = fst (snd (snd invM-sing))
          evM-h = fst (snd (snd (snd invM-sing)))
          fm-h  = fst (snd (snd (snd (snd invM-sing))))
          evPi  = snd (snd (snd (snd (snd invM-sing))))
      in app-h-case w v nbv cv evN evM-sing h piaf le-sing-h evM-h fm-h evPi

    invTyp-App-aux : (v : FinEl) -> EvalRel (App M N) rho v ->
      Typed (App M N) (subst1 B N) rho v
    invTyp-App-aux Bot ev =
      mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt (EvalRel-Bot (subst1 B N) rho)))))
    invTyp-App-aux UCode ev =
      let w = fst ev ; evN = fst (snd ev) ; evM-sing = snd (snd ev)
          cv = EvalRel-coh (App M N) rho UCode ev
      in app-main w UCode tt cv evN evM-sing
    invTyp-App-aux PropCode ev =
      let w = fst ev ; evN = fst (snd ev) ; evM-sing = snd (snd ev)
          cv = EvalRel-coh (App M N) rho PropCode ev
      in app-main w PropCode tt cv evN evM-sing
    invTyp-App-aux (FunEl g) ev =
      let w = fst ev ; evN = fst (snd ev) ; evM-sing = snd (snd ev)
          cv = EvalRel-coh (App M N) rho (FunEl g) ev
      in app-main w (FunEl g) tt cv evN evM-sing
    invTyp-App-aux (PiCode a0 f0) ev =
      let w = fst ev ; evN = fst (snd ev) ; evM-sing = snd (snd ev)
          cv = EvalRel-coh (App M N) rho (PiCode a0 f0) ev
      in app-main w (PiCode a0 f0) tt cv evN evM-sing
    invTyp-App-aux (SigmaCode a0 f0) ev =
      let w = fst ev ; evN = fst (snd ev) ; evM-sing = snd (snd ev)
          cv = EvalRel-coh (App M N) rho (SigmaCode a0 f0) ev
      in app-main w (SigmaCode a0 f0) tt cv evN evM-sing
    invTyp-App-aux (PairCode u0 v0) ev =
      let w = fst ev ; evN = fst (snd ev) ; evM-sing = snd (snd ev)
          cv = EvalRel-coh (App M N) rho (PairCode u0 v0) ev
      in app-main w (PairCode u0 v0) tt cv evN evM-sing

------------------------------------------------------------------------
-- InvConv-beta
------------------------------------------------------------------------

InvConv-beta : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M : Expr (suc n)) (N : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G N A rho ->
  ((rho' : EnvApprox n) (x a : FinEl) ->
    Fits G rho' -> FinMem x a -> EvalRel A rho' a ->
    InvTyp (extend G A) M B (extendEnv rho' x)) ->
  InvConv G (App (Lam A M) N) (subst1 M N) (subst1 B N) rho
InvConv-beta {G = G} A B M N rho fits invN body-ih =
  mkSigma invTyp-app (mkSigma invTyp-sub (mkSigma conv-app-to-sub conv-sub-to-app))
  where
    crho = Fits-CoherentEnv rho fits

    conv-app-to-sub-nonbot : (u : FinEl) -> NotBot u ->
      EvalRel (App (Lam A M) N) rho u -> EvalRel (subst1 M N) rho u
    conv-app-to-sub-nonbot u nbu ev =
      let dec = App-decompose (Lam A M) N rho u nbu ev
          v   = fst dec
          evN = fst (snd dec)
          evLam-sing = snd (snd dec)
          ew  = Lam-edgewise A M rho (cons (mkSigma v u) nil) evLam-sing
          a   = fst ew
          wp  = snd (snd (snd (snd ew))) (mkSigma v u) here
          z   = fst wp
          lez = fst (snd wp)
          memz = fst (snd (snd wp))
          evMz = snd (snd (snd wp))
          cz  = FinMem-coh-u z a memz
          cv  = EvalRel-coh N rho v evN
          evNz = EvalRel-down N rho v z crho cz evN lez
      in EvalRel-subst1-backward M N rho z u crho evNz evMz

    conv-app-to-sub : (u : FinEl) -> EvalRel (App (Lam A M) N) rho u ->
      EvalRel (subst1 M N) rho u
    conv-app-to-sub Bot ev = EvalRel-Bot (subst1 M N) rho
    conv-app-to-sub UCode ev = conv-app-to-sub-nonbot UCode tt ev
    conv-app-to-sub PropCode ev = conv-app-to-sub-nonbot PropCode tt ev
    conv-app-to-sub (FunEl g') ev = conv-app-to-sub-nonbot (FunEl g') tt ev
    conv-app-to-sub (PiCode a0 f0) ev = conv-app-to-sub-nonbot (PiCode a0 f0) tt ev
    conv-app-to-sub (SigmaCode a0 f0) ev = conv-app-to-sub-nonbot (SigmaCode a0 f0) tt ev
    conv-app-to-sub (PairCode u0 v0) ev = conv-app-to-sub-nonbot (PairCode u0 v0) tt ev

    mkLamEvidence : (u : FinEl) -> NotBot u ->
      EvalRel (subst1 M N) rho u ->
      Sigma FinEl (\ y0 -> Pair (EvalRel N rho y0)
        (EvalRel (Lam A M) rho (FunEl (cons (mkSigma y0 u) nil))))
    mkLamEvidence u nbu ev = mkSigma y (mkSigma evNy evLam)
      where
        fwd  = EvalRel-subst1-forward M N rho u crho ev
        v    = fst fwd
        evNv = fst (snd fwd)
        evMv = snd (snd fwd)
        typed = invN v evNv
        y    = fst typed
        a'   = fst (snd typed)
        le-v-y = fst (snd (snd typed))
        evNy = fst (snd (snd (snd typed)))
        memy = fst (snd (snd (snd (snd typed))))
        evAa' = snd (snd (snd (snd (snd typed))))
        cy   = FinMem-coh-u y a' memy
        cv   = EvalRel-coh N rho v evNv
        a'U  = FinMem-a-in-U y a' memy
        envle = mkSigma (EnvLe-refl rho crho) (mkSigma cv (mkSigma cy le-v-y))
        evMy = EvalRel-mon-env M (extendEnv rho v) (extendEnv rho y) u evMv envle
        cu   = EvalRel-coh M (extendEnv rho y) u evMy
        cg-sing : CoherentFun (cons (mkSigma y u) nil)
        cg-sing = mkCFT cy cu nbu tt tt
        selBody : (x0 v0 : FinEl) ->
          Selection (cons (mkSigma y u) nil) x0 v0 ->
          Sigma FinEl (\ z0 -> Pair (LeCode z0 x0)
            (Pair (FinMem z0 a') (EvalRel M (extendEnv rho z0) v0)))
        selBody .Bot .Bot (sel-skip sel-nil) =
          mkSigma Bot (mkSigma tt (mkSigma a'U (EvalRel-Bot M (extendEnv rho Bot))))
        selBody .(Sup y Bot) .(Sup u Bot) (sel-take {._} {.Bot} {.Bot} ck cv0 sel-nil) =
          mkSigma y (mkSigma
            (Eq-transport (LeCode y) (Eq-sym (Sup-Bot-r y)) (LeCode-refl y cy))
            (mkSigma memy
              (Eq-transport (EvalRel M (extendEnv rho y)) (Eq-sym (Sup-Bot-r u)) evMy)))
        evLam : EvalRel (Lam A M) rho (FunEl (cons (mkSigma y u) nil))
        evLam = mkSigma a' (mkSigma cg-sing (mkSigma a'U
                  (mkSigma evAa' selBody)))

    conv-sub-to-app : (u : FinEl) -> EvalRel (subst1 M N) rho u ->
      EvalRel (App (Lam A M) N) rho u
    conv-sub-to-app Bot ev = tt
    conv-sub-to-app UCode ev =
      let r = mkLamEvidence UCode tt ev
      in mkSigma (fst r) (mkSigma (fst (snd r)) (snd (snd r)))
    conv-sub-to-app PropCode ev =
      let r = mkLamEvidence PropCode tt ev
      in mkSigma (fst r) (mkSigma (fst (snd r)) (snd (snd r)))
    conv-sub-to-app (FunEl g') ev =
      let r = mkLamEvidence (FunEl g') tt ev
      in mkSigma (fst r) (mkSigma (fst (snd r)) (snd (snd r)))
    conv-sub-to-app (PiCode a0 f0) ev =
      let r = mkLamEvidence (PiCode a0 f0) tt ev
      in mkSigma (fst r) (mkSigma (fst (snd r)) (snd (snd r)))
    conv-sub-to-app (SigmaCode a0 f0) ev =
      let r = mkLamEvidence (SigmaCode a0 f0) tt ev
      in mkSigma (fst r) (mkSigma (fst (snd r)) (snd (snd r)))
    conv-sub-to-app (PairCode u0 v0) ev =
      let r = mkLamEvidence (PairCode u0 v0) tt ev
      in mkSigma (fst r) (mkSigma (fst (snd r)) (snd (snd r)))

    invLam : InvTyp G (Lam A M) (Pi A B) rho
    invLam = InvTyp-Lam A B M body-ih rho fits

    invTyp-app : InvTyp G (App (Lam A M) N) (subst1 B N) rho
    invTyp-app = InvTyp-App A B (Lam A M) N rho fits invLam invN

    invTyp-sub : InvTyp G (subst1 M N) (subst1 B N) rho
    invTyp-sub u ev =
      let evApp = conv-sub-to-app u ev
          typed = invTyp-app u evApp
          u'    = fst typed
          a'    = fst (snd typed)
          le-u  = fst (snd (snd typed))
          evApp' = fst (snd (snd (snd typed)))
          fm'   = fst (snd (snd (snd (snd typed))))
          evBN' = snd (snd (snd (snd (snd typed))))
          evSub' = conv-app-to-sub u' evApp'
      in mkSigma u' (mkSigma a' (mkSigma le-u (mkSigma evSub' (mkSigma fm' evBN'))))

------------------------------------------------------------------------
-- InvConv-funext
------------------------------------------------------------------------

InvConv-funext : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M N : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G M (Pi A B) rho ->
  InvTyp G N (Pi A B) rho ->
  ((x a : FinEl) ->
    FinMem x a -> EvalRel A rho a ->
    InvConv (extend G A) (App (wkExpr M) (Var fzero))
                          (App (wkExpr N) (Var fzero)) B (extendEnv rho x)) ->
  InvConv G M N (Pi A B) rho
InvConv-funext {G = G} A B M N rho fits invM invN ih =
  mkSigma invM (mkSigma invN (mkSigma conv-M-to-N conv-N-to-M))
  where
    crho = Fits-CoherentEnv rho fits

    mkAppEvidence : (F : Expr _) (x vi : FinEl) -> Coherent x -> NotBot vi ->
      EvalRel F rho (FunEl (cons (mkSigma x vi) nil)) ->
      EvalRel (App (wkExpr F) (Var fzero)) (extendEnv rho x) vi
    mkAppEvidence F x Bot cx () evF
    mkAppEvidence F x UCode cx nbvi evF =
      mkSigma x (mkSigma (mkSigma cx (LeCode-refl x cx))
        (EvalRel-wk F rho x (FunEl (cons (mkSigma x UCode) nil)) evF))
    mkAppEvidence F x PropCode cx nbvi evF =
      mkSigma x (mkSigma (mkSigma cx (LeCode-refl x cx))
        (EvalRel-wk F rho x (FunEl (cons (mkSigma x PropCode) nil)) evF))
    mkAppEvidence F x (FunEl g') cx nbvi evF =
      mkSigma x (mkSigma (mkSigma cx (LeCode-refl x cx))
        (EvalRel-wk F rho x (FunEl (cons (mkSigma x (FunEl g')) nil)) evF))
    mkAppEvidence F x (PiCode a0 f0) cx nbvi evF =
      mkSigma x (mkSigma (mkSigma cx (LeCode-refl x cx))
        (EvalRel-wk F rho x (FunEl (cons (mkSigma x (PiCode a0 f0)) nil)) evF))
    mkAppEvidence F x (SigmaCode a0 f0) cx nbvi evF =
      mkSigma x (mkSigma (mkSigma cx (LeCode-refl x cx))
        (EvalRel-wk F rho x (FunEl (cons (mkSigma x (SigmaCode a0 f0)) nil)) evF))
    mkAppEvidence F x (PairCode u0 v0) cx nbvi evF =
      mkSigma x (mkSigma (mkSigma cx (LeCode-refl x cx))
        (EvalRel-wk F rho x (FunEl (cons (mkSigma x (PairCode u0 v0)) nil)) evF))

    decompAppEvidence : (F : Expr _) (x vi : FinEl) -> NotBot vi ->
      EvalRel (App (wkExpr F) (Var fzero)) (extendEnv rho x) vi ->
      Sigma FinEl (\ w -> Pair (LeCode w x) (Pair (Coherent w)
        (EvalRel F rho (FunEl (cons (mkSigma w vi) nil)))))
    decompAppEvidence F x UCode nbvi ev =
      let w = fst ev ; evV0 = fst (snd ev) ; evWkF = snd (snd ev)
      in mkSigma w (mkSigma (snd evV0) (mkSigma (fst evV0)
           (EvalRel-unwk F rho x (FunEl (cons (mkSigma w UCode) nil)) evWkF)))
    decompAppEvidence F x PropCode nbvi ev =
      let w = fst ev ; evV0 = fst (snd ev) ; evWkF = snd (snd ev)
      in mkSigma w (mkSigma (snd evV0) (mkSigma (fst evV0)
           (EvalRel-unwk F rho x (FunEl (cons (mkSigma w PropCode) nil)) evWkF)))
    decompAppEvidence F x (FunEl g') nbvi ev =
      let w = fst ev ; evV0 = fst (snd ev) ; evWkF = snd (snd ev)
      in mkSigma w (mkSigma (snd evV0) (mkSigma (fst evV0)
           (EvalRel-unwk F rho x (FunEl (cons (mkSigma w (FunEl g')) nil)) evWkF)))
    decompAppEvidence F x (PiCode a0 f0) nbvi ev =
      let w = fst ev ; evV0 = fst (snd ev) ; evWkF = snd (snd ev)
      in mkSigma w (mkSigma (snd evV0) (mkSigma (fst evV0)
           (EvalRel-unwk F rho x (FunEl (cons (mkSigma w (PiCode a0 f0)) nil)) evWkF)))
    decompAppEvidence F x (SigmaCode a0 f0) nbvi ev =
      let w = fst ev ; evV0 = fst (snd ev) ; evWkF = snd (snd ev)
      in mkSigma w (mkSigma (snd evV0) (mkSigma (fst evV0)
           (EvalRel-unwk F rho x (FunEl (cons (mkSigma w (SigmaCode a0 f0)) nil)) evWkF)))
    decompAppEvidence F x (PairCode u0 v0) nbvi ev =
      let w = fst ev ; evV0 = fst (snd ev) ; evWkF = snd (snd ev)
      in mkSigma w (mkSigma (snd evV0) (mkSigma (fst evV0)
           (EvalRel-unwk F rho x (FunEl (cons (mkSigma w (PairCode u0 v0)) nil)) evWkF)))

    edge-transfer : (F F' : Expr _) ->
      ((x a0 : FinEl) -> FinMem x a0 -> EvalRel A rho a0 ->
        (v : FinEl) ->
        EvalRel (App (wkExpr F) (Var fzero)) (extendEnv rho x) v ->
        EvalRel (App (wkExpr F') (Var fzero)) (extendEnv rho x) v) ->
      (a : FinEl) -> (f : FinFun) -> EvalRel A rho a ->
      (g' : FinFun) -> CoherentFun g' -> FinMemFun g' a f ->
      EvalRel F rho (FunEl g') ->
      (p : Edge) -> EdgeIn p g' ->
      Sigma FinEl (\ w -> Pair (LeCode w (fst p)) (Pair (Coherent w)
        (EvalRel F' rho (FunEl (cons (mkSigma w (snd p)) nil)))))
    edge-transfer F F' convDir a f evA g' cfg fmf evF-g' p ein =
      let ui  = fst p ; vi = snd p
          cft = cft-from-cf g' cfg
          cui = CoherentFun-edge-key p g' cft ein
          cvi-nb = cft-edge-val p g' cft ein
          cvi = fst cvi-nb ; nbvi = snd cvi-nb
          fmui = fmf-key g' a _ fmf p ein
          cf-sing : CoherentFun (cons (mkSigma ui vi) nil)
          cf-sing = mkCFT cui cvi nbvi tt tt
          lf-sing : LeFunCode (cons (mkSigma ui vi) nil) g'
          lf-sing = mkSigma (EvalFun-edge-le p g' ui cft ein cui
                      (LeCode-refl ui cui)) tt
          evF-sing = EvalRel-down F rho (FunEl g') (FunEl (cons (mkSigma ui vi) nil))
                       crho cf-sing evF-g' lf-sing
          evAppF = mkAppEvidence F ui vi cui nbvi evF-sing
          evAppF' = convDir ui a fmui evA vi evAppF
      in decompAppEvidence F' ui vi nbvi evAppF'
      where
        fmf-key : (h : FinFun) (a0 : FinEl) (f0 : FinFun) -> FinMemFun h a0 f0 ->
          (e : Edge) -> EdgeIn e h -> FinMem (fst e) a0
        fmf-key (cons q qs) a0 f0 fmf .q here = fst (fst fmf)
        fmf-key (cons q qs) a0 f0 fmf e (there ein) = fmf-key qs a0 f0 (snd fmf) e ein
        cft-edge-val : (e : Edge) (h : FinFun) ->
          CoherentFunTail h -> EdgeIn e h ->
          Pair (Coherent (snd e)) (NotBot (snd e))
        cft-edge-val e (cons q qs) cft here = mkSigma (val-coh cft) (val-nbot cft)
        cft-edge-val e (cons q (cons r rs)) cft (there ein) =
          cft-edge-val e (cons r rs) (tail-coh cft) ein

    edge-original : (F F' : Expr _) ->
      ((x a0 : FinEl) -> FinMem x a0 -> EvalRel A rho a0 ->
        (v : FinEl) ->
        EvalRel (App (wkExpr F) (Var fzero)) (extendEnv rho x) v ->
        EvalRel (App (wkExpr F') (Var fzero)) (extendEnv rho x) v) ->
      (a : FinEl) -> (f : FinFun) -> EvalRel A rho a ->
      (g-full : FinFun) -> CoherentFun g-full -> FinMemFun g-full a f ->
      EvalRel F rho (FunEl g-full) ->
      (p : Edge) -> EdgeIn p g-full ->
      EvalRel F' rho (FunEl (cons p nil))
    edge-original F F' convDir a f evA gf cfg fmf evF p ein =
      let et   = edge-transfer F F' convDir a f evA gf cfg fmf evF p ein
          wp   = fst et
          le-wp = fst (snd et)
          cwp  = fst (snd (snd et))
          evF'-wp = snd (snd (snd et))
          cft-gf = cft-from-cf gf cfg
          cui  = CoherentFun-edge-key p gf cft-gf ein
          cvi  = fst (cft-edge-val p gf cft-gf ein)
          nbvi = snd (cft-edge-val p gf cft-gf ein)
          cf-orig : CoherentFun (cons p nil)
          cf-orig = mkCFT cui cvi nbvi tt tt
          cft-wp = cft-from-cf (cons (mkSigma wp (snd p)) nil)
                     (mkCFT cwp cvi nbvi tt tt)
          le-v = EvalFun-edge-le (mkSigma wp (snd p))
                   (cons (mkSigma wp (snd p)) nil) (fst p)
                   cft-wp here cui le-wp
          lf-orig : LeFunCode (cons p nil) (cons (mkSigma wp (snd p)) nil)
          lf-orig = mkSigma le-v tt
      in EvalRel-down F' rho (FunEl (cons (mkSigma wp (snd p)) nil))
           (FunEl (cons p nil)) crho cf-orig evF'-wp lf-orig
      where
        cft-edge-val : (e : Edge) (h0 : FinFun) ->
          CoherentFunTail h0 -> EdgeIn e h0 ->
          Pair (Coherent (snd e)) (NotBot (snd e))
        cft-edge-val e (cons q qs) cft0 here = mkSigma (val-coh cft0) (val-nbot cft0)
        cft-edge-val e (cons q (cons r rs)) cft0 (there ein0) =
          cft-edge-val e (cons r rs) (tail-coh cft0) ein0

    build-graph : (F' : Expr _) ->
      (g : FinFun) -> CoherentFun g ->
      ((p : Edge) -> EdgeIn p g -> EvalRel F' rho (FunEl (cons p nil))) ->
      EvalRel F' rho (FunEl g)
    build-graph F' nil () _
    build-graph F' (cons p nil) _ f = f p here
    build-graph F' (cons p (cons q qs)) cfg f =
      let evSing = f p here
          cf-rest = tail-coh cfg
          evRest = build-graph F' (cons q qs) cf-rest (\ r rin -> f r (there rin))
          sing = FunEl (cons p nil)
          rest = FunEl (cons q qs)
          csing = EvalRel-coh F' rho sing evSing
          crest = EvalRel-coh F' rho rest evRest
          comp  = EvalRel-Comp F' rho crho sing rest evSing evRest
      in EvalRel-Sup F' rho sing rest crho csing crest comp evSing evRest

    conv-main : (F F' : Expr _) ->
      ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
        (v : FinEl) ->
        EvalRel (App (wkExpr F) (Var fzero)) (extendEnv rho x) v ->
        EvalRel (App (wkExpr F') (Var fzero)) (extendEnv rho x) v) ->
      (u u' piaf : FinEl) -> Coherent u ->
      LeCode u u' -> EvalRel F rho u' -> FinMem u' piaf -> EvalRel (Pi A B) rho piaf ->
      EvalRel F' rho u
    conv-main F F' convDir Bot Bot piaf cu le-u evF fm evPi =
      EvalRel-Bot F' rho
    conv-main F F' convDir UCode Bot piaf cu () evF fm evPi
    conv-main F F' convDir PropCode Bot piaf cu () evF fm evPi
    conv-main F F' convDir (FunEl _) Bot piaf cu () evF fm evPi
    conv-main F F' convDir (PiCode _ _) Bot piaf cu () evF fm evPi
    conv-main F F' convDir (SigmaCode _ _) Bot piaf cu () evF fm evPi
    conv-main F F' convDir (PairCode _ _) Bot piaf cu () evF fm evPi
    conv-main F F' convDir u (FunEl g') Bot cu le-u evF () evPi
    conv-main F F' convDir u (FunEl g') UCode cu le-u evF () evPi
    conv-main F F' convDir u (FunEl g') PropCode cu le-u evF () evPi
    conv-main F F' convDir u (FunEl g') (FunEl _) cu le-u evF () evPi
    conv-main F F' convDir u (FunEl g') (SigmaCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u (FunEl g') (PairCode _ _) cu le-u evF () evPi
    conv-main F F' convDir Bot (FunEl g') (PiCode a f) cu le-u evF fm evPi =
      EvalRel-Bot F' rho
    conv-main F F' convDir UCode (FunEl g') (PiCode a f) cu () evF fm evPi
    conv-main F F' convDir PropCode (FunEl g') (PiCode a f) cu () evF fm evPi
    conv-main F F' convDir (FunEl h) (FunEl g') (PiCode a f) cu le-u evF fm evPi =
      let cf-g'  = fst (snd fm)
          fmf-g' = fst fm
          evA    = fst (snd evPi)
          evF'-g' = build-graph F' g' cf-g'
                      (\ p ein -> edge-original F F' convDir a f evA g' cf-g' fmf-g' evF p ein)
      in EvalRel-down F' rho (FunEl g') (FunEl h) crho cu evF'-g' le-u
    conv-main F F' convDir (PiCode _ _) (FunEl g') (PiCode a f) cu () evF fm evPi
    conv-main F F' convDir (SigmaCode _ _) (FunEl g') (PiCode a f) cu () evF fm evPi
    conv-main F F' convDir (PairCode _ _) (FunEl g') (PiCode a f) cu () evF fm evPi
    conv-main F F' convDir u UCode Bot cu le-u evF () evPi
    conv-main F F' convDir u UCode UCode cu le-u evF fm ()
    conv-main F F' convDir u UCode PropCode cu le-u evF () evPi
    conv-main F F' convDir u UCode (FunEl _) cu le-u evF () evPi
    conv-main F F' convDir u UCode (PiCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u UCode (SigmaCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u UCode (PairCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u PropCode Bot cu le-u evF () evPi
    conv-main F F' convDir u PropCode UCode cu le-u evF fm ()
    conv-main F F' convDir u PropCode PropCode cu le-u evF () evPi
    conv-main F F' convDir u PropCode (FunEl _) cu le-u evF () evPi
    conv-main F F' convDir u PropCode (PiCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u PropCode (SigmaCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u PropCode (PairCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u (PiCode a0 f0) Bot cu le-u evF () evPi
    conv-main F F' convDir u (PiCode a0 f0) UCode cu le-u evF fm ()
    conv-main F F' convDir u (PiCode a0 f0) PropCode cu le-u evF fm ()
    conv-main F F' convDir u (PiCode a0 f0) (FunEl _) cu le-u evF () evPi
    conv-main F F' convDir u (PiCode a0 f0) (PiCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u (PiCode a0 f0) (SigmaCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u (PiCode a0 f0) (PairCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u (SigmaCode a0 f0) Bot cu le-u evF () evPi
    conv-main F F' convDir u (SigmaCode a0 f0) UCode cu le-u evF fm ()
    conv-main F F' convDir u (SigmaCode a0 f0) PropCode cu le-u evF fm ()
    conv-main F F' convDir u (SigmaCode a0 f0) (FunEl _) cu le-u evF () evPi
    conv-main F F' convDir u (SigmaCode a0 f0) (PiCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u (SigmaCode a0 f0) (SigmaCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u (SigmaCode a0 f0) (PairCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u (PairCode u0 v0) Bot cu le-u evF () evPi
    conv-main F F' convDir u (PairCode u0 v0) UCode cu le-u evF fm ()
    conv-main F F' convDir u (PairCode u0 v0) PropCode cu le-u evF fm ()
    conv-main F F' convDir u (PairCode u0 v0) (FunEl _) cu le-u evF () evPi
    conv-main F F' convDir u (PairCode u0 v0) (PiCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u (PairCode u0 v0) (SigmaCode _ _) cu le-u evF fm ()
    conv-main F F' convDir u (PairCode u0 v0) (PairCode _ _) cu le-u evF () evPi

    conv-nonbot : (F F' : Expr _) ->
      InvTyp G F (Pi A B) rho ->
      ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
        (u : FinEl) ->
        EvalRel (App (wkExpr F) (Var fzero)) (extendEnv rho x) u ->
        EvalRel (App (wkExpr F') (Var fzero)) (extendEnv rho x) u) ->
      (u : FinEl) -> NotBot u -> EvalRel F rho u -> EvalRel F' rho u
    conv-nonbot F F' invF convDir u nbu ev =
      let typed = invF u ev
          u'   = fst typed
          piaf = fst (snd typed)
          le-u = fst (snd (snd typed))
          evF  = fst (snd (snd (snd typed)))
          fm   = fst (snd (snd (snd (snd typed))))
          evPi = snd (snd (snd (snd (snd typed))))
          cu   = EvalRel-coh F rho u ev
      in conv-main F F' convDir u u' piaf cu le-u evF fm evPi

    conv-one-dir : (F F' : Expr _) ->
      InvTyp G F (Pi A B) rho ->
      ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
        (u : FinEl) ->
        EvalRel (App (wkExpr F) (Var fzero)) (extendEnv rho x) u ->
        EvalRel (App (wkExpr F') (Var fzero)) (extendEnv rho x) u) ->
      (u : FinEl) -> EvalRel F rho u -> EvalRel F' rho u
    conv-one-dir F F' invF convDir Bot ev = EvalRel-Bot F' rho
    conv-one-dir F F' invF convDir UCode ev =
      conv-nonbot F F' invF convDir UCode tt ev
    conv-one-dir F F' invF convDir PropCode ev =
      conv-nonbot F F' invF convDir PropCode tt ev
    conv-one-dir F F' invF convDir (FunEl g0) ev =
      conv-nonbot F F' invF convDir (FunEl g0) tt ev
    conv-one-dir F F' invF convDir (PiCode a0 f0) ev =
      conv-nonbot F F' invF convDir (PiCode a0 f0) tt ev
    conv-one-dir F F' invF convDir (SigmaCode a0 f0) ev =
      conv-nonbot F F' invF convDir (SigmaCode a0 f0) tt ev
    conv-one-dir F F' invF convDir (PairCode u0 v0) ev =
      conv-nonbot F F' invF convDir (PairCode u0 v0) tt ev

    conv-M-to-N : (u : FinEl) -> EvalRel M rho u -> EvalRel N rho u
    conv-M-to-N = conv-one-dir M N invM
      (\ x a mx evAa u evApp -> fst (snd (snd (ih x a mx evAa))) u evApp)

    conv-N-to-M : (u : FinEl) -> EvalRel N rho u -> EvalRel M rho u
    conv-N-to-M = conv-one-dir N M invN
      (\ x a mx evAa u evApp -> snd (snd (snd (ih x a mx evAa))) u evApp)

------------------------------------------------------------------------
-- InvConv-App-fun
------------------------------------------------------------------------

InvConv-App-fun : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (f f' a : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvConv G f f' (Pi A B) rho ->
  InvTyp G a A rho ->
  InvConv G (App f a) (App f' a) (subst1 B a) rho
InvConv-App-fun A B f f' a rho fits invFF' invA =
  let invF  = fst invFF'
      invF' = fst (snd invFF')
      fwdF  = fst (snd (snd invFF'))
      bwdF  = snd (snd (snd invFF'))
      invLHS = InvTyp-App A B f  a rho fits invF  invA
      invRHS = InvTyp-App A B f' a rho fits invF' invA
  in mkSigma invLHS (mkSigma invRHS (mkSigma (conv-fwd fwdF) (conv-fwd bwdF)))
  where
    conv-fwd : {F F' : Expr _} ->
      ((w : FinEl) -> EvalRel F rho w -> EvalRel F' rho w) ->
      (u : FinEl) -> EvalRel (App F a) rho u -> EvalRel (App F' a) rho u
    conv-fwd eqF Bot ev = tt
    conv-fwd eqF UCode (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma eva (eqF (FunEl (cons (mkSigma v UCode) nil)) evf))
    conv-fwd eqF PropCode (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma eva (eqF (FunEl (cons (mkSigma v PropCode) nil)) evf))
    conv-fwd eqF (FunEl g') (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma eva (eqF (FunEl (cons (mkSigma v (FunEl g')) nil)) evf))
    conv-fwd eqF (PiCode a0 f0) (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma eva (eqF (FunEl (cons (mkSigma v (PiCode a0 f0)) nil)) evf))
    conv-fwd eqF (SigmaCode a0 f0) (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma eva (eqF (FunEl (cons (mkSigma v (SigmaCode a0 f0)) nil)) evf))
    conv-fwd eqF (PairCode u0 v0) (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma eva (eqF (FunEl (cons (mkSigma v (PairCode u0 v0)) nil)) evf))

------------------------------------------------------------------------
-- InvConv-App-arg
------------------------------------------------------------------------

InvConv-App-arg : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (f a a' : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G f (Pi A B) rho ->
  InvConv G a a' A rho ->
  InvConv G (App f a) (App f a') (subst1 B a) rho
InvConv-App-arg {G = G} A B f a a' rho fits invF invAA' =
  let invA  = fst invAA'
      invA' = fst (snd invAA')
      fwdA  = fst (snd (snd invAA'))
      bwdA  = snd (snd (snd invAA'))
      invLHS = InvTyp-App A B f a rho fits invF invA
  in mkSigma invLHS (mkSigma invRHS (mkSigma conv-fwd conv-bwd))
  where
    crho = Fits-CoherentEnv rho fits
    invA  = fst invAA'
    fwdA  = fst (snd (snd invAA'))
    bwdA  = snd (snd (snd invAA'))

    conv-fwd : (u : FinEl) -> EvalRel (App f a) rho u -> EvalRel (App f a') rho u
    conv-fwd Bot ev = tt
    conv-fwd UCode (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma (fwdA v eva) evf)
    conv-fwd PropCode (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma (fwdA v eva) evf)
    conv-fwd (FunEl g') (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma (fwdA v eva) evf)
    conv-fwd (PiCode a0 f0) (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma (fwdA v eva) evf)
    conv-fwd (SigmaCode a0 f0) (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma (fwdA v eva) evf)
    conv-fwd (PairCode u0 v0) (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma (fwdA v eva) evf)

    conv-bwd : (u : FinEl) -> EvalRel (App f a') rho u -> EvalRel (App f a) rho u
    conv-bwd Bot ev = tt
    conv-bwd UCode (mkSigma v (mkSigma eva' evf)) =
      mkSigma v (mkSigma (bwdA v eva') evf)
    conv-bwd PropCode (mkSigma v (mkSigma eva' evf)) =
      mkSigma v (mkSigma (bwdA v eva') evf)
    conv-bwd (FunEl g') (mkSigma v (mkSigma eva' evf)) =
      mkSigma v (mkSigma (bwdA v eva') evf)
    conv-bwd (PiCode a0 f0) (mkSigma v (mkSigma eva' evf)) =
      mkSigma v (mkSigma (bwdA v eva') evf)
    conv-bwd (SigmaCode a0 f0) (mkSigma v (mkSigma eva' evf)) =
      mkSigma v (mkSigma (bwdA v eva') evf)
    conv-bwd (PairCode u0 v0) (mkSigma v (mkSigma eva' evf)) =
      mkSigma v (mkSigma (bwdA v eva') evf)

    invLHS = InvTyp-App A B f a rho fits invF invA
    invRHS : InvTyp G (App f a') (subst1 B a) rho
    invRHS u ev =
      let typed = invLHS u (conv-bwd u ev)
          u'  = fst typed
          a0  = fst (snd typed)
          le  = fst (snd (snd typed))
          evAppA  = fst (snd (snd (snd typed)))
          fm  = fst (snd (snd (snd (snd typed))))
          evBA = snd (snd (snd (snd (snd typed))))
      in mkSigma u' (mkSigma a0 (mkSigma le (mkSigma (conv-fwd u' evAppA) (mkSigma fm evBA))))

------------------------------------------------------------------------
-- Pi-L1: Pi inversion with typed keys
------------------------------------------------------------------------

Pi-L1 : {n : Nat} (A : Expr n) (B : Expr (suc n))
  (rho : EnvApprox n) (b : FinEl) (f : FinFun) ->
  CoherentEnv rho ->
  EvalRel (Pi A B) rho (PiCode b f) ->
  Sigma FinEl (\ a -> Sigma FinFun (\ f' ->
    Pair (EvalRel A rho a)
      (Pair (FinMem a UCode)
        (Pair (LeFunCode f f')
          (Pair (EvalRel (Pi A B) rho (PiCode a f'))
            ((p : Edge) -> EdgeIn p f' ->
              Pair (FinMem (fst p) a)
                   (EvalRel B (extendEnv rho (fst p)) (snd p))))))))
Pi-L1 A B rho b f crho ev =
  let coh    = fst ev
      cb     = fst coh
      cf     = snd coh
      evA-b  = fst (snd ev)
      pew    = Pi-edgewise A B rho b f ev
      a'     = fst (snd (snd pew))
      evA-a' = fst (snd (snd (snd pew)))
      ew     = snd (snd (snd (snd pew)))
      selBody = snd (snd (snd (snd ev)))
      a'U    = get-a'U a' f cf ew selBody
      ca'    = coh-from-aU a' a'U
      cft-f  = cf
      f'     = replaceKeys f (\ p ein -> fst (ew p ein))
      cft'   = replaceKeys-CoherentFunTail B rho a' f crho cft-f ew
      ew'    = replaceKeys-edgewise B rho a' f ew
      lf     = replaceKeys-LeFunCode B rho a' f crho cft-f ew
      selbody : (u' v' : FinEl) -> Selection f' u' v' ->
        Sigma FinEl (\ x -> Pair (LeCode x u')
          (Pair (FinMem x a') (EvalRel B (extendEnv rho x) v')))
      selbody u' v' sel =
        replaceKeys-selection-body B rho a' f' u' v' crho a'U cft' ew' sel
      evPi   = mkSigma (mkSigma ca' cft')
                 (mkSigma evA-a' (mkSigma a' (mkSigma evA-a' selbody)))
  in mkSigma a' (mkSigma f' (mkSigma evA-a' (mkSigma a'U (mkSigma lf (mkSigma evPi ew')))))
  where
    get-a'U : (a0 : FinEl) ->
      (g : FinFun) -> CoherentFunTail g ->
      ((p : Edge) -> EdgeIn p g ->
        Sigma FinEl (\ x -> Pair (LeCode x (fst p))
                                 (Pair (FinMem x a0) (EvalRel B (extendEnv rho x) (snd p))))) ->
      ((u v : FinEl) -> Selection g u v ->
        Sigma FinEl (\ x -> Pair (LeCode x u)
                                 (Pair (FinMem x a0) (EvalRel B (extendEnv rho x) v)))) ->
      FinMem a0 UCode
    get-a'U a0 nil _ _ rawBody =
      let w = rawBody Bot Bot sel-nil
      in FinMem-a-in-U (fst w) a0 (fst (snd (snd w)))
    get-a'U a0 (cons p ps) _ ew0 _ =
      let w = ew0 p here
      in FinMem-a-in-U (fst w) a0 (fst (snd (snd w)))

------------------------------------------------------------------------
-- Sigma-L1: Sigma inversion with typed keys (mirrors Pi-L1)
------------------------------------------------------------------------

Sigma-L1 : {n : Nat} (A : Expr n) (B : Expr (suc n))
  (rho : EnvApprox n) (b : FinEl) (f : FinFun) ->
  CoherentEnv rho ->
  EvalRel (RawSyntaxSigma.Sigma A B) rho (SigmaCode b f) ->
  Sigma FinEl (\ a -> Sigma FinFun (\ f' ->
    Pair (EvalRel A rho a)
      (Pair (FinMem a UCode)
        (Pair (LeFunCode f f')
          (Pair (EvalRel (RawSyntaxSigma.Sigma A B) rho (SigmaCode a f'))
            ((p : Edge) -> EdgeIn p f' ->
              Pair (FinMem (fst p) a)
                   (EvalRel B (extendEnv rho (fst p)) (snd p))))))))
Sigma-L1 A B rho b f crho ev =
  let coh    = fst ev
      cb     = fst coh
      cf     = snd coh
      evA-b  = fst (snd ev)
      sew    = Sigma-edgewise A B rho b f ev
      a'     = fst (snd (snd sew))
      evA-a' = fst (snd (snd (snd sew)))
      ew     = snd (snd (snd (snd sew)))
      selBody = snd (snd (snd (snd ev)))
      a'U    = get-a'U a' f cf ew selBody
      ca'    = coh-from-aU a' a'U
      cft-f  = cf
      f'     = replaceKeys f (\ p ein -> fst (ew p ein))
      cft'   = replaceKeys-CoherentFunTail B rho a' f crho cft-f ew
      ew'    = replaceKeys-edgewise B rho a' f ew
      lf     = replaceKeys-LeFunCode B rho a' f crho cft-f ew
      selbody : (u' v' : FinEl) -> Selection f' u' v' ->
        Sigma FinEl (\ x -> Pair (LeCode x u')
          (Pair (FinMem x a') (EvalRel B (extendEnv rho x) v')))
      selbody u' v' sel =
        replaceKeys-selection-body B rho a' f' u' v' crho a'U cft' ew' sel
      evSigma = mkSigma (mkSigma ca' cft')
                  (mkSigma evA-a' (mkSigma a' (mkSigma evA-a' selbody)))
  in mkSigma a' (mkSigma f' (mkSigma evA-a' (mkSigma a'U (mkSigma lf (mkSigma evSigma ew')))))
  where
    get-a'U : (a0 : FinEl) ->
      (g : FinFun) -> CoherentFunTail g ->
      ((p : Edge) -> EdgeIn p g ->
        Sigma FinEl (\ x -> Pair (LeCode x (fst p))
                                 (Pair (FinMem x a0) (EvalRel B (extendEnv rho x) (snd p))))) ->
      ((u v : FinEl) -> Selection g u v ->
        Sigma FinEl (\ x -> Pair (LeCode x u)
                                 (Pair (FinMem x a0) (EvalRel B (extendEnv rho x) v)))) ->
      FinMem a0 UCode
    get-a'U a0 nil _ _ rawBody =
      let w = rawBody Bot Bot sel-nil
      in FinMem-a-in-U (fst w) a0 (fst (snd (snd w)))
    get-a'U a0 (cons p ps) _ ew0 _ =
      let w = ew0 p here
      in FinMem-a-in-U (fst w) a0 (fst (snd (snd w)))

------------------------------------------------------------------------
-- InvTyp-Pi
------------------------------------------------------------------------

InvTyp-Pi : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n)) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G A U rho ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
    InvTyp (extend G A) B U (extendEnv rho x)) ->
  InvTyp G (Pi A B) U rho
InvTyp-Pi A B rho fits invA body-ih Bot ev =
  mkSigma Bot (mkSigma UCode (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma tt tt)))))
InvTyp-Pi A B rho fits invA body-ih UCode ()
InvTyp-Pi A B rho fits invA body-ih PropCode ()
InvTyp-Pi A B rho fits invA body-ih (FunEl g) ()
InvTyp-Pi A B rho fits invA body-ih (SigmaCode a0 f0) ()
InvTyp-Pi A B rho fits invA body-ih (PairCode u0 v0) ()
InvTyp-Pi A B rho fits invA body-ih (PiCode b f) ev = result
  where
    crho = Fits-CoherentEnv rho fits
    coh   = fst ev
    cb    = fst coh
    cf    = snd coh
    evA-b = fst (snd ev)
    a'    = fst (snd (snd ev))
    evA-a' = fst (snd (snd (snd ev)))
    body  = snd (snd (snd (snd ev)))

    pew = Pi-edgewise A B rho b f ev
    ew : (p : Edge) -> EdgeIn p f ->
      Sigma FinEl (\ x -> Pair (LeCode x (fst p))
                               (Pair (FinMem x a') (EvalRel B (extendEnv rho x) (snd p))))
    ew = snd (snd (snd (snd pew)))

    typed-b = invA b evA-b
    b1    = fst typed-b
    ab1   = fst (snd typed-b)
    le-b-b1 = fst (snd (snd typed-b))
    evA-b1 = fst (snd (snd (snd typed-b)))
    fm-b1  = fst (snd (snd (snd (snd typed-b))))
    evU-ab1 = snd (snd (snd (snd (snd typed-b))))

    finMem-from-U-top : (x : FinEl) -> EvalRel U rho x ->
      (y : FinEl) -> FinMem y x -> FinMem y UCode
    finMem-from-U-top Bot evU Bot fm = tt
    finMem-from-U-top Bot evU UCode ()
    finMem-from-U-top Bot evU PropCode ()
    finMem-from-U-top Bot evU (FunEl g) ()
    finMem-from-U-top Bot evU (PiCode a0 f0) ()
    finMem-from-U-top Bot evU (SigmaCode a0 f0) ()
    finMem-from-U-top Bot evU (PairCode u0 v0) ()
    finMem-from-U-top UCode evU y fm = fm
    finMem-from-U-top PropCode (mkSigma _ ()) y fm
    finMem-from-U-top (FunEl g) (mkSigma _ ()) y fm
    finMem-from-U-top (PiCode a0 f0) (mkSigma _ ()) y fm
    finMem-from-U-top (SigmaCode a0 f0) (mkSigma _ ()) y fm
    finMem-from-U-top (PairCode u0 v0) (mkSigma _ ()) y fm

    b1U : FinMem b1 UCode
    b1U = finMem-from-U-top ab1 evU-ab1 b1 fm-b1

    a'U : FinMem a' UCode
    a'U = get-a'U f cf ew body
      where
        get-a'U : (g : FinFun) -> CoherentFunTail g ->
          ((p : Edge) -> EdgeIn p g ->
            Sigma FinEl (\ x -> Pair (LeCode x (fst p))
                                     (Pair (FinMem x a') (EvalRel B (extendEnv rho x) (snd p))))) ->
          ((u v : FinEl) -> Selection g u v ->
            Sigma FinEl (\ x -> Pair (LeCode x u)
                                     (Pair (FinMem x a') (EvalRel B (extendEnv rho x) v)))) ->
          FinMem a' UCode
        get-a'U nil _ _ rawBody =
          let w = rawBody Bot Bot sel-nil
          in FinMem-a-in-U (fst w) a' (fst (snd (snd w)))
        get-a'U (cons p ps) _ ew0 _ =
          let w = ew0 p here
          in FinMem-a-in-U (fst w) a' (fst (snd (snd w)))

    cb1 = coh-from-aU b1 b1U
    ca' = coh-from-aU a' a'U
    comp-a'-b1 : Comp a' b1
    comp-a'-b1 = EvalRel-Comp A rho crho a' b1 evA-a' evA-b1
    b_new = Sup a' b1
    b_newU : FinMem b_new UCode
    b_newU = finMemUCode-Sup a' b1 comp-a'-b1 a'U b1U
    cb_new = coh-from-aU b_new b_newU
    le-a'-b_new = LeCode-Sup-left a' b1 comp-a'-b1 ca' cb1
    le-b1-b_new = LeCode-Sup-right a' b1 comp-a'-b1 ca' cb1
    le-b-b_new = LeCode-trans b b1 b_new cb cb1 cb_new le-b-b1 le-b1-b_new
    evA-b_new = EvalRel-Sup A rho a' b1 crho ca' cb1 comp-a'-b1 evA-a' evA-b1

    finMem-from-U : (vi0 : FinEl) -> (x : FinEl) ->
      EvalRel U (extendEnv rho vi0) x -> (y : FinEl) -> FinMem y x -> FinMem y UCode
    finMem-from-U vi0 Bot evU Bot fm = tt
    finMem-from-U vi0 Bot evU UCode ()
    finMem-from-U vi0 Bot evU PropCode ()
    finMem-from-U vi0 Bot evU (FunEl g) ()
    finMem-from-U vi0 Bot evU (PiCode a0 f0) ()
    finMem-from-U vi0 Bot evU (SigmaCode a0 f0) ()
    finMem-from-U vi0 Bot evU (PairCode u0 v0) ()
    finMem-from-U vi0 UCode evU y fm = fm
    finMem-from-U vi0 PropCode (mkSigma _ ()) y fm
    finMem-from-U vi0 (FunEl g) (mkSigma _ ()) y fm
    finMem-from-U vi0 (PiCode a0 f0) (mkSigma _ ()) y fm
    finMem-from-U vi0 (SigmaCode a0 f0) (mkSigma _ ()) y fm
    finMem-from-U vi0 (PairCode u0 v0) (mkSigma _ ()) y fm

    edge-data : (p : Edge) -> EdgeIn p f ->
      Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
        Pair (LeCode xi (fst p))
        (Pair (FinMem xi a')
        (Pair (EvalRel B (extendEnv rho xi) (snd p))
        (Pair (LeCode (snd p) vi')
        (Pair (EvalRel B (extendEnv rho xi) vi')
              (FinMem vi' UCode)))))))
    edge-data p ein =
      let w    = ew p ein
          xi   = fst w
          le-xi = fst (snd w)
          fm-xi = fst (snd (snd w))
          evB-xi = snd (snd (snd w))
          typed-vi = body-ih xi a' fm-xi evA-a' (snd p) evB-xi
          vi' = fst typed-vi
          bvi = fst (snd typed-vi)
          le-vi = fst (snd (snd typed-vi))
          evB-vi' = fst (snd (snd (snd typed-vi)))
          fm-vi' = fst (snd (snd (snd (snd typed-vi))))
          evU-bvi = snd (snd (snd (snd (snd typed-vi))))
          vi'U = finMem-from-U xi bvi evU-bvi vi' fm-vi'
      in mkSigma xi (mkSigma vi'
           (mkSigma le-xi (mkSigma fm-xi (mkSigma evB-xi
             (mkSigma le-vi (mkSigma evB-vi' vi'U))))))

    new-edge : (p : Edge) -> EdgeIn p f -> Edge
    new-edge p ein =
      let d = edge-data p ein
      in mkSigma (fst d) (fst (snd d))

    f' : FinFun
    f' = mapEdges f new-edge

    f'-has : (p : Edge) -> (ein : EdgeIn p f) -> EdgeIn (new-edge p ein) f'
    f'-has p ein = mapEdges-corr f new-edge p ein

    -- Edgewise
    f'-ew : (e : Edge) -> EdgeIn e f' ->
      Pair (FinMem (fst e) b_new) (EvalRel B (extendEnv rho (fst e)) (snd e))
    f'-ew = me-ew f edge-data
      where
        me-ew : (g : FinFun) ->
          (ed : (p : Edge) -> EdgeIn p g ->
            Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
              Pair (LeCode xi (fst p))
              (Pair (FinMem xi a')
              (Pair (EvalRel B (extendEnv rho xi) (snd p))
              (Pair (LeCode (snd p) vi')
              (Pair (EvalRel B (extendEnv rho xi) vi')
                    (FinMem vi' UCode)))))))) ->
          (e : Edge) ->
          EdgeIn e (mapEdges g (\ p ein -> mkSigma (fst (ed p ein)) (fst (snd (ed p ein))))) ->
          Pair (FinMem (fst e) b_new) (EvalRel B (extendEnv rho (fst e)) (snd e))
        me-ew (cons p ps) ed .(mkSigma (fst (ed p here)) (fst (snd (ed p here)))) here =
          let d = ed p here
          in mkSigma (finMem-upward (fst d) a' b_new le-a'-b_new ca' cb_new
                        (fst (snd (snd (snd d)))) b_newU)
                     (fst (snd (snd (snd (snd (snd (snd d)))))))
        me-ew (cons p ps) ed e (there ein) =
          me-ew ps (\ q qin -> ed q (there qin)) e ein

    -- FinMemAllU f' b_new
    fmAllU-f' : FinMemAllU f' b_new
    fmAllU-f' = me-fmAllU f edge-data
      where
        me-fmAllU : (g : FinFun) ->
          (ed : (p : Edge) -> EdgeIn p g ->
            Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
              Pair (LeCode xi (fst p))
              (Pair (FinMem xi a')
              (Pair (EvalRel B (extendEnv rho xi) (snd p))
              (Pair (LeCode (snd p) vi')
              (Pair (EvalRel B (extendEnv rho xi) vi')
                    (FinMem vi' UCode)))))))) ->
          FinMemAllU (mapEdges g (\ p ein -> mkSigma (fst (ed p ein)) (fst (snd (ed p ein))))) b_new
        me-fmAllU nil ed = tt
        me-fmAllU (cons p ps) ed =
          let d = ed p here
              fm-xi = finMem-upward (fst d) a' b_new le-a'-b_new ca' cb_new
                        (fst (snd (snd (snd d)))) b_newU
              vi'U = snd (snd (snd (snd (snd (snd (snd d))))))
          in mkSigma (mkSigma fm-xi vi'U)
                     (me-fmAllU ps (\ q qin -> ed q (there qin)))

    -- CoherentWith / CoherentFunTail for mapEdges
    me-cw : (sk sv : FinEl) -> (rest : FinFun) ->
      Coherent sk -> CoherentFunTail rest ->
      EvalRel B (extendEnv rho sk) sv ->
      (ed : (q : Edge) -> EdgeIn q rest ->
        Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
          Pair (LeCode xi (fst q))
          (Pair (FinMem xi a')
          (Pair (EvalRel B (extendEnv rho xi) (snd q))
          (Pair (LeCode (snd q) vi')
          (Pair (EvalRel B (extendEnv rho xi) vi')
                (FinMem vi' UCode)))))))) ->
      CoherentWith (mkSigma sk sv)
        (mapEdges rest (\ q ein -> mkSigma (fst (ed q ein)) (fst (snd (ed q ein)))))
    me-cw sk sv nil csk crest evBsk ed = tt
    me-cw sk sv (cons t ts) csk crest evBsk ed =
      let dt  = ed t here
          xt  = fst dt
          vt' = fst (snd dt)
          evB-xt = fst (snd (snd (snd (snd (snd (snd dt))))))
          ct  = key-coh crest
          cxt = FinMem-coh-u xt a' (fst (snd (snd (snd dt))))
          step : Comp sk xt -> Comp sv vt'
          step ck = EvalRel-Comp-ext B rho sk xt sv vt'
                      crho ck csk cxt evBsk evB-xt
      in mkSigma step
           (me-cw sk sv ts csk (tail-coh crest) evBsk
             (\ q qin -> ed q (there qin)))

    me-cft : (g : FinFun) -> CoherentFunTail g ->
      (ed : (p : Edge) -> EdgeIn p g ->
        Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
          Pair (LeCode xi (fst p))
          (Pair (FinMem xi a')
          (Pair (EvalRel B (extendEnv rho xi) (snd p))
          (Pair (LeCode (snd p) vi')
          (Pair (EvalRel B (extendEnv rho xi) vi')
                (FinMem vi' UCode)))))))) ->
      CoherentFunTail (mapEdges g (\ p ein -> mkSigma (fst (ed p ein)) (fst (snd (ed p ein)))))
    me-cft nil cg ed = tt
    me-cft (cons p ps) cg ed =
      let dp    = ed p here
          xp    = fst dp
          vp'   = fst (snd dp)
          cxp   = FinMem-coh-u xp a' (fst (snd (snd (snd dp))))
          vp'U  = snd (snd (snd (snd (snd (snd (snd dp))))))
          cvp'  = coh-from-aU vp' vp'U
          ck    = key-coh cg
          cv    = val-coh cg
          nb    = val-nbot cg
          le-vp = fst (snd (snd (snd (snd (snd dp)))))
          nbvp' = NotBot-from-Le (snd p) vp' cv nb le-vp
          evB-vp' = fst (snd (snd (snd (snd (snd (snd dp))))))
          cw    = me-cw xp vp' ps cxp (tail-coh cg) evB-vp'
                    (\ q qin -> ed q (there qin))
          tail  = me-cft ps (tail-coh cg)
                    (\ q qin -> ed q (there qin))
      in mkCFT cxp cvp' nbvp' cw tail

    cft-f' : CoherentFunTail f'
    cft-f' = me-cft f cf edge-data

    cf-f' : CoherentFunTail f'
    cf-f' = cft-f'

    lf-f-f' : LeFunCode f f'
    lf-f-f' = me-lf-tail f cf (\ q qin -> qin)
      where
        cft-edge : {g : FinFun} -> CoherentFunTail g -> {e : Edge} ->
          EdgeIn e g -> CoherentFunTail (cons e nil)
        cft-edge {cons p ps} cg0 here = mkCFT (key-coh cg0) (val-coh cg0) (val-nbot cg0) tt tt
        cft-edge {cons p nil} cg0 (there ())
        cft-edge {cons p (cons q qs)} cg0 (there ein) =
          cft-edge (tail-coh cg0) ein

        me-lf-tail : (ps : FinFun) -> CoherentFunTail f ->
          (shift : (q : Edge) -> EdgeIn q ps -> EdgeIn q f) ->
          LeFunCode ps f'
        me-lf-tail nil cg0 shift = tt
        me-lf-tail (cons q qs) cg0 shift =
          let dq    = edge-data q (shift q here)
              xq    = fst dq
              vq'   = fst (snd dq)
              le-xq = fst (snd (snd dq))
              le-vq = fst (snd (snd (snd (snd (snd dq)))))
              ck-q  = key-coh (cft-edge cg0 (shift q here))
              cv-q  = val-coh (cft-edge cg0 (shift q here))
              ein-f' = mapEdges-corr f new-edge q (shift q here)
              head-le = EvalFun-edge-le (new-edge q (shift q here)) f' (fst q)
                          cft-f' ein-f' ck-q le-xq
              cvq'  = coh-from-aU vq' (snd (snd (snd (snd (snd (snd (snd dq)))))))
              cefg' = Coherent-EvalFun f' (fst q) cft-f' ck-q
              head  = LeCode-trans (snd q) vq' (EvalFun f' (fst q))
                        cv-q cvq' cefg' le-vq head-le
              tail  = me-lf-tail qs cg0 (\ r rin -> shift r (there rin))
          in mkSigma head tail

    evPi-new : EvalRel (Pi A B) rho (PiCode b_new f')
    evPi-new =
      let selbody : (u' v' : FinEl) -> Selection f' u' v' ->
            Sigma FinEl (\ x -> Pair (LeCode x u')
              (Pair (FinMem x b_new) (EvalRel B (extendEnv rho x) v')))
          selbody u' v' sel =
            replaceKeys-selection-body B rho b_new f' u' v' crho b_newU cft-f' f'-ew sel
      in mkSigma (mkSigma cb_new cf-f')
           (mkSigma evA-b_new (mkSigma b_new (mkSigma evA-b_new selbody)))

    fm-pi-U : FinMem (PiCode b_new f') UCode
    fm-pi-U = mkSigma b_newU (mkSigma fmAllU-f' cf-f')

    result : Typed (Pi A B) U rho (PiCode b f)
    result = mkSigma (PiCode b_new f') (mkSigma UCode
      (mkSigma (mkSigma le-b-b_new lf-f-f')
        (mkSigma evPi-new (mkSigma fm-pi-U (mkSigma tt tt)))))

------------------------------------------------------------------------
-- InvTyp-Sigma (mirrors InvTyp-Pi)
------------------------------------------------------------------------

InvTyp-Sigma : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n)) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G A U rho ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
    InvTyp (extend G A) B U (extendEnv rho x)) ->
  InvTyp G (RawSyntaxSigma.Sigma A B) U rho
InvTyp-Sigma A B rho fits invA body-ih Bot ev =
  mkSigma Bot (mkSigma UCode (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma tt tt)))))
InvTyp-Sigma A B rho fits invA body-ih UCode ()
InvTyp-Sigma A B rho fits invA body-ih PropCode ()
InvTyp-Sigma A B rho fits invA body-ih (FunEl g) ()
InvTyp-Sigma A B rho fits invA body-ih (PiCode a0 f0) ()
InvTyp-Sigma A B rho fits invA body-ih (PairCode u0 v0) ()
InvTyp-Sigma A B rho fits invA body-ih (SigmaCode b f) ev = result
  where
    crho = Fits-CoherentEnv rho fits
    coh   = fst ev
    cb    = fst coh
    cf    = snd coh
    evA-b = fst (snd ev)
    a'    = fst (snd (snd ev))
    evA-a' = fst (snd (snd (snd ev)))
    body  = snd (snd (snd (snd ev)))

    sew = Sigma-edgewise A B rho b f ev
    ew : (p : Edge) -> EdgeIn p f ->
      Sigma FinEl (\ x -> Pair (LeCode x (fst p))
                               (Pair (FinMem x a') (EvalRel B (extendEnv rho x) (snd p))))
    ew = snd (snd (snd (snd sew)))

    typed-b = invA b evA-b
    b1    = fst typed-b
    ab1   = fst (snd typed-b)
    le-b-b1 = fst (snd (snd typed-b))
    evA-b1 = fst (snd (snd (snd typed-b)))
    fm-b1  = fst (snd (snd (snd (snd typed-b))))
    evU-ab1 = snd (snd (snd (snd (snd typed-b))))

    finMem-from-U-top : (x : FinEl) -> EvalRel U rho x ->
      (y : FinEl) -> FinMem y x -> FinMem y UCode
    finMem-from-U-top Bot evU Bot fm = tt
    finMem-from-U-top Bot evU UCode ()
    finMem-from-U-top Bot evU PropCode ()
    finMem-from-U-top Bot evU (FunEl g) ()
    finMem-from-U-top Bot evU (PiCode a0 f0) ()
    finMem-from-U-top Bot evU (SigmaCode a0 f0) ()
    finMem-from-U-top Bot evU (PairCode u0 v0) ()
    finMem-from-U-top UCode evU y fm = fm
    finMem-from-U-top PropCode (mkSigma _ ()) y fm
    finMem-from-U-top (FunEl g) (mkSigma _ ()) y fm
    finMem-from-U-top (PiCode a0 f0) (mkSigma _ ()) y fm
    finMem-from-U-top (SigmaCode a0 f0) (mkSigma _ ()) y fm
    finMem-from-U-top (PairCode u0 v0) (mkSigma _ ()) y fm

    b1U = finMem-from-U-top ab1 evU-ab1 b1 fm-b1

    a'U : FinMem a' UCode
    a'U = get-a'U f cf ew body
      where
        get-a'U : (g : FinFun) -> CoherentFunTail g ->
          ((p : Edge) -> EdgeIn p g ->
            Sigma FinEl (\ x -> Pair (LeCode x (fst p))
                                     (Pair (FinMem x a') (EvalRel B (extendEnv rho x) (snd p))))) ->
          ((u v : FinEl) -> Selection g u v ->
            Sigma FinEl (\ x -> Pair (LeCode x u)
                                     (Pair (FinMem x a') (EvalRel B (extendEnv rho x) v)))) ->
          FinMem a' UCode
        get-a'U nil _ _ rawBody =
          let w = rawBody Bot Bot sel-nil
          in FinMem-a-in-U (fst w) a' (fst (snd (snd w)))
        get-a'U (cons p ps) _ ew0 _ =
          let w = ew0 p here
          in FinMem-a-in-U (fst w) a' (fst (snd (snd w)))

    cb1 = coh-from-aU b1 b1U
    ca' = coh-from-aU a' a'U
    comp-a'-b1 = EvalRel-Comp A rho crho a' b1 evA-a' evA-b1
    b_new = Sup a' b1
    b_newU = finMemUCode-Sup a' b1 comp-a'-b1 a'U b1U
    cb_new = coh-from-aU b_new b_newU
    le-a'-b_new = LeCode-Sup-left a' b1 comp-a'-b1 ca' cb1
    le-b1-b_new = LeCode-Sup-right a' b1 comp-a'-b1 ca' cb1
    le-b-b_new = LeCode-trans b b1 b_new cb cb1 cb_new le-b-b1 le-b1-b_new
    evA-b_new = EvalRel-Sup A rho a' b1 crho ca' cb1 comp-a'-b1 evA-a' evA-b1

    finMem-from-U : (vi0 : FinEl) -> (x : FinEl) ->
      EvalRel U (extendEnv rho vi0) x -> (y : FinEl) -> FinMem y x -> FinMem y UCode
    finMem-from-U vi0 Bot evU Bot fm = tt
    finMem-from-U vi0 Bot evU UCode ()
    finMem-from-U vi0 Bot evU PropCode ()
    finMem-from-U vi0 Bot evU (FunEl g) ()
    finMem-from-U vi0 Bot evU (PiCode a0 f0) ()
    finMem-from-U vi0 Bot evU (SigmaCode a0 f0) ()
    finMem-from-U vi0 Bot evU (PairCode u0 v0) ()
    finMem-from-U vi0 UCode evU y fm = fm
    finMem-from-U vi0 PropCode (mkSigma _ ()) y fm
    finMem-from-U vi0 (FunEl g) (mkSigma _ ()) y fm
    finMem-from-U vi0 (PiCode a0 f0) (mkSigma _ ()) y fm
    finMem-from-U vi0 (SigmaCode a0 f0) (mkSigma _ ()) y fm
    finMem-from-U vi0 (PairCode u0 v0) (mkSigma _ ()) y fm

    edge-data : (p : Edge) -> EdgeIn p f ->
      Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
        Pair (LeCode xi (fst p))
        (Pair (FinMem xi a')
        (Pair (EvalRel B (extendEnv rho xi) (snd p))
        (Pair (LeCode (snd p) vi')
        (Pair (EvalRel B (extendEnv rho xi) vi')
              (FinMem vi' UCode)))))))
    edge-data p ein =
      let w    = ew p ein
          xi   = fst w
          le-xi = fst (snd w)
          fm-xi = fst (snd (snd w))
          evB-xi = snd (snd (snd w))
          typed-vi = body-ih xi a' fm-xi evA-a' (snd p) evB-xi
          vi' = fst typed-vi
          bvi = fst (snd typed-vi)
          le-vi = fst (snd (snd typed-vi))
          evB-vi' = fst (snd (snd (snd typed-vi)))
          fm-vi' = fst (snd (snd (snd (snd typed-vi))))
          evU-bvi = snd (snd (snd (snd (snd typed-vi))))
          vi'U = finMem-from-U xi bvi evU-bvi vi' fm-vi'
      in mkSigma xi (mkSigma vi'
           (mkSigma le-xi (mkSigma fm-xi (mkSigma evB-xi
             (mkSigma le-vi (mkSigma evB-vi' vi'U))))))

    new-edge : (p : Edge) -> EdgeIn p f -> Edge
    new-edge p ein =
      let d = edge-data p ein
      in mkSigma (fst d) (fst (snd d))

    f' = mapEdges f new-edge

    f'-ew : (e : Edge) -> EdgeIn e f' ->
      Pair (FinMem (fst e) b_new) (EvalRel B (extendEnv rho (fst e)) (snd e))
    f'-ew = me-ew f edge-data
      where
        me-ew : (g : FinFun) ->
          (ed : (p : Edge) -> EdgeIn p g ->
            Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
              Pair (LeCode xi (fst p))
              (Pair (FinMem xi a')
              (Pair (EvalRel B (extendEnv rho xi) (snd p))
              (Pair (LeCode (snd p) vi')
              (Pair (EvalRel B (extendEnv rho xi) vi')
                    (FinMem vi' UCode)))))))) ->
          (e : Edge) ->
          EdgeIn e (mapEdges g (\ p ein -> mkSigma (fst (ed p ein)) (fst (snd (ed p ein))))) ->
          Pair (FinMem (fst e) b_new) (EvalRel B (extendEnv rho (fst e)) (snd e))
        me-ew (cons p ps) ed .(mkSigma (fst (ed p here)) (fst (snd (ed p here)))) here =
          let d = ed p here
          in mkSigma (finMem-upward (fst d) a' b_new le-a'-b_new ca' cb_new
                        (fst (snd (snd (snd d)))) b_newU)
                     (fst (snd (snd (snd (snd (snd (snd d)))))))
        me-ew (cons p ps) ed e (there ein) =
          me-ew ps (\ q qin -> ed q (there qin)) e ein

    fmAllU-f' : FinMemAllU f' b_new
    fmAllU-f' = me-fmAllU f edge-data
      where
        me-fmAllU : (g : FinFun) ->
          (ed : (p : Edge) -> EdgeIn p g ->
            Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
              Pair (LeCode xi (fst p))
              (Pair (FinMem xi a')
              (Pair (EvalRel B (extendEnv rho xi) (snd p))
              (Pair (LeCode (snd p) vi')
              (Pair (EvalRel B (extendEnv rho xi) vi')
                    (FinMem vi' UCode)))))))) ->
          FinMemAllU (mapEdges g (\ p ein -> mkSigma (fst (ed p ein)) (fst (snd (ed p ein))))) b_new
        me-fmAllU nil ed = tt
        me-fmAllU (cons p ps) ed =
          let d = ed p here
              fm-xi = finMem-upward (fst d) a' b_new le-a'-b_new ca' cb_new
                        (fst (snd (snd (snd d)))) b_newU
              vi'U = snd (snd (snd (snd (snd (snd (snd d))))))
          in mkSigma (mkSigma fm-xi vi'U)
                     (me-fmAllU ps (\ q qin -> ed q (there qin)))

    me-cw : (sk sv : FinEl) -> (rest : FinFun) ->
      Coherent sk -> CoherentFunTail rest ->
      EvalRel B (extendEnv rho sk) sv ->
      (ed : (q : Edge) -> EdgeIn q rest ->
        Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
          Pair (LeCode xi (fst q))
          (Pair (FinMem xi a')
          (Pair (EvalRel B (extendEnv rho xi) (snd q))
          (Pair (LeCode (snd q) vi')
          (Pair (EvalRel B (extendEnv rho xi) vi')
                (FinMem vi' UCode)))))))) ->
      CoherentWith (mkSigma sk sv)
        (mapEdges rest (\ q ein -> mkSigma (fst (ed q ein)) (fst (snd (ed q ein)))))
    me-cw sk sv nil csk crest evBsk ed = tt
    me-cw sk sv (cons t ts) csk crest evBsk ed =
      let dt  = ed t here
          xt  = fst dt
          vt' = fst (snd dt)
          evB-xt = fst (snd (snd (snd (snd (snd (snd dt))))))
          ct  = key-coh crest
          cxt = FinMem-coh-u xt a' (fst (snd (snd (snd dt))))
          step : Comp sk xt -> Comp sv vt'
          step ck = EvalRel-Comp-ext B rho sk xt sv vt'
                      crho ck csk cxt evBsk evB-xt
      in mkSigma step
           (me-cw sk sv ts csk (tail-coh crest) evBsk
             (\ q qin -> ed q (there qin)))

    me-cft : (g : FinFun) -> CoherentFunTail g ->
      (ed : (p : Edge) -> EdgeIn p g ->
        Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
          Pair (LeCode xi (fst p))
          (Pair (FinMem xi a')
          (Pair (EvalRel B (extendEnv rho xi) (snd p))
          (Pair (LeCode (snd p) vi')
          (Pair (EvalRel B (extendEnv rho xi) vi')
                (FinMem vi' UCode)))))))) ->
      CoherentFunTail (mapEdges g (\ p ein -> mkSigma (fst (ed p ein)) (fst (snd (ed p ein)))))
    me-cft nil cg ed = tt
    me-cft (cons p ps) cg ed =
      let dp    = ed p here
          xp    = fst dp
          vp'   = fst (snd dp)
          cxp   = FinMem-coh-u xp a' (fst (snd (snd (snd dp))))
          vp'U  = snd (snd (snd (snd (snd (snd (snd dp))))))
          cvp'  = coh-from-aU vp' vp'U
          ck    = key-coh cg
          cv    = val-coh cg
          nb    = val-nbot cg
          le-vp = fst (snd (snd (snd (snd (snd dp)))))
          nbvp' = NotBot-from-Le (snd p) vp' cv nb le-vp
          evB-vp' = fst (snd (snd (snd (snd (snd (snd dp))))))
          cw    = me-cw xp vp' ps cxp (tail-coh cg) evB-vp'
                    (\ q qin -> ed q (there qin))
          tail  = me-cft ps (tail-coh cg)
                    (\ q qin -> ed q (there qin))
      in mkCFT cxp cvp' nbvp' cw tail

    cft-f' = me-cft f cf edge-data
    cf-f' = cft-f'

    lf-f-f' : LeFunCode f f'
    lf-f-f' = me-lf-tail f cf (\ q qin -> qin)
      where
        cft-edge : {g : FinFun} -> CoherentFunTail g -> {e : Edge} ->
          EdgeIn e g -> CoherentFunTail (cons e nil)
        cft-edge {cons p ps} cg0 here = mkCFT (key-coh cg0) (val-coh cg0) (val-nbot cg0) tt tt
        cft-edge {cons p nil} cg0 (there ())
        cft-edge {cons p (cons q qs)} cg0 (there ein) =
          cft-edge (tail-coh cg0) ein

        me-lf-tail : (ps : FinFun) -> CoherentFunTail f ->
          (shift : (q : Edge) -> EdgeIn q ps -> EdgeIn q f) ->
          LeFunCode ps f'
        me-lf-tail nil cg0 shift = tt
        me-lf-tail (cons q qs) cg0 shift =
          let dq    = edge-data q (shift q here)
              xq    = fst dq
              vq'   = fst (snd dq)
              le-xq = fst (snd (snd dq))
              le-vq = fst (snd (snd (snd (snd (snd dq)))))
              ck-q  = key-coh (cft-edge cg0 (shift q here))
              cv-q  = val-coh (cft-edge cg0 (shift q here))
              ein-f' = mapEdges-corr f new-edge q (shift q here)
              head-le = EvalFun-edge-le (new-edge q (shift q here)) f' (fst q)
                          cft-f' ein-f' ck-q le-xq
              cvq'  = coh-from-aU vq' (snd (snd (snd (snd (snd (snd (snd dq)))))))
              cefg' = Coherent-EvalFun f' (fst q) cft-f' ck-q
              head  = LeCode-trans (snd q) vq' (EvalFun f' (fst q))
                        cv-q cvq' cefg' le-vq head-le
              tail  = me-lf-tail qs cg0 (\ r rin -> shift r (there rin))
          in mkSigma head tail

    evSigma-new : EvalRel (RawSyntaxSigma.Sigma A B) rho (SigmaCode b_new f')
    evSigma-new =
      let selbody : (u' v' : FinEl) -> Selection f' u' v' ->
            Sigma FinEl (\ x -> Pair (LeCode x u')
              (Pair (FinMem x b_new) (EvalRel B (extendEnv rho x) v')))
          selbody u' v' sel =
            replaceKeys-selection-body B rho b_new f' u' v' crho b_newU cft-f' f'-ew sel
      in mkSigma (mkSigma cb_new cf-f')
           (mkSigma evA-b_new (mkSigma b_new (mkSigma evA-b_new selbody)))

    fm-sigma-U : FinMem (SigmaCode b_new f') UCode
    fm-sigma-U = mkSigma b_newU (mkSigma fmAllU-f' cf-f')

    result : Typed (RawSyntaxSigma.Sigma A B) U rho (SigmaCode b f)
    result = mkSigma (SigmaCode b_new f') (mkSigma UCode
      (mkSigma (mkSigma le-b-b_new lf-f-f')
        (mkSigma evSigma-new (mkSigma fm-sigma-U (mkSigma tt tt)))))

------------------------------------------------------------------------
-- InvTyp-MkPair
------------------------------------------------------------------------

InvTyp-MkPair : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M N : Expr n) (rho : EnvApprox n) ->
  Fits G rho ->
  InvTyp G A U rho ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
    InvTyp (extend G A) B U (extendEnv rho x)) ->
  InvTyp G M A rho ->
  InvTyp G N (subst1 B M) rho ->
  InvTyp G (MkPair M N) (RawSyntaxSigma.Sigma A B) rho
InvTyp-MkPair A B M N rho fits invTypA body-ih invM invN Bot ev =
  mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt))))
InvTyp-MkPair A B M N rho fits invTypA body-ih invM invN UCode ()
InvTyp-MkPair A B M N rho fits invTypA body-ih invM invN PropCode ()
InvTyp-MkPair A B M N rho fits invTypA body-ih invM invN (FunEl g) ()
InvTyp-MkPair A B M N rho fits invTypA body-ih invM invN (PiCode a0 f0) ()
InvTyp-MkPair A B M N rho fits invTypA body-ih invM invN (SigmaCode a0 f0) ()
InvTyp-MkPair A B M N rho fits invTypA body-ih invM invN (PairCode u0 v0) ev =
  mkpair-dispatch u0 v0 ev
  where
    crho = Fits-CoherentEnv rho fits

    -- Case v0 = Bot: simplified construction with nil graph
    mkpair-v0bot : (u0 : FinEl) ->
      EvalRel (MkPair M N) rho (PairCode u0 Bot) ->
      Typed (MkPair M N) (RawSyntaxSigma.Sigma A B) rho (PairCode u0 Bot)
    mkpair-v0bot u0 ev0 = result-v0bot
      where
        coh-pair = fst ev0
        cu0   = fst (fst coh-pair)
        or-nb = snd coh-pair
        evM-u0 = fst (snd ev0)

        nb-u0 : NotBot u0
        nb-u0 = or-elim or-nb
          where
            or-elim : Or (NotBot u0) Empty -> NotBot u0
            or-elim (inl x) = x

        typed-M = invM u0 evM-u0
        u0'    = fst typed-M
        a'     = fst (snd typed-M)
        le-u0  = fst (snd (snd typed-M))
        evM-u0' = fst (snd (snd (snd typed-M)))
        fm-u0' = fst (snd (snd (snd (snd typed-M))))
        evA-a' = snd (snd (snd (snd (snd typed-M))))

        a'U    = FinMem-a-in-U u0' a' fm-u0'
        ca'    = coh-from-aU a' a'U
        cu0'   = FinMem-coh-u u0' a' fm-u0'
        nb-u0' = NotBot-from-Le u0 u0' cu0 nb-u0 le-u0

        coh-pair' : Coherent (PairCode u0' Bot)
        coh-pair' = mkSigma (mkSigma cu0' tt) (inl nb-u0')

        evMkPair-u0' : EvalRel (MkPair M N) rho (PairCode u0' Bot)
        evMkPair-u0' = mkSigma coh-pair' (mkSigma evM-u0' (EvalRel-Bot N rho))

        coh-sig : Coherent (SigmaCode a' nil)
        coh-sig = mkSigma ca' tt

        fm-pair-sig : FinMem (PairCode u0' Bot) (SigmaCode a' nil)
        fm-pair-sig = mkSigma (mkSigma fm-u0' tt) (mkSigma coh-pair' (mkSigma a'U (mkSigma tt tt)))

        sel-body-nil : (u v : FinEl) -> Selection nil u v ->
          Sigma FinEl (\ x -> Pair (LeCode x u) (Pair (FinMem x a') (EvalRel B (extendEnv rho x) v)))
        sel-body-nil .Bot .Bot sel-nil =
          mkSigma Bot (mkSigma tt (mkSigma a'U (EvalRel-Bot B (extendEnv rho Bot))))

        evSig : EvalRel (RawSyntaxSigma.Sigma A B) rho (SigmaCode a' nil)
        evSig = mkSigma coh-sig (mkSigma evA-a' (mkSigma a' (mkSigma evA-a' sel-body-nil)))

        result-v0bot : Typed (MkPair M N) (RawSyntaxSigma.Sigma A B) rho (PairCode u0 Bot)
        result-v0bot = mkSigma (PairCode u0' Bot) (mkSigma (SigmaCode a' nil)
          (mkSigma (mkSigma le-u0 tt) (mkSigma evMkPair-u0' (mkSigma fm-pair-sig evSig))))

    -- Case v0 NotBot: full construction with singleton graph
    mkpair-nonbot : (u0 v0 : FinEl) -> NotBot v0 ->
      EvalRel (MkPair M N) rho (PairCode u0 v0) ->
      Typed (MkPair M N) (RawSyntaxSigma.Sigma A B) rho (PairCode u0 v0)
    mkpair-nonbot u0 v0 nb-v0 ev0 = result-main
      where
        coh-pair = fst ev0
        cu0   = fst (fst coh-pair)
        cv0   = snd (fst coh-pair)
        evM-u0 = fst (snd ev0)
        evN-v0 = snd (snd ev0)

        typed-M = invM u0 evM-u0
        u0'    = fst typed-M
        a'     = fst (snd typed-M)
        le-u0  = fst (snd (snd typed-M))
        evM-u0' = fst (snd (snd (snd typed-M)))
        fm-u0' = fst (snd (snd (snd (snd typed-M))))
        evA-a' = snd (snd (snd (snd (snd typed-M))))

        typed-N = invN v0 evN-v0
        v0'    = fst typed-N
        bm'    = fst (snd typed-N)
        le-v0  = fst (snd (snd typed-N))
        evN-v0' = fst (snd (snd (snd typed-N)))
        fm-v0' = fst (snd (snd (snd (snd typed-N))))
        evBM-bm' = snd (snd (snd (snd (snd typed-N))))

        a'U    = FinMem-a-in-U u0' a' fm-u0'
        ca'    = coh-from-aU a' a'U
        cu0'   = FinMem-coh-u u0' a' fm-u0'
        cv0'   = EvalRel-coh N rho v0' evN-v0'
        nb-v0' = NotBot-from-Le v0 v0' cv0 nb-v0 le-v0
        nb-bm' = NotBot-from-FinMem v0' bm' nb-v0' fm-v0'

        -- Forward substitution
        fwd    = EvalRel-subst1-forward B M rho bm' crho evBM-bm'
        v-wit  = fst fwd
        evM-vwit = fst (snd fwd)
        evB-vwit-bm' = snd (snd fwd)

        -- invM on v-wit
        typed-vwit = invM v-wit evM-vwit
        vw-up  = fst typed-vwit
        a-vw   = fst (snd typed-vwit)
        le-vwit = fst (snd (snd typed-vwit))
        evM-vwup = fst (snd (snd (snd typed-vwit)))
        fm-vwup = fst (snd (snd (snd (snd typed-vwit))))
        evA-avw = snd (snd (snd (snd (snd typed-vwit))))

        a-vwU  = FinMem-a-in-U vw-up a-vw fm-vwup
        ca-vw  = coh-from-aU a-vw a-vwU
        cvwup  = FinMem-coh-u vw-up a-vw fm-vwup
        cvwit  = EvalRel-coh M rho v-wit evM-vwit

        -- u-big = Sup u0' vw-up
        comp-M = EvalRel-Comp M rho crho u0' vw-up evM-u0' evM-vwup
        u-big  = Sup u0' vw-up
        cu-big = Coherent-Sup u0' vw-up comp-M cu0' cvwup
        le-u0'-ubig = LeCode-Sup-left u0' vw-up comp-M cu0' cvwup
        le-vwup-ubig = LeCode-Sup-right u0' vw-up comp-M cu0' cvwup
        evM-ubig = EvalRel-Sup M rho u0' vw-up crho cu0' cvwup comp-M evM-u0' evM-vwup

        -- a-big = Sup a' a-vw
        comp-A = EvalRel-Comp A rho crho a' a-vw evA-a' evA-avw
        a-big  = Sup a' a-vw
        a-bigU = finMemUCode-Sup a' a-vw comp-A a'U a-vwU
        ca-big = coh-from-aU a-big a-bigU
        le-a'-abig = LeCode-Sup-left a' a-vw comp-A ca' ca-vw
        evA-abig = EvalRel-Sup A rho a' a-vw crho ca' ca-vw comp-A evA-a' evA-avw

        -- FinMem u-big a-big
        fm-u0'-abig = finMem-upward u0' a' a-big le-a'-abig ca' ca-big fm-u0' a-bigU
        fm-vwup-abig = finMem-upward vw-up a-vw a-big
          (LeCode-Sup-right a' a-vw comp-A ca' ca-vw) ca-vw ca-big fm-vwup a-bigU
        fm-ubig-abig = FinMem-Sup-element u0' vw-up a-big comp-M ca-big fm-u0'-abig fm-vwup-abig

        -- Transport evB to u-big env
        le-vwit-ubig = LeCode-trans v-wit vw-up u-big cvwit cvwup cu-big le-vwit le-vwup-ubig
        envle-vwit-ubig : EnvLe (extendEnv rho v-wit) (extendEnv rho u-big)
        envle-vwit-ubig = mkSigma (EnvLe-refl rho crho) (mkSigma cvwit (mkSigma cu-big le-vwit-ubig))
        evB-ubig-bm' = EvalRel-mon-env B (extendEnv rho v-wit) (extendEnv rho u-big)
          bm' evB-vwit-bm' envle-vwit-ubig

        -- body-ih at u-big
        bodyInv = body-ih u-big a-big fm-ubig-abig evA-abig
        bodyTyped = bodyInv bm' evB-ubig-bm'
        bm''   = fst bodyTyped
        ucode-bm = fst (snd bodyTyped)
        le-bm' = fst (snd (snd bodyTyped))
        evB-ubig-bm'' = fst (snd (snd (snd bodyTyped)))
        fm-bm'' = fst (snd (snd (snd (snd bodyTyped))))
        evU-ucbm = snd (snd (snd (snd (snd bodyTyped))))

        finMem-from-U : (x : FinEl) -> EvalRel U (extendEnv rho u-big) x ->
          (y : FinEl) -> FinMem y x -> FinMem y UCode
        finMem-from-U Bot evU Bot fm = tt
        finMem-from-U Bot evU UCode ()
        finMem-from-U Bot evU PropCode ()
        finMem-from-U Bot evU (FunEl g) ()
        finMem-from-U Bot evU (PiCode a1 f1) ()
        finMem-from-U Bot evU (SigmaCode a1 f1) ()
        finMem-from-U Bot evU (PairCode u1 v1) ()
        finMem-from-U UCode evU y fm = fm
        finMem-from-U PropCode (mkSigma _ ()) y fm
        finMem-from-U (FunEl g) (mkSigma _ ()) y fm
        finMem-from-U (PiCode a1 f1) (mkSigma _ ()) y fm
        finMem-from-U (SigmaCode a1 f1) (mkSigma _ ()) y fm
        finMem-from-U (PairCode u1 v1) (mkSigma _ ()) y fm

        bm''U  = finMem-from-U ucode-bm evU-ucbm bm'' fm-bm''
        cbm''  = coh-from-aU bm'' bm''U
        cbm'   = EvalRel-coh (subst1 B M) rho bm' evBM-bm'
        nb-bm'' = NotBot-from-Le bm' bm''
          (EvalRel-coh B (extendEnv rho u-big) bm' evB-ubig-bm') nb-bm' le-bm'

        -- f-code = singleton (u-big, bm'')
        f-code = cons (mkSigma u-big bm'') nil

        cft-fcode : CoherentFunTail f-code
        cft-fcode = mkCFT cu-big cbm'' nb-bm'' tt tt

        fmAllU-fcode : FinMemAllU f-code a-big
        fmAllU-fcode = mkSigma (mkSigma fm-ubig-abig bm''U) tt

        fm-sig-U : FinMem (SigmaCode a-big f-code) UCode
        fm-sig-U = mkSigma a-bigU (mkSigma fmAllU-fcode cft-fcode)

        coh-sig : Coherent (SigmaCode a-big f-code)
        coh-sig = mkSigma ca-big cft-fcode

        -- EvalFun f-code u-big >= bm''
        le-bm''-ef : LeCode bm'' (EvalFun f-code u-big)
        le-bm''-ef = EvalFun-edge-le (mkSigma u-big bm'') f-code u-big
          cft-fcode here cu-big (LeCode-refl u-big cu-big)

        cef = Coherent-EvalFun f-code u-big cft-fcode cu-big
        fm-v0'-bm'' = finMem-upward v0' bm' bm'' le-bm' cbm' cbm'' fm-v0' bm''U
        fm-v0'-ef = finMem-upward v0' bm'' (EvalFun f-code u-big) le-bm''-ef cbm'' cef fm-v0'-bm''
          (EvalFun-in-UCode f-code u-big a-big cft-fcode cu-big fmAllU-fcode)

        coh-pair' : Coherent (PairCode u-big v0')
        coh-pair' = mkSigma (mkSigma cu-big cv0') (inr nb-v0')

        fm-pair-sig : FinMem (PairCode u-big v0') (SigmaCode a-big f-code)
        fm-pair-sig = mkSigma (mkSigma fm-ubig-abig fm-v0'-ef) (mkSigma coh-pair' fm-sig-U)

        evMkPair : EvalRel (MkPair M N) rho (PairCode u-big v0')
        evMkPair = mkSigma coh-pair' (mkSigma evM-ubig evN-v0')

        ew-fcode : (e : Edge) -> EdgeIn e f-code ->
          Pair (FinMem (fst e) a-big) (EvalRel B (extendEnv rho (fst e)) (snd e))
        ew-fcode .(mkSigma u-big bm'') here = mkSigma fm-ubig-abig evB-ubig-bm''

        sel-body : (u v : FinEl) -> Selection f-code u v ->
          Sigma FinEl (\ x -> Pair (LeCode x u) (Pair (FinMem x a-big) (EvalRel B (extendEnv rho x) v)))
        sel-body u v sel = replaceKeys-selection-body B rho a-big f-code u v crho a-bigU cft-fcode ew-fcode sel

        evSig : EvalRel (RawSyntaxSigma.Sigma A B) rho (SigmaCode a-big f-code)
        evSig = mkSigma coh-sig (mkSigma evA-abig (mkSigma a-big (mkSigma evA-abig sel-body)))

        le-pair : LeCode (PairCode u0 v0) (PairCode u-big v0')
        le-pair = mkSigma (LeCode-trans u0 u0' u-big cu0 cu0' cu-big le-u0 le-u0'-ubig) le-v0

        result-main : Typed (MkPair M N) (RawSyntaxSigma.Sigma A B) rho (PairCode u0 v0)
        result-main = mkSigma (PairCode u-big v0') (mkSigma (SigmaCode a-big f-code)
          (mkSigma le-pair (mkSigma evMkPair (mkSigma fm-pair-sig evSig))))

    -- Dispatch on v0
    mkpair-dispatch : (u0 v0 : FinEl) ->
      EvalRel (MkPair M N) rho (PairCode u0 v0) ->
      Typed (MkPair M N) (RawSyntaxSigma.Sigma A B) rho (PairCode u0 v0)
    mkpair-dispatch u0 Bot ev0 = mkpair-v0bot u0 ev0
    mkpair-dispatch u0 UCode ev0 = mkpair-nonbot u0 UCode tt ev0
    mkpair-dispatch u0 PropCode ev0 = mkpair-nonbot u0 PropCode tt ev0
    mkpair-dispatch u0 (FunEl g) ev0 = mkpair-nonbot u0 (FunEl g) tt ev0
    mkpair-dispatch u0 (PiCode a1 f1) ev0 = mkpair-nonbot u0 (PiCode a1 f1) tt ev0
    mkpair-dispatch u0 (SigmaCode a1 f1) ev0 = mkpair-nonbot u0 (SigmaCode a1 f1) tt ev0
    mkpair-dispatch u0 (PairCode u1 v1) ev0 = mkpair-nonbot u0 (PairCode u1 v1) tt ev0

------------------------------------------------------------------------
-- InvTyp-Fst
------------------------------------------------------------------------

InvTyp-Fst : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M : Expr n) (rho : EnvApprox n) ->
  Fits G rho ->
  InvTyp G M (RawSyntaxSigma.Sigma A B) rho ->
  InvTyp G (Fst M) A rho
InvTyp-Fst A B M rho fits invM = invTyp-Fst-aux
  where
    crho = Fits-CoherentEnv rho fits

    mkFstEv : (u' v' : FinEl) ->
      EvalRel M rho (PairCode u' v') -> EvalRel (Fst M) rho u'
    mkFstEv Bot v' evM = tt
    mkFstEv UCode v' evM = mkSigma v' evM
    mkFstEv PropCode v' evM = mkSigma v' evM
    mkFstEv (FunEl g) v' evM = mkSigma v' evM
    mkFstEv (PiCode a0 f0) v' evM = mkSigma v' evM
    mkFstEv (SigmaCode a0 f0) v' evM = mkSigma v' evM
    mkFstEv (PairCode u0 v0) v' evM = mkSigma v' evM

    fst-h-case : (u v : FinEl) -> NotBot u ->
      EvalRel M rho (PairCode u v) ->
      (w sigaf : FinEl) ->
      LeCode (PairCode u v) w ->
      EvalRel M rho w ->
      FinMem w sigaf ->
      EvalRel (RawSyntaxSigma.Sigma A B) rho sigaf ->
      Typed (Fst M) A rho u
    fst-h-case u v nbu evM-pair Bot sigaf () evM-w fm-w evSig
    fst-h-case u v nbu evM-pair UCode sigaf () evM-w fm-w evSig
    fst-h-case u v nbu evM-pair PropCode sigaf () evM-w fm-w evSig
    fst-h-case u v nbu evM-pair (FunEl _) sigaf () evM-w fm-w evSig
    fst-h-case u v nbu evM-pair (PiCode _ _) sigaf () evM-w fm-w evSig
    fst-h-case u v nbu evM-pair (SigmaCode _ _) sigaf () evM-w fm-w evSig
    fst-h-case u v nbu evM-pair (PairCode u' v') Bot le-pv evM-w () evSig
    fst-h-case u v nbu evM-pair (PairCode u' v') UCode le-pv evM-w () evSig
    fst-h-case u v nbu evM-pair (PairCode u' v') PropCode le-pv evM-w () evSig
    fst-h-case u v nbu evM-pair (PairCode u' v') (FunEl _) le-pv evM-w () evSig
    fst-h-case u v nbu evM-pair (PairCode u' v') (PiCode _ _) le-pv evM-w () evSig
    fst-h-case u v nbu evM-pair (PairCode u' v') (PairCode _ _) le-pv evM-w () evSig
    fst-h-case u v nbu evM-pair (PairCode u' v') (SigmaCode a f) le-pv evM-w fm-w evSig =
      let le-u-u' = fst le-pv
          fm-u'-a = fst (fst fm-w)
          evA-a = fst (snd evSig)
          evFst-u' = mkFstEv u' v' evM-w
      in mkSigma u' (mkSigma a
           (mkSigma le-u-u' (mkSigma evFst-u' (mkSigma fm-u'-a evA-a))))

    fst-main : (u v : FinEl) -> NotBot u ->
      EvalRel M rho (PairCode u v) ->
      Typed (Fst M) A rho u
    fst-main u v nbu evM-pair =
      let typed = invM (PairCode u v) evM-pair
          w     = fst typed
          sigaf = fst (snd typed)
          le-pv = fst (snd (snd typed))
          evM-w = fst (snd (snd (snd typed)))
          fm-w  = fst (snd (snd (snd (snd typed))))
          evSig = snd (snd (snd (snd (snd typed))))
      in fst-h-case u v nbu evM-pair w sigaf le-pv evM-w fm-w evSig

    invTyp-Fst-aux : (u : FinEl) -> EvalRel (Fst M) rho u ->
      Typed (Fst M) A rho u
    invTyp-Fst-aux Bot ev =
      mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt (EvalRel-Bot A rho)))))
    invTyp-Fst-aux UCode ev =
      let v = fst ev ; evM-pair = snd ev
      in fst-main UCode v tt evM-pair
    invTyp-Fst-aux PropCode ev =
      let v = fst ev ; evM-pair = snd ev
      in fst-main PropCode v tt evM-pair
    invTyp-Fst-aux (FunEl g) ev =
      let v = fst ev ; evM-pair = snd ev
      in fst-main (FunEl g) v tt evM-pair
    invTyp-Fst-aux (PiCode a0 f0) ev =
      let v = fst ev ; evM-pair = snd ev
      in fst-main (PiCode a0 f0) v tt evM-pair
    invTyp-Fst-aux (SigmaCode a0 f0) ev =
      let v = fst ev ; evM-pair = snd ev
      in fst-main (SigmaCode a0 f0) v tt evM-pair
    invTyp-Fst-aux (PairCode u0 v0) ev =
      let v = fst ev ; evM-pair = snd ev
      in fst-main (PairCode u0 v0) v tt evM-pair

------------------------------------------------------------------------
-- InvTyp-Snd
------------------------------------------------------------------------

InvTyp-Snd : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M : Expr n) (rho : EnvApprox n) ->
  Fits G rho ->
  InvTyp G M (RawSyntaxSigma.Sigma A B) rho ->
  InvTyp G (Snd M) (subst1 B (Fst M)) rho
InvTyp-Snd A B M rho fits invM = invTyp-Snd-aux
  where
    crho = Fits-CoherentEnv rho fits

    mkFstEvSnd : (u' v' : FinEl) ->
      EvalRel M rho (PairCode u' v') -> EvalRel (Fst M) rho u'
    mkFstEvSnd Bot v' evM = tt
    mkFstEvSnd UCode v' evM = mkSigma v' evM
    mkFstEvSnd PropCode v' evM = mkSigma v' evM
    mkFstEvSnd (FunEl g) v' evM = mkSigma v' evM
    mkFstEvSnd (PiCode a0 f0) v' evM = mkSigma v' evM
    mkFstEvSnd (SigmaCode a0 f0) v' evM = mkSigma v' evM
    mkFstEvSnd (PairCode u0 v0) v' evM = mkSigma v' evM

    mkSndEv : (u' v' : FinEl) ->
      EvalRel M rho (PairCode u' v') -> EvalRel (Snd M) rho v'
    mkSndEv u' Bot evM = tt
    mkSndEv u' UCode evM = mkSigma u' evM
    mkSndEv u' PropCode evM = mkSigma u' evM
    mkSndEv u' (FunEl g) evM = mkSigma u' evM
    mkSndEv u' (PiCode a0 f0) evM = mkSigma u' evM
    mkSndEv u' (SigmaCode a0 f0) evM = mkSigma u' evM
    mkSndEv u' (PairCode u0 v0) evM = mkSigma u' evM

    snd-h-case : (u v : FinEl) -> NotBot v ->
      EvalRel M rho (PairCode u v) ->
      (w sigaf : FinEl) ->
      LeCode (PairCode u v) w ->
      EvalRel M rho w ->
      FinMem w sigaf ->
      EvalRel (RawSyntaxSigma.Sigma A B) rho sigaf ->
      Typed (Snd M) (subst1 B (Fst M)) rho v
    snd-h-case u v nbv evM-pair Bot sigaf () evM-w fm-w evSig
    snd-h-case u v nbv evM-pair UCode sigaf () evM-w fm-w evSig
    snd-h-case u v nbv evM-pair PropCode sigaf () evM-w fm-w evSig
    snd-h-case u v nbv evM-pair (FunEl _) sigaf () evM-w fm-w evSig
    snd-h-case u v nbv evM-pair (PiCode _ _) sigaf () evM-w fm-w evSig
    snd-h-case u v nbv evM-pair (SigmaCode _ _) sigaf () evM-w fm-w evSig
    snd-h-case u v nbv evM-pair (PairCode u' v') Bot le-pv evM-w () evSig
    snd-h-case u v nbv evM-pair (PairCode u' v') UCode le-pv evM-w () evSig
    snd-h-case u v nbv evM-pair (PairCode u' v') PropCode le-pv evM-w () evSig
    snd-h-case u v nbv evM-pair (PairCode u' v') (FunEl _) le-pv evM-w () evSig
    snd-h-case u v nbv evM-pair (PairCode u' v') (PiCode _ _) le-pv evM-w () evSig
    snd-h-case u v nbv evM-pair (PairCode u' v') (PairCode _ _) le-pv evM-w () evSig
    snd-h-case u v nbv evM-pair (PairCode u' v') (SigmaCode a f) le-pv evM-w fm-w evSig =
      let le-v-v' = snd le-pv
          fm-v'-fu' = snd (fst fm-w)
          sigU = snd (snd fm-w)
          cf-f = snd (snd sigU)
          cu' = fst (fst (fst (snd fm-w)))
          evSnd-v' = mkSndEv u' v' evM-w
          fu' = EvalFun f u'
          selbody = snd (snd (snd (snd evSig)))
          sb = selectionBelow f u' cf-f cu'
          x-f = fst sb
          w-f = fst (snd sb)
          sel-f = fst (snd (snd sb))
          le-xf = fst (snd (snd (snd sb)))
          eq-wf = snd (snd (snd (snd sb)))
          sb-result = selbody x-f w-f sel-f
          z = fst sb-result
          le-z-xf = fst (snd sb-result)
          fm-z-a' = fst (snd (snd sb-result))
          evB-z-wf = snd (snd (snd sb-result))
          cz = FinMem-coh-u z (fst (snd (snd evSig))) fm-z-a'
          cx-f = Coherent-Selection sel-f cf-f
          le-z-u' = LeCode-trans z x-f u' cz cx-f cu' le-z-xf le-xf
          evB-z-fu' = Eq-transport (\ x -> EvalRel B (extendEnv rho z) x)
                        (Eq-sym eq-wf) evB-z-wf
          envle = mkSigma (EnvLe-refl rho crho)
                    (mkSigma cz (mkSigma cu' le-z-u'))
          evB-u'-fu' = EvalRel-mon-env B (extendEnv rho z)
                         (extendEnv rho u') fu' evB-z-fu' envle
          evFst-u' = mkFstEvSnd u' v' evM-w
          evBFst-fu' = EvalRel-subst1-backward B (Fst M) rho u' fu' crho evFst-u' evB-u'-fu'
      in mkSigma v' (mkSigma fu'
           (mkSigma le-v-v' (mkSigma evSnd-v' (mkSigma fm-v'-fu' evBFst-fu'))))

    snd-main : (u v : FinEl) -> NotBot v ->
      EvalRel M rho (PairCode u v) ->
      Typed (Snd M) (subst1 B (Fst M)) rho v
    snd-main u v nbv evM-pair =
      let typed = invM (PairCode u v) evM-pair
          w     = fst typed
          sigaf = fst (snd typed)
          le-pv = fst (snd (snd typed))
          evM-w = fst (snd (snd (snd typed)))
          fm-w  = fst (snd (snd (snd (snd typed))))
          evSig = snd (snd (snd (snd (snd typed))))
      in snd-h-case u v nbv evM-pair w sigaf le-pv evM-w fm-w evSig

    invTyp-Snd-aux : (v : FinEl) -> EvalRel (Snd M) rho v ->
      Typed (Snd M) (subst1 B (Fst M)) rho v
    invTyp-Snd-aux Bot ev =
      mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt (EvalRel-Bot (subst1 B (Fst M)) rho)))))
    invTyp-Snd-aux UCode ev =
      let u = fst ev ; evM-pair = snd ev
      in snd-main u UCode tt evM-pair
    invTyp-Snd-aux PropCode ev =
      let u = fst ev ; evM-pair = snd ev
      in snd-main u PropCode tt evM-pair
    invTyp-Snd-aux (FunEl g) ev =
      let u = fst ev ; evM-pair = snd ev
      in snd-main u (FunEl g) tt evM-pair
    invTyp-Snd-aux (PiCode a0 f0) ev =
      let u = fst ev ; evM-pair = snd ev
      in snd-main u (PiCode a0 f0) tt evM-pair
    invTyp-Snd-aux (SigmaCode a0 f0) ev =
      let u = fst ev ; evM-pair = snd ev
      in snd-main u (SigmaCode a0 f0) tt evM-pair
    invTyp-Snd-aux (PairCode u0 v0) ev =
      let u = fst ev ; evM-pair = snd ev
      in snd-main u (PairCode u0 v0) tt evM-pair

------------------------------------------------------------------------
-- InvTyp-Pi-Prop
------------------------------------------------------------------------

InvTyp-Pi-Prop : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n)) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G A U rho ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
    InvTyp (extend G A) B Prop (extendEnv rho x)) ->
  InvTyp G (Pi A B) Prop rho
InvTyp-Pi-Prop A B rho fits invA body-ih Bot ev =
  mkSigma Bot (mkSigma PropCode (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma tt tt)))))
InvTyp-Pi-Prop A B rho fits invA body-ih UCode ()
InvTyp-Pi-Prop A B rho fits invA body-ih PropCode ()
InvTyp-Pi-Prop A B rho fits invA body-ih (FunEl g) ()
InvTyp-Pi-Prop A B rho fits invA body-ih (SigmaCode a0 f0) ()
InvTyp-Pi-Prop A B rho fits invA body-ih (PairCode u0 v0) ()
InvTyp-Pi-Prop A B rho fits invA body-ih (PiCode b f) ev = result
  where
    crho = Fits-CoherentEnv rho fits

    -- Decompose ev
    coh   = fst ev
    cb    = fst coh
    cf    = snd coh
    evA-b = fst (snd ev)
    a'    = fst (snd (snd ev))
    evA-a' = fst (snd (snd (snd ev)))
    body  = snd (snd (snd (snd ev)))

    -- Pi-edgewise: per-edge data
    pew = Pi-edgewise A B rho b f ev
    ew : (p : Edge) -> EdgeIn p f ->
      Sigma FinEl (\ x -> Pair (LeCode x (fst p))
                               (Pair (FinMem x a') (EvalRel B (extendEnv rho x) (snd p))))
    ew = snd (snd (snd (snd pew)))

    -- Step 1: type b using invA
    typed-b = invA b evA-b
    b1    = fst typed-b
    ab1   = fst (snd typed-b)
    le-b-b1 = fst (snd (snd typed-b))
    evA-b1 = fst (snd (snd (snd typed-b)))
    fm-b1  = fst (snd (snd (snd (snd typed-b))))
    evU-ab1 = snd (snd (snd (snd (snd typed-b))))

    finMem-from-U-top : (x : FinEl) -> EvalRel U rho x ->
      (y : FinEl) -> FinMem y x -> FinMem y UCode
    finMem-from-U-top Bot evU Bot fm = tt
    finMem-from-U-top Bot evU UCode ()
    finMem-from-U-top Bot evU PropCode ()
    finMem-from-U-top Bot evU (FunEl g) ()
    finMem-from-U-top Bot evU (PiCode a0 f0) ()
    finMem-from-U-top Bot evU (SigmaCode a0 f0) ()
    finMem-from-U-top Bot evU (PairCode u0 v0) ()
    finMem-from-U-top UCode evU y fm = fm
    finMem-from-U-top PropCode (mkSigma _ ()) y fm
    finMem-from-U-top (FunEl g) (mkSigma _ ()) y fm
    finMem-from-U-top (PiCode a0 f0) (mkSigma _ ()) y fm
    finMem-from-U-top (SigmaCode a0 f0) (mkSigma _ ()) y fm
    finMem-from-U-top (PairCode u0 v0) (mkSigma _ ()) y fm

    b1U : FinMem b1 UCode
    b1U = finMem-from-U-top ab1 evU-ab1 b1 fm-b1

    -- Step 2: get FinMem a' UCode
    a'U : FinMem a' UCode
    a'U = get-a'U f cf ew body
      where
        get-a'U : (g : FinFun) -> CoherentFunTail g ->
          ((p : Edge) -> EdgeIn p g ->
            Sigma FinEl (\ x -> Pair (LeCode x (fst p))
                                     (Pair (FinMem x a') (EvalRel B (extendEnv rho x) (snd p))))) ->
          ((u v : FinEl) -> Selection g u v ->
            Sigma FinEl (\ x -> Pair (LeCode x u)
                                     (Pair (FinMem x a') (EvalRel B (extendEnv rho x) v)))) ->
          FinMem a' UCode
        get-a'U nil _ _ rawBody =
          let w = rawBody Bot Bot sel-nil
              xi = fst w
              fm-xi = fst (snd (snd w))
          in FinMem-a-in-U xi a' fm-xi
        get-a'U (cons p ps) _ ew0 _ =
          let w = ew0 p here
              xi = fst w
              fm-xi = fst (snd (snd w))
          in FinMem-a-in-U xi a' fm-xi

    -- Step 3: build b_new = Sup a' b1
    cb1 = coh-from-aU b1 b1U
    ca' = coh-from-aU a' a'U
    comp-a'-b1 : Comp a' b1
    comp-a'-b1 = EvalRel-Comp A rho crho a' b1 evA-a' evA-b1
    b_new = Sup a' b1
    b_newU : FinMem b_new UCode
    b_newU = finMemUCode-Sup a' b1 comp-a'-b1 a'U b1U
    cb_new = coh-from-aU b_new b_newU
    le-a'-b_new : LeCode a' b_new
    le-a'-b_new = LeCode-Sup-left a' b1 comp-a'-b1 ca' cb1
    le-b1-b_new : LeCode b1 b_new
    le-b1-b_new = LeCode-Sup-right a' b1 comp-a'-b1 ca' cb1
    le-b-b_new : LeCode b b_new
    le-b-b_new = LeCode-trans b b1 b_new cb cb1 cb_new le-b-b1 le-b1-b_new
    evA-b_new : EvalRel A rho b_new
    evA-b_new = EvalRel-Sup A rho a' b1 crho ca' cb1 comp-a'-b1 evA-a' evA-b1

    -- Step 4: per-edge IH
    finMem-from-Prop : (vi0 : FinEl) -> (x : FinEl) ->
      EvalRel Prop (extendEnv rho vi0) x -> (y : FinEl) -> FinMem y x -> FinMem y PropCode
    finMem-from-Prop vi0 Bot evP Bot fm = tt
    finMem-from-Prop vi0 Bot evP UCode ()
    finMem-from-Prop vi0 Bot evP PropCode ()
    finMem-from-Prop vi0 Bot evP (FunEl g) ()
    finMem-from-Prop vi0 Bot evP (PiCode a0 f0) ()
    finMem-from-Prop vi0 Bot evP (SigmaCode a0 f0) ()
    finMem-from-Prop vi0 Bot evP (PairCode u0 v0) ()
    finMem-from-Prop vi0 PropCode evP y fm = fm
    finMem-from-Prop vi0 UCode (mkSigma _ ()) y fm
    finMem-from-Prop vi0 (FunEl g) (mkSigma _ ()) y fm
    finMem-from-Prop vi0 (PiCode a0 f0) (mkSigma _ ()) y fm
    finMem-from-Prop vi0 (SigmaCode a0 f0) (mkSigma _ ()) y fm
    finMem-from-Prop vi0 (PairCode u0 v0) (mkSigma _ ()) y fm

    edge-data : (p : Edge) -> EdgeIn p f ->
      Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
        Pair (LeCode xi (fst p))
        (Pair (FinMem xi a')
        (Pair (EvalRel B (extendEnv rho xi) (snd p))
        (Pair (LeCode (snd p) vi')
        (Pair (EvalRel B (extendEnv rho xi) vi')
              (FinMem vi' PropCode)))))))
    edge-data p ein =
      let w    = ew p ein
          xi   = fst w
          le-xi = fst (snd w)
          fm-xi = fst (snd (snd w))
          evB-xi = snd (snd (snd w))
          typed-vi = body-ih xi a' fm-xi evA-a' (snd p) evB-xi
          vi' = fst typed-vi
          bvi = fst (snd typed-vi)
          le-vi = fst (snd (snd typed-vi))
          evB-vi' = fst (snd (snd (snd typed-vi)))
          fm-vi' = fst (snd (snd (snd (snd typed-vi))))
          evP-bvi = snd (snd (snd (snd (snd typed-vi))))
          vi'P = finMem-from-Prop xi bvi evP-bvi vi' fm-vi'
      in mkSigma xi (mkSigma vi'
           (mkSigma le-xi (mkSigma fm-xi (mkSigma evB-xi
             (mkSigma le-vi (mkSigma evB-vi' vi'P))))))

    -- Step 5: build f'
    new-edge : (p : Edge) -> EdgeIn p f -> Edge
    new-edge p ein =
      let d = edge-data p ein
      in mkSigma (fst d) (fst (snd d))

    f' = mapEdges f new-edge

    -- Edgewise properties
    f'-ew : (e : Edge) -> EdgeIn e f' ->
      Pair (FinMem (fst e) b_new) (EvalRel B (extendEnv rho (fst e)) (snd e))
    f'-ew = me-ew f edge-data
      where
        me-ew : (g : FinFun) ->
          (ed : (p : Edge) -> EdgeIn p g ->
            Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
              Pair (LeCode xi (fst p))
              (Pair (FinMem xi a')
              (Pair (EvalRel B (extendEnv rho xi) (snd p))
              (Pair (LeCode (snd p) vi')
              (Pair (EvalRel B (extendEnv rho xi) vi')
                    (FinMem vi' PropCode)))))))) ->
          (e : Edge) ->
          EdgeIn e (mapEdges g (\ p ein -> mkSigma (fst (ed p ein)) (fst (snd (ed p ein))))) ->
          Pair (FinMem (fst e) b_new) (EvalRel B (extendEnv rho (fst e)) (snd e))
        me-ew (cons p ps) ed .(mkSigma (fst (ed p here)) (fst (snd (ed p here)))) here =
          let d = ed p here
          in mkSigma (finMem-upward (fst d) a' b_new le-a'-b_new ca' cb_new
                        (fst (snd (snd (snd d)))) b_newU)
                     (fst (snd (snd (snd (snd (snd (snd d)))))))
        me-ew (cons p ps) ed e (there ein) =
          me-ew ps (\ q qin -> ed q (there qin)) e ein

    -- FinMemAllProp f' b_new
    fmAllProp-f' : FinMemAllProp f' b_new
    fmAllProp-f' = me-fmAllProp f edge-data
      where
        me-fmAllProp : (g : FinFun) ->
          (ed : (p : Edge) -> EdgeIn p g ->
            Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
              Pair (LeCode xi (fst p))
              (Pair (FinMem xi a')
              (Pair (EvalRel B (extendEnv rho xi) (snd p))
              (Pair (LeCode (snd p) vi')
              (Pair (EvalRel B (extendEnv rho xi) vi')
                    (FinMem vi' PropCode)))))))) ->
          FinMemAllProp (mapEdges g (\ p ein -> mkSigma (fst (ed p ein)) (fst (snd (ed p ein))))) b_new
        me-fmAllProp nil ed = tt
        me-fmAllProp (cons p ps) ed =
          let d = ed p here
              fm-xi = finMem-upward (fst d) a' b_new le-a'-b_new ca' cb_new
                        (fst (snd (snd (snd d)))) b_newU
              vi'P = snd (snd (snd (snd (snd (snd (snd d))))))
          in mkSigma (mkSigma fm-xi vi'P)
                     (me-fmAllProp ps (\ q qin -> ed q (there qin)))

    -- CoherentWith
    me-cw : (sk sv : FinEl) -> (rest : FinFun) ->
      Coherent sk -> CoherentFunTail rest ->
      EvalRel B (extendEnv rho sk) sv ->
      (ed : (q : Edge) -> EdgeIn q rest ->
        Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
          Pair (LeCode xi (fst q))
          (Pair (FinMem xi a')
          (Pair (EvalRel B (extendEnv rho xi) (snd q))
          (Pair (LeCode (snd q) vi')
          (Pair (EvalRel B (extendEnv rho xi) vi')
                (FinMem vi' PropCode)))))))) ->
      CoherentWith (mkSigma sk sv)
        (mapEdges rest (\ q ein -> mkSigma (fst (ed q ein)) (fst (snd (ed q ein)))))
    me-cw sk sv nil csk crest evBsk ed = tt
    me-cw sk sv (cons t ts) csk crest evBsk ed =
      let dt  = ed t here
          xt  = fst dt
          vt' = fst (snd dt)
          evB-xt = fst (snd (snd (snd (snd (snd (snd dt))))))
          ct  = key-coh crest
          cxt = FinMem-coh-u xt a' (fst (snd (snd (snd dt))))
          step : Comp sk xt -> Comp sv vt'
          step ck = EvalRel-Comp-ext B rho sk xt sv vt'
                      crho ck csk cxt evBsk evB-xt
      in mkSigma step
           (me-cw sk sv ts csk (tail-coh crest) evBsk
             (\ q qin -> ed q (there qin)))

    -- CoherentFunTail
    me-cft : (g : FinFun) -> CoherentFunTail g ->
      (ed : (p : Edge) -> EdgeIn p g ->
        Sigma FinEl (\ xi -> Sigma FinEl (\ vi' ->
          Pair (LeCode xi (fst p))
          (Pair (FinMem xi a')
          (Pair (EvalRel B (extendEnv rho xi) (snd p))
          (Pair (LeCode (snd p) vi')
          (Pair (EvalRel B (extendEnv rho xi) vi')
                (FinMem vi' PropCode)))))))) ->
      CoherentFunTail (mapEdges g (\ p ein -> mkSigma (fst (ed p ein)) (fst (snd (ed p ein)))))
    me-cft nil cg ed = tt
    me-cft (cons p ps) cg ed =
      let dp    = ed p here
          xp    = fst dp
          vp'   = fst (snd dp)
          cxp   = FinMem-coh-u xp a' (fst (snd (snd (snd dp))))
          vp'P  = snd (snd (snd (snd (snd (snd (snd dp))))))
          cvp'  = FinMem-coh-u vp' PropCode vp'P
          ck    = key-coh cg
          cv    = val-coh cg
          nb    = val-nbot cg
          le-vp = fst (snd (snd (snd (snd (snd dp)))))
          nbvp' = NotBot-from-Le (snd p) vp' cv nb le-vp
          evB-vp' = fst (snd (snd (snd (snd (snd (snd dp))))))
          cw    = me-cw xp vp' ps cxp (tail-coh cg) evB-vp'
                    (\ q qin -> ed q (there qin))
          tail  = me-cft ps (tail-coh cg)
                    (\ q qin -> ed q (there qin))
      in mkCFT cxp cvp' nbvp' cw tail

    cft-f' = me-cft f cf edge-data
    cf-f' = cft-f'

    -- LeFunCode f f'
    lf-f-f' : LeFunCode f f'
    lf-f-f' = me-lf-tail f cf (\ q qin -> qin)
      where
        cft-edge : {g : FinFun} -> CoherentFunTail g -> {e : Edge} ->
          EdgeIn e g -> CoherentFunTail (cons e nil)
        cft-edge {cons p ps} cg0 here = mkCFT (key-coh cg0) (val-coh cg0) (val-nbot cg0) tt tt
        cft-edge {cons p nil} cg0 (there ())
        cft-edge {cons p (cons q qs)} cg0 (there ein) =
          cft-edge (tail-coh cg0) ein

        me-lf-tail : (ps : FinFun) -> CoherentFunTail f ->
          (shift : (q : Edge) -> EdgeIn q ps -> EdgeIn q f) ->
          LeFunCode ps f'
        me-lf-tail nil cg0 shift = tt
        me-lf-tail (cons q qs) cg0 shift =
          let dq    = edge-data q (shift q here)
              xq    = fst dq
              vq'   = fst (snd dq)
              le-xq = fst (snd (snd dq))
              le-vq = fst (snd (snd (snd (snd (snd dq)))))
              ck-q  = key-coh (cft-edge cg0 (shift q here))
              cv-q  = val-coh (cft-edge cg0 (shift q here))
              ein-f' = mapEdges-corr f new-edge q (shift q here)
              head-le = EvalFun-edge-le (new-edge q (shift q here)) f' (fst q)
                          cft-f' ein-f' ck-q le-xq
              vq'P  = snd (snd (snd (snd (snd (snd (snd dq))))))
              cvq'  = FinMem-coh-u vq' PropCode vq'P
              cefg' = Coherent-EvalFun f' (fst q) cft-f' ck-q
              head  = LeCode-trans (snd q) vq' (EvalFun f' (fst q))
                        cv-q cvq' cefg' le-vq head-le
              tail  = me-lf-tail qs cg0 (\ r rin -> shift r (there rin))
          in mkSigma head tail

    evPi-new : EvalRel (Pi A B) rho (PiCode b_new f')
    evPi-new =
      let selbody : (u' v' : FinEl) -> Selection f' u' v' ->
            Sigma FinEl (\ x -> Pair (LeCode x u')
              (Pair (FinMem x b_new) (EvalRel B (extendEnv rho x) v')))
          selbody u' v' sel =
            replaceKeys-selection-body B rho b_new f' u' v' crho b_newU cft-f' f'-ew sel
      in mkSigma (mkSigma cb_new cf-f')
           (mkSigma evA-b_new (mkSigma b_new (mkSigma evA-b_new selbody)))

    fm-pi-P : FinMem (PiCode b_new f') PropCode
    fm-pi-P = mkSigma b_newU (mkSigma fmAllProp-f' cf-f')

    result : Typed (Pi A B) Prop rho (PiCode b f)
    result = mkSigma (PiCode b_new f') (mkSigma PropCode
      (mkSigma (mkSigma le-b-b_new lf-f-f')
        (mkSigma evPi-new (mkSigma fm-pi-P (mkSigma tt tt)))))

------------------------------------------------------------------------
-- Helper: absurdEl (eliminate Empty)
------------------------------------------------------------------------

absurdEl : {A : Set} -> Empty -> A
absurdEl ()

------------------------------------------------------------------------
-- Helper: mkFstEv / mkSndEv (global versions)
------------------------------------------------------------------------

mkFstEv-g : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (u' v' : FinEl) ->
  EvalRel M rho (PairCode u' v') -> EvalRel (Fst M) rho u'
mkFstEv-g M rho Bot v' evM = tt
mkFstEv-g M rho UCode v' evM = mkSigma v' evM
mkFstEv-g M rho PropCode v' evM = mkSigma v' evM
mkFstEv-g M rho (FunEl g) v' evM = mkSigma v' evM
mkFstEv-g M rho (PiCode a0 f0) v' evM = mkSigma v' evM
mkFstEv-g M rho (SigmaCode a0 f0) v' evM = mkSigma v' evM
mkFstEv-g M rho (PairCode u0 v0) v' evM = mkSigma v' evM

mkSndEv-g : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (u' v' : FinEl) ->
  EvalRel M rho (PairCode u' v') -> EvalRel (Snd M) rho v'
mkSndEv-g M rho u' Bot evM = tt
mkSndEv-g M rho u' UCode evM = mkSigma u' evM
mkSndEv-g M rho u' PropCode evM = mkSigma u' evM
mkSndEv-g M rho u' (FunEl g) evM = mkSigma u' evM
mkSndEv-g M rho u' (PiCode a0 f0) evM = mkSigma u' evM
mkSndEv-g M rho u' (SigmaCode a0 f0) evM = mkSigma u' evM
mkSndEv-g M rho u' (PairCode u0 v0) evM = mkSigma u' evM

------------------------------------------------------------------------
-- Helper: fstEv-extract / sndEv-extract
------------------------------------------------------------------------

fstEv-extract : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (u : FinEl) -> NotBot u -> EvalRel (Fst M) rho u ->
  Sigma FinEl (\ v -> EvalRel M rho (PairCode u v))
fstEv-extract M rho Bot ()
fstEv-extract M rho UCode nb ev = ev
fstEv-extract M rho PropCode nb ev = ev
fstEv-extract M rho (FunEl g) nb ev = ev
fstEv-extract M rho (PiCode a f) nb ev = ev
fstEv-extract M rho (SigmaCode a f) nb ev = ev
fstEv-extract M rho (PairCode u0 v0) nb ev = ev

sndEv-extract : {n : Nat} (M : Expr n) (rho : EnvApprox n)
  (v : FinEl) -> NotBot v -> EvalRel (Snd M) rho v ->
  Sigma FinEl (\ u -> EvalRel M rho (PairCode u v))
sndEv-extract M rho Bot ()
sndEv-extract M rho UCode nb ev = ev
sndEv-extract M rho PropCode nb ev = ev
sndEv-extract M rho (FunEl g) nb ev = ev
sndEv-extract M rho (PiCode a f) nb ev = ev
sndEv-extract M rho (SigmaCode a f) nb ev = ev
sndEv-extract M rho (PairCode u0 v0) nb ev = ev

------------------------------------------------------------------------
-- Helper: FinMem-Bot-elim
------------------------------------------------------------------------

FinMem-Bot-elim : (u' : FinEl) -> FinMem u' Bot -> Eq u' Bot
FinMem-Bot-elim Bot          mem = refl
FinMem-Bot-elim UCode        ()
FinMem-Bot-elim PropCode     ()
FinMem-Bot-elim (FunEl g)    ()
FinMem-Bot-elim (PiCode a f) ()
FinMem-Bot-elim (SigmaCode a f) ()
FinMem-Bot-elim (PairCode u v)  ()

------------------------------------------------------------------------
-- Helper: LeCode-Bot-eq
------------------------------------------------------------------------

LeCode-Bot-eq : (u u' : FinEl) -> LeCode u u' -> Eq u' Bot -> Eq u Bot
LeCode-Bot-eq Bot u' le eq = refl
LeCode-Bot-eq UCode Bot ()
LeCode-Bot-eq UCode UCode le ()
LeCode-Bot-eq UCode PropCode le ()
LeCode-Bot-eq UCode (FunEl h) le ()
LeCode-Bot-eq UCode (PiCode b g) le ()
LeCode-Bot-eq UCode (SigmaCode b g) le ()
LeCode-Bot-eq UCode (PairCode u v) le ()
LeCode-Bot-eq PropCode Bot ()
LeCode-Bot-eq PropCode UCode le ()
LeCode-Bot-eq PropCode PropCode le ()
LeCode-Bot-eq PropCode (FunEl h) le ()
LeCode-Bot-eq PropCode (PiCode b g) le ()
LeCode-Bot-eq PropCode (SigmaCode b g) le ()
LeCode-Bot-eq PropCode (PairCode u v) le ()
LeCode-Bot-eq (FunEl g) Bot ()
LeCode-Bot-eq (FunEl g) UCode le ()
LeCode-Bot-eq (FunEl g) PropCode le ()
LeCode-Bot-eq (FunEl g) (FunEl h) le ()
LeCode-Bot-eq (FunEl g) (PiCode b h) le ()
LeCode-Bot-eq (FunEl g) (SigmaCode b h) le ()
LeCode-Bot-eq (FunEl g) (PairCode u v) le ()
LeCode-Bot-eq (PiCode a f) Bot ()
LeCode-Bot-eq (PiCode a f) UCode le ()
LeCode-Bot-eq (PiCode a f) PropCode le ()
LeCode-Bot-eq (PiCode a f) (FunEl h) le ()
LeCode-Bot-eq (PiCode a f) (PiCode b g) le ()
LeCode-Bot-eq (PiCode a f) (SigmaCode b g) le ()
LeCode-Bot-eq (PiCode a f) (PairCode u v) le ()
LeCode-Bot-eq (SigmaCode a f) Bot ()
LeCode-Bot-eq (SigmaCode a f) UCode le ()
LeCode-Bot-eq (SigmaCode a f) PropCode le ()
LeCode-Bot-eq (SigmaCode a f) (FunEl h) le ()
LeCode-Bot-eq (SigmaCode a f) (PiCode b g) le ()
LeCode-Bot-eq (SigmaCode a f) (SigmaCode b g) le ()
LeCode-Bot-eq (SigmaCode a f) (PairCode u v) le ()
LeCode-Bot-eq (PairCode u v) Bot ()
LeCode-Bot-eq (PairCode u v) UCode le ()
LeCode-Bot-eq (PairCode u v) PropCode le ()
LeCode-Bot-eq (PairCode u v) (FunEl h) le ()
LeCode-Bot-eq (PairCode u v) (PiCode b g) le ()
LeCode-Bot-eq (PairCode u v) (SigmaCode b g) le ()
LeCode-Bot-eq (PairCode u v) (PairCode u2 v2) le ()

------------------------------------------------------------------------
-- InvConv-MkPair-fst
--   From InvConv G M M' A rho (M = M' : A), build
--   InvConv G (MkPair M N) (MkPair M' N) (Sigma A B) rho.
--   Only takes InvTyp for the LHS MkPair; derives the RHS internally
--   using the fwd/bwd transfer (mirrors InvConv-App-fun pattern).
------------------------------------------------------------------------

InvConv-MkPair-fst : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M M' N : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvConv G M M' A rho ->
  InvTyp G (MkPair M N) (RawSyntaxSigma.Sigma A B) rho ->
  InvConv G (MkPair M N) (MkPair M' N) (RawSyntaxSigma.Sigma A B) rho
InvConv-MkPair-fst {G = G} A B M M' N rho fits invMM' invMkP-lhs =
  mkSigma invMkP-lhs (mkSigma invMkP-rhs (mkSigma conv-fwd conv-bwd))
  where
    fwdM = fst (snd (snd invMM'))
    bwdM = snd (snd (snd invMM'))

    conv-MkPair-fst-dir : {P Q : Expr _} ->
      ((w : FinEl) -> EvalRel P rho w -> EvalRel Q rho w) ->
      (u : FinEl) -> EvalRel (MkPair P N) rho u -> EvalRel (MkPair Q N) rho u
    conv-MkPair-fst-dir eq Bot ev = tt
    conv-MkPair-fst-dir eq (PairCode u0 v0) (mkSigma coh (mkSigma evP evN)) =
      mkSigma coh (mkSigma (eq u0 evP) evN)
    conv-MkPair-fst-dir eq UCode ()
    conv-MkPair-fst-dir eq PropCode ()
    conv-MkPair-fst-dir eq (FunEl g) ()
    conv-MkPair-fst-dir eq (PiCode a0 f0) ()
    conv-MkPair-fst-dir eq (SigmaCode a0 f0) ()

    conv-fwd : (u : FinEl) -> EvalRel (MkPair M N) rho u -> EvalRel (MkPair M' N) rho u
    conv-fwd = conv-MkPair-fst-dir fwdM

    conv-bwd : (u : FinEl) -> EvalRel (MkPair M' N) rho u -> EvalRel (MkPair M N) rho u
    conv-bwd = conv-MkPair-fst-dir bwdM

    -- Derive RHS InvTyp from LHS InvTyp using bwd/fwd transfer
    invMkP-rhs : InvTyp G (MkPair M' N) (RawSyntaxSigma.Sigma A B) rho
    invMkP-rhs u ev =
      let ev-lhs = conv-bwd u ev
          mkSigma u' (mkSigma a' (mkSigma le (mkSigma evMkP-u' (mkSigma fm evA)))) =
            invMkP-lhs u ev-lhs
          evMkP-rhs-u' = conv-fwd u' evMkP-u'
      in mkSigma u' (mkSigma a' (mkSigma le (mkSigma evMkP-rhs-u' (mkSigma fm evA))))

------------------------------------------------------------------------
-- InvConv-MkPair-snd
--   From InvConv G N N' (subst1 B M) rho, build
--   InvConv G (MkPair M N) (MkPair M N') (Sigma A B) rho.
------------------------------------------------------------------------

InvConv-MkPair-snd : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M N N' : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvConv G N N' (subst1 B M) rho ->
  InvTyp G (MkPair M N) (RawSyntaxSigma.Sigma A B) rho ->
  InvTyp G (MkPair M N') (RawSyntaxSigma.Sigma A B) rho ->
  InvConv G (MkPair M N) (MkPair M N') (RawSyntaxSigma.Sigma A B) rho
InvConv-MkPair-snd A B M N N' rho fits invNN' invMkP-lhs invMkP-rhs =
  mkSigma invMkP-lhs (mkSigma invMkP-rhs (mkSigma conv-fwd conv-bwd))
  where
    fwdN = fst (snd (snd invNN'))
    bwdN = snd (snd (snd invNN'))

    conv-MkPair-snd-dir : {P Q : Expr _} ->
      ((w : FinEl) -> EvalRel P rho w -> EvalRel Q rho w) ->
      (u : FinEl) -> EvalRel (MkPair M P) rho u -> EvalRel (MkPair M Q) rho u
    conv-MkPair-snd-dir eq Bot ev = tt
    conv-MkPair-snd-dir eq (PairCode u0 v0) (mkSigma coh (mkSigma evM evP)) =
      mkSigma coh (mkSigma evM (eq v0 evP))
    conv-MkPair-snd-dir eq UCode ()
    conv-MkPair-snd-dir eq PropCode ()
    conv-MkPair-snd-dir eq (FunEl g) ()
    conv-MkPair-snd-dir eq (PiCode a0 f0) ()
    conv-MkPair-snd-dir eq (SigmaCode a0 f0) ()

    conv-fwd : (u : FinEl) -> EvalRel (MkPair M N) rho u -> EvalRel (MkPair M N') rho u
    conv-fwd = conv-MkPair-snd-dir fwdN

    conv-bwd : (u : FinEl) -> EvalRel (MkPair M N') rho u -> EvalRel (MkPair M N) rho u
    conv-bwd = conv-MkPair-snd-dir bwdN

------------------------------------------------------------------------
-- InvConv-Fst
--   From InvConv G M M' (Sigma A B) rho, build
--   InvConv G (Fst M) (Fst M') A rho.
------------------------------------------------------------------------

InvConv-Fst : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M M' : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvConv G M M' (RawSyntaxSigma.Sigma A B) rho ->
  InvConv G (Fst M) (Fst M') A rho
InvConv-Fst A B M M' rho fits invMM' =
  let invM  = fst invMM'
      invM' = fst (snd invMM')
      fwdM  = fst (snd (snd invMM'))
      bwdM  = snd (snd (snd invMM'))
      invFst-lhs = InvTyp-Fst A B M rho fits invM
      invFst-rhs = InvTyp-Fst A B M' rho fits invM'
  in mkSigma invFst-lhs (mkSigma invFst-rhs (mkSigma (conv-fwd fwdM) (conv-fwd bwdM)))
  where
    conv-fwd : {F F' : Expr _} ->
      ((w : FinEl) -> EvalRel F rho w -> EvalRel F' rho w) ->
      (u : FinEl) -> EvalRel (Fst F) rho u -> EvalRel (Fst F') rho u
    conv-fwd eqF Bot ev = tt
    conv-fwd eqF UCode (mkSigma v evM) =
      mkSigma v (eqF (PairCode UCode v) evM)
    conv-fwd eqF PropCode (mkSigma v evM) =
      mkSigma v (eqF (PairCode PropCode v) evM)
    conv-fwd eqF (FunEl g) (mkSigma v evM) =
      mkSigma v (eqF (PairCode (FunEl g) v) evM)
    conv-fwd eqF (PiCode a0 f0) (mkSigma v evM) =
      mkSigma v (eqF (PairCode (PiCode a0 f0) v) evM)
    conv-fwd eqF (SigmaCode a0 f0) (mkSigma v evM) =
      mkSigma v (eqF (PairCode (SigmaCode a0 f0) v) evM)
    conv-fwd eqF (PairCode u0 v0) (mkSigma v evM) =
      mkSigma v (eqF (PairCode (PairCode u0 v0) v) evM)

------------------------------------------------------------------------
-- InvConv-Snd
--   From InvConv G M M' (Sigma A B) rho, build
--   InvConv G (Snd M) (Snd M') (subst1 B (Fst M)) rho.
------------------------------------------------------------------------

InvConv-Snd : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M M' : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvConv G M M' (RawSyntaxSigma.Sigma A B) rho ->
  InvConv G (Snd M) (Snd M') (subst1 B (Fst M)) rho
InvConv-Snd {G = G} A B M M' rho fits invMM' =
  let invM  = fst invMM'
      invM' = fst (snd invMM')
      fwdM  = fst (snd (snd invMM'))
      bwdM  = snd (snd (snd invMM'))
      invSnd-lhs = InvTyp-Snd A B M rho fits invM
  in mkSigma invSnd-lhs (mkSigma invSnd-rhs (mkSigma conv-fwd conv-bwd))
  where
    fwdM  = fst (snd (snd invMM'))
    bwdM  = snd (snd (snd invMM'))

    conv-fwd : (u : FinEl) -> EvalRel (Snd M) rho u -> EvalRel (Snd M') rho u
    conv-fwd Bot ev = tt
    conv-fwd UCode (mkSigma u evM) =
      mkSigma u (fwdM (PairCode u UCode) evM)
    conv-fwd PropCode (mkSigma u evM) =
      mkSigma u (fwdM (PairCode u PropCode) evM)
    conv-fwd (FunEl g) (mkSigma u evM) =
      mkSigma u (fwdM (PairCode u (FunEl g)) evM)
    conv-fwd (PiCode a0 f0) (mkSigma u evM) =
      mkSigma u (fwdM (PairCode u (PiCode a0 f0)) evM)
    conv-fwd (SigmaCode a0 f0) (mkSigma u evM) =
      mkSigma u (fwdM (PairCode u (SigmaCode a0 f0)) evM)
    conv-fwd (PairCode u0 v0) (mkSigma u evM) =
      mkSigma u (fwdM (PairCode u (PairCode u0 v0)) evM)

    conv-bwd : (u : FinEl) -> EvalRel (Snd M') rho u -> EvalRel (Snd M) rho u
    conv-bwd Bot ev = tt
    conv-bwd UCode (mkSigma u evM') =
      mkSigma u (bwdM (PairCode u UCode) evM')
    conv-bwd PropCode (mkSigma u evM') =
      mkSigma u (bwdM (PairCode u PropCode) evM')
    conv-bwd (FunEl g) (mkSigma u evM') =
      mkSigma u (bwdM (PairCode u (FunEl g)) evM')
    conv-bwd (PiCode a0 f0) (mkSigma u evM') =
      mkSigma u (bwdM (PairCode u (PiCode a0 f0)) evM')
    conv-bwd (SigmaCode a0 f0) (mkSigma u evM') =
      mkSigma u (bwdM (PairCode u (SigmaCode a0 f0)) evM')
    conv-bwd (PairCode u0 v0) (mkSigma u evM') =
      mkSigma u (bwdM (PairCode u (PairCode u0 v0)) evM')

    invSnd-lhs = InvTyp-Snd A B M rho fits (fst invMM')

    invSnd-rhs : InvTyp G (Snd M') (subst1 B (Fst M)) rho
    invSnd-rhs u ev =
      let typed = invSnd-lhs u (conv-bwd u ev)
          u'  = fst typed
          a0  = fst (snd typed)
          le  = fst (snd (snd typed))
          evSndM  = fst (snd (snd (snd typed)))
          fm  = fst (snd (snd (snd (snd typed))))
          evBFstM = snd (snd (snd (snd (snd typed))))
      in mkSigma u' (mkSigma a0
           (mkSigma le (mkSigma (conv-fwd u' evSndM) (mkSigma fm evBFstM))))

------------------------------------------------------------------------
-- mkTyped-split: build Typed tuple with case split to avoid
-- FinMem (PairCode _ _) Bot elaboration issue
------------------------------------------------------------------------

mkTyped-split : {n : Nat} {M A : Expr n} {rho : EnvApprox n}
  (u u' a' : FinEl) -> LeCode u u' -> EvalRel M rho u' ->
  FinMem u' a' -> EvalRel A rho a' -> Typed M A rho u
mkTyped-split u Bot Bot le ev fm evA =
  mkSigma Bot (mkSigma Bot (mkSigma le (mkSigma ev (mkSigma fm evA))))
mkTyped-split u UCode Bot le ev () evA
mkTyped-split u PropCode Bot le ev () evA
mkTyped-split u (FunEl g) Bot le ev () evA
mkTyped-split u (PiCode a f) Bot le ev () evA
mkTyped-split u (SigmaCode a f) Bot le ev () evA
mkTyped-split u (PairCode u0 v0) Bot le ev () evA
mkTyped-split u u' UCode le ev fm evA =
  mkSigma u' (mkSigma UCode (mkSigma le (mkSigma ev (mkSigma fm evA))))
mkTyped-split u u' PropCode le ev fm evA =
  mkSigma u' (mkSigma PropCode (mkSigma le (mkSigma ev (mkSigma fm evA))))
mkTyped-split u u' (FunEl g) le ev fm evA =
  mkSigma u' (mkSigma (FunEl g) (mkSigma le (mkSigma ev (mkSigma fm evA))))
mkTyped-split u u' (PiCode a f) le ev fm evA =
  mkSigma u' (mkSigma (PiCode a f) (mkSigma le (mkSigma ev (mkSigma fm evA))))
mkTyped-split u u' (SigmaCode a f) le ev fm evA =
  mkSigma u' (mkSigma (SigmaCode a f) (mkSigma le (mkSigma ev (mkSigma fm evA))))
mkTyped-split u u' (PairCode u0 v0) le ev fm evA =
  mkSigma u' (mkSigma (PairCode u0 v0) (mkSigma le (mkSigma ev (mkSigma fm evA))))

------------------------------------------------------------------------
-- InvConv-beta-fst
--   InvConv G (Fst (MkPair M N)) M A rho
------------------------------------------------------------------------

InvConv-beta-fst : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M N : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G M A rho ->
  InvTyp G (MkPair M N) (RawSyntaxSigma.Sigma A B) rho ->
  InvConv G (Fst (MkPair M N)) M A rho
InvConv-beta-fst {G = G} A B M N rho fits invM invMkP =
  mkSigma invFstMkPair (mkSigma invM (mkSigma conv-fwd conv-bwd))
  where
    crho = Fits-CoherentEnv rho fits

    conv-fwd : (u : FinEl) -> EvalRel (Fst (MkPair M N)) rho u -> EvalRel M rho u
    conv-fwd Bot ev = EvalRel-Bot M rho
    conv-fwd UCode (mkSigma v (mkSigma coh (mkSigma evM evN))) = evM
    conv-fwd PropCode (mkSigma v (mkSigma coh (mkSigma evM evN))) = evM
    conv-fwd (FunEl g) (mkSigma v (mkSigma coh (mkSigma evM evN))) = evM
    conv-fwd (PiCode a f) (mkSigma v (mkSigma coh (mkSigma evM evN))) = evM
    conv-fwd (SigmaCode a f) (mkSigma v (mkSigma coh (mkSigma evM evN))) = evM
    conv-fwd (PairCode u0 v0) (mkSigma v (mkSigma coh (mkSigma evM evN))) = evM

    conv-bwd : (u : FinEl) -> EvalRel M rho u -> EvalRel (Fst (MkPair M N)) rho u
    conv-bwd Bot ev = tt
    conv-bwd UCode ev =
      mkSigma Bot (mkSigma (mkSigma (mkSigma tt tt) (inl tt))
        (mkSigma ev (EvalRel-Bot N rho)))
    conv-bwd PropCode ev =
      mkSigma Bot (mkSigma (mkSigma (mkSigma tt tt) (inl tt))
        (mkSigma ev (EvalRel-Bot N rho)))
    conv-bwd (FunEl g) ev =
      mkSigma Bot (mkSigma (mkSigma (mkSigma (EvalRel-coh M rho (FunEl g) ev) tt) (inl tt))
        (mkSigma ev (EvalRel-Bot N rho)))
    conv-bwd (PiCode a f) ev =
      mkSigma Bot (mkSigma (mkSigma (mkSigma (EvalRel-coh M rho (PiCode a f) ev) tt) (inl tt))
        (mkSigma ev (EvalRel-Bot N rho)))
    conv-bwd (SigmaCode a f) ev =
      mkSigma Bot (mkSigma (mkSigma (mkSigma (EvalRel-coh M rho (SigmaCode a f) ev) tt) (inl tt))
        (mkSigma ev (EvalRel-Bot N rho)))
    conv-bwd (PairCode u0 v0) ev =
      mkSigma Bot (mkSigma (mkSigma (mkSigma (EvalRel-coh M rho (PairCode u0 v0) ev) tt) (inl tt))
        (mkSigma ev (EvalRel-Bot N rho)))

    invFstMkPair : InvTyp G (Fst (MkPair M N)) A rho
    invFstMkPair u ev =
      let evM' = conv-fwd u ev
          r = invM u evM'
          u' = fst r
          a' = fst (snd r)
          le = fst (snd (snd r))
          evM-u' = fst (snd (snd (snd r)))
          fm = fst (snd (snd (snd (snd r))))
          evA = snd (snd (snd (snd (snd r))))
          evFstMkPair-u' = conv-bwd u' evM-u'
      in mkTyped-split u u' a' le evFstMkPair-u' fm evA

------------------------------------------------------------------------
-- InvConv-beta-snd
--   InvConv G (Snd (MkPair M N)) N (subst1 B M) rho
------------------------------------------------------------------------

InvConv-beta-snd : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M N : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G N (subst1 B M) rho ->
  InvTyp G (MkPair M N) (RawSyntaxSigma.Sigma A B) rho ->
  InvConv G (Snd (MkPair M N)) N (subst1 B M) rho
InvConv-beta-snd {G = G} A B M N rho fits invN invMkP =
  mkSigma invSndMkPair (mkSigma invN (mkSigma conv-fwd conv-bwd))
  where
    crho = Fits-CoherentEnv rho fits

    conv-fwd : (u : FinEl) -> EvalRel (Snd (MkPair M N)) rho u -> EvalRel N rho u
    conv-fwd Bot ev = EvalRel-Bot N rho
    conv-fwd UCode (mkSigma u0 (mkSigma coh (mkSigma evM evN))) = evN
    conv-fwd PropCode (mkSigma u0 (mkSigma coh (mkSigma evM evN))) = evN
    conv-fwd (FunEl g) (mkSigma u0 (mkSigma coh (mkSigma evM evN))) = evN
    conv-fwd (PiCode a f) (mkSigma u0 (mkSigma coh (mkSigma evM evN))) = evN
    conv-fwd (SigmaCode a f) (mkSigma u0 (mkSigma coh (mkSigma evM evN))) = evN
    conv-fwd (PairCode u0' v0') (mkSigma u0 (mkSigma coh (mkSigma evM evN))) = evN

    conv-bwd : (u : FinEl) -> EvalRel N rho u -> EvalRel (Snd (MkPair M N)) rho u
    conv-bwd Bot ev = tt
    conv-bwd UCode ev =
      mkSigma Bot (mkSigma (mkSigma (mkSigma tt tt) (inr tt))
        (mkSigma (EvalRel-Bot M rho) ev))
    conv-bwd PropCode ev =
      mkSigma Bot (mkSigma (mkSigma (mkSigma tt tt) (inr tt))
        (mkSigma (EvalRel-Bot M rho) ev))
    conv-bwd (FunEl g) ev =
      mkSigma Bot (mkSigma (mkSigma (mkSigma tt (EvalRel-coh N rho (FunEl g) ev)) (inr tt))
        (mkSigma (EvalRel-Bot M rho) ev))
    conv-bwd (PiCode a f) ev =
      mkSigma Bot (mkSigma (mkSigma (mkSigma tt (EvalRel-coh N rho (PiCode a f) ev)) (inr tt))
        (mkSigma (EvalRel-Bot M rho) ev))
    conv-bwd (SigmaCode a f) ev =
      mkSigma Bot (mkSigma (mkSigma (mkSigma tt (EvalRel-coh N rho (SigmaCode a f) ev)) (inr tt))
        (mkSigma (EvalRel-Bot M rho) ev))
    conv-bwd (PairCode u0 v0) ev =
      mkSigma Bot (mkSigma (mkSigma (mkSigma tt (EvalRel-coh N rho (PairCode u0 v0) ev)) (inr tt))
        (mkSigma (EvalRel-Bot M rho) ev))

    invSndMkPair : InvTyp G (Snd (MkPair M N)) (subst1 B M) rho
    invSndMkPair u ev =
      let evN' = conv-fwd u ev
          r = invN u evN'
          u' = fst r
          a' = fst (snd r)
          le = fst (snd (snd r))
          evN-u' = fst (snd (snd (snd r)))
          fm = fst (snd (snd (snd (snd r))))
          evBM = snd (snd (snd (snd (snd r))))
          evSndMkPair-u' = conv-bwd u' evN-u'
      in mkTyped-split u u' a' le evSndMkPair-u' fm evBM

------------------------------------------------------------------------
-- InvConv-pair-eta
--   InvConv G (MkPair (Fst M) (Snd M)) M (Sigma A B) rho
------------------------------------------------------------------------

InvConv-pair-eta : {n : Nat} {G : Ctx n} (A : Expr n) (B : Expr (suc n))
  (M : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G M (RawSyntaxSigma.Sigma A B) rho ->
  InvConv G (MkPair (Fst M) (Snd M)) M (RawSyntaxSigma.Sigma A B) rho
InvConv-pair-eta {G = G} A B M rho fits invM =
  mkSigma invMkPairFstSnd (mkSigma invM (mkSigma conv-eta-fwd conv-eta-bwd))
  where
    crho = Fits-CoherentEnv rho fits

    -- Forward: MkPair(Fst M)(Snd M) -> M
    -- For PairCode u0 v0: extract evFst and evSnd, then combine to get evM (PairCode u0 v0)
    fwd-with-fst : (u0 v0 v1 : FinEl) -> NotBot u0 ->
      Coherent u0 -> Coherent v0 ->
      EvalRel M rho (PairCode u0 v1) ->
      EvalRel (Snd M) rho v0 ->
      EvalRel M rho (PairCode u0 v0)
    fwd-with-fst u0 v0 v1 nbu0 cu0 cv0 evM-u0v1 evSnd
      with sndOr v0 evSnd
      where
        sndOr : (v : FinEl) -> EvalRel (Snd M) rho v ->
          Or (Eq v Bot) (Sigma FinEl (\ u -> EvalRel M rho (PairCode u v)))
        sndOr Bot ev = inl refl
        sndOr UCode ev = inr ev
        sndOr PropCode ev = inr ev
        sndOr (FunEl g) ev = inr ev
        sndOr (PiCode a f) ev = inr ev
        sndOr (SigmaCode a f) ev = inr ev
        sndOr (PairCode u0' v0') ev = inr ev
    ... | inl v0bot =
      EvalRel-down M rho (PairCode u0 v1) (PairCode u0 v0) crho
        (mkSigma (mkSigma cu0 cv0) (inl nbu0))
        evM-u0v1
        (mkSigma (LeCode-refl u0 cu0) (Eq-transport (\ x -> LeCode x v1) (Eq-sym v0bot) tt))
    ... | inr (mkSigma u1 evM-u1v0) =
      let comp = EvalRel-Comp M rho crho (PairCode u0 v1) (PairCode u1 v0) evM-u0v1 evM-u1v0
          cu0v1 = EvalRel-coh M rho (PairCode u0 v1) evM-u0v1
          cu1v0 = EvalRel-coh M rho (PairCode u1 v0) evM-u1v0
          evM-sup = EvalRel-Sup M rho (PairCode u0 v1) (PairCode u1 v0) crho
                      cu0v1 cu1v0 comp evM-u0v1 evM-u1v0
          le-u0 = LeCode-Sup-left u0 u1 (fst comp) (fst (fst cu0v1)) (fst (fst cu1v0))
          le-v0 = LeCode-Sup-right v1 v0 (snd comp) (snd (fst cu0v1)) (snd (fst cu1v0))
      in EvalRel-down M rho (PairCode (Sup u0 u1) (Sup v1 v0)) (PairCode u0 v0) crho
           (mkSigma (mkSigma cu0 cv0) (inl nbu0))
           evM-sup (mkSigma le-u0 le-v0)

    fwd-with-snd : (u0 v0 u1 : FinEl) -> NotBot v0 ->
      Coherent u0 -> Coherent v0 ->
      EvalRel (Fst M) rho u0 ->
      EvalRel M rho (PairCode u1 v0) ->
      EvalRel M rho (PairCode u0 v0)
    fwd-with-snd u0 v0 u1 nbv0 cu0 cv0 evFst evM-u1v0
      with fstOr u0 evFst
      where
        fstOr : (u : FinEl) -> EvalRel (Fst M) rho u ->
          Or (Eq u Bot) (Sigma FinEl (\ v -> EvalRel M rho (PairCode u v)))
        fstOr Bot ev = inl refl
        fstOr UCode ev = inr ev
        fstOr PropCode ev = inr ev
        fstOr (FunEl g) ev = inr ev
        fstOr (PiCode a f) ev = inr ev
        fstOr (SigmaCode a f) ev = inr ev
        fstOr (PairCode u0' v0') ev = inr ev
    ... | inl u0bot =
      EvalRel-down M rho (PairCode u1 v0) (PairCode u0 v0) crho
        (mkSigma (mkSigma cu0 cv0) (inr nbv0))
        evM-u1v0
        (mkSigma (Eq-transport (\ x -> LeCode x u1) (Eq-sym u0bot) tt) (LeCode-refl v0 cv0))
    ... | inr (mkSigma v1 evM-u0v1) =
      let comp = EvalRel-Comp M rho crho (PairCode u0 v1) (PairCode u1 v0) evM-u0v1 evM-u1v0
          cu0v1 = EvalRel-coh M rho (PairCode u0 v1) evM-u0v1
          cu1v0 = EvalRel-coh M rho (PairCode u1 v0) evM-u1v0
          evM-sup = EvalRel-Sup M rho (PairCode u0 v1) (PairCode u1 v0) crho
                      cu0v1 cu1v0 comp evM-u0v1 evM-u1v0
          le-u0 = LeCode-Sup-left u0 u1 (fst comp) (fst (fst cu0v1)) (fst (fst cu1v0))
          le-v0 = LeCode-Sup-right v1 v0 (snd comp) (snd (fst cu0v1)) (snd (fst cu1v0))
      in EvalRel-down M rho (PairCode (Sup u0 u1) (Sup v1 v0)) (PairCode u0 v0) crho
           (mkSigma (mkSigma cu0 cv0) (inr nbv0))
           evM-sup (mkSigma le-u0 le-v0)

    conv-eta-fwd-pair : (u0 v0 : FinEl) -> Or (NotBot u0) (NotBot v0) ->
      Coherent u0 -> Coherent v0 ->
      EvalRel (Fst M) rho u0 -> EvalRel (Snd M) rho v0 ->
      EvalRel M rho (PairCode u0 v0)
    conv-eta-fwd-pair u0 Bot (inl nbu0) cu0 cv0 evFst evSnd =
      let r = fstEv-extract M rho u0 nbu0 evFst
          v1 = fst r
          evM-pv1 = snd r
      in EvalRel-down M rho (PairCode u0 v1) (PairCode u0 Bot) crho
           (mkSigma (mkSigma cu0 tt) (inl nbu0))
           evM-pv1
           (mkSigma (LeCode-refl u0 cu0) tt)
    conv-eta-fwd-pair u0 Bot (inr ()) cu0 cv0 evFst evSnd
    conv-eta-fwd-pair Bot v0 (inl ()) cu0 cv0 evFst evSnd
    conv-eta-fwd-pair Bot v0 (inr nbv0) cu0 cv0 evFst evSnd =
      let r = sndEv-extract M rho v0 nbv0 evSnd
          u1 = fst r
          evM-pu1 = snd r
      in EvalRel-down M rho (PairCode u1 v0) (PairCode Bot v0) crho
           (mkSigma (mkSigma tt cv0) (inr nbv0))
           evM-pu1
           (mkSigma tt (LeCode-refl v0 cv0))
    conv-eta-fwd-pair u0 v0 (inl nbu0) cu0 cv0 evFst evSnd =
      let r1 = fstEv-extract M rho u0 nbu0 evFst
          v1 = fst r1
          evM-u0v1 = snd r1
      in fwd-with-fst u0 v0 v1 nbu0 cu0 cv0 evM-u0v1 evSnd
    conv-eta-fwd-pair u0 v0 (inr nbv0) cu0 cv0 evFst evSnd =
      let r2 = sndEv-extract M rho v0 nbv0 evSnd
          u1 = fst r2
          evM-u1v0 = snd r2
      in fwd-with-snd u0 v0 u1 nbv0 cu0 cv0 evFst evM-u1v0

    conv-eta-fwd : (u : FinEl) -> EvalRel (MkPair (Fst M) (Snd M)) rho u ->
      EvalRel M rho u
    conv-eta-fwd Bot ev = EvalRel-Bot M rho
    conv-eta-fwd (PairCode u0 v0) (mkSigma coh (mkSigma evFst evSnd)) =
      conv-eta-fwd-pair u0 v0 (snd coh) (fst (fst coh)) (snd (fst coh)) evFst evSnd
    conv-eta-fwd UCode ()
    conv-eta-fwd PropCode ()
    conv-eta-fwd (FunEl g) ()
    conv-eta-fwd (PiCode a f) ()
    conv-eta-fwd (SigmaCode a f) ()

    -- Backward: M -> MkPair(Fst M)(Snd M)
    -- For Bot/PairCode: direct.
    -- For other shapes: use InvTyp to derive contradiction
    --   (M typed at Sigma A B evaluates to non-Bot non-PairCode, absurd).
    NotBotPair : FinEl -> Set
    NotBotPair Bot = Empty
    NotBotPair UCode = Top
    NotBotPair PropCode = Top
    NotBotPair (FunEl g) = Top
    NotBotPair (PiCode a f) = Top
    NotBotPair (SigmaCode a f) = Top
    NotBotPair (PairCode u v) = Empty

    bwd-absurd : (u : FinEl) -> NotBotPair u ->
      Typed M (RawSyntaxSigma.Sigma A B) rho u -> Empty
    bwd-absurd Bot ()
    bwd-absurd (PairCode u1 v1) ()
    bwd-absurd UCode nb (mkSigma u' (mkSigma Bot (mkSigma le (mkSigma _ (mkSigma fm _))))) =
      Eq-transport NotBot (LeCode-Bot-eq UCode u' le (FinMem-Bot-elim u' fm)) tt
    bwd-absurd UCode nb (mkSigma u' (mkSigma UCode (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd UCode nb (mkSigma u' (mkSigma PropCode (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd UCode nb (mkSigma u' (mkSigma (FunEl g) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd UCode nb (mkSigma u' (mkSigma (PiCode a0 f0) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd UCode nb (mkSigma u' (mkSigma (PairCode u1 v1) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd UCode nb (mkSigma Bot (mkSigma (SigmaCode a0 f0) (mkSigma () _)))
    bwd-absurd UCode nb (mkSigma UCode (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd UCode nb (mkSigma PropCode (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd UCode nb (mkSigma (FunEl g) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd UCode nb (mkSigma (PiCode a1 f1) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd UCode nb (mkSigma (SigmaCode a1 f1) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd UCode nb (mkSigma (PairCode u1 v1) (mkSigma (SigmaCode a0 f0) (mkSigma () _)))
    bwd-absurd PropCode nb (mkSigma u' (mkSigma Bot (mkSigma le (mkSigma _ (mkSigma fm _))))) =
      Eq-transport NotBot (LeCode-Bot-eq PropCode u' le (FinMem-Bot-elim u' fm)) tt
    bwd-absurd PropCode nb (mkSigma u' (mkSigma UCode (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd PropCode nb (mkSigma u' (mkSigma PropCode (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd PropCode nb (mkSigma u' (mkSigma (FunEl g) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd PropCode nb (mkSigma u' (mkSigma (PiCode a0 f0) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd PropCode nb (mkSigma u' (mkSigma (PairCode u1 v1) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd PropCode nb (mkSigma Bot (mkSigma (SigmaCode a0 f0) (mkSigma () _)))
    bwd-absurd PropCode nb (mkSigma UCode (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd PropCode nb (mkSigma PropCode (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd PropCode nb (mkSigma (FunEl g) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd PropCode nb (mkSigma (PiCode a1 f1) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd PropCode nb (mkSigma (SigmaCode a1 f1) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd PropCode nb (mkSigma (PairCode u1 v1) (mkSigma (SigmaCode a0 f0) (mkSigma () _)))
    bwd-absurd (FunEl g) nb (mkSigma u' (mkSigma Bot (mkSigma le (mkSigma _ (mkSigma fm _))))) =
      Eq-transport NotBot (LeCode-Bot-eq (FunEl g) u' le (FinMem-Bot-elim u' fm)) tt
    bwd-absurd (FunEl g) nb (mkSigma u' (mkSigma UCode (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (FunEl g) nb (mkSigma u' (mkSigma PropCode (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (FunEl g) nb (mkSigma u' (mkSigma (FunEl g1) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (FunEl g) nb (mkSigma u' (mkSigma (PiCode a0 f0) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (FunEl g) nb (mkSigma u' (mkSigma (PairCode u1 v1) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (FunEl g) nb (mkSigma Bot (mkSigma (SigmaCode a0 f0) (mkSigma () _)))
    bwd-absurd (FunEl g) nb (mkSigma UCode (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (FunEl g) nb (mkSigma PropCode (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (FunEl g) nb (mkSigma (FunEl g1) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (FunEl g) nb (mkSigma (PiCode a1 f1) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (FunEl g) nb (mkSigma (SigmaCode a1 f1) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (FunEl g) nb (mkSigma (PairCode u1 v1) (mkSigma (SigmaCode a0 f0) (mkSigma () _)))
    bwd-absurd (PiCode a1 f1) nb (mkSigma u' (mkSigma Bot (mkSigma le (mkSigma _ (mkSigma fm _))))) =
      Eq-transport NotBot (LeCode-Bot-eq (PiCode a1 f1) u' le (FinMem-Bot-elim u' fm)) tt
    bwd-absurd (PiCode a1 f1) nb (mkSigma u' (mkSigma UCode (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (PiCode a1 f1) nb (mkSigma u' (mkSigma PropCode (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (PiCode a1 f1) nb (mkSigma u' (mkSigma (FunEl g) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (PiCode a1 f1) nb (mkSigma u' (mkSigma (PiCode a2 f2) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (PiCode a1 f1) nb (mkSigma u' (mkSigma (PairCode u1 v1) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (PiCode a1 f1) nb (mkSigma Bot (mkSigma (SigmaCode a0 f0) (mkSigma () _)))
    bwd-absurd (PiCode a1 f1) nb (mkSigma UCode (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (PiCode a1 f1) nb (mkSigma PropCode (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (PiCode a1 f1) nb (mkSigma (FunEl g) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (PiCode a1 f1) nb (mkSigma (PiCode a2 f2) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (PiCode a1 f1) nb (mkSigma (SigmaCode a2 f2) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (PiCode a1 f1) nb (mkSigma (PairCode u1 v1) (mkSigma (SigmaCode a0 f0) (mkSigma () _)))
    bwd-absurd (SigmaCode a1 f1) nb (mkSigma u' (mkSigma Bot (mkSigma le (mkSigma _ (mkSigma fm _))))) =
      Eq-transport NotBot (LeCode-Bot-eq (SigmaCode a1 f1) u' le (FinMem-Bot-elim u' fm)) tt
    bwd-absurd (SigmaCode a1 f1) nb (mkSigma u' (mkSigma UCode (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (SigmaCode a1 f1) nb (mkSigma u' (mkSigma PropCode (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (SigmaCode a1 f1) nb (mkSigma u' (mkSigma (FunEl g) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (SigmaCode a1 f1) nb (mkSigma u' (mkSigma (PiCode a2 f2) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (SigmaCode a1 f1) nb (mkSigma u' (mkSigma (PairCode u1 v1) (mkSigma le (mkSigma _ (mkSigma fm ())))))
    bwd-absurd (SigmaCode a1 f1) nb (mkSigma Bot (mkSigma (SigmaCode a0 f0) (mkSigma () _)))
    bwd-absurd (SigmaCode a1 f1) nb (mkSigma UCode (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (SigmaCode a1 f1) nb (mkSigma PropCode (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (SigmaCode a1 f1) nb (mkSigma (FunEl g) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (SigmaCode a1 f1) nb (mkSigma (PiCode a2 f2) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (SigmaCode a1 f1) nb (mkSigma (SigmaCode a2 f2) (mkSigma (SigmaCode a0 f0) (mkSigma le (mkSigma _ (mkSigma () _)))))
    bwd-absurd (SigmaCode a1 f1) nb (mkSigma (PairCode u1 v1) (mkSigma (SigmaCode a0 f0) (mkSigma () _)))

    conv-eta-bwd : (u : FinEl) -> EvalRel M rho u ->
      EvalRel (MkPair (Fst M) (Snd M)) rho u
    conv-eta-bwd Bot ev = tt
    conv-eta-bwd (PairCode u0 v0) ev =
      let cu0v0 = EvalRel-coh M rho (PairCode u0 v0) ev
      in mkSigma cu0v0
           (mkSigma (mkFstEv-g M rho u0 v0 ev) (mkSndEv-g M rho u0 v0 ev))
    conv-eta-bwd UCode ev = absurdEl (bwd-absurd UCode tt (invM UCode ev))
    conv-eta-bwd PropCode ev = absurdEl (bwd-absurd PropCode tt (invM PropCode ev))
    conv-eta-bwd (FunEl g) ev = absurdEl (bwd-absurd (FunEl g) tt (invM (FunEl g) ev))
    conv-eta-bwd (PiCode a0 f0) ev = absurdEl (bwd-absurd (PiCode a0 f0) tt (invM (PiCode a0 f0) ev))
    conv-eta-bwd (SigmaCode a0 f0) ev = absurdEl (bwd-absurd (SigmaCode a0 f0) tt (invM (SigmaCode a0 f0) ev))

    invMkPairFstSnd : InvTyp G (MkPair (Fst M) (Snd M)) (RawSyntaxSigma.Sigma A B) rho
    invMkPairFstSnd u ev =
      let evM' = conv-eta-fwd u ev
          r = invM u evM'
          u' = fst r
          a' = fst (snd r)
          le = fst (snd (snd r))
          evM-u' = fst (snd (snd (snd r)))
          fm = fst (snd (snd (snd (snd r))))
          evSig = snd (snd (snd (snd (snd r))))
          evMkPair-u' = conv-eta-bwd u' evM-u'
      in mkTyped-split u u' a' le evMkPair-u' fm evSig
