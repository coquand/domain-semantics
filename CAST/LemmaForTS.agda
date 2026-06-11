{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- MIN/LemmaForTS.agda  (Pi + U fragment)
--
-- Provides:
-- - replaceKeys and related graph manipulation
-- - Lam-L1 (Lam inversion with typed keys)
-- - Fits / Typed / InvTyp / InvConv
-- - InvTyp-Lam / InvTyp-Pi
-- - InvTyp-App
-- - InvConv-beta / InvConv-funext / InvConv-App-fun / InvConv-App-arg
--
-- 0 postulates.
------------------------------------------------------------------------

module CAST.LemmaForTS where

import CAST.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ; fst ; snd ;
              Pair ; List ; nil ; cons ; Eq ; refl ; Eq-transport ; Eq-sym ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; FinFun)
open import CAST.PaperSemantics using (LeCode ; LeCode-refl ; LeCode-trans ; LeCode-Bot ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ; cft-from-cf ;
  CoherentWith ;
  NotBot ; FinMem ; FinMemFun ; FinMemAllU ; FinMem-coh-u ; FinMem-a-in-U ; coh-from-aU ;
  finMem-bot-from ; finMem-piU-mk ; finMem-funel-mk ;
  finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft ;
  finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf ;
  finMem-upward ;
  Sup ; Sup-Bot-r ; Sup-Bot-l ;
  Comp ; comp-Bot-r ; comp-Bot-l ; Comp-down ; Comp-sym ;
  Coherent-Sup ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub ;
  LeCode-Comp ;
  EvalFun ; EvalFun-mon-arg ; Coherent-EvalFun ;
  FinMem-Sup-element ;
  LeFunCode ; LeFunCode-refl ; append ;
  EvalFun-in-UCode ;
  finMemUCode-Sup ; Comp-refl)
open CFTcons
open import CAST.FinMemStageUnfold using ( finMemC-idU-mk )
open import CAST.Selection using (Selection ; Edge ; EdgeIn ; here ; there ;
  sel-nil ; sel-take ; sel-skip ;
  Coherent-Selection ; Coherent-Selection-val ;
  CoherentFun-edge-key ;
  singleton-selection ; Selection-le-EvalFun ; selectionBelow ;
  FinMem-Selection ; FinMem-Selection-codomain)
open import CAST.RawSyntax using (Expr ; Var ; U ; Pi ; Lam ; App ; Id ;
  Fin ; fzero ; fsuc ; Ren ; liftRen ; renExpr ; wkRen ; wkExpr ; subst1)
open import CAST.RawSemantics
open import CAST.TypingRules using (Ctx ; empty ; extend ; lookup ;
  HasType ; ty-var ; ty-conv ; ty-U ; ty-Pi ; ty-Lam ; ty-App ;
  WfCtx ; wf-empty ; wf-extend ;
  ConvTm ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg)
open import CAST.EvalSubstitution using (EvalRel-ren ; EvalRel-wk ; EvalRel-unwk ;
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
  mkSigma Bot (mkSigma tt (mkSigma (finMem-bot-from a aU) (EvalRel-Bot M (extendEnv rho Bot))))
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
Lam-L1 A M rho (PiCode a f)     nb crho ()
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
NotBot-from-Le u (FunEl g) cu nbu le = tt
NotBot-from-Le u (PiCode a f) cu nbu le = tt
NotBot-from-Le u (IdCode a b) cu nbu le = tt

NotBot-from-FinMem : (u a : FinEl) -> NotBot u -> FinMem u a -> NotBot a
NotBot-from-FinMem Bot a () fm
NotBot-from-FinMem UCode Bot nbu ()
NotBot-from-FinMem UCode UCode nbu fm = tt
NotBot-from-FinMem UCode (FunEl g) nbu ()
NotBot-from-FinMem UCode (PiCode a f) nbu ()
NotBot-from-FinMem UCode (IdCode a b) nbu ()
NotBot-from-FinMem (FunEl g) Bot nbu ()
NotBot-from-FinMem (FunEl g) (PiCode a f) nbu fm = tt
NotBot-from-FinMem (FunEl g) UCode nbu ()
NotBot-from-FinMem (FunEl g) (FunEl h) nbu ()
NotBot-from-FinMem (FunEl g) (IdCode a b) nbu ()
NotBot-from-FinMem (PiCode a f) Bot nbu ()
NotBot-from-FinMem (PiCode a f) UCode nbu fm = tt
NotBot-from-FinMem (PiCode a f) (PiCode c h) nbu ()
NotBot-from-FinMem (PiCode a f) (FunEl h) nbu ()
NotBot-from-FinMem (PiCode a f) (IdCode c d) nbu ()
NotBot-from-FinMem (IdCode a b) Bot nbu ()
NotBot-from-FinMem (IdCode a b) UCode nbu fm = tt
NotBot-from-FinMem (IdCode a b) (FunEl h) nbu ()
NotBot-from-FinMem (IdCode a b) (PiCode c h) nbu ()
NotBot-from-FinMem (IdCode a b) (IdCode c d) nbu ()

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
InvTyp-Lam A B M body-ih rho fits (PiCode a0 f0) ()
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
      fm-pi-U = finMem-piU-mk ac f aU fmAllU cft-f
      fmFun  = rv-fmFun ac g' ew' wf f cft-f fmAllU
                  (\ p ein -> replaceVals-corr g' (\ q qin -> fst (snd (wf q qin))) p ein)
      fm-h-pi = finMem-funel-mk h ac f fmFun cf-h fm-pi-U
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
    mkEvalApp (FunEl g) nbv0 w evN evM-sing = mkSigma w (mkSigma evN evM-sing)
    mkEvalApp (PiCode a0 f0) nbv0 w evN evM-sing = mkSigma w (mkSigma evN evM-sing)
    mkEvalApp (IdCode a0 b0) nbv0 w evN evM-sing = mkSigma w (mkSigma evN evM-sing)

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
    app-h-case w v nbv cv evN evM-sing (PiCode _ _) piaf () evPi
    app-h-case w v nbv cv evN evM-sing (FunEl g') Bot le-g' evM-g' () evPi
    app-h-case w v nbv cv evN evM-sing (FunEl g') UCode le-g' evM-g' () evPi
    app-h-case w v nbv cv evN evM-sing (FunEl g') (FunEl _) le-g' evM-g' () evPi
    app-h-case w v nbv cv evN evM-sing (FunEl g') (PiCode a f) le-g' evM-g' fm-g' evPi =
      let fmFun-g' = finMem-funel-fun g' a f fm-g'
          cf-g'    = finMem-funel-coh g' a f fm-g'
          piU      = finMem-funel-wf g' a f fm-g'
          aU       = finMem-piU-dom a f piU
          fmAllU-f = finMem-piU-allU a f piU
          cf-f     = finMem-piU-cft a f piU
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
    invTyp-App-aux (FunEl g) ev =
      let w = fst ev ; evN = fst (snd ev) ; evM-sing = snd (snd ev)
          cv = EvalRel-coh (App M N) rho (FunEl g) ev
      in app-main w (FunEl g) tt cv evN evM-sing
    invTyp-App-aux (PiCode a0 f0) ev =
      let w = fst ev ; evN = fst (snd ev) ; evM-sing = snd (snd ev)
          cv = EvalRel-coh (App M N) rho (PiCode a0 f0) ev
      in app-main w (PiCode a0 f0) tt cv evN evM-sing
    invTyp-App-aux (IdCode a0 b0) ev =
      let w = fst ev ; evN = fst (snd ev) ; evM-sing = snd (snd ev)
          cv = EvalRel-coh (App M N) rho (IdCode a0 b0) ev
      in app-main w (IdCode a0 b0) tt cv evN evM-sing

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
    conv-app-to-sub (FunEl g') ev = conv-app-to-sub-nonbot (FunEl g') tt ev
    conv-app-to-sub (PiCode a0 f0) ev = conv-app-to-sub-nonbot (PiCode a0 f0) tt ev
    conv-app-to-sub (IdCode a0 b0) ev = conv-app-to-sub-nonbot (IdCode a0 b0) tt ev

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
          mkSigma Bot (mkSigma tt (mkSigma (finMem-bot-from a' a'U) (EvalRel-Bot M (extendEnv rho Bot))))
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
    conv-sub-to-app (FunEl g') ev =
      let r = mkLamEvidence (FunEl g') tt ev
      in mkSigma (fst r) (mkSigma (fst (snd r)) (snd (snd r)))
    conv-sub-to-app (PiCode a0 f0) ev =
      let r = mkLamEvidence (PiCode a0 f0) tt ev
      in mkSigma (fst r) (mkSigma (fst (snd r)) (snd (snd r)))
    conv-sub-to-app (IdCode a0 b0) ev =
      let r = mkLamEvidence (IdCode a0 b0) tt ev
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
    mkAppEvidence F x (FunEl g') cx nbvi evF =
      mkSigma x (mkSigma (mkSigma cx (LeCode-refl x cx))
        (EvalRel-wk F rho x (FunEl (cons (mkSigma x (FunEl g')) nil)) evF))
    mkAppEvidence F x (PiCode a0 f0) cx nbvi evF =
      mkSigma x (mkSigma (mkSigma cx (LeCode-refl x cx))
        (EvalRel-wk F rho x (FunEl (cons (mkSigma x (PiCode a0 f0)) nil)) evF))
    mkAppEvidence F x (IdCode a0 b0) cx nbvi evF =
      mkSigma x (mkSigma (mkSigma cx (LeCode-refl x cx))
        (EvalRel-wk F rho x (FunEl (cons (mkSigma x (IdCode a0 b0)) nil)) evF))

    decompAppEvidence : (F : Expr _) (x vi : FinEl) -> NotBot vi ->
      EvalRel (App (wkExpr F) (Var fzero)) (extendEnv rho x) vi ->
      Sigma FinEl (\ w -> Pair (LeCode w x) (Pair (Coherent w)
        (EvalRel F rho (FunEl (cons (mkSigma w vi) nil)))))
    decompAppEvidence F x UCode nbvi ev =
      let w = fst ev ; evV0 = fst (snd ev) ; evWkF = snd (snd ev)
      in mkSigma w (mkSigma (snd evV0) (mkSigma (fst evV0)
           (EvalRel-unwk F rho x (FunEl (cons (mkSigma w UCode) nil)) evWkF)))
    decompAppEvidence F x (FunEl g') nbvi ev =
      let w = fst ev ; evV0 = fst (snd ev) ; evWkF = snd (snd ev)
      in mkSigma w (mkSigma (snd evV0) (mkSigma (fst evV0)
           (EvalRel-unwk F rho x (FunEl (cons (mkSigma w (FunEl g')) nil)) evWkF)))
    decompAppEvidence F x (PiCode a0 f0) nbvi ev =
      let w = fst ev ; evV0 = fst (snd ev) ; evWkF = snd (snd ev)
      in mkSigma w (mkSigma (snd evV0) (mkSigma (fst evV0)
           (EvalRel-unwk F rho x (FunEl (cons (mkSigma w (PiCode a0 f0)) nil)) evWkF)))
    decompAppEvidence F x (IdCode a0 b0) nbvi ev =
      let w = fst ev ; evV0 = fst (snd ev) ; evWkF = snd (snd ev)
      in mkSigma w (mkSigma (snd evV0) (mkSigma (fst evV0)
           (EvalRel-unwk F rho x (FunEl (cons (mkSigma w (IdCode a0 b0)) nil)) evWkF)))

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
    conv-main F F' convDir (FunEl _) Bot piaf cu () evF fm evPi
    conv-main F F' convDir (PiCode _ _) Bot piaf cu () evF fm evPi
    conv-main F F' convDir (IdCode _ _) Bot piaf cu () evF fm evPi
    conv-main F F' convDir u (FunEl g') Bot cu le-u evF () evPi
    conv-main F F' convDir u (FunEl g') UCode cu le-u evF () evPi
    conv-main F F' convDir u (FunEl g') (FunEl _) cu le-u evF () evPi
    conv-main F F' convDir u (FunEl g') (IdCode _ _) cu le-u evF () evPi
    conv-main F F' convDir Bot (FunEl g') (PiCode a f) cu le-u evF fm evPi =
      EvalRel-Bot F' rho
    conv-main F F' convDir UCode (FunEl g') (PiCode a f) cu () evF fm evPi
    conv-main F F' convDir (FunEl h) (FunEl g') (PiCode a f) cu le-u evF fm evPi =
      let cf-g'  = finMem-funel-coh g' a f fm
          fmf-g' = finMem-funel-fun g' a f fm
          evA    = fst (snd evPi)
          evF'-g' = build-graph F' g' cf-g'
                      (\ p ein -> edge-original F F' convDir a f evA g' cf-g' fmf-g' evF p ein)
      in EvalRel-down F' rho (FunEl g') (FunEl h) crho cu evF'-g' le-u
    conv-main F F' convDir (PiCode _ _) (FunEl g') (PiCode a f) cu () evF fm evPi
    conv-main F F' convDir u UCode Bot cu le-u evF () evPi
    conv-main F F' convDir u UCode UCode cu le-u evF fm ()
    conv-main F F' convDir u UCode (FunEl _) cu le-u evF () evPi
    conv-main F F' convDir u UCode (PiCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u UCode (IdCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u (PiCode a0 f0) Bot cu le-u evF () evPi
    conv-main F F' convDir u (PiCode a0 f0) UCode cu le-u evF fm ()
    conv-main F F' convDir u (PiCode a0 f0) (FunEl _) cu le-u evF () evPi
    conv-main F F' convDir u (PiCode a0 f0) (PiCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u (PiCode a0 f0) (IdCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u (IdCode _ _) Bot cu le-u evF () evPi
    conv-main F F' convDir u (IdCode _ _) UCode cu le-u evF fm ()
    conv-main F F' convDir u (IdCode _ _) (FunEl _) cu le-u evF () evPi
    conv-main F F' convDir u (IdCode _ _) (PiCode _ _) cu le-u evF () evPi
    conv-main F F' convDir u (IdCode _ _) (IdCode _ _) cu le-u evF () evPi

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
    conv-one-dir F F' invF convDir (FunEl g0) ev =
      conv-nonbot F F' invF convDir (FunEl g0) tt ev
    conv-one-dir F F' invF convDir (PiCode a0 f0) ev =
      conv-nonbot F F' invF convDir (PiCode a0 f0) tt ev
    conv-one-dir F F' invF convDir (IdCode a0 b0) ev =
      conv-nonbot F F' invF convDir (IdCode a0 b0) tt ev

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
    conv-fwd eqF (FunEl g') (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma eva (eqF (FunEl (cons (mkSigma v (FunEl g')) nil)) evf))
    conv-fwd eqF (PiCode a0 f0) (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma eva (eqF (FunEl (cons (mkSigma v (PiCode a0 f0)) nil)) evf))
    conv-fwd eqF (IdCode a0 b0) (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma eva (eqF (FunEl (cons (mkSigma v (IdCode a0 b0)) nil)) evf))

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
    conv-fwd (FunEl g') (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma (fwdA v eva) evf)
    conv-fwd (PiCode a0 f0) (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma (fwdA v eva) evf)
    conv-fwd (IdCode a0 b0) (mkSigma v (mkSigma eva evf)) =
      mkSigma v (mkSigma (fwdA v eva) evf)

    conv-bwd : (u : FinEl) -> EvalRel (App f a') rho u -> EvalRel (App f a) rho u
    conv-bwd Bot ev = tt
    conv-bwd UCode (mkSigma v (mkSigma eva' evf)) =
      mkSigma v (mkSigma (bwdA v eva') evf)
    conv-bwd (FunEl g') (mkSigma v (mkSigma eva' evf)) =
      mkSigma v (mkSigma (bwdA v eva') evf)
    conv-bwd (PiCode a0 f0) (mkSigma v (mkSigma eva' evf)) =
      mkSigma v (mkSigma (bwdA v eva') evf)
    conv-bwd (IdCode a0 b0) (mkSigma v (mkSigma eva' evf)) =
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
InvTyp-Pi A B rho fits invA body-ih (FunEl g) ()
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
    finMem-from-U-top Bot evU (FunEl g) ()
    finMem-from-U-top Bot evU (PiCode a0 f0) ()
    finMem-from-U-top UCode evU y fm = fm
    finMem-from-U-top (FunEl g) (mkSigma _ ()) y fm
    finMem-from-U-top (PiCode a0 f0) (mkSigma _ ()) y fm

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
    finMem-from-U vi0 Bot evU (FunEl g) ()
    finMem-from-U vi0 Bot evU (PiCode a0 f0) ()
    finMem-from-U vi0 UCode evU y fm = fm
    finMem-from-U vi0 (FunEl g) (mkSigma _ ()) y fm
    finMem-from-U vi0 (PiCode a0 f0) (mkSigma _ ()) y fm

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
    fm-pi-U = finMem-piU-mk b_new f' b_newU fmAllU-f' cf-f'

    result : Typed (Pi A B) U rho (PiCode b f)
    result = mkSigma (PiCode b_new f') (mkSigma UCode
      (mkSigma (mkSigma le-b-b_new lf-f-f')
        (mkSigma evPi-new (mkSigma fm-pi-U (mkSigma tt tt)))))

------------------------------------------------------------------------
-- InvTyp-Id
--
-- Adequacy for the Id-former  Γ ⊢ Id A B : U.  Mirrors InvTyp-Pi but the
-- proof-irrelevant Id has NO function part: an approximant of (Id A B) is a
-- code (IdCode a b) with a approximating A and b approximating B.  The typed
-- enlargement at the IdCode case just takes the typed enlargements a1, b1 of
-- the two components (already in U), so no Sup is needed.
------------------------------------------------------------------------

InvTyp-Id : {n : Nat} {G : Ctx n} (A B : Expr n) ->
  (rho : EnvApprox n) -> Fits G rho ->
  InvTyp G A U rho ->
  InvTyp G B U rho ->
  InvTyp G (Id A B) U rho
InvTyp-Id A B rho fits invA invB Bot ev =
  mkSigma Bot (mkSigma UCode (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma tt tt)))))
InvTyp-Id A B rho fits invA invB UCode ()
InvTyp-Id A B rho fits invA invB (FunEl g) ()
InvTyp-Id A B rho fits invA invB (PiCode a f) ()
InvTyp-Id A B rho fits invA invB (IdCode a b) ev =
  mkSigma (IdCode a1 b1) (mkSigma UCode
    (mkSigma (mkSigma le-a-a1 le-b-b1)
      (mkSigma (mkSigma (mkSigma ca1 cb1) (mkSigma evA-a1 evB-b1))
        (mkSigma (finMemC-idU-mk a1 b1 a1U b1U) (mkSigma tt tt)))))
  where
    evA-a = fst (snd ev)
    evB-b = snd (snd ev)

    finMem-from-U : (x : FinEl) -> EvalRel U rho x ->
      (y : FinEl) -> FinMem y x -> FinMem y UCode
    finMem-from-U Bot evU Bot fm = tt
    finMem-from-U Bot evU UCode ()
    finMem-from-U Bot evU (FunEl g0) ()
    finMem-from-U Bot evU (PiCode a0 f0) ()
    finMem-from-U Bot evU (IdCode a0 b0) ()
    finMem-from-U UCode evU y fm = fm
    finMem-from-U (FunEl g0) (mkSigma _ ()) y fm
    finMem-from-U (PiCode a0 f0) (mkSigma _ ()) y fm
    finMem-from-U (IdCode a0 b0) (mkSigma _ ()) y fm

    typed-a = invA a evA-a
    a1      = fst typed-a
    atype   = fst (snd typed-a)
    le-a-a1 = fst (snd (snd typed-a))
    evA-a1  = fst (snd (snd (snd typed-a)))
    fm-a1   = fst (snd (snd (snd (snd typed-a))))
    evU-at  = snd (snd (snd (snd (snd typed-a))))
    a1U     = finMem-from-U atype evU-at a1 fm-a1
    ca1     = coh-from-aU a1 a1U

    typed-b = invB b evB-b
    b1      = fst typed-b
    btype   = fst (snd typed-b)
    le-b-b1 = fst (snd (snd typed-b))
    evB-b1  = fst (snd (snd (snd typed-b)))
    fm-b1   = fst (snd (snd (snd (snd typed-b))))
    evU-bt  = snd (snd (snd (snd (snd typed-b))))
    b1U     = finMem-from-U btype evU-bt b1 fm-b1
    cb1     = coh-from-aU b1 b1U

