{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Model/SemLam.agda
--
-- Semantic typing ("every approximant has a typed enlargement"),
-- generically for predicates, and its two key instances:
--   Lam-typed : lambda approximants are typed in Pi(A, \x:A.B)
--   App-typed : applications of typed functions are typed
-- (ported from NAT/Model/SoundnessLemmas: replaceKeys / replaceVals,
--  InvTyp-Lam, InvTyp-App, with the body expressions replaced by
--  abstract body families).
------------------------------------------------------------------------

module MAHLOINJ.Model.SemLam where

open import MAHLOINJ.Domain.Basic
  using ( Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-transport ; Eq-sym
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl
        ; PairEl ; SigmaCode ; FinFun ; nil ; cons )
open import MAHLOINJ.Domain.Kernel
open import MAHLOINJ.Model.Selection
open import MAHLOINJ.Model.Comb

------------------------------------------------------------------------
-- Semantic typing of predicates
------------------------------------------------------------------------

TypedP : Pred -> Pred -> FinEl -> Set
TypedP PM PA u =
  Sigma FinEl (\ u' -> Sigma FinEl (\ a' ->
    Pair (LeCode u u') (Pair (PM u') (Pair (FinMem u' a') (PA a')))))

InvTypP : Pred -> Pred -> Set
InvTypP PM PA = (u : FinEl) -> PM u -> TypedP PM PA u

TypedP-Bot : (PM PA : Pred) -> PM Bot -> PA Bot -> TypedP PM PA Bot
TypedP-Bot PM PA pm pa = mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma pm (mkSigma tt pa))))

-- transport of typing along inclusions
InvTypP-map : (PM PM' PA PA' : Pred) -> ((u : FinEl) -> PM u -> PM' u) -> ((u : FinEl) -> PM' u -> PM u) ->
  ((u : FinEl) -> PA u -> PA' u) -> InvTypP PM PA -> InvTypP PM' PA'
InvTypP-map PM PM' PA PA' f g h inv u e =
  let t = inv u (g u e)
  in mkSigma (fst t) (mkSigma (fst (snd t)) (mkSigma (fst (snd (snd t)))
       (mkSigma (f _ (fst (snd (snd (snd t))))) (mkSigma (fst (snd (snd (snd (snd t)))))
         (h _ (snd (snd (snd (snd (snd t))))))))))

------------------------------------------------------------------------
-- small helpers on graphs
------------------------------------------------------------------------

NotBot-from-FinMem : (u a : FinEl) -> NotBot u -> FinMem u a -> NotBot a
NotBot-from-FinMem u Bot nb fm = go u nb fm
  where
    go : (u : FinEl) -> NotBot u -> FinMem u Bot -> NotBot Bot
    go Bot () fm
NotBot-from-FinMem u UCode           nb fm = tt
NotBot-from-FinMem u (FunEl _)       nb fm = tt
NotBot-from-FinMem u (PiCode _ _)    nb fm = tt
NotBot-from-FinMem u NatCode         nb fm = tt
NotBot-from-FinMem u ZeroEl          nb fm = tt
NotBot-from-FinMem u (SucEl _)       nb fm = tt
NotBot-from-FinMem u (PairEl _ _)    nb fm = tt
NotBot-from-FinMem u (SigmaCode _ _) nb fm = tt

LeFunCode-lookup : (e : Edge) (g h : FinFun) ->
  LeFunCode g h -> EdgeIn e g -> LeCode (snd e) (EvalFun h (fst e))
LeFunCode-lookup e (cons p ps) h lf here = fst lf
LeFunCode-lookup e (cons p ps) h lf (there ein) = LeFunCode-lookup e ps h (snd lf) ein

cft-edge-val : (e : Edge) (g : FinFun) -> CoherentFunTail g -> EdgeIn e g ->
  Pair (Coherent (snd e)) (NotBot (snd e))
cft-edge-val e (cons p ps) cg here = mkSigma (CFTcons.val-coh cg) (CFTcons.val-nbot cg)
cft-edge-val e (cons p ps) cg (there ein) = cft-edge-val e ps (CFTcons.tail-coh cg) ein

cft-edge : {g : FinFun} -> CoherentFunTail g -> {e : Edge} -> EdgeIn e g -> CoherentFunTail (cons e nil)
cft-edge {cons p ps} cg here = mkCFT (CFTcons.key-coh cg) (CFTcons.val-coh cg) (CFTcons.val-nbot cg) tt tt
cft-edge {cons p ps} cg (there ein) = cft-edge (CFTcons.tail-coh cg) ein

EvalFun-edge-le : (e : Edge) (g : FinFun) (u : FinEl) ->
  CoherentFunTail g -> EdgeIn e g -> Coherent u -> LeCode (fst e) u ->
  LeCode (snd e) (EvalFun g u)
EvalFun-edge-le e (cons p ps) u cg ein cu le =
  let ck   = CoherentFun-edge-key e (cons p ps) cg ein
      cv   = fst (cft-edge-val e (cons p ps) cg ein)
      lr   = LeFunCode-refl (cons p ps) cg
      le-k = LeFunCode-lookup e (cons p ps) (cons p ps) lr ein
      cef  = Coherent-EvalFun (cons p ps) (fst e) cg ck
      cefu = Coherent-EvalFun (cons p ps) u cg cu
      mon  = EvalFun-mon-arg (cons p ps) (fst e) u le cg ck cu
  in LeCode-trans (snd e) (EvalFun (cons p ps) (fst e)) (EvalFun (cons p ps) u) cv cef cefu le-k mon

replaceKeys : (g : FinFun) -> ((p : Edge) -> EdgeIn p g -> FinEl) -> FinFun
replaceKeys nil         f = nil
replaceKeys (cons p ps) f = cons (mkSigma (f p here) (snd p)) (replaceKeys ps (\ q ein -> f q (there ein)))

replaceKeys-corr : (g : FinFun) (f : (p : Edge) -> EdgeIn p g -> FinEl) (q : Edge) (ein : EdgeIn q g) ->
  EdgeIn (mkSigma (f q ein) (snd q)) (replaceKeys g f)
replaceKeys-corr (cons p ps) f .p here = here
replaceKeys-corr (cons p ps) f q (there ein) = there (replaceKeys-corr ps (\ r rin -> f r (there rin)) q ein)

replaceVals : (g : FinFun) -> ((p : Edge) -> EdgeIn p g -> FinEl) -> FinFun
replaceVals nil         f = nil
replaceVals (cons p ps) f = cons (mkSigma (fst p) (f p here)) (replaceVals ps (\ q ein -> f q (there ein)))

replaceVals-corr : (g : FinFun) (f : (p : Edge) -> EdgeIn p g -> FinEl) (q : Edge) (ein : EdgeIn q g) ->
  EdgeIn (mkSigma (fst q) (f q ein)) (replaceVals g f)
replaceVals-corr (cons p ps) f .p here = here
replaceVals-corr (cons p ps) f q (there ein) = there (replaceVals-corr ps (\ r rin -> f r (there rin)) q ein)

------------------------------------------------------------------------
-- Lambda, generically over a domain predicate PA and body families
------------------------------------------------------------------------

module LamTyping (PA : Pred) (iA : Ideal PA) where

  -- edge witnesses for a body family B
  EW : (B : FinEl -> Pred) -> FinEl -> FinFun -> Set
  EW B a g = (p : Edge) -> EdgeIn p g ->
    Sigma FinEl (\ x -> Pair (LeCode x (fst p)) (Pair (FinMem x a) (B x (snd p))))

  -- edgewise data at the keys themselves
  EK : (B : FinEl -> Pred) -> FinEl -> FinFun -> Set
  EK B a g = (e : Edge) -> EdgeIn e g -> Pair (FinMem (fst e) a) (B (fst e) (snd e))

  EK-to-EW : (B : FinEl -> Pred) (a : FinEl) (g : FinFun) -> EK B a g -> EW B a g
  EK-to-EW B a g ek e ein =
    let k = ek e ein ; ck = FinMem-coh-u (fst e) a (fst k)
    in mkSigma (fst e) (mkSigma (LeCode-refl (fst e) ck) k)

  module Keys (B : FinEl -> Pred) (bB : BodyOK B) where

    open LamProps PA B iA bB using (comp-via-body)

    rk-cw : (a : FinEl) (s : Edge) (rest : FinFun) ->
      FinMem (fst s) a -> B (fst s) (snd s) -> (wf : EW B a rest) ->
      CoherentWith s (replaceKeys rest (\ p ein -> fst (wf p ein)))
    rk-cw a s nil ms evs wf = tt
    rk-cw a s (cons t ts) ms evs wf =
      let wt = wf t here ; xt = fst wt ; mt = fst (snd (snd wt)) ; evt = snd (snd (snd wt))
          step : Comp (fst s) xt -> Comp (snd s) (snd t)
          step ck = comp-via-body (fst s) xt (snd s) (snd t) ck (FinMem-coh-u (fst s) a ms)
                      (FinMem-coh-u xt a mt) evs evt
      in mkSigma step (rk-cw a s ts ms evs (\ q qin -> wf q (there qin)))

    rk-cft : (a : FinEl) (g : FinFun) -> CoherentFunTail g -> (wf : EW B a g) ->
      CoherentFunTail (replaceKeys g (\ p ein -> fst (wf p ein)))
    rk-cft a nil cg wf = tt
    rk-cft a (cons p ps) cg wf =
      let wp = wf p here ; xp = fst wp ; mp = fst (snd (snd wp)) ; evp = snd (snd (snd wp))
      in mkCFT (FinMem-coh-u xp a mp) (CFTcons.val-coh cg) (CFTcons.val-nbot cg)
           (rk-cw a (mkSigma xp (snd p)) ps mp evp (\ q qin -> wf q (there qin)))
           (rk-cft a ps (CFTcons.tail-coh cg) (\ q qin -> wf q (there qin)))

    rk-ek : (a : FinEl) (g : FinFun) (wf : EW B a g) -> EK B a (replaceKeys g (\ p ein -> fst (wf p ein)))
    rk-ek a (cons p ps) wf .(mkSigma (fst (wf p here)) (snd p)) here =
      mkSigma (fst (snd (snd (wf p here)))) (snd (snd (snd (wf p here))))
    rk-ek a (cons p ps) wf e (there ein) = rk-ek a ps (\ q qin -> wf q (there qin)) e ein

    rk-le-tail : (a : FinEl) (ps orig : FinFun) -> CoherentFunTail orig -> (wf : EW B a orig) ->
      CoherentFunTail (replaceKeys orig (\ q ein -> fst (wf q ein))) ->
      (shift : (q : Edge) -> EdgeIn q ps -> EdgeIn q orig) ->
      ((q : Edge) (ein : EdgeIn q ps) ->
         EdgeIn (mkSigma (fst (wf q (shift q ein))) (snd q)) (replaceKeys orig (\ q ein -> fst (wf q ein)))) ->
      LeFunCode ps (replaceKeys orig (\ q ein -> fst (wf q ein)))
    rk-le-tail a nil orig cg wf cft' shift corr = tt
    rk-le-tail a (cons q qs) orig cg wf cft' shift corr =
      let wq = wf q (shift q here)
          ck = CFTcons.key-coh (cft-edge cg (shift q here))
      in mkSigma (EvalFun-edge-le (mkSigma (fst wq) (snd q)) _ (fst q) cft' (corr q here) ck (fst (snd wq)))
                 (rk-le-tail a qs orig cg wf cft' (\ r rin -> shift r (there rin)) (\ r rin -> corr r (there rin)))

    rk-le : (a : FinEl) (g : FinFun) -> CoherentFunTail g -> (wf : EW B a g) ->
      LeFunCode g (replaceKeys g (\ p ein -> fst (wf p ein)))
    rk-le a g cg wf =
      rk-le-tail a g g cg wf (rk-cft a g cg wf) (\ q qin -> qin)
        (\ q qin -> replaceKeys-corr g (\ r rin -> fst (wf r rin)) q qin)

  -- Lam-L1 : a Lam approximant is below one whose keys are typed in a
  Lam-L1 : (B : FinEl -> Pred) (bB : BodyOK B) (g : FinFun) -> LamBody PA B g ->
    Sigma FinEl (\ a -> Sigma FinFun (\ g' ->
      Pair (PA a) (Pair (FinMem a UCode) (Pair (LeFunCode g g')
        (Pair (LamBody PA B g') (EK B a g'))))))
  Lam-L1 B bB nil e = Empty-elim (fst (snd e))
  Lam-L1 B bB (cons p0 ps0) e =
    let g  = cons p0 ps0
        a  = fst e ; cg = fst (snd e) ; aU = fst (snd (snd e)) ; evA = fst (snd (snd (snd e)))
        wf = LamBody-edge a B g (snd (snd (snd (snd e))))
        g' = replaceKeys g (\ p ein -> fst (wf p ein))
        cg' = Keys.rk-cft B bB a g cg wf
        ek = Keys.rk-ek B bB a g wf
        lb : LamBody PA B g'
        lb = mkSigma a (mkSigma cg' (mkSigma aU (mkSigma evA
               (LamEdges.from-edges B bB a g' cg' aU (EK-to-EW B a g' ek)))))
    in mkSigma a (mkSigma g' (mkSigma evA (mkSigma aU (mkSigma (Keys.rk-le B bB a g cg wf) (mkSigma lb ek)))))

  ----------------------------------------------------------------------
  -- Lam-typed
  ----------------------------------------------------------------------

  module Typing (Bm Bb : FinEl -> Pred) (okm : BodyOK Bm) (okb : BodyOK Bb)
    (body-ih : (x a : FinEl) -> FinMem x a -> PA a -> InvTypP (Bm x) (Bb x)) where

    open LamProps PA Bm iA okm using () renaming (comp-via-body to compM)
    open LamProps PA Bb iA okb using () renaming (comp-via-body to compB)

    WF : FinFun -> Set
    WF g = (p : Edge) -> EdgeIn p g ->
      Sigma FinEl (\ yi -> Sigma FinEl (\ bi ->
        Pair (LeCode (snd p) yi) (Pair (Bm (fst p) yi) (Pair (FinMem yi bi) (Bb (fst p) bi)))))

    rv-cw : (sk sv : FinEl) (rest : FinFun) -> Coherent sk -> CoherentFunTail rest -> Bm sk sv ->
      (wf0 : WF rest) -> CoherentWith (mkSigma sk sv) (replaceVals rest (\ q ein -> fst (wf0 q ein)))
    rv-cw sk sv nil csk crest evs wf0 = tt
    rv-cw sk sv (cons t ts) csk crest evs wf0 =
      let wt = wf0 t here
      in mkSigma (\ ck -> compM sk (fst t) sv (fst wt) ck csk (CFTcons.key-coh crest) evs
                            (fst (snd (snd (snd wt)))))
                 (rv-cw sk sv ts csk (CFTcons.tail-coh crest) evs (\ q qin -> wf0 q (there qin)))

    rv-cft : (g : FinFun) -> CoherentFunTail g -> (wf0 : WF g) ->
      CoherentFunTail (replaceVals g (\ p ein -> fst (wf0 p ein)))
    rv-cft nil cg wf0 = tt
    rv-cft (cons p ps) cg wf0 =
      let wp = wf0 p here ; yp = fst wp ; bp = fst (snd wp)
          le-vp = fst (snd (snd wp)) ; ev-yp = fst (snd (snd (snd wp))) ; fm-yp = fst (snd (snd (snd (snd wp))))
          ck = CFTcons.key-coh cg
          nbyp = NotBot-from-Le (snd p) yp (CFTcons.val-nbot cg) le-vp
      in mkCFT ck (FinMem-coh-u yp bp fm-yp) nbyp
           (rv-cw (fst p) yp ps ck (CFTcons.tail-coh cg) ev-yp (\ q qin -> wf0 q (there qin)))
           (rv-cft ps (CFTcons.tail-coh cg) (\ q qin -> wf0 q (there qin)))

    rv-cw-f : (sk bk : FinEl) (rest : FinFun) -> Coherent sk -> CoherentFunTail rest -> Bb sk bk ->
      (wf0 : WF rest) -> CoherentWith (mkSigma sk bk) (replaceVals rest (\ q ein -> fst (snd (wf0 q ein))))
    rv-cw-f sk bk nil csk crest evs wf0 = tt
    rv-cw-f sk bk (cons t ts) csk crest evs wf0 =
      let wt = wf0 t here
      in mkSigma (\ ck -> compB sk (fst t) bk (fst (snd wt)) ck csk (CFTcons.key-coh crest) evs
                            (snd (snd (snd (snd (snd wt))))))
                 (rv-cw-f sk bk ts csk (CFTcons.tail-coh crest) evs (\ q qin -> wf0 q (there qin)))

    rv-cft-f : (g : FinFun) -> CoherentFunTail g -> (wf0 : WF g) ->
      CoherentFunTail (replaceVals g (\ p ein -> fst (snd (wf0 p ein))))
    rv-cft-f nil cg wf0 = tt
    rv-cft-f (cons p ps) cg wf0 =
      let wp = wf0 p here ; yp = fst wp ; bp = fst (snd wp)
          le-vp = fst (snd (snd wp)) ; fm-yp = fst (snd (snd (snd (snd wp))))
          ev-bp = snd (snd (snd (snd (snd wp))))
          ck = CFTcons.key-coh cg
          nbyp = NotBot-from-Le (snd p) yp (CFTcons.val-nbot cg) le-vp
          nbbp = NotBot-from-FinMem yp bp nbyp fm-yp
          cbp = coh-from-aU bp (FinMem-a-in-U yp bp fm-yp)
      in mkCFT ck cbp nbbp
           (rv-cw-f (fst p) bp ps ck (CFTcons.tail-coh cg) ev-bp (\ q qin -> wf0 q (there qin)))
           (rv-cft-f ps (CFTcons.tail-coh cg) (\ q qin -> wf0 q (there qin)))

    rv-ek : (a0 : FinEl) (g : FinFun) -> EK Bm a0 g -> (wf0 : WF g) ->
      EK Bm a0 (replaceVals g (\ p ein -> fst (wf0 p ein)))
    rv-ek a0 (cons p ps) ek wf0 .(mkSigma (fst p) (fst (wf0 p here))) here =
      mkSigma (fst (ek p here)) (fst (snd (snd (snd (wf0 p here)))))
    rv-ek a0 (cons p ps) ek wf0 e (there ein) =
      rv-ek a0 ps (\ q qin -> ek q (there qin)) (\ q qin -> wf0 q (there qin)) e ein

    rv-ek-f : (a0 : FinEl) (g : FinFun) -> EK Bm a0 g -> (wf0 : WF g) ->
      EK Bb a0 (replaceVals g (\ p ein -> fst (snd (wf0 p ein))))
    rv-ek-f a0 (cons p ps) ek wf0 .(mkSigma (fst p) (fst (snd (wf0 p here)))) here =
      mkSigma (fst (ek p here)) (snd (snd (snd (snd (snd (wf0 p here))))))
    rv-ek-f a0 (cons p ps) ek wf0 e (there ein) =
      rv-ek-f a0 ps (\ q qin -> ek q (there qin)) (\ q qin -> wf0 q (there qin)) e ein

    rv-lf-tail : (ps orig : FinFun) -> CoherentFunTail orig -> (wf0 : WF orig) ->
      CoherentFunTail (replaceVals orig (\ q ein -> fst (wf0 q ein))) ->
      (shift : (q : Edge) -> EdgeIn q ps -> EdgeIn q orig) ->
      ((q : Edge) (ein : EdgeIn q ps) ->
         EdgeIn (mkSigma (fst q) (fst (wf0 q (shift q ein)))) (replaceVals orig (\ q ein -> fst (wf0 q ein)))) ->
      LeFunCode ps (replaceVals orig (\ q ein -> fst (wf0 q ein)))
    rv-lf-tail nil orig cg wf0 cft-h shift corr = tt
    rv-lf-tail (cons q qs) orig cg wf0 cft-h shift corr =
      let h = replaceVals orig (\ r rin -> fst (wf0 r rin))
          wq = wf0 q (shift q here) ; yq = fst wq ; bq = fst (snd wq)
          le-vq = fst (snd (snd wq)) ; fm-yq = fst (snd (snd (snd (snd wq))))
          ce = cft-edge cg (shift q here)
          ck-q = CFTcons.key-coh ce ; cv-q = CFTcons.val-coh ce
          head-le = EvalFun-edge-le (mkSigma (fst q) yq) h (fst q) cft-h (corr q here) ck-q (LeCode-refl (fst q) ck-q)
          head = LeCode-trans (snd q) yq (EvalFun h (fst q)) cv-q (FinMem-coh-u yq bq fm-yq)
                   (Coherent-EvalFun h (fst q) cft-h ck-q) le-vq head-le
      in mkSigma head (rv-lf-tail qs orig cg wf0 cft-h (\ r rin -> shift r (there rin)) (\ r rin -> corr r (there rin)))

    rv-lf : (g : FinFun) -> CoherentFunTail g -> (wf0 : WF g) ->
      CoherentFunTail (replaceVals g (\ p ein -> fst (wf0 p ein))) ->
      LeFunCode g (replaceVals g (\ p ein -> fst (wf0 p ein)))
    rv-lf g cg wf0 cft-h =
      rv-lf-tail g g cg wf0 cft-h (\ q qin -> qin) (\ q qin -> replaceVals-corr g (\ r rin -> fst (wf0 r rin)) q qin)

    rv-fmFun : (a0 : FinEl) (g : FinFun) -> EK Bm a0 g -> (wf0 : WF g) ->
      (ff : FinFun) -> CoherentFunTail ff -> FinMemAllU ff a0 ->
      ((p : Edge) (ein : EdgeIn p g) -> EdgeIn (mkSigma (fst p) (fst (snd (wf0 p ein)))) ff) ->
      FinMemFun (replaceVals g (\ p ein -> fst (wf0 p ein))) a0 ff
    rv-fmFun a0 nil ek wf0 ff cft-ff allU corr = tt
    rv-fmFun a0 (cons p ps) ek wf0 ff cft-ff allU corr =
      let fm-k = fst (ek p here)
          wp = wf0 p here ; yp = fst wp ; bp = fst (snd wp) ; fm-yp = fst (snd (snd (snd (snd wp))))
          ck-p = FinMem-coh-u (fst p) a0 fm-k
          cbp = coh-from-aU bp (FinMem-a-in-U yp bp fm-yp)
          cef = Coherent-EvalFun ff (fst p) cft-ff ck-p
          efU = EvalFun-in-UCode ff (fst p) a0 cft-ff ck-p allU
          le-bp-ef = EvalFun-edge-le (mkSigma (fst p) bp) ff (fst p) cft-ff (corr p here) ck-p (LeCode-refl (fst p) ck-p)
      in mkSigma (mkSigma fm-k (finMem-upward yp bp (EvalFun ff (fst p)) le-bp-ef cbp cef fm-yp efU))
           (rv-fmFun a0 ps (\ q qin -> ek q (there qin)) (\ q qin -> wf0 q (there qin)) ff cft-ff allU
              (\ q qin -> corr q (there qin)))

    rv-fmAllU : (a0 : FinEl) (g : FinFun) -> EK Bm a0 g -> (wf0 : WF g) ->
      FinMemAllU (replaceVals g (\ p ein -> fst (snd (wf0 p ein)))) a0
    rv-fmAllU a0 nil ek wf0 = tt
    rv-fmAllU a0 (cons p ps) ek wf0 =
      let wp = wf0 p here
      in mkSigma (mkSigma (fst (ek p here)) (FinMem-a-in-U (fst wp) (fst (snd wp)) (fst (snd (snd (snd (snd wp)))))))
           (rv-fmAllU a0 ps (\ q qin -> ek q (there qin)) (\ q qin -> wf0 q (there qin)))

    Lam-typed : InvTypP (LamS PA Bm) (PiS PA (LamS PA Bb))
    Lam-typed Bot e = TypedP-Bot _ _ tt tt
    Lam-typed (FunEl nil) e = Empty-elim (fst (snd e))
    Lam-typed (FunEl (cons p0 ps0)) e =
      let g = cons p0 ps0
          l1 = Lam-L1 Bm okm g e
          ac = fst l1 ; g' = fst (snd l1) ; evA = fst (snd (snd l1)) ; aU = fst (snd (snd (snd l1)))
          le-g = fst (snd (snd (snd (snd l1)))) ; lb' = fst (snd (snd (snd (snd (snd l1)))))
          ek' = snd (snd (snd (snd (snd (snd l1)))))
          cg' = fst (snd lb')
          wf : WF g'
          wf p ein =
            let ep = ek' p ein
                inv = body-ih (fst p) ac (fst ep) evA (snd p) (snd ep)
            in mkSigma (fst inv) (mkSigma (fst (snd inv)) (snd (snd inv)))
          h = replaceVals g' (\ p ein -> fst (wf p ein))
          f = replaceVals g' (\ p ein -> fst (snd (wf p ein)))
          cft-h = rv-cft g' (cft-from-cf g' cg') wf
          cft-f = rv-cft-f g' (cft-from-cf g' cg') wf
          ek-h = rv-ek ac g' ek' wf
          ek-f = rv-ek-f ac g' ek' wf
          cu = cft-from-cf g (fst (snd e))
          le-u-h = LeCode-trans (FunEl g) (FunEl g') (FunEl h) (fst (snd e)) cg' cft-h
                     le-g (rv-lf g' (cft-from-cf g' cg') wf cft-h)
          lb-h : LamBody PA Bm h
          lb-h = mkSigma ac (mkSigma cft-h (mkSigma aU (mkSigma evA
                   (LamEdges.from-edges Bm okm ac h cft-h aU (EK-to-EW Bm ac h ek-h)))))
          lb-f : LamBody PA Bb f
          lb-f = mkSigma ac (mkSigma cft-f (mkSigma aU (mkSigma evA
                   (LamEdges.from-edges Bb okb ac f cft-f aU (EK-to-EW Bb ac f ek-f)))))
          ca = coh-from-aU ac aU
          allU = rv-fmAllU ac g' ek' wf
          fm-pi-U = finMem-piU-mk ac f aU allU cft-f
          fmFun = rv-fmFun ac g' ek' wf f cft-f allU
                    (\ p ein -> replaceVals-corr g' (\ q qin -> fst (snd (wf q qin))) p ein)
          fm-h = finMem-funel-mk h ac f fmFun cft-h fm-pi-U
      in mkSigma (FunEl h) (mkSigma (PiCode ac f)
           (mkSigma le-u-h (mkSigma lb-h (mkSigma fm-h
             (mkSigma (mkSigma ca cft-f) (mkSigma evA lb-f))))))

------------------------------------------------------------------------
-- App-typed : if PM is typed in Pi(PA, \x.Bb) then  PM PN  is typed in
-- any PT containing Bb w v for w in PN.  (N itself need not be typed.)
------------------------------------------------------------------------

module AppTyping (PM PN PA : Pred) (Bb : FinEl -> Pred) (PT : Pred)
  (iM : Ideal PM) (iN : Ideal PN) (okb : BodyOK Bb)
  (invM : InvTypP PM (PiS PA (LamS PA Bb)))
  (toT : (w v : FinEl) -> PN w -> Bb w v -> PT v) (tBot : PT Bot) where

  -- the codomain value of the typing code at the argument
  cod : (w u0 : FinEl) (a : FinEl) (f : FinFun) -> PN w -> Coherent u0 -> LeCode u0 w ->
    CoherentFunTail f -> FamRel (LamS PA Bb) f -> PT (EvalFun f u0)
  cod w u0 a nil ew cu0 le cf fr = tBot
  cod w u0 a (cons q qs) ew cu0 le cf lb =
    let f = cons q qs
        sb-f = selectionBelow f u0 cf cu0
        x-f = fst sb-f ; w-f = fst (snd sb-f) ; sel-f = fst (snd (snd sb-f))
        le-xf = fst (snd (snd (snd sb-f))) ; eq-wf = snd (snd (snd (snd sb-f)))
        r = snd (snd (snd (snd lb))) x-f w-f sel-f
        z = fst r ; le-z-xf = fst (snd r) ; fm-z = fst (snd (snd r)) ; bz = snd (snd (snd r))
        cz = FinMem-coh-u z (fst lb) fm-z
        cxf = Coherent-Selection sel-f cf
        cw = Ideal.coh iN w ew
        le-z-w = LeCode-trans z u0 w cz cu0 cw (LeCode-trans z x-f u0 cz cxf cu0 le-z-xf le-xf) le
        bz' = Eq-transport (Bb z) (Eq-sym eq-wf) bz
        bw = BodyOK.mon okb z w (EvalFun f u0) cz cw le-z-w bz'
    in toT w (EvalFun f u0) ew bw

  main : (w v : FinEl) -> NotBot v -> Coherent v -> PN w -> PM (sing w v) -> TypedP (AppS PM PN) PT v
  main w v nbv cv ew em = go (fst t) (fst (snd t)) (fst (snd (snd t))) (fst (snd (snd (snd t))))
                             (fst (snd (snd (snd (snd t))))) (snd (snd (snd (snd (snd t)))))
    where
      t = invM (sing w v) em
      go : (h piaf : FinEl) -> LeCode (sing w v) h -> PM h -> FinMem h piaf ->
           PiS PA (LamS PA Bb) piaf -> TypedP (AppS PM PN) PT v
      go (FunEl g') (PiCode a f) le-g' em-g' fm-g' evPi =
        let fmFun = finMem-funel-fun g' a f fm-g'
            cf-g' = finMem-funel-coh g' a f fm-g'
            piU = finMem-funel-wf g' a f fm-g'
            aU = finMem-piU-dom a f piU
            allU = finMem-piU-allU a f piU
            cf-f = finMem-piU-cft a f piU
            ca = coh-from-aU a aU
            cw = Ideal.coh iN w ew
            ctg' = cft-from-cf g' cf-g'
            sb = selectionBelow g' w ctg' cw
            u0 = fst sb ; v0 = fst (snd sb) ; sel-g' = fst (snd (snd sb))
            le-u0-w = fst (snd (snd (snd sb))) ; eq-v0 = snd (snd (snd (snd sb)))
            le-v-v0 = Eq-transport (LeCode v) eq-v0 (fst le-g')
            cu0 = Coherent-Selection sel-g' ctg'
            cv0 = Coherent-Selection-val sel-g' ctg'
            fm-v0 = FinMem-Selection-codomain a f sel-g' fmFun ctg' cf-f allU
            lf-v0 : LeFunCode (cons (mkSigma w v0) nil) g'
            lf-v0 = mkSigma (Eq-transport (\ x -> LeCode x (EvalFun g' w)) eq-v0
                       (LeCode-refl (EvalFun g' w) (Coherent-EvalFun g' w ctg' cw))) tt
            nbv0 = NotBot-from-Le v v0 nbv le-v-v0
            em-v0 = Ideal.down iM (FunEl g') (sing w v0) em-g' (sing-coh w v0 cw cv0 nbv0) lf-v0
        in mkSigma v0 (mkSigma (EvalFun f u0) (mkSigma le-v-v0
             (mkSigma (guard-intro v0 nbv0 (mkSigma w (mkSigma ew em-v0)))
               (mkSigma fm-v0 (cod w u0 a f ew cu0 le-u0-w cf-f (snd (snd evPi)))))))

  App-typed : InvTypP (AppS PM PN) PT
  App-typed v e = go (bot-or v)
    where
      go : Or (Eq v Bot) (NotBot v) -> TypedP (AppS PM PN) PT v
      go (left refl) = TypedP-Bot _ _ tt tBot
      go (right nb) =
        let b = guard-elim v nb e
            cv = sing-val-coh (fst b) v (Ideal.coh iM _ (snd (snd b)))
        in main (fst b) v nb cv (fst (snd b)) (snd (snd b))
