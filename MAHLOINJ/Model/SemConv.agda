{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Model/SemConv.agda
--
-- Semantic content of beta and eta (funext), generically
-- (port of NAT InvConv-beta / InvConv-funext).
------------------------------------------------------------------------

module MAHLOINJ.Model.SemConv where

open import MAHLOINJ.Domain.Basic
  using ( Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-transport ; Eq-sym
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl
        ; PairEl ; SigmaCode ; FinFun ; nil ; cons )
open import MAHLOINJ.Domain.Kernel
open import MAHLOINJ.Model.Selection
open import MAHLOINJ.Model.Comb
open import MAHLOINJ.Model.SemLam

Incl : Pred -> Pred -> Set
Incl P Q = (u : FinEl) -> P u -> Q u

-- typing transfers along a semantic equality
InvTyp-transfer : (P Q T : Pred) -> Incl P Q -> Incl Q P -> InvTypP P T -> InvTypP Q T
InvTyp-transfer P Q T pq qp inv u e =
  let t = inv u (qp u e)
  in mkSigma (fst t) (mkSigma (fst (snd t)) (mkSigma (fst (snd (snd t)))
       (mkSigma (pq _ (fst (snd (snd (snd t))))) (snd (snd (snd (snd t)))))))

ew-single : (B : FinEl -> Pred) (y u a : FinEl) -> LeCode y y -> FinMem y a -> B y u ->
  (p : Edge) -> EdgeIn p (cons (mkSigma y u) nil) ->
  Sigma FinEl (\ x -> Pair (LeCode x (fst p)) (Pair (FinMem x a) (B x (snd p))))
ew-single B y u a le m b .(mkSigma y u) here = mkSigma y (mkSigma le (mkSigma m b))

------------------------------------------------------------------------
-- beta:  (\x:A.M) N  ==  M[N]
------------------------------------------------------------------------

module Beta (PA PN PS : Pred) (Bm : FinEl -> Pred) (iA : Ideal PA) (iN : Ideal PN) (iS : Ideal PS)
  (okm : BodyOK Bm)
  (bwd : (z u : FinEl) -> PN z -> Bm z u -> PS u)
  (fwd : (u : FinEl) -> PS u -> Sigma FinEl (\ v -> Pair (PN v) (Bm v u)))
  (invN : InvTypP PN PA) where

  app-to-sub : Incl (AppS (LamS PA Bm) PN) PS
  app-to-sub u e = go (bot-or u)
    where
      go : Or (Eq u Bot) (NotBot u) -> PS u
      go (left refl) = Ideal.bot iS
      go (right nb) =
        let b = guard-elim u nb e
            v = fst b ; ev = fst (snd b) ; lam = snd (snd b)
            wp = LamBody-edge (fst lam) Bm (cons (mkSigma v u) nil) (snd (snd (snd (snd lam)))) (mkSigma v u) here
            z = fst wp
            cz = FinMem-coh-u z (fst lam) (fst (snd (snd wp)))
        in bwd z u (Ideal.down iN v z ev cz (fst (snd wp))) (snd (snd (snd wp)))

  sub-to-app : Incl PS (AppS (LamS PA Bm) PN)
  sub-to-app u e = go (bot-or u)
    where
      go : Or (Eq u Bot) (NotBot u) -> AppS (LamS PA Bm) PN u
      go (left refl) = tt
      go (right nb) =
        let fw = fwd u e
            v = fst fw ; evNv = fst (snd fw) ; evMv = snd (snd fw)
            t = invN v evNv
            y = fst t ; a' = fst (snd t) ; le-v-y = fst (snd (snd t)) ; evNy = fst (snd (snd (snd t)))
            memy = fst (snd (snd (snd (snd t)))) ; evAa' = snd (snd (snd (snd (snd t))))
            cy = FinMem-coh-u y a' memy
            cv = Ideal.coh iN v evNv
            evMy = BodyOK.mon okm v y u cv cy le-v-y evMv
            cu = Ideal.coh (BodyOK.ideal okm y cy) u evMy
            a'U = FinMem-a-in-U y a' memy
            ew = ew-single Bm y u a' (LeCode-refl y cy) memy evMy
            lam : LamBody PA Bm (cons (mkSigma y u) nil)
            lam = mkSigma a' (mkSigma (sing-coh y u cy cu nb) (mkSigma a'U (mkSigma evAa'
                    (LamEdges.from-edges Bm okm a' (cons (mkSigma y u) nil) (sing-coh y u cy cu nb) a'U ew))))
        in guard-intro u nb (mkSigma y (mkSigma evNy lam))

------------------------------------------------------------------------
-- funext:  M, N : Pi(A,\x.B)  and  M x == N x  pointwise  ==>  M == N
------------------------------------------------------------------------

module Funext (PA PM PN : Pred) (Bb : FinEl -> Pred) (iM : Ideal PM) (iN : Ideal PN)
  (invM : InvTypP PM (PiS PA (LamS PA Bb)))
  (pt : (x a : FinEl) -> FinMem x a -> PA a -> Incl (AppS PM (AtomS x)) (AppS PN (AtomS x))) where

  fmf-key : (h : FinFun) (a0 : FinEl) (f0 : FinFun) -> FinMemFun h a0 f0 ->
    (e : Edge) -> EdgeIn e h -> FinMem (fst e) a0
  fmf-key (cons q qs) a0 f0 fm .q here = fst (fst fm)
  fmf-key (cons q qs) a0 f0 fm e (there ein) = fmf-key qs a0 f0 (snd fm) e ein

  -- each edge of a typed graph of M is an edge of N
  edge : (a : FinEl) (f : FinFun) -> PA a -> (g' : FinFun) -> CoherentFun g' -> FinMemFun g' a f ->
    PM (FunEl g') -> (p : Edge) -> EdgeIn p g' -> PN (FunEl (cons p nil))
  edge a f evA g' cfg fmf evM p ein =
    let cft = cft-from-cf g' cfg
        cui = CoherentFun-edge-key p g' cft ein
        cvn = cft-edge-val p g' cft ein
        cs  = sing-coh (fst p) (snd p) cui (fst cvn) (snd cvn)
        lf  : LeFunCode (cons p nil) g'
        lf  = mkSigma (EvalFun-edge-le p g' (fst p) cft ein cui (LeCode-refl (fst p) cui)) tt
        evs = Ideal.down iM (FunEl g') (sing (fst p) (snd p)) evM cs lf
        ap  = guard-intro (snd p) (snd cvn) (mkSigma (fst p) (mkSigma (mkSigma cui (LeCode-refl (fst p) cui)) evs))
        ap' = pt (fst p) a (fmf-key g' a f fmf p ein) evA (snd p) ap
        b   = guard-elim (snd p) (snd cvn) ap'
        w   = fst b
        lew : LeFunCode (cons p nil) (cons (mkSigma w (snd p)) nil)
        lew = mkSigma (sing-EvalFun w (snd p) (fst p)
                         (Ideal.coh iN _ (snd (snd b))) cui (snd (fst (snd b)))) tt
    in Ideal.down iN (sing w (snd p)) (FunEl (cons p nil)) (snd (snd b)) cs lew

  build : (g : FinFun) -> CoherentFun g -> ((p : Edge) -> EdgeIn p g -> PN (FunEl (cons p nil))) -> PN (FunEl g)
  build (cons p nil) cg h = h p here
  build (cons p (cons q qs)) cg h =
    Ideal.sup iN (FunEl (cons p nil)) (FunEl (cons q qs)) (h p here)
      (build (cons q qs) (CFTcons.tail-coh cg) (\ r rin -> h r (there rin)))

  incl : Incl PM PN
  incl u e =
    let t = invM u e
    in Ideal.down iN (fst t) u (main (fst t) (fst (snd t)) (fst (snd (snd (snd t))))
                                 (fst (snd (snd (snd (snd t))))) (snd (snd (snd (snd (snd t))))))
         (Ideal.coh iM u e) (fst (snd (snd t)))
    where
      main : (u' piaf : FinEl) -> PM u' -> FinMem u' piaf -> PiS PA (LamS PA Bb) piaf -> PN u'
      main Bot piaf e' fm ep = Ideal.bot iN
      main (FunEl g') (PiCode a f) e' fm ep =
        let cf-g' = finMem-funel-coh g' a f fm
        in build g' cf-g' (edge a f (fst (snd ep)) g' cf-g' (finMem-funel-fun g' a f fm) e')
      main UCode (PiCode _ _) e' () ep
      main (PiCode _ _) (PiCode _ _) e' () ep
      main NatCode (PiCode _ _) e' () ep
      main ZeroEl (PiCode _ _) e' () ep
      main (SucEl _) (PiCode _ _) e' () ep
      main (PairEl _ _) (PiCode _ _) e' () ep
      main (SigmaCode _ _) (PiCode _ _) e' () ep
