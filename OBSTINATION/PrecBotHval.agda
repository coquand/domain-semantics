{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecBotHval
--
-- "hval" providers for the finite-incomplete first argument: they turn
-- h's obstination case at the inner point  B = cons (bot c) (cons v1 Y)
-- into the exact value-on-a-region hypothesis consumed by the witness
-- builders of PrecBotCase23.  Each combines `pull-h` (the single-
-- coordinate pull-back) with h's own universality field and the
-- coordinate pin.
--
-- This file covers the NON-coord1 cases (coordinate 0, and a genuine
-- Y-coordinate); the recursion-result coupling (coord 1) is handled
-- separately with the Berry-stability kernel.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecBotHval where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Extension using (embed-inj ; LeFTup-length ; get-embedTup ; del-LeFTup)
open import OBSTINATION.Refine using (Below-length ; get-inf-in-range ; del-repl ; Below-repl-into)
open import OBSTINATION.Prop1Base using (repl ; getF-repl ; length-repl)
open import OBSTINATION.CompCase3Helpers using (le-inf-fbot)
open import OBSTINATION.PrecBotEngine using (FcFun ; recstep-eq ; pred-of ; pred-ge)
open import OBSTINATION.PrecBotReach using (frec-ge)
open import OBSTINATION.Mono using (consLe)
open import OBSTINATION.PrecBotPull using (pull-h ; LeFTup-trans)
open import OBSTINATION.PrecBotCase23 using (prec-bot-Case2-Ycoord ; prec-bot-Case3-Ycoord)
open import OBSTINATION.Meet using (joinT ; join-ubT-l ; join-ubT-r)
open import OBSTINATION.JoinD using (Below-joinT ; BndT-from-Below ; getF-joinT ; joinF-absorb-r)
open import OBSTINATION.LeReassemble using (LeFTup-from-del)
open import OBSTINATION.PrecFun using (RecData ; PF ; precFun)

phiok-weaken : (kH kF : Nat) (phi : Nat -> Nat) -> LeN kH kF ->
  PhiOK kH phi -> PhiOK kF phi
phiok-weaken kH kF phi lek (inl cst) =
  inl (\ m lem -> Eq-trans (cst m (LeN-trans {kH} {kF} {m} lek lem))
                           (Eq-sym (cst kF lek)))
phiok-weaken kH kF phi lek (inr sinc) =
  inr (\ m lem -> sinc m (LeN-trans {kH} {kF} {m} lek lem))

module _ (rd : RecData) where
  open RecData rd

  ------------------------------------------------------------------------
  -- Coordinate 0 controls h  ->  constant value on a region (feeds W2).
  ------------------------------------------------------------------------

  hval-coord0 : (c mh : Nat) (Y : Tup) (v1 : D)
    (reach : (u : FEl) -> LeD (embed u) v1 ->
       Sigma FTup (\ A0' -> Pair (Below A0' Y)
         ((X' : FTup) -> LeFTup A0' X' -> LeF u (FcFun rd c X'))))
    (A0H : FTup) (belA0H : Below A0H (cons (bot c) (cons v1 Y)))
    (eqinv : Eq (embed (getF zero A0H)) (bot c))
    (univH : (Z : FTup) -> Eq (length Z) (length A0H) ->
       Eq (getF zero Z) (getF zero A0H) ->
       LeFTup (del zero A0H) (del zero Z) -> Eq (H Z) (fbot mh)) ->
    Sigma FTup (\ A0t -> Pair (Below A0t Y)
      ((X' : FTup) -> LeFTup A0t X' ->
         Eq (H (cons (fbot c) (cons (FcFun rd c X') X'))) (fbot mh)))
  hval-coord0 c mh Y v1 reach A0H belA0H eqinv univH =
    mkSigma A0t (mkSigma belA0t hval)
    where
      pb    = pull-h rd c Y v1 reach A0H belA0H
      A0t   = fst pb
      belA0t = fst (snd pb)
      dom   = snd (snd pb)
      A0H-coord0 : Eq (getF zero A0H) (fbot c)
      A0H-coord0 = embed-inj {getF zero A0H} {fbot c} eqinv
      hval : (X' : FTup) -> LeFTup A0t X' ->
             Eq (H (cons (fbot c) (cons (FcFun rd c X') X'))) (fbot mh)
      hval X' leX' =
        univH Z (Eq-sym (LeFTup-length domZ))
               (Eq-sym A0H-coord0)
               (del-LeFTup zero domZ)
        where
          Z : FTup
          Z = cons (fbot c) (cons (FcFun rd c X') X')
          domZ : LeFTup A0H Z
          domZ = dom (fbot c) X' (LeF-refl (fbot c)) leX'

  ------------------------------------------------------------------------
  -- A finite Y-coordinate controls h  ->  f is Case 2 at that coordinate.
  -- (Mirrors CompCase2.case2-from-uo2: pull back, join with h's witness,
  -- reconcile the pinned coordinate by join-absorption.)
  ------------------------------------------------------------------------

  hval-Ycoord-Case2 : (c mh j : Nat) (Y : Tup) (v1 : D)
    (reach : (u : FEl) -> LeD (embed u) v1 ->
       Sigma FTup (\ A0' -> Pair (Below A0' Y)
         ((X' : FTup) -> LeFTup A0' X' -> LeF u (FcFun rd c X'))))
    (a0 a1 : FEl) (B0t : FTup)
    (le0 : LeD (embed a0) (bot c)) (le1 : LeD (embed a1) v1)
    (belB0t : Below B0t Y)
    (irangeH : LeN (suc (suc (suc j))) (suc (suc (length B0t))))
    (incomplH : IncompleteFinite (get j Y))
    (eqinvH : Eq (embed (getF j B0t)) (get j Y))
    (univH : (Z : FTup) -> Eq (length Z) (suc (suc (length B0t))) ->
       Eq (getF (suc (suc j)) Z) (getF j B0t) ->
       LeFTup (del (suc (suc j)) (cons a0 (cons a1 B0t))) (del (suc (suc j)) Z) ->
       Eq (H Z) (fbot mh)) ->
    UO (PF G H) (cons (bot (suc c)) Y)
  hval-Ycoord-Case2 c mh j Y v1 reach a0 a1 B0t le0 le1 belB0t
    irangeH incomplH eqinvH univH =
    prec-bot-Case2-Ycoord rd c mh j Y A0t belA0t jrange incomplH eqinv hval
    where
      A0H : FTup
      A0H = cons a0 (cons a1 B0t)
      rr    = reach a1 le1
      A0''  = fst rr
      belA'' = fst (snd rr)
      domFc  = snd (snd rr)
      A0t : FTup
      A0t = joinT A0'' B0t
      bnd = BndT-from-Below belA'' belB0t
      belA0t : Below A0t Y
      belA0t = Below-joinT belA'' belB0t
      lenA''B0t : Eq (length A0'') (length B0t)
      lenA''B0t = Eq-trans (Below-length belA'') (Eq-sym (Below-length belB0t))
      lenA0t-B0t : Eq (length A0t) (length B0t)
      lenA0t-B0t = Eq-trans (Below-length belA0t) (Eq-sym (Below-length belB0t))
      A0''-le-B0t : LeF (getF j A0'') (getF j B0t)
      A0''-le-B0t =
        Eq-transport (\ z -> LeD (embed (getF j A0'')) z) (Eq-sym eqinvH)
          (Eq-transport (\ z -> LeD z (get j Y)) (get-embedTup j A0'')
            (LeTup-get j belA''))
      getF-A0t : Eq (getF j A0t) (getF j B0t)
      getF-A0t = Eq-trans (getF-joinT j A0'' B0t lenA''B0t) (joinF-absorb-r A0''-le-B0t)
      jrange : LeN (suc j) (length A0t)
      jrange = Eq-transport (\ n -> LeN (suc j) n) (Eq-sym lenA0t-B0t) irangeH
      eqinv : Eq (embed (getF j A0t)) (get j Y)
      eqinv = Eq-trans (Eq-cong embed getF-A0t) eqinvH
      hval : (x : FEl) (xs : FTup) -> LeF (fbot (suc c)) x ->
             Eq (length xs) (length A0t) -> Eq (getF j xs) (getF j A0t) ->
             LeFTup (del j A0t) (del j xs) -> Eq (precFun G H x xs) (fbot mh)
      hval x xs lex lenxs coordX delX =
        Eq-trans (recstep-eq rd c x xs lex) (univH Z lenZ coordZ delZ)
        where
          xsGeA0t : LeFTup A0t xs
          xsGeA0t = LeFTup-from-del j A0t xs (Eq-sym lenxs)
                      (Eq-transport (\ z -> LeF (getF j A0t) z) (Eq-sym coordX)
                        (LeF-refl (getF j A0t)))
                      delX
          predge : LeF (fbot c) (pred-of x)
          predge = pred-ge c x lex
          p : FEl
          p = pred-of x
          rec : FEl
          rec = precFun G H p xs
          Z : FTup
          Z = cons p (cons rec xs)
          xsGeA'' : LeFTup A0'' xs
          xsGeA'' = LeFTup-trans (join-ubT-l bnd) xsGeA0t
          xsGeB0t : LeFTup B0t xs
          xsGeB0t = LeFTup-trans (join-ubT-r bnd) xsGeA0t
          c0 : LeF a0 p
          c0 = LeD-trans {embed a0} {bot c} {embed p} le0 predge
          c1 : LeF a1 rec
          c1 = frec-ge rd c a1 A0'' domFc p xs predge xsGeA''
          domZ : LeFTup (cons a0 (cons a1 B0t)) (cons p (cons rec xs))
          domZ = consLe {a0} {p} {cons a1 B0t} {cons rec xs} c0
                   (consLe {a1} {rec} {B0t} {xs} c1 xsGeB0t)
          lenZ : Eq (length Z) (suc (suc (length B0t)))
          lenZ = Eq-sym (LeFTup-length {cons a0 (cons a1 B0t)} {cons p (cons rec xs)} domZ)
          delZ : LeFTup (del (suc (suc j)) (cons a0 (cons a1 B0t))) (del (suc (suc j)) Z)
          delZ = del-LeFTup (suc (suc j)) {cons a0 (cons a1 B0t)} {cons p (cons rec xs)} domZ
          coordZ : Eq (getF (suc (suc j)) Z) (getF j B0t)
          coordZ = Eq-trans coordX getF-A0t

  ------------------------------------------------------------------------
  -- An infinite Y-coordinate controls h  ->  f is Case 3 at that coordinate
  -- (same phi).  Mirrors CompCase2.case2-from-uo3inl: repl the pinned
  -- coordinate to a threshold kF = max(kH, q) absorbing the pull region.
  ------------------------------------------------------------------------

  hval-Ycoord-Case3 : (c j kH : Nat) (phiH : Nat -> Nat)
    (Y : Tup) (v1 : D)
    (reach : (u : FEl) -> LeD (embed u) v1 ->
       Sigma FTup (\ A0' -> Pair (Below A0' Y)
         ((X' : FTup) -> LeFTup A0' X' -> LeF u (FcFun rd c X'))))
    (a0 a1 : FEl) (B0t : FTup)
    (le0 : LeD (embed a0) (bot c)) (le1 : LeD (embed a1) v1)
    (belB0t : Below B0t Y)
    (eqinfH : Eq (get j Y) inf)
    (eqA0H : Eq (getF j B0t) (fbot kH))
    (phiokH : PhiOK kH phiH)
    (univH : (Z : FTup) (p : Nat) -> Eq (length Z) (suc (suc (length B0t))) ->
       LeN kH p -> Eq (getF (suc (suc j)) Z) (fbot p) ->
       LeFTup (del (suc (suc j)) (cons a0 (cons a1 B0t))) (del (suc (suc j)) Z) ->
       Eq (H Z) (fbot (phiH p))) ->
    UO (PF G H) (cons (bot (suc c)) Y)
  hval-Ycoord-Case3 c j kH phiH Y v1 reach a0 a1 B0t le0 le1 belB0t
    eqinfH eqA0H phiokH univH =
    prec-bot-Case3-Ycoord rd c j kF phiH Y A0t belA0t eqinfH eqA0F phiokF hval
    where
      rr    = reach a1 le1
      A0''  = fst rr
      belA'' = fst (snd rr)
      domFc  = snd (snd rr)
      -- getF j A0'' is below inf, hence some fbot q
      coordA''-le : LeD (embed (getF j A0'')) inf
      coordA''-le =
        Eq-transport (\ z -> LeD (embed (getF j A0'')) z) eqinfH
          (Eq-transport (\ z -> LeD z (get j Y)) (get-embedTup j A0'')
            (LeTup-get j belA''))
      qext = le-inf-fbot (getF j A0'') coordA''-le
      q    = fst qext
      qeq  = snd qext                     -- Eq (getF j A0'') (fbot q)
      kF   = maxN kH q
      JT : FTup
      JT = joinT A0'' B0t
      bnd = BndT-from-Below belA'' belB0t
      belJT : Below JT Y
      belJT = Below-joinT belA'' belB0t
      lenJT-Y : Eq (length JT) (length Y)
      lenJT-Y = Below-length belJT
      A0t : FTup
      A0t = repl j (fbot kF) JT
      lenA0t-Y : Eq (length A0t) (length Y)
      lenA0t-Y = Eq-trans (length-repl j (fbot kF) JT) lenJT-Y
      jrangeJT : LeN (suc j) (length JT)
      jrangeJT = Eq-transport (\ n -> LeN (suc j) n) (Eq-sym lenJT-Y)
                   (get-inf-in-range j Y eqinfH)
      eqA0F : Eq (getF j A0t) (fbot kF)
      eqA0F = getF-repl j (fbot kF) JT jrangeJT
      phiokF : PhiOK kF phiH
      phiokF = phiok-weaken kH kF phiH (maxN-le-l kH q) phiokH
      belA0t : Below A0t Y
      belA0t = Below-repl-into j (fbot kF) JT Y belJT
                 (Eq-transport (\ z -> LeD (bot kF) z) (Eq-sym eqinfH) tt)
      hval : (x : FEl) (xs : FTup) (p : Nat) -> LeF (fbot (suc c)) x ->
             Eq (length xs) (length A0t) -> LeN kF p ->
             Eq (getF j xs) (fbot p) -> LeFTup (del j A0t) (del j xs) ->
             Eq (precFun G H x xs) (fbot (phiH p))
      hval x xs p lex lenxs pkF coordX delX =
        Eq-trans (recstep-eq rd c x xs lex) (univH Z p lenZ pkH coordZ delZ)
        where
          pkH : LeN kH p
          pkH = LeN-trans {kH} {kF} {p} (maxN-le-l kH q) pkF
          pq : LeN q p
          pq = LeN-trans {q} {kF} {p} (maxN-le-r kH q) pkF
          -- xs >= A0'' : at coord j, getF j xs = fbot p >= fbot q = getF j A0''
          coordA''-xs : LeF (getF j A0'') (getF j xs)
          coordA''-xs =
            Eq-transport (\ z -> LeF (getF j A0'') z) (Eq-sym coordX)
              (Eq-transport (\ z -> LeF z (fbot p)) (Eq-sym qeq) pq)
          -- del j A0t = del j JT (repl at j deleted)
          delJT : LeFTup (del j JT) (del j xs)
          delJT = Eq-transport (\ W -> LeFTup W (del j xs)) (del-repl j (fbot kF) JT) delX
          lenA''-xs : Eq (length A0'') (length xs)
          lenA''-xs = Eq-trans (Below-length belA'') (Eq-sym (Eq-trans lenxs lenA0t-Y))
          lenB0t-xs : Eq (length B0t) (length xs)
          lenB0t-xs = Eq-trans (Below-length belB0t) (Eq-sym (Eq-trans lenxs lenA0t-Y))
          delA''-xs : LeFTup (del j A0'') (del j xs)
          delA''-xs = LeFTup-trans (del-LeFTup j (join-ubT-l bnd)) delJT
          delB0t-xs : LeFTup (del j B0t) (del j xs)
          delB0t-xs = LeFTup-trans (del-LeFTup j (join-ubT-r bnd)) delJT
          coordB0t-xs : LeF (getF j B0t) (getF j xs)
          coordB0t-xs =
            Eq-transport (\ z -> LeF (getF j B0t) z) (Eq-sym coordX)
              (Eq-transport (\ z -> LeF z (fbot p)) (Eq-sym eqA0H) pkH)
          xsGeA'' : LeFTup A0'' xs
          xsGeA'' = LeFTup-from-del j A0'' xs lenA''-xs coordA''-xs delA''-xs
          xsGeB0t : LeFTup B0t xs
          xsGeB0t = LeFTup-from-del j B0t xs lenB0t-xs coordB0t-xs delB0t-xs
          predge : LeF (fbot c) (pred-of x)
          predge = pred-ge c x lex
          pd : FEl
          pd = pred-of x
          rec : FEl
          rec = precFun G H pd xs
          Z : FTup
          Z = cons pd (cons rec xs)
          c0 : LeF a0 pd
          c0 = LeD-trans {embed a0} {bot c} {embed pd} le0 predge
          c1 : LeF a1 rec
          c1 = frec-ge rd c a1 A0'' domFc pd xs predge xsGeA''
          domZ : LeFTup (cons a0 (cons a1 B0t)) (cons pd (cons rec xs))
          domZ = consLe {a0} {pd} {cons a1 B0t} {cons rec xs} c0
                   (consLe {a1} {rec} {B0t} {xs} c1 xsGeB0t)
          lenZ : Eq (length Z) (suc (suc (length B0t)))
          lenZ = Eq-sym (LeFTup-length {cons a0 (cons a1 B0t)} {cons pd (cons rec xs)} domZ)
          delZ : LeFTup (del (suc (suc j)) (cons a0 (cons a1 B0t))) (del (suc (suc j)) Z)
          delZ = del-LeFTup (suc (suc j)) {cons a0 (cons a1 B0t)} {cons pd (cons rec xs)} domZ
          coordZ : Eq (getF (suc (suc j)) Z) (fbot p)
          coordZ = coordX
