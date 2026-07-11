{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecBotCoord1C
--
-- The recursion-result coupling, Case 3 (h is Case 3 at coordinate 1 of
-- B = cons (bot c) (cons v1 Y), so v1 = inf).  This forces Fc to be
-- Case-3-INCREASING at some Y-coordinate jf.  But h being controlled by
-- coordinate 1 makes `base-const` (Berry stability) FLATTEN Fc to a
-- constant on a region -- contradicting the increase.  Hence this case
-- is IMPOSSIBLE: it is discharged to Empty, no psi / stab-exclude needed.
--
--   Build Y0 (coord jf = S^{m0}(bot)) and X1 (coord jf = S^{m0+1}(bot))
--   with X1 >= Y0.  Fc Y0 = S^{phi_Fc m0}(bot) =: S^N(bot), Fc X1 =
--   S^{phi_Fc(m0+1)}(bot).  base-const gives Fc X1 = Fc Y0, so
--   phi_Fc(m0+1) = N = phi_Fc m0, contradicting strict increase.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecBotCoord1C where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Extension using (del-LeFTup ; get-embedTup ; LeFTup-length)
open import OBSTINATION.Refine using
  (Below-length ; get-inf-in-range ; del-repl ; Below-repl-into)
open import OBSTINATION.Prop1Base using (repl ; getF-repl ; length-repl)
open import OBSTINATION.CompCase3Helpers using (bot-not-inf ; le-inf-fbot ; extract-inr ; Case3Inr)
open import OBSTINATION.StabExclude using (fbot-inj ; LeN-suc-not)
open import OBSTINATION.LeReassemble using (LeFTup-from-del)
open import OBSTINATION.Meet using (joinT ; join-ubT-l ; join-ubT-r)
open import OBSTINATION.JoinD using (Below-joinT ; BndT-from-Below)
open import OBSTINATION.PhiComp using (sinc-mono-le ; sinc-mono-lt)
open import OBSTINATION.PhiProps using (phi-escape)
open import OBSTINATION.PrecBaseConst using (base-const)
open import OBSTINATION.PrecBotEngine using (FcFun ; FcConst)
open import OBSTINATION.PrecBotReach using (fc-v1)
open import OBSTINATION.PrecFun using (RecData ; PF ; precFun)

module _ (rd : RecData) where
  open RecData rd

  ------------------------------------------------------------------------
  -- The discharge (returns any goal, via Empty-elim).
  ------------------------------------------------------------------------

  coord1-Case3-absurd : (c mh : Nat) (Y : Tup)
    (o : Or (UO (FcFun rd c) Y) (FcConst rd c Y)) ->
    Eq (fc-v1 rd c Y o) inf ->
    (a0 : FEl) (kh : Nat) (phih : Nat -> Nat) (A0Ht : FTup)
    (le0 : LeD (embed a0) (bot c)) (belA0Ht : Below A0Ht Y)
    -- h Case3 at coordinate 1, threshold kh, witness phih
    (univH : (Z : FTup) (p : Nat) -> Eq (length Z) (suc (suc (length A0Ht))) ->
       LeN kh p -> Eq (getF (suc zero) Z) (fbot p) ->
       LeFTup (cons a0 A0Ht) (del (suc zero) Z) -> Eq (H Z) (fbot (phih p))) ->
    Empty
  coord1-Case3-absurd c mh Y (inr (mkSigma m'' _)) veq a0 kh phih A0Ht le0 belA0Ht univH =
    bot-not-inf veq
  coord1-Case3-absurd c mh Y (inl pf) veq a0 kh phih A0Ht le0 belA0Ht univH =
    LeN-suc-not N (Eq-transport (\ n -> LeN (suc N) n) phi-eq gt)
    where
      Fc = FcFun rd c
      c3 : Case3Inr Fc Y
      c3 = extract-inr Fc Y pf veq
      A0F   = fst c3
      belA0F = fst (snd c3)
      jf    = fst (snd (snd c3))
      eqinf = fst (snd (snd (snd c3)))
      kF    = fst (snd (snd (snd (snd c3))))
      eqA0F = fst (snd (snd (snd (snd (snd c3)))))
      phiF  = fst (snd (snd (snd (snd (snd (snd c3))))))
      sincF = fst (snd (snd (snd (snd (snd (snd (snd c3)))))))
      univF = snd (snd (snd (snd (snd (snd (snd (snd c3)))))))
      -- A0Ht's coord jf is finite (below inf): height q_A
      coordAHt-le : LeD (embed (getF jf A0Ht)) inf
      coordAHt-le = Eq-transport (\ z -> LeD (embed (getF jf A0Ht)) z) eqinf
                      (Eq-transport (\ z -> LeD z (get jf Y)) (get-embedTup jf A0Ht)
                        (LeTup-get jf belA0Ht))
      qA   = fst (le-inf-fbot (getF jf A0Ht) coordAHt-le)
      qAeq = snd (le-inf-fbot (getF jf A0Ht) coordAHt-le)
      -- pick m0 : >= kF, phiF m0 >= kh, m0 >= qA
      esc  = phi-escape kF phiF sincF kh
      me   = fst esc
      kFme = fst (snd esc)
      kh-le = snd (snd esc)                     -- LeN kh (phiF me)
      m0   = maxN me qA
      kFm0 : LeN kF m0
      kFm0 = LeN-trans {kF} {me} {m0} kFme (maxN-le-l me qA)
      m0-ge-qA : LeN qA m0
      m0-ge-qA = maxN-le-r me qA
      N : Nat
      N = phiF m0
      kh-N : LeN kh N
      kh-N = LeN-trans {kh} {phiF me} {phiF m0} kh-le
               (sinc-mono-le kF phiF sincF me m0 kFme (maxN-le-l me qA))
      -- the join and the two test points
      J = joinT A0F A0Ht
      bnd = BndT-from-Below belA0F belA0Ht
      belJ : Below J Y
      belJ = Below-joinT belA0F belA0Ht
      lenJ-Y = Below-length belJ
      lenA0F-Y = Below-length belA0F
      jf-rng-Y : LeN (suc jf) (length Y)
      jf-rng-Y = get-inf-in-range jf Y eqinf
      jf-rng-J : LeN (suc jf) (length J)
      jf-rng-J = Eq-transport (\ n -> LeN (suc jf) n) (Eq-sym lenJ-Y) jf-rng-Y
      ub-inf : (m : Nat) -> LeD (bot m) (get jf Y)
      ub-inf m = Eq-transport (\ z -> LeD (bot m) z) (Eq-sym eqinf) tt
      Y0 = repl jf (fbot m0) J
      X1 = repl jf (fbot (suc m0)) J
      belY0 : Below Y0 Y
      belY0 = Below-repl-into jf (fbot m0) J Y belJ (ub-inf m0)
      -- lengths
      lenY0-A0F : Eq (length Y0) (length A0F)
      lenY0-A0F = Eq-trans (length-repl jf (fbot m0) J) (Eq-trans lenJ-Y (Eq-sym lenA0F-Y))
      lenX1-A0F : Eq (length X1) (length A0F)
      lenX1-A0F = Eq-trans (length-repl jf (fbot (suc m0)) J) (Eq-trans lenJ-Y (Eq-sym lenA0F-Y))
      -- del jf A0F <= del jf (repl ...) = del jf J
      delA0F-J : LeFTup (del jf A0F) (del jf J)
      delA0F-J = del-LeFTup jf (join-ubT-l bnd)
      delA0F-Y0 : LeFTup (del jf A0F) (del jf Y0)
      delA0F-Y0 = Eq-transport (\ W -> LeFTup (del jf A0F) W) (Eq-sym (del-repl jf (fbot m0) J)) delA0F-J
      delA0F-X1 : LeFTup (del jf A0F) (del jf X1)
      delA0F-X1 = Eq-transport (\ W -> LeFTup (del jf A0F) W) (Eq-sym (del-repl jf (fbot (suc m0)) J)) delA0F-J
      -- Fc values at the two test points
      FcY0eq : Eq (Fc Y0) (fbot (phiF m0))
      FcY0eq = univF Y0 m0 lenY0-A0F kFm0 (getF-repl jf (fbot m0) J jf-rng-J) delA0F-Y0
      FcX1eq : Eq (Fc X1) (fbot (phiF (suc m0)))
      FcX1eq = univF X1 (suc m0) lenX1-A0F (LeN-trans {kF} {m0} {suc m0} kFm0 (LeN-suc m0))
                 (getF-repl jf (fbot (suc m0)) J jf-rng-J) delA0F-X1
      -- X1 >= Y0  (differ only at jf: fbot m0 <= fbot (suc m0))
      leX1Y0 : LeFTup Y0 X1
      leX1Y0 = LeFTup-from-del jf Y0 X1 lenY0-X1 coordY0-X1 delY0-X1
        where
          lenY0-X1 : Eq (length Y0) (length X1)
          lenY0-X1 = Eq-trans lenY0-A0F (Eq-sym lenX1-A0F)
          coordY0-X1 : LeF (getF jf Y0) (getF jf X1)
          coordY0-X1 =
            Eq-transport (\ z -> LeF z (getF jf X1)) (Eq-sym (getF-repl jf (fbot m0) J jf-rng-J))
              (Eq-transport (\ z -> LeF (fbot m0) z) (Eq-sym (getF-repl jf (fbot (suc m0)) J jf-rng-J))
                (LeN-suc m0))
          delY0-X1 : LeFTup (del jf Y0) (del jf X1)
          delY0-X1 = Eq-transport (\ W1 -> LeFTup W1 (del jf X1)) (Eq-sym (del-repl jf (fbot m0) J))
                       (Eq-transport (\ W2 -> LeFTup (del jf J) W2) (Eq-sym (del-repl jf (fbot (suc m0)) J))
                         (LeFTup-refl (del jf J)))
      -- A0Ht <= Y0  (needed for base-const's germN0 tail region)
      A0Ht-le-Y0 : LeFTup A0Ht Y0
      A0Ht-le-Y0 = LeFTup-from-del jf A0Ht Y0 lenAHt-Y0 coordAHt-Y0 delAHt-Y0
        where
          lenAHt-Y0 : Eq (length A0Ht) (length Y0)
          lenAHt-Y0 = Eq-trans (Below-length belA0Ht) (Eq-sym (Eq-trans (length-repl jf (fbot m0) J) lenJ-Y))
          coordAHt-Y0 : LeF (getF jf A0Ht) (getF jf Y0)
          coordAHt-Y0 =
            Eq-transport (\ z -> LeF z (getF jf Y0)) (Eq-sym qAeq)
              (Eq-transport (\ z -> LeF (fbot qA) z) (Eq-sym (getF-repl jf (fbot m0) J jf-rng-J))
                m0-ge-qA)
          delAHt-Y0 : LeFTup (del jf A0Ht) (del jf Y0)
          delAHt-Y0 = Eq-transport (\ W -> LeFTup (del jf A0Ht) W) (Eq-sym (del-repl jf (fbot m0) J))
                        (del-LeFTup jf (join-ubT-r bnd))
      -- base-const inputs
      Neq : Eq (PF G H (cons (fbot c) Y0)) (fbot N)
      Neq = FcY0eq
      germN0 : (X : FTup) -> LeFTup Y0 X ->
               Eq (H (cons (fbot c) (cons (fbot N) X))) (fbot (phih N))
      germN0 X leX = univH Z N lenZ kh-N refl delZ
        where
          Z : FTup
          Z = cons (fbot c) (cons (fbot N) X)
          lenX-A0Ht : Eq (length X) (length A0Ht)
          lenX-A0Ht = Eq-trans (Eq-sym (LeFTup-length {Y0} {X} leX))
                        (Eq-trans (Below-length belY0) (Eq-sym (Below-length belA0Ht)))
          lenZ : Eq (length Z) (suc (suc (length A0Ht)))
          lenZ = Eq-cong (\ n -> suc (suc n)) lenX-A0Ht
          delZ : LeFTup (cons a0 A0Ht) (cons (fbot c) X)
          delZ = mkSigma le0 (LeFTup-trans-local A0Ht-le-Y0 leX)
            where
              LeFTup-trans-local : {A B Cc : FTup} -> LeFTup A B -> LeFTup B Cc -> LeFTup A Cc
              LeFTup-trans-local {A} {B} {Cc} p q = LeTup-trans {embedTup A} {embedTup B} {embedTup Cc} p q
      -- base-const: Fc X1 = Fc Y0
      bc : Eq (PF G H (cons (fbot c) X1)) (PF G H (cons (fbot c) Y0))
      bc = base-const rd c N (phih N) Y0 Neq germN0 c X1 (LeN-refl c) leX1Y0
      -- so phiF (suc m0) = phiF m0 = N, contradicting strict increase
      phi-eq : Eq (phiF (suc m0)) N
      phi-eq = fbot-inj (Eq-trans (Eq-sym FcX1eq) (Eq-trans bc FcY0eq))
      gt : LeN (suc N) (phiF (suc m0))
      gt = sinc-mono-lt kF phiF sincF m0 (suc m0) kFm0 (LeN-refl m0)
