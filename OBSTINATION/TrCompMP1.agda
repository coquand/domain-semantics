{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrCompMP1
--
-- **MP1 IS PRESERVED BY COMPOSITION, WITHOUT PROPOSITION 1.**
--
--     compTr-verdict : Verdict (W.ovf p Tg a Ths)
--     compTr-MP1     : MP1T a (compTr p Tg a Ths)
--
-- from the induction hypotheses alone -- `MonoTr` and `MP1T` of the outer
-- trace and of every argument -- and nothing else.
--
-- The index clause was already Prop-1-free: `TrSelStab.compTr-ivAll-full`
-- takes exactly these hypotheses.  This file supplies the VALUE clause,
-- which `TrMP1Red.mp1T-from-iv` used to read off `Property.UO`.
--
-- HOW THE PIECES FIT.
--
--   * `TrSelStab.SS.selStab` -- the demand `sel k = blockOn p Tg (vals k)`
--     is eventually CONSTANT (as an `Or Top Nat`, not merely its index).
--     One case split on that constant value:
--
--       `inl tt` -- the outer trace waits for nothing, and `sem-sat` needs
--                   no agreement at all, so the value is constant
--                   (`TrCompVerdict.fedV-inl`);
--       `inr J`  -- the outer trace waits on argument `J` for ever.
--
--   * for `inr J`, argument `J`'s OWN `Verdict`, split by
--     `TrCompSel.verdict-split` into "settles" or "grows", is transported
--     from `J`'s private replay depth to the composite's clock by the
--     DRIVE (`TrCompIv.CI.Sel.dep-step` / `dep-drive`): while `J` is
--     selected, the composite raises exactly the level `J` is stuck on, so
--     `dep k J` advances by at least one per stage.  That is the only
--     place the sharing of variables between the arguments matters, and it
--     is where `TrComp`'s design -- one shared level function, each
--     argument replayed against it -- pays.
--
--   * `TrCompVerdict.fedV` then delivers the verdict, by structural
--     recursion on the outer trace (descents included).
--
-- No Proposition 1.  No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrCompMP1 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.BlkReplay using (plus ; plus-ge-r)
open import OBSTINATION.MP1 using (plus-ge-l ; ConstFrom ; StrictIncFrom ; PhiOK)
open import OBSTINATION.PhiComp using (sinc-mono-lt)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (IsCpl ; LeX ; MonoTr)
open import OBSTINATION.TrMono using (ovOf-mono)
open import OBSTINATION.TrMP1 using (Never ; Verdict ; MP1T ; IvAll)
open import OBSTINATION.TrPrec using (InRange ; blockOn-range)
open import OBSTINATION.TrComp using (module W ; compTr ; orC)
open import OBSTINATION.TrCompIv using (module CI)
open import OBSTINATION.TrCompSel using
  (OvSettles ; OvGrows ; stop-settles ; module CS)
open import OBSTINATION.TrSelStab using (module SS ; compTr-ivAll-full)
open import OBSTINATION.TrCompVerdict using
  (VerdictFrom ; fedV ; fedV-inl ; verdictFrom-verdict)

------------------------------------------------------------------------
-- THE VALUE CLAUSE FOR A COMPOSITE
------------------------------------------------------------------------

compTr-verdict : (p : Nat) (Tg : Tr p) -> MonoTr p Tg -> MP1T p Tg
               -> (a : Nat) (Ths : Nat -> Tr (suc a))
               -> ((i : Nat) -> MonoTr (suc a) (Ths i))
               -> ((i : Nat) -> MP1T (suc a) (Ths i))
               -> ((m n : Nat) -> LeN m n
                     -> LeF (W.ovf p Tg a Ths m) (W.ovf p Tg a Ths n))
               -> Verdict (W.ovf p Tg a Ths)
compTr-verdict p Tg mtg m1g a Ths mTh m1h ovm =
  verdictFrom-verdict (W.ovf p Tg a Ths) ovm K (go (WW.sel K) refl)
  where
    module WW = W p Tg a Ths

    open CS p Tg mtg a Ths mTh using (valAt ; valAt-eq ; vals-mono)
    open CI p Tg a Ths using (dep-mono ; module Sel)

    ss : Sigma Nat (\ K -> (k : Nat) -> LeN K k -> Eq (WW.sel k) (WW.sel K))
    ss = SS.selStab p Tg mtg m1g a Ths mTh m1h

    K : Nat
    K = fst ss

    con : (k : Nat) -> LeN K k -> Eq (WW.sel k) (WW.sel K)
    con = snd ss

    ------------------------------------------------------------------
    -- the outer trace waits on argument `J` for ever
    ------------------------------------------------------------------

    module ATJ (J : Nat) (e : Eq (WW.sel K) (inr J)) where

      stab : (k : Nat) -> LeN K k -> Eq (blockOn p Tg (WW.vals k)) (inr J)
      stab k lk = Eq-trans (con k lk) e

      lJ : LeN (suc J) p
      lJ =
        Eq-transport (\ z -> InRange p z) e
          (blockOn-range p Tg (WW.vals K))

      selCJ : (k : Nat) -> LeN K k -> Eq (WW.selC k) J
      selCJ k lk = Eq-cong orC (stab k lk)

      -- argument `J`'s own dichotomy, on ITS replay depth
      Reg : Set
      Reg = Or (OvSettles (\ k -> valAt k J)) (OvGrows (\ k -> valAt k J))

      reg : Reg
      reg = rr (Ths J) refl
        where
          rr : (T : Tr (suc a)) -> Eq (Ths J) T -> Reg
          --------------------------------------------------------------
          -- a `stop` argument: its value never moves, so neither does
          -- what the outer trace sees
          --------------------------------------------------------------
          rr (stop w) ej = inl (mkSigma zero (\ m lm -> cst m))
            where
              cst : (m : Nat) -> Eq (valAt m J) (valAt zero J)
              cst m =
                Eq-trans (valAt-eq m J lJ)
                  (Eq-trans
                    (Eq-trans (Eq-cong (\ T -> ovOf T (WW.dep m J)) ej)
                      (Eq-sym (Eq-cong (\ T -> ovOf T (WW.dep zero J)) ej)))
                    (Eq-sym (valAt-eq zero J lJ)))
          --------------------------------------------------------------
          -- a `node` argument: the drive pushes its replay past its own
          -- threshold, and its `Verdict` transports to the composite's
          -- clock
          --------------------------------------------------------------
          rr (node ivj ivjr ovj contj) ej = split vsplit
            where
              open Sel J ivj ivjr ovj contj ej using (dep-step ; dep-drive)

              vsplit : Or (OvSettles (ovOf (Ths J))) (OvGrows (ovOf (Ths J)))
              vsplit =
                stop-settles (suc a) (Ths J) (mTh J) (m1h J)
                  (ovOf-mono (suc a) (Ths J) (mTh J))

              drive : (s : Nat) -> LeN (plus s (WW.dep K J)) (WW.dep (plus s K) J)
              drive = dep-drive K (\ k lk -> selCJ k lk)

              -- `dep` is past `n1` from stage `plus n1 K` on
              past : (n1 m : Nat) -> LeN (plus n1 K) m -> LeN n1 (WW.dep m J)
              past n1 m lm =
                LeN-trans {n1} {WW.dep (plus n1 K) J} {WW.dep m J}
                  (LeN-trans {n1} {plus n1 (WW.dep K J)} {WW.dep (plus n1 K) J}
                    (plus-ge-l n1 (WW.dep K J)) (drive n1))
                  (dep-mono (plus n1 K) m lm J)

              split : Or (OvSettles (ovOf (Ths J))) (OvGrows (ovOf (Ths J))) -> Reg
              ----------------------------------------------------------
              -- it settles
              ----------------------------------------------------------
              split (inl (mkSigma n1 set)) = inl (mkSigma N go')
                where
                  N : Nat
                  N = plus n1 K

                  at1 : (m : Nat) -> LeN N m -> Eq (valAt m J) (ovOf (Ths J) n1)
                  at1 m lm =
                    Eq-trans (valAt-eq m J lJ) (set (WW.dep m J) (past n1 m lm))

                  go' : (m : Nat) -> LeN N m -> Eq (valAt m J) (valAt N J)
                  go' m lm = Eq-trans (at1 m lm) (Eq-sym (at1 N (LeN-refl N)))
              ----------------------------------------------------------
              -- it grows
              ----------------------------------------------------------
              split (inr (mkSigma nev (mkSigma n1 si))) =
                inr (mkSigma nvr (mkSigma N inc))
                where
                  N : Nat
                  N = plus n1 K

                  lKN : LeN K N
                  lKN = plus-ge-r n1 K

                  nvr : Never (\ k -> valAt k J)
                  nvr k =
                    Eq-transport (\ z -> Eq z (fbot (hgt z)))
                      (Eq-sym (valAt-eq k J lJ)) (nev (WW.dep k J))

                  inc : StrictIncFrom N (\ k -> hgt (valAt k J))
                  inc m lm =
                    Eq-transport (\ z -> LeN (suc (hgt z)) (hgt (valAt (suc m) J)))
                      (Eq-sym (valAt-eq m J lJ))
                      (Eq-transport
                        (\ z -> LeN (suc (hgt (ovOf (Ths J) (WW.dep m J)))) (hgt z))
                        (Eq-sym (valAt-eq (suc m) J lJ))
                        (sinc-mono-lt n1 (\ n -> hgt (ovOf (Ths J) n)) si
                          (WW.dep m J) (WW.dep (suc m) J)
                          (past n1 m lm)
                          (dep-step m
                            (selCJ m (LeN-trans {K} {N} {m} lKN lm)))))

      verd : VerdictFrom K (W.ovf p Tg a Ths)
      verd = fedV p Tg mtg m1g WW.vals vals-mono K J stab reg

    go : (r : Or Top Nat) -> Eq (WW.sel K) r -> VerdictFrom K (W.ovf p Tg a Ths)
    go (inl tt) e = fedV-inl p Tg mtg WW.vals vals-mono K e
    go (inr J)  e = ATJ.verd J e

------------------------------------------------------------------------
-- MP1 FOR THE COMPOSITE
------------------------------------------------------------------------

compTr-MP1 : (p : Nat) (Tg : Tr p) -> MonoTr p Tg -> MP1T p Tg
           -> (a : Nat) (Ths : Nat -> Tr (suc a))
           -> ((i : Nat) -> MonoTr (suc a) (Ths i))
           -> ((i : Nat) -> MP1T (suc a) (Ths i))
           -> ((m n : Nat) -> LeN m n
                 -> LeF (W.ovf p Tg a Ths m) (W.ovf p Tg a Ths n))
           -> Pair (Verdict (W.ovf p Tg a Ths)) (IvAll (suc a) (compTr p Tg (suc a) Ths))
compTr-MP1 p Tg mtg m1g a Ths mTh m1h ovm =
  mkSigma (compTr-verdict p Tg mtg m1g a Ths mTh m1h ovm)
    (compTr-ivAll-full p Tg mtg m1g (suc a) Ths mTh m1h)
