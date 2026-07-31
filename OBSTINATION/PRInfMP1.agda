{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PRInfMP1
--
-- **f(S^w(bot), ..., S^w(bot)) IS COMPUTABLE -- FROM MP1, WITHOUT
-- PROPOSITION 1.**
--
--     prValMP     : (q : PR) (n : Nat) -> Wf q n -> D
--     prValMP-lub : prValMP q n wf IS the least upper bound of the chain
--                   evalF q (S^m(bot), ..., S^m(bot))
--
-- `PRInf` proves the same thing by reading `Property.uoValue` off
-- `Prop1.prop1`.  This file proves it from `TrTermMP1.traceOf-MP1np`
-- instead, so the whole cone is Proposition-1-free -- which is what makes
-- it portable to mutual blocks, where `Property.UO` is FALSE
-- (`MutUOFail`) but the trace-level statement survives.
--
-- WHY IT IS SO SHORT.  At the all-infinite point nothing is complete and
-- nothing is finite, so the trace never descends and never blocks:
-- `TrSat.sem-bot` collapses the whole chain to a single lookup,
--
--     evalF q (S^m bot, ..., S^m bot)  =  ov (NN m) ,
--     NN m = nOf n iv ivr (m, ..., m)  >=  m
--
-- (the walk spends at most one level per step, `ReplayLv.lv-le`), so `NN`
-- is cofinal and the lub of the chain IS the lub of `ov`.  And `MP1T`'s
-- `Verdict ov` names that lub outright, exactly as `Property.uoValue`
-- does but with no `UO` in sight:
--
--     EvTot ov at n0            -->  embed (ov n0)      -- a numeral
--     Never + ConstFrom k       -->  bot (hgt (ov k))   -- S^h(bot)
--     Never + StrictIncFrom k   -->  inf                -- S^w(bot)
--
-- Only the third needs work, and only for the LEAST part: `phi-escape`
-- makes the heights unbounded, so no `bot K` and no `cpl K` can bound the
-- chain.
--
-- No Proposition 1.  No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PRInfMP1 where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using
  (D ; bot ; cpl ; inf ; LeD ; LeD-refl ; FEl ; fbot ; fcpl ; embed ; LeF ; LeF-refl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.PR using (PR ; evalF)
open import OBSTINATION.Prop1 using (Wf)
open import OBSTINATION.MP1 using (ConstFrom ; StrictIncFrom ; PhiOK)
open import OBSTINATION.PhiProps using (phi-escape)
open import OBSTINATION.BlkReplay using (nle-lt)
open import OBSTINATION.ReplayLv using (lv ; lv-le ; Adv ; nOf ; nOf-ge ; nOf-mono)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using
  (IsCpl ; cpl-max ; leF-hgt ; MonoTr ; botTup ; sem-bot)
open import OBSTINATION.TrDen using (Den)
open import OBSTINATION.TrWalk using (den-sem)
open import OBSTINATION.TrMP1 using (EvTot ; Never ; Verdict ; MP1T)
open import OBSTINATION.TrTerm using (traceOf ; traceOf-ok)
open import OBSTINATION.TrTermMP1 using (traceOf-MP1np)

------------------------------------------------------------------------
-- THE CHAIN  (S^m(bot), ..., S^m(bot))
--
-- The levels are `m` inside the arity and `0` outside it, which is what
-- `TrSat.sem-bot` asks for; the tuple itself has only `n` entries, so it
-- IS the all-`S^m(bot)` tuple.
------------------------------------------------------------------------

avm : Nat -> Nat -> Nat -> Nat
avm n m c with LeN-dec (suc c) n
... | yes _ = m
... | no  _ = zero

avm-in : (n m c : Nat) -> LeN (suc c) n -> Eq (avm n m c) m
avm-in n m c lc with LeN-dec (suc c) n
... | yes _ = refl
... | no  x = Empty-elim (x lc)

avm-out : (n m c : Nat) -> Not (LeN (suc c) n) -> Eq (avm n m c) zero
avm-out n m c nc with LeN-dec (suc c) n
... | yes x = Empty-elim (nc x)
... | no  _ = refl

avm-mono : (n m m' : Nat) -> LeN m m' -> (c : Nat) -> LeN (avm n m c) (avm n m' c)
avm-mono n m m' le c = route (LeN-dec (suc c) n)
  where
    route : Dec (LeN (suc c) n) -> LeN (avm n m c) (avm n m' c)
    route (yes lc) =
      Eq-transport (\ z -> LeN z (avm n m' c)) (Eq-sym (avm-in n m c lc))
        (Eq-transport (\ z -> LeN m z) (Eq-sym (avm-in n m' c lc)) le)
    route (no  nc) =
      Eq-transport (\ z -> LeN z (avm n m' c)) (Eq-sym (avm-out n m c nc))
        (Eq-transport (\ z -> LeN zero z) (Eq-sym (avm-out n m' c nc)) tt)

BT : Nat -> Nat -> FTup
BT n m = botTup n (avm n m)

BT-len : (n m : Nat) -> Eq (length (BT n m)) n
BT-len n m = tup-len n (\ c -> fbot (avm n m c))

Chain : (q : PR) (n : Nat) -> Nat -> FEl
Chain q n m = evalF q (BT n m)

IsLub : (u : Nat -> FEl) -> D -> Set
IsLub u d =
  Pair ((m : Nat) -> LeD (embed (u m)) d)
       ((e : D) -> ((m : Nat) -> LeD (embed (u m)) e) -> LeD d e)

------------------------------------------------------------------------
-- THE LUB OF A TRACE'S CHAIN
------------------------------------------------------------------------

lubOf : (n : Nat) (T : Tr n) (F : FTup -> FEl)
      -> MonoTr n T -> MP1T n T -> Den n T F
      -> Sigma D (\ d -> IsLub (\ m -> F (BT n m)) d)
------------------------------------------------------------------------
-- a `stop`: the chain is constant
------------------------------------------------------------------------
lubOf n (stop v) F mt m1 dn = mkSigma (embed v) (mkSigma ub lb)
  where
    ch : (m : Nat) -> Eq (F (BT n m)) v
    ch m = Eq-sym (dn (BT n m) (BT-len n m))

    ub : (m : Nat) -> LeD (embed (F (BT n m))) (embed v)
    ub m =
      Eq-transport (\ z -> LeD (embed z) (embed v)) (Eq-sym (ch m))
        (LeD-refl (embed v))

    lb : (e : D) -> ((m : Nat) -> LeD (embed (F (BT n m))) e) -> LeD (embed v) e
    lb e h =
      Eq-transport (\ z -> LeD (embed z) e) (ch zero) (h zero)
------------------------------------------------------------------------
-- a node: the chain is `ov` along a cofinal replay
------------------------------------------------------------------------
lubOf (suc n) (node iv ivr ov cont) F mt m1 dn = route (fst (snd m1))
  where
    T : Tr (suc n)
    T = node iv ivr ov cont

    NN : Nat -> Nat
    NN m = nOf (suc n) iv ivr (avm (suc n) m)

    mo : (a b : Nat) -> LeN a b -> LeF (ov a) (ov b)
    mo = fst mt

    ----------------------------------------------------------------------
    -- the chain IS `ov` at the replay depth
    ----------------------------------------------------------------------

    ch : (m : Nat) -> Eq (F (BT (suc n) m)) (ov (NN m))
    ch m =
      Eq-trans
        (Eq-sym (den-sem (suc n) T F dn (BT (suc n) m) (BT-len (suc n) m)))
        (sem-bot (suc n) T (avm (suc n) m) (\ c nc -> avm-out (suc n) m c nc))

    ----------------------------------------------------------------------
    -- ... and the replay is cofinal: the walk spends at most one level
    -- per step, so `m` levels everywhere carry it `m` steps
    ----------------------------------------------------------------------

    NN-ge : (m : Nat) -> LeN m (NN m)
    NN-ge m = nOf-ge (suc n) iv ivr (avm (suc n) m) m adv
      where
        adv : (k : Nat) -> LeN (suc k) m -> Adv (suc n) iv ivr (avm (suc n) m) k
        adv k lk =
          Eq-transport (\ z -> LeN (suc (lv (suc n) iv ivr (iv k) k)) z)
            (Eq-sym (avm-in (suc n) m (iv k) (ivr k)))
            (LeN-trans {suc (lv (suc n) iv ivr (iv k) k)} {suc k} {m}
              (lv-le (suc n) iv ivr (iv k) k) lk)

    ----------------------------------------------------------------------
    -- `Verdict ov` names the lub
    ----------------------------------------------------------------------

    route : Verdict ov -> Sigma D (\ d -> IsLub (\ m -> F (BT (suc n) m)) d)
    ------------------------------------------------------------------
    -- the value goes total: that numeral is the lub
    ------------------------------------------------------------------
    route (inl (mkSigma n0 icn)) = mkSigma (embed (ov n0)) (mkSigma ub lb)
      where
        at : (j : Nat) -> LeN n0 j -> Eq (ov j) (ov n0)
        at j lj = Eq-sym (cpl-max (ov n0) (ov j) (mo n0 j lj) icn)

        below : (m : Nat) -> LeF (ov (NN m)) (ov n0)
        below m = pick (LeN-dec (NN m) n0)
          where
            pick : Dec (LeN (NN m) n0) -> LeF (ov (NN m)) (ov n0)
            pick (yes l) = mo (NN m) n0 l
            pick (no  x) =
              Eq-transport (\ z -> LeF z (ov n0)) (Eq-sym (at (NN m) lge))
                (LeF-refl (ov n0))
              where
                lge : LeN n0 (NN m)
                lge =
                  LeN-trans {n0} {suc n0} {NN m} (LeN-suc n0) (nle-lt (NN m) n0 x)

        ub : (m : Nat) -> LeD (embed (F (BT (suc n) m))) (embed (ov n0))
        ub m =
          Eq-transport (\ z -> LeD (embed z) (embed (ov n0))) (Eq-sym (ch m))
            (below m)

        lb : (e : D) -> ((m : Nat) -> LeD (embed (F (BT (suc n) m))) e)
           -> LeD (embed (ov n0)) e
        lb e h =
          Eq-transport (\ z -> LeD (embed z) e)
            (Eq-trans (ch n0) (at (NN n0) (NN-ge n0))) (h n0)
    ------------------------------------------------------------------
    -- it never does: the height decides
    ------------------------------------------------------------------
    route (inr (mkSigma nev (mkSigma k pk))) = split pk
      where
        emb : (j : Nat) -> Eq (embed (ov j)) (bot (hgt (ov j)))
        emb j = Eq-cong embed (nev j)

        split : Or (ConstFrom k (\ j -> hgt (ov j)))
                   (StrictIncFrom k (\ j -> hgt (ov j)))
              -> Sigma D (\ d -> IsLub (\ m -> F (BT (suc n) m)) d)
        --------------------------------------------------------------
        -- the height settles: the lub is that `S^h(bot)`
        --------------------------------------------------------------
        split (inl cf) = mkSigma (bot (hgt (ov k))) (mkSigma ub lb)
          where
            hle : (m : Nat) -> LeN (hgt (ov (NN m))) (hgt (ov k))
            hle m = pick (LeN-dec (NN m) k)
              where
                pick : Dec (LeN (NN m) k) -> LeN (hgt (ov (NN m))) (hgt (ov k))
                pick (yes l) = leF-hgt (ov (NN m)) (ov k) (mo (NN m) k l)
                pick (no  x) =
                  Eq-transport (\ z -> LeN z (hgt (ov k))) (Eq-sym (cf (NN m) lge))
                    (LeN-refl (hgt (ov k)))
                  where
                    lge : LeN k (NN m)
                    lge =
                      LeN-trans {k} {suc k} {NN m} (LeN-suc k) (nle-lt (NN m) k x)

            ub : (m : Nat) -> LeD (embed (F (BT (suc n) m))) (bot (hgt (ov k)))
            ub m =
              Eq-transport (\ z -> LeD z (bot (hgt (ov k))))
                (Eq-sym (Eq-trans (Eq-cong embed (ch m)) (emb (NN m))))
                (hle m)

            lb : (e : D) -> ((m : Nat) -> LeD (embed (F (BT (suc n) m))) e)
               -> LeD (bot (hgt (ov k))) e
            lb e h =
              Eq-transport (\ z -> LeD (bot z) e) (cf (NN k) (NN-ge k))
                (Eq-transport (\ z -> LeD z e)
                  (Eq-trans (Eq-cong embed (ch k)) (emb (NN k))) (h k))
        --------------------------------------------------------------
        -- the height grows without bound: the lub is `S^w(bot)`
        --------------------------------------------------------------
        split (inr si) = mkSigma inf (mkSigma ub lb)
          where
            shape : (m : Nat) -> Eq (embed (F (BT (suc n) m))) (bot (hgt (ov (NN m))))
            shape m = Eq-trans (Eq-cong embed (ch m)) (emb (NN m))

            ub : (m : Nat) -> LeD (embed (F (BT (suc n) m))) inf
            ub m =
              Eq-transport (\ z -> LeD z inf) (Eq-sym (shape m)) tt

            -- for every bound there is a stage past it
            esc : (p : Nat) -> Sigma Nat (\ m -> LeN p (hgt (ov (NN m))))
            esc p = grab (phi-escape k (\ j -> hgt (ov j)) si p)
              where
                grab : Sigma Nat (\ j -> Pair (LeN k j) (LeN p (hgt (ov j))))
                     -> Sigma Nat (\ m -> LeN p (hgt (ov (NN m))))
                grab (mkSigma j (mkSigma lkj big)) =
                  mkSigma j
                    (LeN-trans {p} {hgt (ov j)} {hgt (ov (NN j))} big
                      (leF-hgt (ov j) (ov (NN j)) (mo j (NN j) (NN-ge j))))

            lb : (e : D) -> ((m : Nat) -> LeD (embed (F (BT (suc n) m))) e)
               -> LeD inf e
            lb e h = go e refl
              where
                hbd : (m : Nat) -> LeD (bot (hgt (ov (NN m)))) e
                hbd m = Eq-transport (\ z -> LeD z e) (shape m) (h m)

                suc-not : (x : Nat) -> Not (LeN (suc x) x)
                suc-not zero    ()
                suc-not (suc x) l = suc-not x l

                go : (y : D) -> Eq e y -> LeD inf e
                go (bot K) ey = Empty-elim (bad (esc (suc K)))
                  where
                    bad : Sigma Nat (\ m -> LeN (suc K) (hgt (ov (NN m)))) -> Empty
                    bad (mkSigma m big) =
                      suc-not K
                        (LeN-trans {suc K} {hgt (ov (NN m))} {K} big
                          (Eq-transport (\ z -> LeD (bot (hgt (ov (NN m)))) z) ey (hbd m)))
                go (cpl K) ey = Empty-elim (bad (esc (suc K)))
                  where
                    bad : Sigma Nat (\ m -> LeN (suc K) (hgt (ov (NN m)))) -> Empty
                    bad (mkSigma m big) =
                      suc-not K
                        (LeN-trans {suc K} {hgt (ov (NN m))} {K} big
                          (Eq-transport (\ z -> LeD (bot (hgt (ov (NN m)))) z) ey (hbd m)))
                go inf     ey = Eq-transport (\ z -> LeD inf z) (Eq-sym ey) tt

------------------------------------------------------------------------
-- THE THEOREM
------------------------------------------------------------------------

prLub : (q : PR) (n : Nat) (wf : Wf q n) -> Sigma D (\ d -> IsLub (Chain q n) d)
prLub q n wf =
  lubOf n (traceOf q n wf) (evalF q)
    (fst (traceOf-ok q n wf)) (traceOf-MP1np q n wf) (snd (traceOf-ok q n wf))

prValMP : (q : PR) (n : Nat) -> Wf q n -> D
prValMP q n wf = fst (prLub q n wf)

prValMP-lub : (q : PR) (n : Nat) (wf : Wf q n) -> IsLub (Chain q n) (prValMP q n wf)
prValMP-lub q n wf = snd (prLub q n wf)
