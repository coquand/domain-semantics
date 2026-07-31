{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.BlkGrowFail
--
-- THE GROWTH CLAUSE (G) IS **NOT** CLOSED UNDER MUTUAL RECURSION.
--
-- (G) -- `MPGrow.GV k` -- is a DECIDED disjunction: `k` is eventually
-- constant with the sup attained, or it grows by at least one every p steps
-- past a threshold M.  This file exhibits the simplest case where that
-- cannot survive the recursion clause: a block at r = 2 whose two step terms
-- have (I) with a CONSTANT index and (G) with an explicit period, but whose
-- component 0 height is the orbit of 0 under a one-coordinate deterministic
-- iteration for which (G) is exactly LPO.
--
-- THE INSTANCE.  Let `b : Nat -> Nat` be ANY binary sequence (b n is 0 or 1;
-- read it as "the machine has not yet halted by step n").  Put
--
--     a = r = 2,   Y = 0,   iv 0 n = 0,   iv 1 n = 1,
--     kv 0 n = b n + n,     kv 1 n = 0.
--
--   * (I) holds for both step terms with threshold 0 and a CONSTANT index
--     (`ivE-stab`), so `MainBlk2.MPblock` applies: the block's index really is
--     eventually constant (`blk-I`).  The obstruction is not about (I).
--   * (G) holds for both step terms, computably and with no appeal to b:
--     `kv 1` is constant, and `kv 0` grows by at least one every TWO steps
--     from threshold 0 (`kv0-grow`) -- because b n + n goes up by 1 + (b(n+2)
--     - b n) >= 0 over two steps whatever b does.
--   * g_0 reads coordinate 0 -- its OWN value one depth down -- at every
--     step, so its replay depth against the available heights is exactly that
--     height (`nOf-const`), and the block's height dynamics collapses to
--
--         x_0 = 0,   x_{m+1} = kv 0 (x_m) = x_m + b (x_m)
--
--     (`hv-orb`): the orbit walks up one step at a time while b is 1 and
--     STOPS FOR EVER at the first n it reaches with b n = 0.
--
-- So the orbit is eventually constant iff b takes the value 0 somewhere, and
-- grows iff b is identically 1 -- and each side of (G) DECIDES that:
--
--     blk-grow-lpo : GV (\ m -> hvE m zero) ->
--                    Or (Sigma Nat (\ n -> Eq (b n) zero))
--                       ((n : Nat) -> Eq (b n) one)
--
-- i.e. (G) for this block IS LPO.  A constructive proof of "(I) and (G) for
-- the step terms implies (I) and (G) for the block" would therefore prove
-- LPO, so there is none.  (The same argument in the classical reading: for a
-- primitive recursive f on lazy naturals, "is the height of f(S^m bot)
-- bounded in m?" is Pi-0-1-hard, so no total procedure returns the verdict.)
--
-- WHAT SURVIVES.  The composition clause (`MainComp.mp-comp`) consumes (G)
-- only through `gv-pass`: "does this height ever pass the level K?", ONE
-- level at a time.  That predicate IS decidable for the orbit above -- run
-- K+1 iterations: a monotone deterministic iteration that has not passed K by
-- then has frozen below it.  See NEXT_SESSION_MP_CMUT.md, and `MPPass.MP`'s
-- comment, for the resulting proposal.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.BlkGrowFail where

open import OBSTINATION.Prelude
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.BlkReplay using
  (plus ; plus-ge-r ; plus-mono ; le-ne-lt ; LeN-suc-not)
open import OBSTINATION.ReplayLv using
  (bump ; bump-eq ; lv ; Adv ; nOf ; nOf-ge ; nOf-le)
open import OBSTINATION.MPGrow using (GV ; GrowN ; grow-unb ; gv-cong)
open import OBSTINATION.MPPass using
  (HPass ; MP ; hpass-cong ; hpass-const ; hpass-ge ; module IterF)
open import OBSTINATION.BlkTraceR using (hv ; av ; nn ; q ; av-rec)
open import OBSTINATION.MainBlk2 using (MPblock)
open import OBSTINATION.BlkPass2 using (hpass-blk ; mp-blk)

one : Nat
one = suc zero

two : Nat
two = suc one

------------------------------------------------------------------------
-- THE DATA: an arbitrary binary sequence
------------------------------------------------------------------------

module _ (b : Nat -> Nat)
         (b-bool : (n : Nat) -> Or (Eq (b n) zero) (Eq (b n) one))
         where

  -- LPO for this sequence
  LPOb : Set
  LPOb = Or (Sigma Nat (\ n -> Eq (b n) zero)) ((n : Nat) -> Eq (b n) one)

  ----------------------------------------------------------------------
  -- THE STEP TERM'S HEIGHT: kv 0 n = b n + n
  ----------------------------------------------------------------------

  kv0 : Nat -> Nat
  kv0 n = plus (b n) n

  b-le1 : (n : Nat) -> LeN (b n) one
  b-le1 n = route (b-bool n)
    where
      route : Or (Eq (b n) zero) (Eq (b n) one) -> LeN (b n) one
      route (inl e) = Eq-transport (\ z -> LeN z one) (Eq-sym e) tt
      route (inr e) = Eq-transport (\ z -> LeN z one) (Eq-sym e) (LeN-refl one)

  kv0-le-suc : (n : Nat) -> LeN (kv0 n) (suc n)
  kv0-le-suc n = plus-mono (b n) one n n (b-le1 n) (LeN-refl n)

  kv0-ge : (n : Nat) -> LeN n (kv0 n)
  kv0-ge n = plus-ge-r (b n) n

  kv0-mono : (n n' : Nat) -> LeN n n' -> LeN (kv0 n) (kv0 n')
  kv0-mono n n' le = route (EqNat-dec n n')
    where
      route : Dec (Eq n n') -> LeN (kv0 n) (kv0 n')
      route (yes e)  =
        Eq-transport (\ z -> LeN (kv0 n) (kv0 z)) e (LeN-refl (kv0 n))
      route (no  ne) =
        LeN-trans {kv0 n} {suc n} {kv0 n'} (kv0-le-suc n)
          (LeN-trans {suc n} {n'} {kv0 n'} (le-ne-lt n n' le (\ e -> ne (Eq-sym e))) (kv0-ge n'))

  -- (G) for it, computably and whatever b does: over TWO steps b n + n goes
  -- up by 2 + (b (n+2) - b n) >= 1
  kv0-grow : GrowN kv0
  kv0-grow = mkSigma two (mkSigma zero (mkSigma tt st))
    where
      st : (n : Nat) -> LeN zero n -> LeN (suc (kv0 n)) (kv0 (plus two n))
      st n _ =
        LeN-trans {suc (kv0 n)} {suc (suc n)} {kv0 (suc (suc n))}
          (kv0-le-suc n) (kv0-ge (suc (suc n)))

  ----------------------------------------------------------------------
  -- THE ORBIT, AND WHAT (G) FOR IT WOULD DECIDE
  ----------------------------------------------------------------------

  orb : Nat -> Nat
  orb zero    = zero
  orb (suc m) = kv0 (orb m)

  -- while b is 1 along the orbit, the orbit is the identity
  orb-run : (T : Nat) -> ((m : Nat) -> LeN (suc m) T -> Eq (b (orb m)) one) ->
    Eq (orb T) T
  orb-run zero    hh = refl
  orb-run (suc T) hh =
    Eq-trans
      (Eq-cong (\ z -> plus (b (orb T)) z) (orb-run T sub))
      (Eq-cong (\ z -> plus z T) (hh T (LeN-refl T)))
    where
      sub : (m : Nat) -> LeN (suc m) T -> Eq (b (orb m)) one
      sub m lm = hh m (LeN-trans {suc m} {T} {suc T} lm (LeN-suc T))

  -- ... and once it reaches a zero of b it stops there for ever
  orb-cap : (s : Nat) -> Eq (b s) zero -> (m : Nat) -> LeN (orb m) s
  orb-cap s e zero    = tt
  orb-cap s e (suc m) = route (EqNat-dec (orb m) s)
    where
      ih : LeN (orb m) s
      ih = orb-cap s e m

      route : Dec (Eq (orb m) s) -> LeN (kv0 (orb m)) s
      route (yes eq) =
        Eq-transport (\ z -> LeN (plus z (orb m)) s)
          (Eq-sym (Eq-transport (\ z -> Eq (b z) zero) (Eq-sym eq) e)) ih
      route (no  ne) =
        LeN-trans {kv0 (orb m)} {suc (orb m)} {s}
          (kv0-le-suc (orb m)) (le-ne-lt (orb m) s ih (\ e -> ne (Eq-sym e)))

  -- so a first zero of b is found by a BOUNDED search once the orbit is known
  -- to stall
  find-zero : (T : Nat) ->
    Or (Sigma Nat (\ n -> Eq (b n) zero))
       ((m : Nat) -> LeN (suc m) T -> Eq (b (orb m)) one)
  find-zero zero    = inr (\ m ())
  find-zero (suc T) = route (find-zero T)
    where
      route :
        Or (Sigma Nat (\ n -> Eq (b n) zero))
           ((m : Nat) -> LeN (suc m) T -> Eq (b (orb m)) one) ->
        Or (Sigma Nat (\ n -> Eq (b n) zero))
           ((m : Nat) -> LeN (suc m) (suc T) -> Eq (b (orb m)) one)
      route (inl w)  = inl w
      route (inr hh) = route2 (b-bool (orb T))
        where
          route2 : Or (Eq (b (orb T)) zero) (Eq (b (orb T)) one) ->
            Or (Sigma Nat (\ n -> Eq (b n) zero))
               ((m : Nat) -> LeN (suc m) (suc T) -> Eq (b (orb m)) one)
          route2 (inl e0) = inl (mkSigma (orb T) e0)
          route2 (inr e1) = inr sub
            where
              sub : (m : Nat) -> LeN (suc m) (suc T) -> Eq (b (orb m)) one
              sub m lm = pick (LeN-dec (suc m) T)
                where
                  eq' : (x y : Nat) -> LeN x y -> Not (LeN (suc x) y) -> Eq x y
                  eq' zero    zero    l nl = refl
                  eq' zero    (suc y) l nl = Empty-elim (nl tt)
                  eq' (suc x) zero    () nl
                  eq' (suc x) (suc y) l nl = Eq-cong suc (eq' x y l nl)

                  pick : Dec (LeN (suc m) T) -> Eq (b (orb m)) one
                  pick (yes l)  = hh m l
                  pick (no  nl) =
                    Eq-transport (\ z -> Eq (b (orb z)) one)
                      (Eq-sym (eq' m T lm nl)) e1

  -- THE REDUCTION: (G) for the orbit decides b
  gv-orb-lpo : GV orb -> LPOb
  gv-orb-lpo (inl (mkSigma M bnd)) = route (find-zero (suc (orb M)))
    where
      route :
        Or (Sigma Nat (\ n -> Eq (b n) zero))
           ((m : Nat) -> LeN (suc m) (suc (orb M)) -> Eq (b (orb m)) one) ->
        LPOb
      route (inl w)  = inl w
      route (inr hh) = Empty-elim (LeN-suc-not (orb M) bad)
        where
          bad : LeN (suc (orb M)) (orb M)
          bad =
            Eq-transport (\ z -> LeN z (orb M))
              (orb-run (suc (orb M)) hh) (bnd (suc (orb M)))
  gv-orb-lpo (inr gr) = inr allone
    where
      allone : (n : Nat) -> Eq (b n) one
      allone n = route (b-bool n)
        where
          route : Or (Eq (b n) zero) (Eq (b n) one) -> Eq (b n) one
          route (inr e) = e
          route (inl e) = Empty-elim (bad (grow-unb orb gr n))
            where
              bad : Sigma Nat (\ s -> LeN (suc n) (orb s)) -> Empty
              bad (mkSigma s big) =
                LeN-suc-not n
                  (LeN-trans {suc n} {orb s} {n} big (orb-cap n e s))

  ----------------------------------------------------------------------
  -- THE BLOCK WHOSE HEIGHT IS THAT ORBIT
  --
  -- g_0 reads coordinate 0 -- its own value one depth down -- at every step,
  -- g_1 reads coordinate 1 and returns bot.  Two recursive slots, no
  -- parameters.
  ----------------------------------------------------------------------

  ivE : Nat -> Nat -> Nat
  ivE zero    n = zero
  ivE (suc _) n = one

  ivrE : (j n : Nat) -> LeN (suc (ivE j n)) two
  ivrE zero    n = tt
  ivrE (suc j) n = tt

  kvE : Nat -> Nat -> Nat
  kvE zero    n = kv0 n
  kvE (suc _) n = zero

  kvE-mono : (j n n' : Nat) -> LeN n n' -> LeN (kvE j n) (kvE j n')
  kvE-mono zero    n n' le = kv0-mono n n' le
  kvE-mono (suc j) n n' le = tt

  YE : Nat -> Nat
  YE c = zero

  hvE : Nat -> Nat -> Nat
  hvE = hv two two ivE ivrE kvE kvE-mono YE

  avE : Nat -> Nat -> Nat
  avE = av two two ivE ivrE kvE kvE-mono YE

  stpE : Nat -> Nat -> Nat
  stpE = nn two two ivE ivrE kvE kvE-mono YE

  ----------------------------------------------------------------------
  -- A WALK THAT ALWAYS DEMANDS COORDINATE 0 REPLAYS EXACTLY THAT HEIGHT
  ----------------------------------------------------------------------

  lv0 : (n : Nat) -> Eq (lv two (ivE zero) (ivrE zero) zero n) n
  lv0 zero    = refl
  lv0 (suc n) =
    Eq-trans (bump-eq zero (\ d -> lv two (ivE zero) (ivrE zero) d n) zero refl)
             (Eq-cong suc (lv0 n))

  nOf-const : (avv : Nat -> Nat) ->
    Eq (nOf two (ivE zero) (ivrE zero) avv) (avv zero)
  nOf-const avv =
    LeN-antisym {nOf two (ivE zero) (ivrE zero) avv} {avv zero} up down
    where
      up : LeN (nOf two (ivE zero) (ivrE zero) avv) (avv zero)
      up = nOf-le two (ivE zero) (ivrE zero) avv (avv zero) nadv
        where
          nadv : Not (Adv two (ivE zero) (ivrE zero) avv (avv zero))
          nadv ad =
            LeN-suc-not (avv zero)
              (Eq-transport (\ z -> LeN (suc z) (avv zero)) (lv0 (avv zero)) ad)

      down : LeN (avv zero) (nOf two (ivE zero) (ivrE zero) avv)
      down = nOf-ge two (ivE zero) (ivrE zero) avv (avv zero) hh
        where
          hh : (n : Nat) -> LeN (suc n) (avv zero) ->
               Adv two (ivE zero) (ivrE zero) avv n
          hh n ln =
            Eq-transport (\ z -> LeN (suc z) (avv zero)) (Eq-sym (lv0 n)) ln

  -- so the block's height dynamics IS the orbit
  hv-orb : (m : Nat) -> Eq (hvE m zero) (orb m)
  hv-orb zero    = refl
  hv-orb (suc m) = Eq-cong kv0 step
    where
      step : Eq (stpE zero m) (orb m)
      step =
        Eq-trans (nOf-const (avE m))
          (Eq-trans (av-rec two two ivE ivrE kvE kvE-mono YE zero tt m)
                    (hv-orb m))

  ----------------------------------------------------------------------
  -- (I) DOES HOLD FOR THIS INSTANCE ...
  ----------------------------------------------------------------------

  IE : Nat -> Nat
  IE zero    = zero
  IE (suc _) = one

  ivE-stab : (j n : Nat) -> LeN zero n -> Eq (ivE j n) (IE j)
  ivE-stab zero    n l = refl
  ivE-stab (suc j) n l = refl

  -- both step terms have (G), computably
  gvE : (j : Nat) -> GV (kvE j)
  gvE zero    = inr kv0-grow
  gvE (suc j) = inl (mkSigma zero (\ s -> tt))

  -- and the block's index is eventually constant, by MainBlk2
  blk-I : (j : Nat) -> LeN (suc j) two ->
    EvConstN (q two two ivE ivrE kvE kvE-mono YE j)
  blk-I = MPblock two ivE ivrE kvE kvE-mono YE (\ _ -> zero) IE ivE-stab

  ----------------------------------------------------------------------
  -- ... AND (G) FOR THE BLOCK IS LPO
  ----------------------------------------------------------------------

  blk-grow-lpo : GV (\ m -> hvE m zero) -> LPOb
  blk-grow-lpo g = gv-orb-lpo (gv-cong (\ m -> hvE m zero) orb hv-orb g)

  ----------------------------------------------------------------------
  -- BUT THE LEVEL-BY-LEVEL VERDICT DOES HOLD, OUTRIGHT
  --
  -- The very same block height satisfies `HPass` -- "does it ever pass K?"
  -- -- with no hypothesis whatever, because it is a deterministic monotone
  -- iteration and so is decided by K+1 iterations (`MPPass.IterF.it-pass`).
  -- So the failure above is a failure of the SHAPE of the height clause,
  -- not of the clause's role in the proof: what `MainComp.hdec` consumes is
  -- exactly `HPass`.
  ----------------------------------------------------------------------

  open IterF kv0 kv0-mono zero tt using (it ; it-pass)

  orb-it : (m : Nat) -> Eq (orb m) (it m)
  orb-it zero    = refl
  orb-it (suc m) = Eq-cong kv0 (orb-it m)

  blk-hpass : HPass (\ m -> hvE m zero)
  blk-hpass =
    hpass-cong it (\ m -> hvE m zero)
      (\ m -> Eq-sym (Eq-trans (hv-orb m) (orb-it m))) it-pass

  ----------------------------------------------------------------------
  -- ... AND (H) IS THERE BY THE GENERAL THEOREM, NOT JUST BY HAND
  --
  -- (H) for the two step terms costs nothing here -- `kv 0 n = b n + n` is at
  -- least `n`, and `kv 1` is constant, so neither verdict looks at `b`
  -- (whereas the bounded side of (G) for the BLOCK would have to).  So the
  -- recursion clause `BlkPass2.hpass-blk` applies, and delivers (H) for this
  -- block; with `MainBlk2.MPblock` for (I), the whole Main Property holds of
  -- the very block for which (G) is LPO.
  ----------------------------------------------------------------------

  hverdE : (j : Nat) -> HPass (kvE j)
  hverdE zero    = hpass-ge (kvE zero) kv0-ge
  hverdE (suc j) = hpass-const zero

  blk-hpass-thm : HPass (\ m -> hvE m zero)
  blk-hpass-thm =
    hpass-blk two ivE ivrE kvE kvE-mono YE (\ _ -> zero) IE ivE-stab hverdE
      zero tt

  blk-mp : MP (q two two ivE ivrE kvE kvE-mono YE zero) (\ m -> hvE m zero)
  blk-mp =
    mp-blk two ivE ivrE kvE kvE-mono YE (\ _ -> zero) IE ivE-stab hverdE zero tt
