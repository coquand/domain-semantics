{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.BlkFunPar
--
-- THE REINDEXING, WITH PARAMETERS: THE PIECES THAT PORT FROM MP1.
--
-- `BlkFun.NoPar.mp-fun` transfers the block's Main Property to the
-- components AS FUNCTIONS WITH A TRACE when there are no parameters,
-- because then the walk raises only the recursion argument and the DEPTH
-- IS THE WALK STEP.  With parameters the component's walk is
-- TWO-DIMENSIONAL:
--
--     A (n+1) = bump (Ivb n) (A n)
--     Ivb n   = q (Ypar n) j (A n 0)        -- the block's index, at the
--     Kvb n   = hv (Ypar n) (A n 0) j       -- levels REACHED so far
--
-- and everything proved about the block (`MainBlk2.MPblock`,
-- `BlkPass2.hpass-blk`) is at a FIXED `Y`.
--
-- THIS IS EXACTLY THE WALK OF `precTr` (`TrPrecIv`, `TrPrecPar`), under
-- the dictionary
--
--     A n        <->  Lv k          the levels reached after n steps
--     A n 0      <->  Lv k 0        the recursion depth
--     Ypar n     <->  the parameter levels
--     Ivb n      <->  ivP k = Qd (Lv k) (Lv k 0)
--     MPblock    <->  Qd-stab-full  (the DEPTH direction, at fixed levels)
--
-- and the one structural fact that made MP1's parameter direction work is
-- present here too: **the chain does not see the depth coordinate**.
-- `Ypar n c = A n (1 + (c-2))` never mentions `A n 0`, so a step with
-- `Ivb n = 0` raises the depth and leaves the parameters alone --- it
-- merely extends the fold.  That is `A-fix` / `A-depth` below, and it is
-- what makes `stretch` work.
--
-- WHAT THIS FILE PROVIDES (all EXIT 0, no postulate/hole/pragma):
--
--   * `q-source`   -- a non-zero demand of the block comes from a
--                     PARAMETER demand of some step term at some depth
--                     below.  (`PZ.Qd-source`.)
--   * `avail-le`   -- the available height at the demanded coordinate is
--                     below the replay depth (`NGf.NG-ge-hts`), whence
--                     `par-small`: a parameter demand whose replay has not
--                     passed the step term's threshold has that
--                     parameter's level BELOW the threshold.  This is
--                     min1.pdf's finiteness of the approximant, and it is
--                     the source of the fuel (`TrCompNG.cg-or-small`).
--   * `stretch`    -- the DEPTH direction for the component's own walk: a
--                     stretch of `Ivb = 0` long enough to pass `MPblock`'s
--                     threshold forces `Ivb = 0` FOR EVER.  (`PZ.stretch`.)
--   * `BUD`        -- the fuel: sum over the parameters of
--                     `min (level) NN`, capped, raised by exactly one on a
--                     cheap bump, and exhausted.  (`TrPrecIv.BUD`.)
--
--   * `RUN.Ivb-EvConstN` -- the INDEX CLAUSE for a block component WITH
--                     parameters, at r = 2, reduced to ONE interface: a
--                     `bsplit` that classifies each bump as TERMINAL,
--                     CHEAP, or an answer outright.  (`TrPrecPar.PAR.RUN`.)
--
-- WHAT IS LEFT is `bsplit`, and the OBVIOUS one is FALSE -- see the
-- comment "WHY THE OBVIOUS `bsplit` DOES NOT CLOSE" below, which gives
-- the concrete two-component instance.  Its cheap half is right and free
-- (`q-source` + `par-small`); its terminal half is not, because with TWO
-- step terms pointing at each other, passing a threshold for the
-- component that EXITS the chain says nothing about the components ABOVE
-- it, which may exit later to a DIFFERENT parameter.  That is the one
-- place where r = 2 genuinely differs from MP1's single step term.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.BlkFunPar where

open import OBSTINATION.Prelude
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.BlkReplay using
  (plus ; plus-ge-r ; plus-suc-r ; plus-mono ; nle-lt ; LeN-suc-not ;
   Eq-cong2 ; le-nlt-eq)
open import OBSTINATION.MPPass using (Mono ; HPass ; MP ; plus-ge-l)
open import OBSTINATION.MP1 using (le-add)
open import OBSTINATION.ReplayLv using
  (bump ; bump-eq ; bump-ne ; lv ; lv-le ; nOf ; nOf-mono ;
   sumTo ; sumTo-mono ; sumTo-bump)
import OBSTINATION.WalkAffine as WA
open import OBSTINATION.BlkTraceR using
  (subN ; hv ; av ; nn ; cIdx ; q ; av-out ; av-rec ; av-mono ;
   pickQ-in ; pickQ-out)
open import OBSTINATION.MainBlk2 using (one ; two ; MPblock)
open import OBSTINATION.BlkFun using (module Trace ; q-Y ; hv-Y ; hv-Y-le)

------------------------------------------------------------------------
-- A NON-ZERO DEMAND OF THE BLOCK COMES FROM A PARAMETER DEMAND OF A STEP
-- TERM AT SOME DEPTH BELOW
--
-- `q` folds DOWN the depth, switching component at each step while the
-- current step term demands a recursive value, and STOPS at the first
-- depth where it demands a parameter.  So a non-zero answer names that
-- depth and that component.  (`TrPrecIv.PZ.Qd-source`.)
------------------------------------------------------------------------

module _ (r a : Nat)
         (iv : Nat -> Nat -> Nat)
         (ivr : (j n : Nat) -> LeN (suc (iv j n)) a)
         (kv : Nat -> Nat -> Nat)
         (kvm : (j n n' : Nat) -> LeN n n' -> LeN (kv j n) (kv j n'))
         (Y : Nat -> Nat)
         where

  private
    CI : Nat -> Nat -> Nat
    CI = cIdx r a iv ivr kv kvm Y

    QQ : Nat -> Nat -> Nat
    QQ = q r a iv ivr kv kvm Y

  Src : Nat -> Nat -> Set
  Src D i =
    Sigma Nat (\ m -> Sigma Nat (\ s ->
      Pair (LeN (suc s) r)
        (Pair (LeN (suc m) D)
          (Pair (Not (LeN (suc (CI s m)) r)) (Eq (subN r (CI s m)) i)))))

  q-source : (j : Nat) -> LeN (suc j) r -> (D i : Nat)
           -> Eq (QQ j D) (suc i) -> Src D i
  q-source j ljr zero    i e = Empty-elim (znot e)
    where
      znot : Not (Eq zero (suc i))
      znot ()
  q-source j ljr (suc m) i e = route (LeN-dec (suc (CI j m)) r)
    where
      route : Dec (LeN (suc (CI j m)) r) -> Src (suc m) i
      route (yes lc) = up (q-source (CI j m) lc m i down)
        where
          down : Eq (QQ (CI j m) m) (suc i)
          down =
            Eq-trans
              (Eq-sym
                (pickQ-in r a iv ivr kv kvm Y (CI j m) (\ s -> QQ s m) lc))
              e

          up : Src m i -> Src (suc m) i
          up (mkSigma m' (mkSigma s (mkSigma ls (mkSigma lm w)))) =
            mkSigma m'
              (mkSigma s
                (mkSigma ls
                  (mkSigma (LeN-trans {suc m'} {m} {suc m} lm (LeN-suc m)) w)))
      route (no nc) =
        mkSigma m
          (mkSigma j (mkSigma ljr (mkSigma (LeN-refl m) (mkSigma nc same))))
        where
          same : Eq (subN r (CI j m)) i
          same =
            suc-inj
              (Eq-trans
                (Eq-sym
                  (pickQ-out r a iv ivr kv kvm Y (CI j m) (\ s -> QQ s m) nc))
                e)

------------------------------------------------------------------------
-- THE AVAILABLE HEIGHT AT THE DEMANDED COORDINATE IS BELOW THE REPLAY
--
-- `stuck-level` says the level the walk has spent at the coordinate it is
-- stuck on IS the height available there, and a walk spends at most one
-- step per level (`lv-le`).  (`TrCompNG.NGf.NG-ge-hts`.)
------------------------------------------------------------------------

avail-le : (a : Nat) (ivs : Nat -> Nat)
           (ivrs : (n : Nat) -> LeN (suc (ivs n)) a)
           (avv : Nat -> Nat)
         -> LeN (avv (ivs (nOf a ivs ivrs avv))) (nOf a ivs ivrs avv)
avail-le a ivs ivrs avv =
  Eq-transport (\ z -> LeN z (nOf a ivs ivrs avv))
    (WA.stuck-level a ivs ivrs avv)
    (lv-le a ivs ivrs (ivs (nOf a ivs ivrs avv)) (nOf a ivs ivrs avv))

------------------------------------------------------------------------
-- A PARAMETER DEMAND BELOW THE STEP TERM'S THRESHOLD HAS A SMALL LEVEL
--
-- If the step term's replay at the source depth has NOT passed its own
-- threshold, then the height available at the coordinate it is stuck on
-- is below that threshold -- and that coordinate being a parameter, that
-- height IS the parameter's level.  This is what bounds the fuel.
-- (`TrCompNG.NGf.cg-or-small`.)
------------------------------------------------------------------------

par-small : (r a : Nat)
            (iv : Nat -> Nat -> Nat)
            (ivr : (j n : Nat) -> LeN (suc (iv j n)) a)
            (kv : Nat -> Nat -> Nat)
            (kvm : (j n n' : Nat) -> LeN n n' -> LeN (kv j n) (kv j n'))
            (Y : Nat -> Nat)
          -> (s m Ns : Nat)
          -> Not (LeN (suc (cIdx r a iv ivr kv kvm Y s m)) r)
          -> Not (LeN Ns (nn r a iv ivr kv kvm Y s m))
          -> LeN (suc (Y (cIdx r a iv ivr kv kvm Y s m))) Ns
par-small r a iv ivr kv kvm Y s m Ns nc nl =
  LeN-trans {suc (Y c)} {suc (nn r a iv ivr kv kvm Y s m)} {Ns}
    (Eq-transport (\ z -> LeN z (nn r a iv ivr kv kvm Y s m))
      (av-out r a iv ivr kv kvm Y c nc m)
      (avail-le a (iv s) (ivr s) (av r a iv ivr kv kvm Y m)))
    (nle-lt Ns (nn r a iv ivr kv kvm Y s m) nl)
  where
    c : Nat
    c = cIdx r a iv ivr kv kvm Y s m

------------------------------------------------------------------------
-- THE COMPONENT'S OWN WALK
------------------------------------------------------------------------

module PAR (a : Nat)
           (iv : Nat -> Nat -> Nat)
           (ivr : (j n : Nat) -> LeN (suc (iv j n)) a)
           (kv : Nat -> Nat -> Nat)
           (kvm : (j n n' : Nat) -> LeN n n' -> LeN (kv j n) (kv j n'))
           (j : Nat) (lj : LeN (suc j) two)
           where

  open Trace a iv ivr kv kvm j lj

  QY : (Nat -> Nat) -> Nat -> Nat -> Nat
  QY Y = q two a iv ivr kv kvm Y

  -- the number of parameters
  P : Nat
  P = subN two a

  ------------------------------------------------------------------
  -- A STRETCH OF `Ivb = 0` LEAVES THE PARAMETERS ALONE
  --
  -- `Ypar n` never mentions `A n 0`, so a `0`-step raises the depth and
  -- nothing else: the chain is the OLD one, one fold deeper.
  ------------------------------------------------------------------

  Zero-upto : Nat -> Nat -> Set
  Zero-upto K t = (t' : Nat) -> LeN (suc t') t -> Eq (Ivb (plus t' K)) zero

  Zero-down : (K t t' : Nat) -> LeN t' t -> Zero-upto K t -> Zero-upto K t'
  Zero-down K t t' le h t'' l =
    h t'' (LeN-trans {suc t''} {t'} {t} l le)

  A-fix : (K t : Nat) -> Zero-upto K t -> (i : Nat)
        -> Eq (A (plus t K) (suc i)) (A K (suc i))
  A-fix K zero    h i = refl
  A-fix K (suc t) h i =
    Eq-trans
      (bump-ne (Ivb (plus t K)) (A (plus t K)) (suc i) ne)
      (A-fix K t (Zero-down K (suc t) t (LeN-suc t) h) i)
    where
      ne : Not (Eq (suc i) (Ivb (plus t K)))
      ne e = zne (Eq-trans e (h t (LeN-refl t)))
        where
          zne : Not (Eq (suc i) zero)
          zne ()

  A-depth : (K t : Nat) -> Zero-upto K t
          -> Eq (A (plus t K) zero) (plus t (A K zero))
  A-depth K zero    h = refl
  A-depth K (suc t) h =
    Eq-trans
      (bump-eq (Ivb (plus t K)) (A (plus t K)) zero
        (Eq-sym (h t (LeN-refl t))))
      (Eq-cong suc (A-depth K t (Zero-down K (suc t) t (LeN-suc t) h)))

  Ypar-fix : (K t : Nat) -> Zero-upto K t
           -> (c : Nat) -> Not (LeN (suc c) two)
           -> Eq (Ypar (plus t K) c) (Ypar K c)
  Ypar-fix K t h c nc = A-fix K t h (subN two c)

  Ivb-along : (K t : Nat) -> Zero-upto K t
            -> Eq (Ivb (plus t K)) (QY (Ypar K) j (plus t (A K zero)))
  Ivb-along K t h =
    Eq-trans
      (q-Y two a iv ivr kv kvm (Ypar (plus t K)) (Ypar K) (Ypar-fix K t h)
        (A (plus t K) zero) j)
      (Eq-cong (\ z -> QY (Ypar K) j z) (A-depth K t h))

  ------------------------------------------------------------------
  -- A BOUNDED CHECK DECIDES A `0`-STRETCH
  --
  -- With `J` the threshold `MainBlk2.MPblock` supplies at the CURRENT
  -- parameter levels, `Ivb` being `0` for the first `J+1` steps forces it
  -- to be `0` FOR EVER.  So a `0`-stretch either settles the index
  -- outright or ends within `J+1` steps, at a stage demanding a
  -- PARAMETER.  (`TrPrecIv.PZ.stretch`.)
  ------------------------------------------------------------------

  stretch : (K J : Nat)
          -> ((m : Nat) -> LeN J m -> Eq (QY (Ypar K) j m) (QY (Ypar K) j J))
          -> Zero-upto K (suc J)
          -> (t : Nat) -> Eq (Ivb (plus t K)) zero
  stretch K J con hyp t = all (suc t) t (LeN-refl t)
    where
      -- the constant value IS `0`, read off the last checked step
      baseEq : Eq (QY (Ypar K) j J) zero
      baseEq =
        Eq-trans
          (Eq-sym
            (Eq-trans
              (Ivb-along K J (Zero-down K (suc J) J (LeN-suc J) hyp))
              (con (plus J (A K zero)) (plus-ge-l J (A K zero)))))
          (hyp J (LeN-refl J))

      all : (n : Nat) -> Zero-upto K n
      all zero    = \ t' ()
      all (suc n) = ext
        where
          ext : (t' : Nat) -> LeN (suc t') (suc n) -> Eq (Ivb (plus t' K)) zero
          ext t' lt = pick (LeN-dec (suc t') (suc J))
            where
              pick : Dec (LeN (suc t') (suc J)) -> Eq (Ivb (plus t' K)) zero
              pick (yes l)  = hyp t' l
              pick (no  nl) =
                Eq-trans (Ivb-along K t' (Zero-down K n t' lt (all n)))
                  (Eq-trans (con (plus t' (A K zero)) big) baseEq)
                where
                  big : LeN J (plus t' (A K zero))
                  big =
                    LeN-trans {J} {t'} {plus t' (A K zero)}
                      (LeN-trans {J} {suc J} {t'}
                        (LeN-suc J) (nle-lt (suc t') (suc J) nl))
                      (plus-ge-l t' (A K zero))

  ------------------------------------------------------------------
  -- THE FUEL
  --
  -- A parameter that is always demanded when it grows can be demanded at
  -- most `NN` times before its level passes the threshold; so the number
  -- of CHEAP bumps is bounded by `P * NN`.  (`TrPrecIv.BUD`.)
  ------------------------------------------------------------------

  sumTo-cong : (n : Nat) (f g : Nat -> Nat) -> ((i : Nat) -> Eq (f i) (g i))
             -> Eq (sumTo n f) (sumTo n g)
  sumTo-cong zero    f g e = refl
  sumTo-cong (suc n) f g e =
    Eq-cong2 plus (e n) (sumTo-cong n f g e)

  minN-mono : (x y z : Nat) -> LeN x y -> LeN (minN x z) (minN y z)
  minN-mono zero    y       z       le = tt
  minN-mono (suc x) zero    z       ()
  minN-mono (suc x) (suc y) zero    le = tt
  minN-mono (suc x) (suc y) (suc z) le = minN-mono x y z le

  module BUD (NN : Nat) where

    Mof : Nat -> Nat
    Mof n = sumTo P (\ i -> minN (A n (suc i)) NN)

    Cap : Nat
    Cap = sumTo P (\ _ -> NN)

    M-bound : (n : Nat) -> LeN (Mof n) Cap
    M-bound n =
      sumTo-mono P (\ i -> minN (A n (suc i)) NN) (\ _ -> NN)
        (\ i -> minN-le-r (A n (suc i)) NN)

    Mof-mono : (n n' : Nat) -> LeN n n' -> LeN (Mof n) (Mof n')
    Mof-mono n n' le =
      sumTo-mono P (\ i -> minN (A n (suc i)) NN)
        (\ i -> minN (A n' (suc i)) NN)
        (\ i -> minN-mono (A n (suc i)) (A n' (suc i)) NN
                  (A-mono n n' le (suc i)))

    -- a CHEAP bump raises the fuel by exactly one
    M-step : (n i0 : Nat) -> LeN (suc i0) P -> Eq (Ivb n) (suc i0)
           -> LeN (suc (A n (suc i0))) NN
           -> Eq (Mof (suc n)) (suc (Mof n))
    M-step n i0 li0 ev cheap =
      Eq-trans
        (sumTo-cong P (\ i -> minN (A (suc n) (suc i)) NN)
          (bump i0 (\ i -> minN (A n (suc i)) NN)) pt)
        (sumTo-bump P i0 li0 (\ i -> minN (A n (suc i)) NN))
      where
        pt : (i : Nat) -> Eq (minN (A (suc n) (suc i)) NN)
                             (bump i0 (\ d -> minN (A n (suc d)) NN) i)
        pt i = route (EqNat-dec i i0)
          where
            route : Dec (Eq i i0)
                  -> Eq (minN (A (suc n) (suc i)) NN)
                        (bump i0 (\ d -> minN (A n (suc d)) NN) i)
            route (yes e) =
              Eq-trans
                (Eq-cong (\ z -> minN (A (suc n) (suc z)) NN) e)
                (Eq-trans atI0
                  (Eq-sym
                    (Eq-trans
                      (Eq-cong (bump i0 (\ d -> minN (A n (suc d)) NN)) e)
                      (bump-eq i0 (\ d -> minN (A n (suc d)) NN) i0 refl))))
              where
                aE : Eq (A (suc n) (suc i0)) (suc (A n (suc i0)))
                aE = bump-eq (Ivb n) (A n) (suc i0) (Eq-sym ev)

                atI0 : Eq (minN (A (suc n) (suc i0)) NN)
                          (suc (minN (A n (suc i0)) NN))
                atI0 =
                  Eq-trans (Eq-cong (\ z -> minN z NN) aE)
                    (Eq-trans (minN-l {suc (A n (suc i0))} {NN} cheap)
                      (Eq-cong suc
                        (Eq-sym
                          (minN-l {A n (suc i0)} {NN}
                            (LeN-trans {A n (suc i0)} {suc (A n (suc i0))} {NN}
                              (LeN-suc (A n (suc i0))) cheap)))))
            route (no ne) =
              Eq-trans
                (Eq-cong (\ z -> minN z NN)
                  (bump-ne (Ivb n) (A n) (suc i)
                    (\ e -> ne (suc-inj (Eq-trans e ev)))))
                (Eq-sym (bump-ne i0 (\ d -> minN (A n (suc d)) NN) i ne))

    -- at the bound, no bump can be cheap
    M-max : (n i0 : Nat) -> LeN (suc i0) P -> Eq (Ivb n) (suc i0)
          -> LeN Cap (Mof n) -> Not (LeN (suc (A n (suc i0))) NN)
    M-max n i0 li0 ev full cheap =
      LeN-suc-not Cap
        (LeN-trans {suc Cap} {suc (Mof n)} {Cap} full
          (Eq-transport (\ z -> LeN z Cap) (M-step n i0 li0 ev cheap)
            (M-bound (suc n))))

  ------------------------------------------------------------------
  -- THE INDEX CLAUSE, REDUCED TO ONE TERMINAL LEMMA
  --
  -- Exactly `TrPrecPar.PAR.RUN`: a fuel recursion on `BUD.Cap = P * B`.
  -- At each stage the index is decided; a `0` runs `stretch` over a
  -- window of `J+1` (`J` from `MainBlk2.MPblock` at the CURRENT parameter
  -- levels) and either wins outright or jumps to the first bump; a bump
  -- is handed to `bsplit`, which must say TERMINAL (the demand persists),
  -- CHEAP (the demanded parameter's level is below `B`, so the bump costs
  -- one unit of the fuel), or produce the answer outright.  `M-max` says
  -- the cheap case cannot recur once the fuel is spent.
  --
  -- `par-small` is what a caller uses to discharge CHEAP: at the source
  -- depth `q-source` names, either the step term's replay has passed its
  -- own threshold -- the TERMINAL case, and the only thing left open --
  -- or the demanded parameter's level is below it.
  ------------------------------------------------------------------

  Res : Set
  Res = EvConstN Ivb

  Persist : Nat -> Nat -> Set
  Persist n i0 = (n' : Nat) -> LeN n n' -> Eq (Ivb n') (suc i0)

  module RUN (N I : Nat -> Nat)
             (iv-stab : (s n : Nat) -> LeN (N s) n -> Eq (iv s n) (I s))
             (B : Nat)
             (bsplit : (n i0 : Nat) -> Eq (Ivb n) (suc i0)
                     -> Or (Persist n i0)
                           (Or (LeN (suc (A n (suc i0))) B) Res))
             where

    module BB = BUD B

    -- the DEPTH direction, at the parameter levels reached so far
    JJ : (n : Nat) -> EvConstN (QY (Ypar n) j)
    JJ n = MPblock a iv ivr kv kvm (Ypar n) N I iv-stab j lj

    loop : (F n : Nat) -> LeN BB.Cap (plus F (BB.Mof n)) -> Res
    loop F n inv = route (Ivb n) refl
      where
        --------------------------------------------------------------
        -- a bump at stage `n'`, demanding parameter `i0`
        --------------------------------------------------------------
        bumpAt : (n' i0 : Nat) -> LeN n n' -> Eq (Ivb n') (suc i0) -> Res
        bumpAt n' i0 lnn' ev = pick (bsplit n' i0 ev)
          where
            pick : Or (Persist n' i0)
                      (Or (LeN (suc (A n' (suc i0))) B) Res)
                 -> Res
            pick (inl pers) =
              mkSigma n' (\ n'' ln -> Eq-trans (pers n'' ln) (Eq-sym ev))
            pick (inr (inr r))  = r
            pick (inr (inl ch)) = spend F inv'
              where
                li0 : LeN (suc i0) P
                li0 =
                  Eq-transport (\ z -> LeN (suc z) (suc P)) ev (Ivb-range n')

                inv' : LeN BB.Cap (plus F (BB.Mof n'))
                inv' =
                  LeN-trans {BB.Cap} {plus F (BB.Mof n)} {plus F (BB.Mof n')}
                    inv
                    (plus-mono F F (BB.Mof n) (BB.Mof n') (LeN-refl F)
                      (BB.Mof-mono n n' lnn'))

                spend : (F' : Nat) -> LeN BB.Cap (plus F' (BB.Mof n')) -> Res
                spend zero     le' =
                  Empty-elim (BB.M-max n' i0 li0 ev le' ch)
                spend (suc F') le' =
                  loop F' (suc n')
                    (Eq-transport (\ z -> LeN BB.Cap z) (Eq-sym stepE) le')
                  where
                    stepE : Eq (plus F' (BB.Mof (suc n')))
                               (suc (plus F' (BB.Mof n')))
                    stepE =
                      Eq-trans
                        (Eq-cong (plus F') (BB.M-step n' i0 li0 ev ch))
                        (plus-suc-r F' (BB.Mof n'))

        --------------------------------------------------------------
        -- the index is `0` here: either for ever, or a bump is near
        --------------------------------------------------------------
        zeroCase : Eq (Ivb n) zero -> Res
        zeroCase ev = jj (JJ n)
          where
            jj : EvConstN (QY (Ypar n) j) -> Res
            jj (mkSigma J con) = sc (scanZ (suc J))
              where
                P0 : Nat -> Set
                P0 t = Eq (Ivb (plus t n)) zero

                P0dec : (t : Nat) -> Dec (P0 t)
                P0dec t = EqNat-dec (Ivb (plus t n)) zero

                scanZ : (s : Nat)
                      -> Or ((t : Nat) -> LeN (suc t) s -> P0 t)
                            (Sigma Nat (\ t ->
                               Pair (LeN (suc t) s) (Not (P0 t))))
                scanZ zero    = inl (\ t ())
                scanZ (suc s) = step (scanZ s)
                  where
                    step : Or ((t : Nat) -> LeN (suc t) s -> P0 t)
                              (Sigma Nat (\ t ->
                                 Pair (LeN (suc t) s) (Not (P0 t))))
                         -> Or ((t : Nat) -> LeN (suc t) (suc s) -> P0 t)
                               (Sigma Nat (\ t ->
                                  Pair (LeN (suc t) (suc s)) (Not (P0 t))))
                    step (inr (mkSigma t (mkSigma lt np))) =
                      inr (mkSigma t
                            (mkSigma
                              (LeN-trans {suc t} {s} {suc s} lt (LeN-suc s))
                              np))
                    step (inl hh) = step2 (P0dec s)
                      where
                        step2 : Dec (P0 s)
                              -> Or ((t : Nat) -> LeN (suc t) (suc s) -> P0 t)
                                    (Sigma Nat (\ t ->
                                       Pair (LeN (suc t) (suc s))
                                            (Not (P0 t))))
                        step2 (no np) =
                          inr (mkSigma s (mkSigma (LeN-refl s) np))
                        step2 (yes ps) = inl ext
                          where
                            ext : (t : Nat) -> LeN (suc t) (suc s) -> P0 t
                            ext t lt = pk (LeN-dec (suc t) s)
                              where
                                pk : Dec (LeN (suc t) s) -> P0 t
                                pk (yes l)  = hh t l
                                pk (no  nl) =
                                  Eq-transport P0
                                    (Eq-sym (le-nlt-eq t s lt nl)) ps

                sc : Or ((t : Nat) -> LeN (suc t) (suc J) -> P0 t)
                        (Sigma Nat (\ t ->
                           Pair (LeN (suc t) (suc J)) (Not (P0 t))))
                   -> Res
                sc (inl hh) = mkSigma n con0
                  where
                    allz : (t : Nat) -> Eq (Ivb (plus t n)) zero
                    allz = stretch n J con hh

                    con0 : (n'' : Nat) -> LeN n n'' -> Eq (Ivb n'') (Ivb n)
                    con0 n'' ln = rt (le-add n n'' ln)
                      where
                        rt : Sigma Nat (\ t -> Eq n'' (plus t n))
                           -> Eq (Ivb n'') (Ivb n)
                        rt (mkSigma t e) =
                          Eq-trans
                            (Eq-transport (\ z -> Eq (Ivb z) zero)
                              (Eq-sym e) (allz t))
                            (Eq-sym ev)
                sc (inr (mkSigma t (mkSigma lt np))) =
                  nz (Ivb (plus t n)) refl
                  where
                    nz : (v : Nat) -> Eq (Ivb (plus t n)) v -> Res
                    nz zero     e = Empty-elim (np e)
                    nz (suc i0) e = bumpAt (plus t n) i0 (plus-ge-r t n) e

        route : (v : Nat) -> Eq (Ivb n) v -> Res
        route zero     ev = zeroCase ev
        route (suc i0) ev = bumpAt n i0 (LeN-refl n) ev

    -- THE INDEX CLAUSE OF THE MAIN PROPERTY FOR THE COMPONENT
    Ivb-EvConstN : EvConstN Ivb
    Ivb-EvConstN = loop BB.Cap zero (plus-ge-l BB.Cap (BB.Mof zero))

  ------------------------------------------------------------------
  -- WHY THE OBVIOUS `bsplit` DOES NOT CLOSE
  --
  -- The tempting move is: `q-source` names the depth `m` and component
  -- `s` whose step term demands the parameter; split on whether THAT step
  -- term's replay has passed ITS threshold; below it `par-small` gives
  -- CHEAP, above it call the bump TERMINAL.  The cheap half is right.
  -- The terminal half is FALSE, and here is the instance.
  --
  -- Take r = 2 with two parameters, at the step terms' coordinates 2 and
  -- 3 (the component's own coordinates 1 and 2), and let j = 0.  At stage
  -- `n`, with depth D = A n 0:
  --
  --     cIdx (Ypar n) 0 (D-1) = 1     -- component 0 wants component 1,
  --                                   -- and its replay is BELOW N 0
  --     cIdx (Ypar n) 1 (D-2) = 2     -- component 1 wants parameter 2,
  --                                   -- and its replay is PAST N 1
  --
  -- so `q (Ypar n) 0 D` descends once and exits with `Ivb n = 1`; the
  -- source is (D-2, 1) and its replay HAS passed `N 1`.  The walk then
  -- bumps the component's coordinate 1, i.e. the step terms' parameter 2.
  -- That raises what is available to component 0 as well, so
  -- `nn (Ypar (n+1)) 0 (D-1)` may advance one step -- and if
  -- `iv 0` changes there from 1 to 3 (legal: it need only be constant
  -- past `N 0`), then
  --
  --     cIdx (Ypar (n+1)) 0 (D-1) = 3   ==>   Ivb (n+1) = 2 /= 1 .
  --
  -- The demand did not persist.  Passing a threshold for the component
  -- that EXITS says nothing about the components ABOVE it in the chain,
  -- and those may exit later, to a DIFFERENT parameter.
  --
  -- THIS IS THE ONE PLACE WHERE r = 2 DIFFERS FROM MP1.  There is a
  -- single step term there, so `cg-past` gives the SAME demand at every
  -- depth above the threshold and the fold's highest non-descending depth
  -- IS the top one; with two step terms pointing at each other that fails.
  -- A correct terminal clause has to constrain BOTH components at once --
  -- `MainBlk2.comp-verdict` ("frozen from D on, or replay past its own
  -- threshold at D") is the natural candidate, since past both thresholds
  -- the chain follows the FIXED map `I` and the answer is a function of
  -- `I` and `j` alone.  What that costs is the cheap half: a component
  -- below its threshold demands a RECURSIVE VALUE, not a parameter, so
  -- `par-small` gives no fuel there.  That trade is the remaining work.
  ------------------------------------------------------------------
