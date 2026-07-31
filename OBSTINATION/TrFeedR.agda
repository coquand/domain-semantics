{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrFeedR
--
-- **THE FED VERDICT WITHOUT ASSUMING THE DEMAND SETTLES.**
--
--     fedR : MonoTr p T -> MP1T p T -> (V : Nat -> FTup) -> monotone
--          -> ((c : Nat) -> Sigma kc. FixC V kc c + GroC V kc c)
--          -> VerdictFrom K (\ k -> sem p T (V k))
--
-- `TrCompVerdict.fedV` needs the demand `blockOn p T (V k)` to be
-- eventually the constant `inr J`.  For a COMPOSITE that comes free from
-- `TrSelStab.selStab`; for the RECURSION's parameter direction there is no
-- counterpart -- `TrPrecPar.ivP-EvConstN` settles `f`'s own walk, not the
-- step term's demand on the family.  This file removes the hypothesis,
-- replacing it by something the recursion does supply: a REGIME per
-- coordinate,
--
--     FixC V kc c  -- coordinate `c`'s VALUE never moves again, past `kc`;
--     GroC V kc c  -- it is never complete and its height grows by at
--                     least one at EVERY step, past `kc`.
--
-- For `f(S x,y) = g(x, f(x,y), y)` with `f`'s walk raising the parameter,
-- the family fed to `g` is
--
--     ( S^c(bot) , f(S^c(bot), S^(l+t)(bot)) , S^(l+t)(bot) )
--
-- and every coordinate is of one of those two kinds: the recursion
-- argument and the frozen parameters are `FixC`, the growing parameter is
-- `GroC`, and the middle coordinate -- the previous unrolling layer -- is
-- whichever its own `Verdict` says (`TrCompSel.verdict-split`).
--
-- THE ARGUMENT.  At every stage the replay is stuck on `cg t`, and
-- `ReplayLv.stuck` says the level it needs IS the height that coordinate
-- offers.  So the coordinate's regime decides, with no third possibility:
--
--     FixC  ==>  it never grows again, so the replay is stuck for ever;
--     GroC  ==>  it grows, which is exactly what the replay wanted.
--
-- Hence `NG` strictly increases until it freezes, and a BOUNDED search of
-- length `Ng` (the threshold of `EvConstN ivg`) decides which: past `Ng`
-- the demanded coordinate is the eventual index for ever.  Then the demand
-- IS eventually constant and `fedV` finishes -- except when the settled
-- coordinate is a NUMERAL, where the computation descends and this file
-- recurses on a trace of strictly smaller arity.
--
-- No Proposition 1.  No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrFeedR where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.ReplayLv using (lv ; Adv ; nOf ; nOf-le ; stuck)
open import OBSTINATION.MP1 using (ConstFrom ; StrictIncFrom ; PhiOK)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using
  (IsCpl ; cpl-max ; LeX ; LeX-del ; nth-del ; MonoTr)
open import OBSTINATION.TrMP1 using (Never ; Verdict ; MP1T)
open import OBSTINATION.TrCompSel using (OvSettles ; OvGrows)
open import OBSTINATION.TrCompVal using (module SEMf)
open import OBSTINATION.TrCompVerdict using
  (VerdictFrom ; fedV ; IsCpl-dec ; notCpl-of)
open import OBSTINATION.TrPrecChain using (Bt ; notCpl-bt)
open import OBSTINATION.TrPrecDecMP using (pl ; pl-ge)
open import OBSTINATION.TrFeed using (maxTo ; maxTo-ge)

------------------------------------------------------------------------
-- MOVING A TAIL VERDICT
------------------------------------------------------------------------

upVF : (u : Nat -> FEl) (K1 K2 : Nat) -> LeN K1 K2
     -> VerdictFrom K2 u -> VerdictFrom K1 u
upVF u K1 K2 le (mkSigma K' (mkSigma l r)) =
  mkSigma K' (mkSigma (LeN-trans {K1} {K2} {K'} le l) r)

vfCong : (u u' : Nat -> FEl) (K1 : Nat)
       -> ((k : Nat) -> LeN K1 k -> Eq (u k) (u' k))
       -> VerdictFrom K1 u' -> VerdictFrom K1 u
vfCong u u' K1 e (mkSigma K' (mkSigma l r)) = mkSigma K' (mkSigma l (tr r))
  where
    eK : (k : Nat) -> LeN K' k -> Eq (u k) (u' k)
    eK k lk = e k (LeN-trans {K1} {K'} {k} l lk)

    tr : Or (IsCpl (u' K'))
            (Pair ((k : Nat) -> LeN K' k -> Bt (u' k)) (PhiOK (\ k -> hgt (u' k))))
       -> Or (IsCpl (u K'))
             (Pair ((k : Nat) -> LeN K' k -> Bt (u k)) (PhiOK (\ k -> hgt (u k))))
    tr (inl ic) = inl (Eq-transport (\ z -> IsCpl z) (Eq-sym (eK K' (LeN-refl K'))) ic)
    tr (inr (mkSigma nv (mkSigma kk pk))) =
      inr (mkSigma
            (\ k lk -> Eq-transport (\ z -> Bt z) (Eq-sym (eK k lk)) (nv k lk))
            (mkSigma (maxN kk K') (phi pk)))
      where
        lK'M : LeN K' (maxN kk K')
        lK'M = maxN-le-r kk K'

        lkkM : LeN kk (maxN kk K')
        lkkM = maxN-le-l kk K'

        phi : Or (ConstFrom kk (\ k -> hgt (u' k))) (StrictIncFrom kk (\ k -> hgt (u' k)))
            -> Or (ConstFrom (maxN kk K') (\ k -> hgt (u k)))
                  (StrictIncFrom (maxN kk K') (\ k -> hgt (u k)))
        phi (inl cf) = inl go
          where
            atk : (k : Nat) -> LeN (maxN kk K') k -> Eq (hgt (u k)) (hgt (u' kk))
            atk k lk =
              Eq-trans
                (Eq-cong hgt (eK k (LeN-trans {K'} {maxN kk K'} {k} lK'M lk)))
                (cf k (LeN-trans {kk} {maxN kk K'} {k} lkkM lk))

            go : ConstFrom (maxN kk K') (\ k -> hgt (u k))
            go k lk =
              Eq-trans (atk k lk) (Eq-sym (atk (maxN kk K') (LeN-refl (maxN kk K'))))
        phi (inr si) = inr go
          where
            go : StrictIncFrom (maxN kk K') (\ k -> hgt (u k))
            go k lk =
              Eq-transport (\ z -> LeN (suc (hgt z)) (hgt (u (suc k))))
                (Eq-sym (eK k lkk))
                (Eq-transport (\ z -> LeN (suc (hgt (u' k))) (hgt z))
                  (Eq-sym (eK (suc k) (LeN-trans {K'} {k} {suc k} lkk (LeN-suc k))))
                  (si k (LeN-trans {kk} {maxN kk K'} {k} lkkM lk)))
              where
                lkk : LeN K' k
                lkk = LeN-trans {K'} {maxN kk K'} {k} lK'M lk

------------------------------------------------------------------------
-- THE TWO REGIMES OF A COORDINATE
------------------------------------------------------------------------

FixC : (Nat -> FTup) -> Nat -> Nat -> Set
FixC V kc c =
  (k k' : Nat) -> LeN kc k -> LeN k k'
  -> Eq (nth (fbot zero) c (V k')) (nth (fbot zero) c (V k))

GroC : (Nat -> FTup) -> Nat -> Nat -> Set
GroC V kc c =
  Pair ((k : Nat) -> Not (IsCpl (nth (fbot zero) c (V k))))
       ((k : Nat) -> LeN kc k -> LeN (suc (hts (V k) c)) (hts (V (suc k)) c))

Reg : (Nat -> FTup) -> Set
Reg V = (c : Nat) -> Sigma Nat (\ kc -> Or (FixC V kc c) (GroC V kc c))

------------------------------------------------------------------------
-- THE THEOREM
------------------------------------------------------------------------

fedR : (p : Nat) (T : Tr p) -> MonoTr p T -> MP1T p T
     -> (V : Nat -> FTup)
     -> ((k k' : Nat) -> LeN k k' -> LeX (V k) (V k'))
     -> (K : Nat) -> Reg V
     -> VerdictFrom K (\ k -> sem p T (V k))
------------------------------------------------------------------------
-- a `stop`: the value is the constant `v`
------------------------------------------------------------------------
fedR p (stop v) mt m1 V Vmono K reg =
  mkSigma K (mkSigma (LeN-refl K) (route (IsCpl-dec v)))
  where
    route : Dec (IsCpl v)
          -> Or (IsCpl v)
                (Pair ((k : Nat) -> LeN K k -> Bt v) (PhiOK (\ k -> hgt v)))
    route (yes ic) = inl ic
    route (no  nc) =
      inr (mkSigma (\ k lk -> notCpl-bt v nc) (mkSigma zero (inl (\ m lm -> refl))))
------------------------------------------------------------------------
-- a node
------------------------------------------------------------------------
fedR (suc q) (node ivg ivgr ovg contg) mt m1 V Vmono K reg = finish (climb Ng)
  where
    open SEMf q ivg ivgr ovg contg V Vmono mt

    Ng : Nat
    Ng = fst (fst m1)

    ivg-const : (n : Nat) -> LeN Ng n -> Eq (ivg n) (ivg Ng)
    ivg-const = snd (fst m1)

    vg : Verdict ovg
    vg = fst (snd m1)

    ------------------------------------------------------------------
    -- past every coordinate's own threshold
    ------------------------------------------------------------------

    K0 : Nat
    K0 = maxN K (maxTo (suc q) (\ c -> fst (reg c)))

    lKK0 : LeN K K0
    lKK0 = maxN-le-l K (maxTo (suc q) (\ c -> fst (reg c)))

    lregT : (t : Nat) -> LeN K0 t -> LeN (fst (reg (cg t))) t
    lregT t lt =
      LeN-trans {fst (reg (cg t))} {K0} {t}
        (LeN-trans {fst (reg (cg t))} {maxTo (suc q) (\ d -> fst (reg d))} {K0}
          (maxTo-ge (suc q) (\ d -> fst (reg d)) (cg t) (ivgr (NG t)))
          (maxN-le-r K (maxTo (suc q) (\ c -> fst (reg c)))))
        lt

    ------------------------------------------------------------------
    -- A FIXED COORDINATE FREEZES THE REPLAY, A GROWING ONE ADVANCES IT
    ------------------------------------------------------------------

    Frozen : Nat -> Set
    Frozen t = (k : Nat) -> LeN t k -> Eq (NG k) (NG t)

    freeze : (t : Nat) -> ((k : Nat) -> LeN t k
              -> Eq (hts (V k) (cg t)) (hts (V t) (cg t)))
           -> Frozen t
    freeze t same k lk =
      LeN-antisym {NG k} {NG t}
        (nOf-le (suc q) ivg ivgr (hts (V k)) (NG t) still) (NG-mono t k lk)
      where
        still : Not (Adv (suc q) ivg ivgr (hts (V k)) (NG t))
        still ad =
          stuck (suc q) ivg ivgr (hts (V t))
            (Eq-transport
              (\ z -> LeN (suc (lv (suc q) ivg ivgr (cg t) (NG t))) z) (same k lk) ad)

    fix-frozen : (t : Nat) -> LeN K0 t -> FixC V (fst (reg (cg t))) (cg t) -> Frozen t
    fix-frozen t lt fx = freeze t (\ k lk -> Eq-cong hgt (fx t k (lregT t lt) lk))

    gro-grow : (t : Nat) -> LeN K0 t -> GroC V (fst (reg (cg t))) (cg t)
             -> LeN (suc (NG t)) (NG (suc t))
    gro-grow t lt gr = NG-grow t (suc t) (LeN-suc t) (snd gr t (lregT t lt))

    ------------------------------------------------------------------
    -- THE BOUNDED SEARCH: the replay climbs until it freezes
    ------------------------------------------------------------------

    climb : (s : Nat)
          -> Or (Sigma Nat (\ t -> Pair (LeN K0 t) (Frozen t)))
                (LeN s (NG (pl K0 s)))
    climb zero    = inr tt
    climb (suc s) = step (climb s)
      where
        t : Nat
        t = pl K0 s

        lt : LeN K0 t
        lt = pl-ge K0 s

        step : Or (Sigma Nat (\ t' -> Pair (LeN K0 t') (Frozen t')))
                  (LeN s (NG t))
             -> Or (Sigma Nat (\ t' -> Pair (LeN K0 t') (Frozen t')))
                   (LeN (suc s) (NG (suc t)))
        step (inl w)  = inl w
        step (inr le) = pick (snd (reg (cg t)))
          where
            pick : Or (FixC V (fst (reg (cg t))) (cg t))
                      (GroC V (fst (reg (cg t))) (cg t))
                 -> Or (Sigma Nat (\ t' -> Pair (LeN K0 t') (Frozen t')))
                       (LeN (suc s) (NG (suc t)))
            pick (inl fx) = inl (mkSigma t (mkSigma lt (fix-frozen t lt fx)))
            pick (inr gr) =
              inr (LeN-trans {suc s} {suc (NG t)} {NG (suc t)} le (gro-grow t lt gr))

    ------------------------------------------------------------------
    -- ONCE THE DEMANDED COORDINATE IS `J` FOR EVER
    ------------------------------------------------------------------

    byJ : (KJ J : Nat) -> LeN K0 KJ -> ((k : Nat) -> LeN KJ k -> Eq (cg k) J)
        -> VerdictFrom K SV
    byJ KJ J lKJ ecg = upVF SV K KJ lKKJ (pick (snd (reg J)))
      where
        lKKJ : LeN K KJ
        lKKJ = LeN-trans {K} {K0} {KJ} lKK0 lKJ

        lK0k : (k : Nat) -> LeN KJ k -> LeN K0 k
        lK0k k lk = LeN-trans {K0} {KJ} {k} lKJ lk

        atJ : (k : Nat) -> LeN KJ k -> Eq (at k) (nth (fbot zero) J (V k))
        atJ k lk = Eq-cong (\ z -> nth (fbot zero) z (V k)) (ecg k lk)

        lregJ : LeN (fst (reg J)) KJ
        lregJ =
          Eq-transport (\ z -> LeN (fst (reg z)) KJ) (ecg KJ (LeN-refl KJ))
            (lregT KJ lKJ)

        pick : Or (FixC V (fst (reg J)) J) (GroC V (fst (reg J)) J)
             -> VerdictFrom KJ SV
        ----------------------------------------------------------------
        -- `J` GROWS: never complete, so no descent
        ----------------------------------------------------------------
        pick (inr gr) = ovroute vg
          where
            naJ : (k : Nat) -> LeN KJ k -> Not (IsCpl (at k))
            naJ k lk ic = fst gr k (Eq-transport (\ z -> IsCpl z) (atJ k lk) ic)

            groAt : (k : Nat) -> LeN KJ k -> LeN (suc (NG k)) (NG (suc k))
            groAt k lk =
              gro-grow k (lK0k k lk)
                (Eq-transport (\ z -> GroC V (fst (reg z)) z) (Eq-sym (ecg k lk)) gr)

            climbJ : (t : Nat) -> LeN t (NG (pl KJ t))
            climbJ zero    = tt
            climbJ (suc t) =
              LeN-trans {suc t} {suc (NG (pl KJ t))} {NG (suc (pl KJ t))}
                (climbJ t) (groAt (pl KJ t) (pl-ge KJ t))

            ovroute : Verdict ovg -> VerdictFrom KJ SV
            -- the outer value goes total: the replay climbs to its depth
            ovroute (inl (mkSigma n0 icn)) =
              mkSigma (pl KJ n0) (mkSigma (pl-ge KJ n0) (inl icSV))
              where
                icOv : IsCpl (ovg (NG (pl KJ n0)))
                icOv =
                  Eq-transport (\ z -> IsCpl z)
                    (cpl-max (ovg n0) (ovg (NG (pl KJ n0)))
                      (fst mt n0 (NG (pl KJ n0)) (climbJ n0)) icn) icn

                icSV : IsCpl (SV (pl KJ n0))
                icSV =
                  Eq-transport (\ z -> IsCpl z)
                    (Eq-sym (sem-inl (pl KJ n0) icOv)) icOv
            -- it never does: the demand is `inr J` for ever, `fedV` finishes
            ovroute (inr (mkSigma nvg pkg)) =
              fedV (suc q) Tg mt m1 V Vmono KJ J stab regJ
              where
                ncov : (k : Nat) -> Not (IsCpl (ovg (NG k)))
                ncov k ic = notCpl-of (ovg (NG k)) (nvg (NG k)) ic

                stab : (k : Nat) -> LeN KJ k -> Eq (blockOn (suc q) Tg (V k)) (inr J)
                stab k lk =
                  Eq-trans (blk-fbot k (ncov k) (naJ k lk)) (Eq-cong inr (ecg k lk))

                regJ : Or (OvSettles (\ k -> nth (fbot zero) J (V k)))
                          (OvGrows (\ k -> nth (fbot zero) J (V k)))
                regJ =
                  inr (mkSigma
                        (\ k -> notCpl-bt (nth (fbot zero) J (V k)) (fst gr k))
                        (mkSigma (fst (reg J)) (snd gr)))
        ----------------------------------------------------------------
        -- `J` IS FIXED: the replay is frozen
        ----------------------------------------------------------------
        pick (inl fx) = route1 (IsCpl-dec (ovg (NG KJ)))
          where
            fxJ : (k k' : Nat) -> LeN KJ k -> LeN k k'
                -> Eq (nth (fbot zero) J (V k')) (nth (fbot zero) J (V k))
            fxJ k k' l1 l2 = fx k k' (LeN-trans {fst (reg J)} {KJ} {k} lregJ l1) l2

            atSame : (k : Nat) -> LeN KJ k -> Eq (at k) (at KJ)
            atSame k lk =
              Eq-trans (atJ k lk)
                (Eq-trans (fxJ KJ k (LeN-refl KJ) lk) (Eq-sym (atJ KJ (LeN-refl KJ))))

            frz : Frozen KJ
            frz =
              fix-frozen KJ lKJ
                (Eq-transport (\ z -> FixC V (fst (reg z)) z)
                  (Eq-sym (ecg KJ (LeN-refl KJ))) fx)

            route1 : Dec (IsCpl (ovg (NG KJ))) -> VerdictFrom KJ SV
            route1 (yes ic) = mkSigma KJ (mkSigma (LeN-refl KJ) (inl icSV))
              where
                icSV : IsCpl (SV KJ)
                icSV = Eq-transport (\ z -> IsCpl z) (Eq-sym (sem-inl KJ ic)) ic
            route1 (no nc) = route2 (IsCpl-dec (at KJ))
              where
                ncov : (k : Nat) -> LeN KJ k -> Not (IsCpl (ovg (NG k)))
                ncov k lk =
                  Eq-transport (\ z -> Not (IsCpl (ovg z))) (Eq-sym (frz k lk)) nc

                route2 : Dec (IsCpl (at KJ)) -> VerdictFrom KJ SV
                --------------------------------------------------------
                -- not a numeral: the demand is `inr J` for ever
                --------------------------------------------------------
                route2 (no na) = fedV (suc q) Tg mt m1 V Vmono KJ J stab regJ
                  where
                    naK : (k : Nat) -> LeN KJ k -> Not (IsCpl (at k))
                    naK k lk ic =
                      na (Eq-transport (\ z -> IsCpl z) (atSame k lk) ic)

                    stab : (k : Nat) -> LeN KJ k
                         -> Eq (blockOn (suc q) Tg (V k)) (inr J)
                    stab k lk =
                      Eq-trans (blk-fbot k (ncov k lk) (naK k lk))
                        (Eq-cong inr (ecg k lk))

                    regJ : Or (OvSettles (\ k -> nth (fbot zero) J (V k)))
                              (OvGrows (\ k -> nth (fbot zero) J (V k)))
                    regJ = inl (mkSigma KJ (\ m lm -> fxJ KJ m (LeN-refl KJ) lm))
                --------------------------------------------------------
                -- a numeral: descend, and recurse at a smaller arity
                --------------------------------------------------------
                route2 (yes ia) = vfCong SV IU KJ semD inner
                  where
                    C : Nat
                    C = cg KJ

                    CT0 : Tr q
                    CT0 = CT KJ

                    V' : Nat -> FTup
                    V' k = del C (V k)

                    IU : Nat -> FEl
                    IU k = sem q CT0 (V' k)

                    icK : (k : Nat) -> LeN KJ k -> IsCpl (at k)
                    icK k lk =
                      Eq-transport (\ z -> IsCpl z) (Eq-sym (atSame k lk)) ia

                    semD : (k : Nat) -> LeN KJ k -> Eq (SV k) (IU k)
                    semD k lk =
                      Eq-trans (sem-descend k (ncov k lk) (icK k lk))
                        (Eq-trans
                          (Eq-cong (\ T' -> sem q T' (del (cg k) (V k)))
                            (CT-freeze KJ ia k lk))
                          (Eq-cong (\ z -> sem q CT0 (del z (V k)))
                            (cg-freeze KJ ia k lk)))

                    Vmono' : (k k' : Nat) -> LeN k k' -> LeX (V' k) (V' k')
                    Vmono' k k' le = LeX-del C (V k) (V k') (Vmono k k' le)

                    reg' : Reg V'
                    reg' c' = mkSigma (fst (reg (su C c'))) (rt (snd (reg (su C c'))))
                      where
                        ed : (k : Nat)
                           -> Eq (nth (fbot zero) c' (V' k))
                                 (nth (fbot zero) (su C c') (V k))
                        ed k = nth-del C c' (V k)

                        rt : Or (FixC V (fst (reg (su C c'))) (su C c'))
                                (GroC V (fst (reg (su C c'))) (su C c'))
                           -> Or (FixC V' (fst (reg (su C c'))) c')
                                 (GroC V' (fst (reg (su C c'))) c')
                        rt (inl fx') =
                          inl (\ k k' l1 l2 ->
                                 Eq-trans (ed k')
                                   (Eq-trans (fx' k k' l1 l2) (Eq-sym (ed k))))
                        rt (inr (mkSigma nc' gr')) =
                          inr (mkSigma
                                (\ k ic ->
                                   nc' k (Eq-transport (\ z -> IsCpl z) (ed k) ic))
                                (\ k l ->
                                   Eq-transport
                                     (\ z -> LeN (suc (hgt z)) (hgt (nth (fbot zero) c' (V' (suc k)))))
                                     (Eq-sym (ed k))
                                     (Eq-transport
                                       (\ z -> LeN (suc (hts (V k) (su C c'))) (hgt z))
                                       (Eq-sym (ed (suc k))) (gr' k l))))

                    inner : VerdictFrom KJ IU
                    inner =
                      fedR q CT0
                        (snd mt C (ivgr (NG KJ)) (hts (V KJ) C))
                        (snd (snd m1) C (ivgr (NG KJ)) (hts (V KJ) C))
                        V' Vmono' KJ reg'

    ------------------------------------------------------------------
    -- THE SEARCH DECIDES WHICH COORDINATE IS DEMANDED FOR EVER
    ------------------------------------------------------------------

    finish : Or (Sigma Nat (\ t -> Pair (LeN K0 t) (Frozen t)))
                (LeN Ng (NG (pl K0 Ng)))
           -> VerdictFrom K SV
    finish (inl (mkSigma t (mkSigma lt frz))) =
      byJ t (cg t) lt (\ k lk -> Eq-cong ivg (frz k lk))
    finish (inr le) =
      byJ Kf (ivg Ng) (pl-ge K0 Ng)
        (\ k lk ->
           ivg-const (NG k) (LeN-trans {Ng} {NG Kf} {NG k} le (NG-mono Kf k lk)))
      where
        Kf : Nat
        Kf = pl K0 Ng
