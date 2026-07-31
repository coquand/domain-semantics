{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrSelStab
--
-- THE BOUNDED CLIMB: THE COMPOSITE'S SELECTION IS EVENTUALLY CONSTANT.
--
-- Every question the climb asks is decidable at ONE stage -- is the outer
-- trace's value total?  is the selected argument's value a numeral?  is
-- the demand still `inr j`? -- so every search is bounded (`TrScan`).
-- What makes the whole thing terminate is that the outer trace can move
-- only finitely often (`TrCompNG`), and what makes each search finite is
-- the drive (`TrCompIv`): while `j` is selected, argument `j`'s replay
-- advances at least one step per stage.
--
-- ONE ROUND, at a stage `k` where the outer trace waits on
-- `j = sh (cg k)`:
--
--   * `Ths j` SETTLES -- drive `n1` steps, then `settles-frozen` freezes
--     the selection for ever;
--   * `Ths j` GROWS -- drive `M + n1` steps; `sinc-grow` makes the height
--     at `j` exceed `M`, and `NG-ge-hts` drags the outer replay depth up
--     with it, so `NG` reaches ANY target in one shot;
--   * and if the scan fails at some stage, that stage is `inl tt`
--     (stable), or a descent, or the demand MOVED -- and then `cg`
--     changed, so `NG` strictly grew.
--
-- `reach` iterates rounds with fuel `M`: each failure costs one unit of
-- `NG`, and `NG` cannot pass `M` without ending the loop.  `phase2`, past
-- the threshold `Ng` of `EvConstN ivg`, knows `cg` is CONSTANT and so
-- rules the third outcome out; there only two things can still happen,
-- and both are decided by `Verdict`: the outer value goes total (drive
-- `NG` up to its witness -- `inl tt`, stable) or it never does, and then
-- the selected coordinate either never goes total (stable) or does, and
-- that is a descent.
--
-- `go` recurses structurally on the outer trace at a descent, which is
-- sound because a descent freezes `NG`, `cg` and the continuation for
-- ever (`TrCompNG.NG-freeze`).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrSelStab where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.BlkReplay using (plus ; plus-ge-r ; plus-suc-r ; plus-mono ; le-ne-lt)
open import OBSTINATION.MP1 using (plus-ge-l ; StrictIncFrom ; sinc-grow)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat
open import OBSTINATION.TrComp
open import OBSTINATION.TrPrec using (su-range)
open import OBSTINATION.TrPrecFrz using (tup-le)
open import OBSTINATION.TrMono using (ovOf-mono)
open import OBSTINATION.TrMP1 using
  (EvTot ; Never ; Verdict ; MP1T ; IvAll ; mp1T-ivAll)
open import OBSTINATION.TrMPT using
  (MPT ; OvUnbT ; UnbN ; mpT-cont ; mpT-split ; mpT-ivAll ; mpT-TN ;
   mpT-tot-or-never)
open import OBSTINATION.TrCompIv using (module CI ; SelStab ; compTr-ivAll)
open import OBSTINATION.TrCompSel using
  (module CS ; OvSettles ; OvGrows ; stop-settles ; ovTot-or-never)
open import OBSTINATION.TrCompNG using (module NGf)
open import OBSTINATION.TrScan

IsCpl-dec : (x : FEl) -> Dec (IsCpl x)
IsCpl-dec (fbot j) = no (\ z -> z)
IsCpl-dec (fcpl j) = yes tt

------------------------------------------------------------------------
-- THE COMPOSITE
------------------------------------------------------------------------

module SS (p : Nat) (Tg : Tr p) (mtg : MonoTr p Tg) (m1g : MPT p Tg)
          (a : Nat) (Ths : Nat -> Tr (suc a))
          (mTh : (i : Nat) -> MonoTr (suc a) (Ths i))
          (mp1h : (i : Nat) -> MPT (suc a) (Ths i))
          where

  module WW = W p Tg a Ths
  open CI p Tg a Ths using (dep-mono ; dep-drive-any)
  open CS p Tg mtg a Ths mTh using
    (valAt ; valAt-eq ; vals-mono ; sel-inl-stable ; sel-frozen ; settles-frozen)

  Stable : Set
  Stable = Sigma Nat (\ K -> (k : Nat) -> LeN K k -> Eq (WW.sel k) (WW.sel K))

  --------------------------------------------------------------------
  -- THE FAMILY, SEEN THROUGH A CHAIN OF FREEZES
  --------------------------------------------------------------------

  Vs : (Nat -> Nat) -> Nat -> Nat -> FTup
  Vs sh q k = tup q (\ c -> ovOf (Ths (sh c)) (WW.dep k (sh c)))

  Vs-nth : (sh : Nat -> Nat) (q k c : Nat) -> LeN (suc c) q
         -> Eq (nth (fbot zero) c (Vs sh q k))
               (ovOf (Ths (sh c)) (WW.dep k (sh c)))
  Vs-nth sh q k c lc =
    tup-nth q (\ d -> ovOf (Ths (sh d)) (WW.dep k (sh d))) c lc

  Vs-mono : (sh : Nat -> Nat) (q : Nat) (k k' : Nat) -> LeN k k'
          -> LeX (Vs sh q k) (Vs sh q k')
  Vs-mono sh q k k' le =
    tup-le q (\ c -> ovOf (Ths (sh c)) (WW.dep k (sh c)))
             (\ c -> ovOf (Ths (sh c)) (WW.dep k' (sh c)))
      (\ c lc ->
         ovOf-mono (suc a) (Ths (sh c)) (mTh (sh c))
           (WW.dep k (sh c)) (WW.dep k' (sh c)) (dep-mono k k' le (sh c)))

  Vs-del : (sh : Nat -> Nat) (q c : Nat) -> LeN (suc c) (suc q) -> (k : Nat)
         -> Eq (del c (Vs sh (suc q) k)) (Vs (\ d -> sh (su c d)) q k)
  Vs-del sh q c lc k =
    del-tup q c lc (\ d -> ovOf (Ths (sh d)) (WW.dep k (sh d)))

  --------------------------------------------------------------------
  -- ONE NODE OF THE OUTER TRACE
  --------------------------------------------------------------------

  module Node (q : Nat) (ivg : Nat -> Nat)
              (ivgr : (n : Nat) -> LeN (suc (ivg n)) (suc q))
              (ovg : Nat -> FEl)
              (contg : (c : Nat) -> LeN (suc c) (suc q) -> (v : Nat) -> Tr q)
              (mt : MonoTr (suc q) (node ivg ivgr ovg contg))
              (m1 : MPT (suc q) (node ivg ivgr ovg contg))
              (sh : Nat -> Nat)
              (shR : (c : Nat) -> LeN (suc c) (suc q) -> LeN (suc (sh c)) p)
              (K0 : Nat)
              (link : (k : Nat) -> LeN K0 k
                    -> Eq (WW.sel k)
                          (orMap sh
                            (blockOn (suc q) (node ivg ivgr ovg contg)
                              (Vs sh (suc q) k))))
              where

    module N = NGf q ivg ivgr ovg contg (Vs sh (suc q)) (Vs-mono sh (suc q)) mt

    Ng : Nat
    Ng = fst (fst m1)

    stabg : (n : Nat) -> LeN Ng n -> Eq (ivg n) (ivg Ng)
    stabg = snd (fst m1)

    ------------------------------------------------------------------
    -- the demand, in ORIGINAL coordinates
    ------------------------------------------------------------------

    jAt : Nat -> Nat
    jAt k = sh (N.cg k)

    ljAt : (k : Nat) -> LeN (suc (jAt k)) p
    ljAt k = shR (N.cg k) (ivgr (N.NG k))

    selEq-inl : (k : Nat) -> LeN K0 k -> IsCpl (ovg (N.NG k))
              -> Eq (WW.sel k) (inl tt)
    selEq-inl k lk ic =
      Eq-trans (link k lk) (Eq-cong (orMap sh) (N.blk-inl k ic))

    selEq-inr : (k : Nat) -> LeN K0 k -> Not (IsCpl (ovg (N.NG k)))
              -> Not (IsCpl (N.at k)) -> Eq (WW.sel k) (inr (jAt k))
    selEq-inr k lk nc na =
      Eq-trans (link k lk) (Eq-cong (orMap sh) (N.blk-fbot k nc na))

    atEq : (k : Nat) -> Eq (N.at k) (ovOf (Ths (jAt k)) (WW.dep k (jAt k)))
    atEq k = Vs-nth sh (suc q) k (N.cg k) (ivgr (N.NG k))

    ------------------------------------------------------------------
    -- the three shapes of a stage, all decidable
    ------------------------------------------------------------------

    Case : Nat -> Set
    Case k =
      Or (IsCpl (ovg (N.NG k)))
         (Pair (Not (IsCpl (ovg (N.NG k))))
               (Or (IsCpl (N.at k)) (Not (IsCpl (N.at k)))))

    caseOf : (k : Nat) -> Case k
    caseOf k = r1 (IsCpl-dec (ovg (N.NG k)))
      where
        r1 : Dec (IsCpl (ovg (N.NG k))) -> Case k
        r1 (yes ic) = inl ic
        r1 (no  nc) = inr (mkSigma nc (r2 (IsCpl-dec (N.at k))))
          where
            r2 : Dec (IsCpl (N.at k))
               -> Or (IsCpl (N.at k)) (Not (IsCpl (N.at k)))
            r2 (yes ia) = inl ia
            r2 (no  na) = inr na

    DescW : Set
    DescW =
      Sigma Nat (\ K -> Pair (LeN K0 K)
                   (Pair (Not (IsCpl (ovg (N.NG K)))) (IsCpl (N.at K))))

    stableInl : (k : Nat) -> LeN K0 k -> IsCpl (ovg (N.NG k)) -> Stable
    stableInl k lk ic =
      mkSigma k
        (\ k' lk' ->
           Eq-trans (sel-inl-stable k (selEq-inl k lk ic) k' lk')
             (Eq-sym (selEq-inl k lk ic)))

    ------------------------------------------------------------------
    -- ONE ROUND
    ------------------------------------------------------------------

    Prog : Nat -> Nat -> Set
    Prog M k =
      Sigma Nat (\ k' -> Pair (LeN k k') (Pair (LeN K0 k')
                   (Or (Not (Eq (N.cg k') (N.cg k))) (LeN M (N.NG k')))))

    Round : Nat -> Nat -> Set
    Round M k = Or Stable (Or DescW (Prog M k))

    -- a stage at which the demand is no longer `inr (jAt k)`
    fail : (M k t : Nat) -> LeN K0 k
         -> Not (Eq (WW.sel (plus t k)) (inr (jAt k))) -> Round M k
    fail M k t lk np = route (caseOf (plus t k))
      where
        lkk : LeN k (plus t k)
        lkk = plus-ge-r t k

        lk' : LeN K0 (plus t k)
        lk' = LeN-trans {K0} {k} {plus t k} lk lkk

        route : Case (plus t k) -> Round M k
        route (inl ic) = inl (stableInl (plus t k) lk' ic)
        route (inr (mkSigma nc (inl ia))) =
          inr (inl (mkSigma (plus t k) (mkSigma lk' (mkSigma nc ia))))
        route (inr (mkSigma nc (inr na))) =
          inr (inr (mkSigma (plus t k) (mkSigma lkk (mkSigma lk' (inl ncg)))))
          where
            ncg : Not (Eq (N.cg (plus t k)) (N.cg k))
            ncg e =
              np (Eq-trans (selEq-inr (plus t k) lk' nc na)
                    (Eq-cong (\ z -> inr (sh z)) e))

    round : (M k : Nat) -> LeN K0 k -> Round M k
    round M k lk = route (caseOf k)
      where
        route : Case k -> Round M k
        route (inl ic) = inl (stableInl k lk ic)
        route (inr (mkSigma nc (inl ia))) =
          inr (inl (mkSigma k (mkSigma lk (mkSigma nc ia))))
        route (inr (mkSigma nc (inr na))) = route2 verd
          where
            j : Nat
            j = jAt k

            eK : Eq (WW.sel k) (inr j)
            eK = selEq-inr k lk nc na

            verd : Or (OvSettles (ovOf (Ths j))) (OvUnbT (ovOf (Ths j)))
            verd = mpT-split (suc a) (Ths j) (mp1h j)

            P : Nat -> Set
            P t = Eq (WW.sel (plus t k)) (inr j)

            Pdec : (t : Nat) -> Dec (P t)
            Pdec t = OrEq-dec (WW.sel (plus t k)) j

            frzOf : (s : Nat) -> ((t : Nat) -> LeN (suc t) s -> P t)
                  -> (t : Nat) -> LeN (suc t) s -> Eq (WW.selC (plus t k)) j
            frzOf s h t lt = Eq-cong orC (h t lt)

            -- a constant argument freezes the selection at once
            constFrz : ((m : Nat) -> Eq (ovOf (Ths j) m) (ovOf (Ths j) zero))
                     -> Round M k
            constFrz cz =
              inl (mkSigma k
                    (settles-frozen k j (ljAt k) eK zero (\ m lm -> cz m) tt))

            Sc : Nat -> Set
            Sc s =
              Or ((t : Nat) -> LeN (suc t) s -> P t)
                 (Sigma Nat (\ t -> Pair (LeN (suc t) s) (Not (P t))))

            route2 : Or (OvSettles (ovOf (Ths j))) (OvUnbT (ovOf (Ths j)))
                   -> Round M k
            ----------------------------------------------------------
            -- THE ARGUMENT SETTLES: freeze the selection
            ----------------------------------------------------------
            route2 (inl (mkSigma n1 con)) = sc (scan P Pdec (suc (suc n1)))
              where
                K1 : Nat
                K1 = plus (suc n1) k

                sc : Sc (suc (suc n1)) -> Round M k
                sc (inr (mkSigma t (mkSigma lt np))) = fail M k t lk np
                sc (inl h) =
                  dr (dep-drive-any j k (suc n1)
                       (\ t lt ->
                          frzOf (suc (suc n1)) h t
                            (LeN-trans {suc t} {suc n1} {suc (suc n1)} lt
                              (LeN-suc (suc n1)))))
                  where
                    e1 : Eq (WW.sel K1) (inr j)
                    e1 = h (suc n1) (LeN-refl (suc n1))

                    dr : Or ((m : Nat) -> Eq (ovOf (Ths j) m) (ovOf (Ths j) zero))
                            (LeN (plus (suc n1) (WW.dep k j)) (WW.dep K1 j))
                       -> Round M k
                    dr (inl cz) = constFrz cz
                    dr (inr le) =
                      inl (mkSigma K1
                            (settles-frozen K1 j (ljAt k) e1 n1 con deep))
                      where
                        deep : LeN n1 (WW.dep K1 j)
                        deep =
                          LeN-trans {n1} {plus (suc n1) (WW.dep k j)}
                            {WW.dep K1 j}
                            (LeN-trans {n1} {suc n1}
                              {plus (suc n1) (WW.dep k j)}
                              (LeN-suc n1) (plus-ge-l (suc n1) (WW.dep k j)))
                            le
            ----------------------------------------------------------
            -- THE ARGUMENT GROWS: drag `NG` up to the target
            ----------------------------------------------------------
            route2 (inr (mkSigma nev unb)) = sc (scan P Pdec (suc s))
              where
                -- NOT a rate: `UnbN` is called at exactly the level the
                -- round needs, and returns the stage that reaches it
                s : Nat
                s = fst (unb M)

                tallS : LeN (suc M) (hgt (ovOf (Ths j) s))
                tallS = snd (unb M)

                K1 : Nat
                K1 = plus s k

                lkK1 : LeN k K1
                lkK1 = plus-ge-r s k

                lK1 : LeN K0 K1
                lK1 = LeN-trans {K0} {k} {K1} lk lkK1

                sc : Sc (suc s) -> Round M k
                sc (inr (mkSigma t (mkSigma lt np))) = fail M k t lk np
                sc (inl h) =
                  dr (dep-drive-any j k s
                       (\ t lt ->
                          frzOf (suc s) h t
                            (LeN-trans {suc t} {s} {suc s} lt (LeN-suc s))))
                  where
                    e1 : Eq (WW.sel K1) (inr j)
                    e1 = h s (LeN-refl s)

                    dr : Or ((m : Nat) -> Eq (ovOf (Ths j) m) (ovOf (Ths j) zero))
                            (LeN (plus s (WW.dep k j)) (WW.dep K1 j))
                       -> Round M k
                    dr (inl cz) = constFrz cz
                    dr (inr le) = fin (caseOf K1)
                      where
                        deep : LeN s (WW.dep K1 j)
                        deep =
                          LeN-trans {s} {plus s (WW.dep k j)} {WW.dep K1 j}
                            (plus-ge-l s (WW.dep k j)) le

                        tall : LeN M (hgt (ovOf (Ths j) (WW.dep K1 j)))
                        tall =
                          LeN-trans {M} {hgt (ovOf (Ths j) s)}
                            {hgt (ovOf (Ths j) (WW.dep K1 j))}
                            (LeN-trans {M} {suc M} {hgt (ovOf (Ths j) s)}
                              (LeN-suc M) tallS)
                            (leF-hgt (ovOf (Ths j) s)
                              (ovOf (Ths j) (WW.dep K1 j))
                              (ovOf-mono (suc a) (Ths j) (mTh j)
                                s (WW.dep K1 j) deep))

                        fin : Case K1 -> Round M k
                        fin (inl ic) = inl (stableInl K1 lK1 ic)
                        fin (inr (mkSigma nc1 (inl ia1))) =
                          inr (inl (mkSigma K1 (mkSigma lK1 (mkSigma nc1 ia1))))
                        fin (inr (mkSigma nc1 (inr na1))) =
                          inr (inr
                            (mkSigma K1 (mkSigma lkK1 (mkSigma lK1 (inr big)))))
                          where
                            ej : Eq (jAt K1) j
                            ej =
                              inr-inj (jAt K1) j
                                (Eq-trans (Eq-sym (selEq-inr K1 lK1 nc1 na1)) e1)

                            hEq : Eq (hts (Vs sh (suc q) K1) (N.cg K1))
                                     (hgt (ovOf (Ths j) (WW.dep K1 j)))
                            hEq =
                              Eq-cong hgt
                                (Eq-trans (atEq K1)
                                  (Eq-cong (\ z -> ovOf (Ths z) (WW.dep K1 z))
                                    ej))

                            big : LeN M (N.NG K1)
                            big =
                              LeN-trans {M} {hts (Vs sh (suc q) K1) (N.cg K1)}
                                {N.NG K1}
                                (Eq-transport (\ z -> LeN M z) (Eq-sym hEq) tall)
                                (N.NG-ge-hts K1)

    ------------------------------------------------------------------
    -- ITERATING ROUNDS
    ------------------------------------------------------------------

    Res : Nat -> Set
    Res M =
      Or Stable (Or DescW (Sigma Nat (\ k -> Pair (LeN K0 k) (LeN M (N.NG k)))))

    reach : (M F k : Nat) -> LeN K0 k -> LeN M (plus F (N.NG k)) -> Res M
    reach M zero    k lk le = inr (inr (mkSigma k (mkSigma lk le)))
    reach M (suc F) k lk le = route (round M k lk)
      where
        route : Round M k -> Res M
        route (inl st) = inl st
        route (inr (inl d)) = inr (inl d)
        route (inr (inr (mkSigma k' (mkSigma lkk (mkSigma lk' (inr big)))))) =
          inr (inr (mkSigma k' (mkSigma lk' big)))
        route (inr (inr (mkSigma k' (mkSigma lkk (mkSigma lk' (inl ncg)))))) =
          reach M F k' lk' le'
          where
            grew : LeN (suc (N.NG k)) (N.NG k')
            grew =
              le-ne-lt (N.NG k) (N.NG k') (N.NG-mono k k' lkk)
                (\ e -> ncg (Eq-cong ivg e))

            le' : LeN M (plus F (N.NG k'))
            le' =
              LeN-trans {M} {plus F (suc (N.NG k))} {plus F (N.NG k')}
                (Eq-transport (\ z -> LeN M z)
                  (Eq-sym (plus-suc-r F (N.NG k))) le)
                (plus-mono F F (suc (N.NG k)) (N.NG k') (LeN-refl F) grew)

    ------------------------------------------------------------------
    -- PAST THE OUTER TRACE'S OWN THRESHOLD
    ------------------------------------------------------------------

    phase2 : (k1 : Nat) -> LeN K0 k1 -> LeN Ng (N.NG k1) -> Or Stable DescW
    phase2 k1 lk1 lNg =
      route (mpT-TN (suc q) (node ivg ivgr ovg contg) mt m1)
      where
        cgConst : (k : Nat) -> LeN k1 k -> Eq (N.cg k) (N.cg k1)
        cgConst k lk =
          Eq-trans
            (stabg (N.NG k)
              (LeN-trans {Ng} {N.NG k1} {N.NG k} lNg (N.NG-mono k1 k lk)))
            (Eq-sym (stabg (N.NG k1) lNg))

        ----------------------------------------------------------------
        -- the outer value never goes total: only the selected
        -- coordinate can still move the demand, and `Verdict` decides
        -- whether it ever will
        ----------------------------------------------------------------
        never : ((m : Nat) -> Not (IsCpl (ovg m))) -> Or Stable DescW
        never nevg = route2 (caseOf k1)
          where
            route2 : Case k1 -> Or Stable DescW
            route2 (inl ic) = Empty-elim (nevg (N.NG k1) ic)
            route2 (inr (mkSigma nc (inl ia))) =
              inr (mkSigma k1 (mkSigma lk1 (mkSigma nc ia)))
            route2 (inr (mkSigma nc (inr na))) =
              route3 (mpT-tot-or-never (suc a) (Ths j) (mTh j) (mp1h j))
              where
                j : Nat
                j = jAt k1

                eK : Eq (WW.sel k1) (inr j)
                eK = selEq-inr k1 lk1 nc na

                jSame : (k : Nat) -> LeN k1 k -> Eq (jAt k) j
                jSame k lk = Eq-cong sh (cgConst k lk)

                atSame : (k : Nat) -> LeN k1 k
                       -> Eq (N.at k) (ovOf (Ths j) (WW.dep k j))
                atSame k lk =
                  Eq-trans (atEq k)
                    (Eq-cong (\ z -> ovOf (Ths z) (WW.dep k z)) (jSame k lk))

                route3 : Or (Sigma Nat (\ n0 -> IsCpl (ovOf (Ths j) n0)))
                            ((m : Nat) -> Not (IsCpl (ovOf (Ths j) m)))
                       -> Or Stable DescW
                ------------------------------------------------------
                -- it never does: the demand is `inr j` for ever
                ------------------------------------------------------
                route3 (inr nev) = inl (mkSigma k1 con)
                  where
                    con : (k : Nat) -> LeN k1 k -> Eq (WW.sel k) (WW.sel k1)
                    con k lk =
                      Eq-trans
                        (Eq-trans
                          (selEq-inr k (LeN-trans {K0} {k1} {k} lk1 lk)
                            (\ ic -> nevg (N.NG k) ic)
                            (\ ia ->
                               nev (WW.dep k j)
                                 (Eq-transport (\ z -> IsCpl z) (atSame k lk) ia)))
                          (Eq-cong inr (jSame k lk)))
                        (Eq-sym eK)
                ------------------------------------------------------
                -- it does: drive the argument up to the witness, and
                -- that stage is a descent
                ------------------------------------------------------
                route3 (inl (mkSigma n0 ic0)) = sc (scan P Pdec (suc (suc n0)))
                  where
                    K1 : Nat
                    K1 = plus (suc n0) k1

                    lkK1 : LeN k1 K1
                    lkK1 = plus-ge-r (suc n0) k1

                    lK1 : LeN K0 K1
                    lK1 = LeN-trans {K0} {k1} {K1} lk1 lkK1

                    P : Nat -> Set
                    P t = Eq (WW.sel (plus t k1)) (inr j)

                    Pdec : (t : Nat) -> Dec (P t)
                    Pdec t = OrEq-dec (WW.sel (plus t k1)) j

                    -- in phase 2 the demand cannot move to another
                    -- coordinate, so a scan failure IS a descent
                    fl : (t : Nat) -> Not (P t) -> Or Stable DescW
                    fl t np = r (caseOf (plus t k1))
                      where
                        lt1 : LeN k1 (plus t k1)
                        lt1 = plus-ge-r t k1

                        lt0 : LeN K0 (plus t k1)
                        lt0 = LeN-trans {K0} {k1} {plus t k1} lk1 lt1

                        r : Case (plus t k1) -> Or Stable DescW
                        r (inl ic) = Empty-elim (nevg (N.NG (plus t k1)) ic)
                        r (inr (mkSigma nc' (inl ia'))) =
                          inr (mkSigma (plus t k1) (mkSigma lt0 (mkSigma nc' ia')))
                        r (inr (mkSigma nc' (inr na'))) =
                          Empty-elim
                            (np (Eq-trans (selEq-inr (plus t k1) lt0 nc' na')
                                  (Eq-cong inr (jSame (plus t k1) lt1))))

                    Sc : Nat -> Set
                    Sc s =
                      Or ((t : Nat) -> LeN (suc t) s -> P t)
                         (Sigma Nat (\ t -> Pair (LeN (suc t) s) (Not (P t))))

                    sc : Sc (suc (suc n0)) -> Or Stable DescW
                    sc (inr (mkSigma t (mkSigma lt np))) = fl t np
                    sc (inl h) =
                      dr (dep-drive-any j k1 (suc n0)
                           (\ t lt ->
                              Eq-cong orC
                                (h t (LeN-trans {suc t} {suc n0} {suc (suc n0)}
                                       lt (LeN-suc (suc n0))))))
                      where
                        dr : Or ((m : Nat) -> Eq (ovOf (Ths j) m) (ovOf (Ths j) zero))
                                (LeN (plus (suc n0) (WW.dep k1 j)) (WW.dep K1 j))
                           -> Or Stable DescW
                        -- a constant argument: total at `n0` means total
                        -- at `k1` already, which the case analysis denied
                        dr (inl cz) =
                          Empty-elim
                            (na (Eq-transport (\ z -> IsCpl z)
                                  (Eq-sym
                                    (Eq-trans (atSame k1 (LeN-refl k1))
                                      (Eq-trans (cz (WW.dep k1 j))
                                        (Eq-sym (cz n0)))))
                                  ic0))
                        dr (inr le) =
                          inr (mkSigma K1 (mkSigma lK1
                                (mkSigma (\ ic -> nevg (N.NG K1) ic) icK1)))
                          where
                            deep : LeN n0 (WW.dep K1 j)
                            deep =
                              LeN-trans {n0} {plus (suc n0) (WW.dep k1 j)}
                                {WW.dep K1 j}
                                (LeN-trans {n0} {suc n0}
                                  {plus (suc n0) (WW.dep k1 j)}
                                  (LeN-suc n0)
                                  (plus-ge-l (suc n0) (WW.dep k1 j)))
                                le

                            icK1 : IsCpl (N.at K1)
                            icK1 =
                              Eq-transport (\ z -> IsCpl z)
                                (Eq-sym
                                  (Eq-trans (atSame K1 lkK1)
                                    (Eq-sym
                                      (cpl-max (ovOf (Ths j) n0)
                                        (ovOf (Ths j) (WW.dep K1 j))
                                        (ovOf-mono (suc a) (Ths j) (mTh j)
                                          n0 (WW.dep K1 j) deep) ic0))))
                                ic0

        ----------------------------------------------------------------
        -- the outer value does go total: drive `NG` up to the witness
        ----------------------------------------------------------------
        route : Or (EvTot ovg) (Never ovg) -> Or Stable DescW
        route (inl (mkSigma n0g icg)) =
          fin (reach n0g n0g k1 lk1 (plus-ge-l n0g (N.NG k1)))
          where
            fin : Res n0g -> Or Stable DescW
            fin (inl st) = inl st
            fin (inr (inl d)) = inr d
            fin (inr (inr (mkSigma k2 (mkSigma lk2 big)))) =
              inl (stableInl k2 lk2 icAt)
              where
                icAt : IsCpl (ovg (N.NG k2))
                icAt =
                  Eq-transport (\ z -> IsCpl z)
                    (cpl-max (ovg n0g) (ovg (N.NG k2)) (fst mt n0g (N.NG k2) big)
                      icg)
                    icg
        route (inr nevg) =
          never (\ m ic -> Eq-transport (\ z -> IsCpl z) (nevg m) ic)

    ------------------------------------------------------------------
    -- THE NODE'S VERDICT
    ------------------------------------------------------------------

    result : Or Stable DescW
    result = fin (reach Ng Ng K0 (LeN-refl K0) (plus-ge-l Ng (N.NG K0)))
      where
        fin : Res Ng -> Or Stable DescW
        fin (inl st) = inl st
        fin (inr (inl d)) = inr d
        fin (inr (inr (mkSigma k1 (mkSigma lk1 big)))) = phase2 k1 lk1 big

  --------------------------------------------------------------------
  -- DESCENDING THROUGH THE OUTER TRACE
  --------------------------------------------------------------------

  go : (q : Nat) (T : Tr q) -> MonoTr q T -> MPT q T
     -> (sh : Nat -> Nat)
     -> ((c : Nat) -> LeN (suc c) q -> LeN (suc (sh c)) p)
     -> (K0 : Nat)
     -> ((k : Nat) -> LeN K0 k
         -> Eq (WW.sel k) (orMap sh (blockOn q T (Vs sh q k))))
     -> Stable
  go q (stop w) mt m1 sh shR K0 link = mkSigma K0 con
    where
      con : (k : Nat) -> LeN K0 k -> Eq (WW.sel k) (WW.sel K0)
      con k lk = Eq-trans (link k lk) (Eq-sym (link K0 (LeN-refl K0)))
  go (suc q) (node ivg ivgr ovg contg) mt m1 sh shR K0 link = fin ND.result
    where
      module ND = Node q ivg ivgr ovg contg mt m1 sh shR K0 link

      fin : Or Stable ND.DescW -> Stable
      fin (inl st) = st
      fin (inr (mkSigma K (mkSigma lK (mkSigma nc ia)))) =
        go q (contg cK lcK wK) (snd mt cK lcK wK) (snd (snd m1) cK lcK wK)
          sh' shR' K link'
        where
          cK : Nat
          cK = ND.N.cg K

          lcK : LeN (suc cK) (suc q)
          lcK = ivgr (ND.N.NG K)

          wK : Nat
          wK = hts (Vs sh (suc q) K) cK

          sh' : Nat -> Nat
          sh' = \ d -> sh (su cK d)

          shR' : (c : Nat) -> LeN (suc c) q -> LeN (suc (sh' c)) p
          shR' c lc = shR (su cK c) (su-range q cK c lcK lc)

          -- the value at `cK` is total, hence maximal, hence unmoving
          atSame : (k : Nat) -> LeN K k
                 -> Eq (nth (fbot zero) cK (Vs sh (suc q) K))
                       (nth (fbot zero) cK (Vs sh (suc q) k))
          atSame k lk =
            cpl-max (nth (fbot zero) cK (Vs sh (suc q) K))
              (nth (fbot zero) cK (Vs sh (suc q) k))
              (Vs-mono sh (suc q) K k lk cK) ia

          hSame : (k : Nat) -> LeN K k
                -> Eq (hts (Vs sh (suc q) k) cK) wK
          hSame k lk = Eq-sym (Eq-cong hgt (atSame k lk))

          iaAt : (k : Nat) -> LeN K k -> IsCpl (ND.N.at k)
          iaAt k lk =
            Eq-transport (\ z -> IsCpl z)
              (Eq-trans (atSame k lk)
                (Eq-cong (\ z -> nth (fbot zero) z (Vs sh (suc q) k))
                  (Eq-sym (ND.N.cg-freeze K ia k lk))))
              ia

          ncAt : (k : Nat) -> LeN K k -> Not (IsCpl (ovg (ND.N.NG k)))
          ncAt k lk ic =
            nc (Eq-transport (\ z -> IsCpl (ovg z)) (ND.N.NG-freeze K ia k lk) ic)

          -- the continuation, and the coordinate, are FIXED from `K` on
          blkEq : (k : Nat) -> LeN K k
                -> Eq (blockOn (suc q) (node ivg ivgr ovg contg)
                        (Vs sh (suc q) k))
                      (shiftOr cK
                        (blockOn q (contg cK lcK wK) (del cK (Vs sh (suc q) k))))
          blkEq k lk =
            Eq-trans (ND.N.blk-descend k (ncAt k lk) (iaAt k lk))
              (Eq-trans
                (Eq-cong
                  (\ n -> shiftOr (ivg n)
                            (blockOn q
                              (contg (ivg n) (ivgr n)
                                (hts (Vs sh (suc q) k) (ivg n)))
                              (del (ivg n) (Vs sh (suc q) k))))
                  (ND.N.NG-freeze K ia k lk))
                (Eq-cong
                  (\ w -> shiftOr cK
                            (blockOn q (contg cK lcK w)
                              (del cK (Vs sh (suc q) k))))
                  (hSame k lk)))

          link' : (k : Nat) -> LeN K k
                -> Eq (WW.sel k)
                      (orMap sh' (blockOn q (contg cK lcK wK) (Vs sh' q k)))
          link' k lk =
            Eq-trans (link k (LeN-trans {K0} {K} {k} lK lk))
              (Eq-trans (Eq-cong (orMap sh) (blkEq k lk))
                (Eq-trans
                  (orMap-shiftOr sh cK
                    (blockOn q (contg cK lcK wK) (del cK (Vs sh (suc q) k))))
                  (Eq-cong (\ Y -> orMap sh' (blockOn q (contg cK lcK wK) Y))
                    (Vs-del sh q cK lcK k))))

  --------------------------------------------------------------------
  -- THE SELECTION IS EVENTUALLY CONSTANT
  --------------------------------------------------------------------

  selStab : Stable
  selStab = go p Tg mtg m1g (\ x -> x) (\ c lc -> lc) zero linkTop
    where
      linkTop : (k : Nat) -> LeN zero k
              -> Eq (WW.sel k)
                    (orMap (\ x -> x) (blockOn p Tg (Vs (\ x -> x) p k)))
      linkTop k lk = Eq-sym (orMap-id (blockOn p Tg (WW.vals k)))

------------------------------------------------------------------------
-- ... AT EVERY ARITY OF THE TOWER
------------------------------------------------------------------------

selStabAll : (p : Nat) (Tg : Tr p) -> MonoTr p Tg -> MPT p Tg
           -> (a : Nat) (Ths : Nat -> Tr a)
           -> ((i : Nat) -> MonoTr a (Ths i)) -> ((i : Nat) -> MPT a (Ths i))
           -> SelStab p Tg a Ths
selStabAll p Tg mtg m1g zero    Ths mTh m1h = tt
selStabAll p Tg mtg m1g (suc a) Ths mTh m1h =
  mkSigma
    (mkSigma K (mkSigma (orC (W.sel p Tg a Ths K))
      (\ k lk -> Eq-cong orC (con k lk))))
    (\ c lc v ->
       selStabAll p Tg mtg m1g a (\ i -> contOf (Ths i) c lc v)
         (\ i -> monoTr-cont a (Ths i) (mTh i) c lc v)
         (\ i -> mpT-cont a (Ths i) (m1h i) c lc v))
  where
    st : SS.Stable p Tg mtg m1g a Ths mTh m1h
    st = SS.selStab p Tg mtg m1g a Ths mTh m1h

    K : Nat
    K = fst st

    con : (k : Nat) -> LeN K k
        -> Eq (W.sel p Tg a Ths k) (W.sel p Tg a Ths K)
    con = snd st

    monoTr-cont : (a' : Nat) (T : Tr (suc a')) -> MonoTr (suc a') T
                -> (c : Nat) (lc : LeN (suc c) (suc a')) (v : Nat)
                -> MonoTr a' (contOf T c lc v)
    monoTr-cont a' (stop w)              mt c lc v = tt
    monoTr-cont a' (node iv ivr ov cont) mt c lc v = snd mt c lc v

------------------------------------------------------------------------
-- MP1'S INDEX CLAUSE IS PRESERVED BY COMPOSITION
--
-- `TrCompIv.compTr-ivAll` turns the stability of `sel` into `IvAll` of
-- the composite; `selStabAll` supplies that stability.  Together with
-- `TrMP1Red` -- which reads the VALUE clause off Proposition 1 -- this is
-- MP1 for a composition.
------------------------------------------------------------------------

compTr-ivAll-full : (p : Nat) (Tg : Tr p) -> MonoTr p Tg -> MPT p Tg
                  -> (a : Nat) (Ths : Nat -> Tr a)
                  -> ((i : Nat) -> MonoTr a (Ths i))
                  -> ((i : Nat) -> MPT a (Ths i))
                  -> IvAll a (compTr p Tg a Ths)
compTr-ivAll-full p Tg mtg m1g a Ths mTh m1h =
  compTr-ivAll p Tg a Ths
    (\ i -> mpT-ivAll a (Ths i) (m1h i))
    (selStabAll p Tg mtg m1g a Ths mTh m1h)
