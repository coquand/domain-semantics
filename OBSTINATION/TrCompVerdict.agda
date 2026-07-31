{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrCompVerdict
--
-- **MP1's VALUE CLAUSE FOR A TRACE FED A FAMILY WHOSE DEMAND HAS SETTLED
-- -- WITHOUT PROPOSITION 1.**
--
--     fedV : MonoTr p T -> MP1T p T
--          -> (V : Nat -> FTup) -> monotone
--          -> (K J : Nat) -> ((k : Nat) -> LeN K k -> blockOn p T (V k) = inr J)
--          -> OvSettles (nth J o V) + OvGrows (nth J o V)
--          -> VerdictFrom K (\ k -> sem p T (V k))
--
-- This is what the composite needs.  `TrSelStab.selStabAll` already gives
-- -- from the induction hypotheses alone, with no Proposition 1 anywhere
-- in the whole `comp` cone -- that the composite's demand
-- `blockOn p Tg (vals k)` is eventually the constant `inr J`, and
-- `TrCompIv`'s drive plus argument `J`'s own `Verdict` gives the last
-- hypothesis.  So this file is the remaining half of MP1 for `comp`.
--
-- STRUCTURAL RECURSION ON THE OUTER TRACE, with three cases, exactly the
-- ones `blockOn` distinguishes (`TrCompVal`):
--
--   * the demand has SETTLED (`OvSettles`) -- then `TrSat.sem-sat` gives
--     the value outright: it needs agreement only at the coordinate the
--     trace is waiting on, and that coordinate has stopped moving, so the
--     value is CONSTANT.  No case analysis at all.
--
--   * the demand keeps GROWING, and the demanded coordinate is a NUMERAL
--     at some stage -- then `TrCompNG.NG-freeze` freezes the replay for
--     ever, the continuation descended into is FIXED (`CT-freeze`), and
--     the whole problem recurses on a trace of strictly smaller arity,
--     on the tuple with that coordinate deleted.
--
--   * the demand keeps growing and no descent happens -- and THAT is
--     decided by a BOUNDED search of length `Ng`, the threshold of
--     `EvConstN ivg`: without a descent the replay strictly increases
--     (`NG-grow`), so after `Ng` steps it is past `Ng`, the demanded
--     coordinate is the eventual index `J` for ever, and `J`'s value is
--     never complete (`OvGrows` carries `Never`).  Then
--     `sem = ovg o NG` with `NG` strictly increasing, and the outer
--     trace's own `PhiOK` transfers verbatim.
--
-- No Proposition 1.  No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrCompVerdict where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.BlkReplay using (nle-lt ; le-ne-lt)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.MP1 using (ConstFrom ; StrictIncFrom ; PhiOK)
open import OBSTINATION.PhiComp using (sinc-mono-lt)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using
  (IsCpl ; cpl-max ; LeX ; LeX-del ; LeX-hts ; nth-del ; MonoTr ; Agr ; sem-sat)
open import OBSTINATION.TrMP1 using (EvTot ; Never ; Verdict ; MP1T)
open import OBSTINATION.TrCompSel using (OvSettles ; OvGrows)
open import OBSTINATION.TrCompVal using (module SEMf)
open import OBSTINATION.TrPrecChain using (Bt ; notCpl-bt)
open import OBSTINATION.TrPrecDecMP using (pl ; pl-ge ; le-pl)
open import OBSTINATION.TrPrecPhi using (pl-ge-r ; suc-not)

------------------------------------------------------------------------
-- SMALL FACTS
------------------------------------------------------------------------

IsCpl-dec : (x : FEl) -> Dec (IsCpl x)
IsCpl-dec (fbot k) = no  (\ z -> z)
IsCpl-dec (fcpl k) = yes tt

orNE : (x : Nat) -> Not (Eq {Or Top Nat} (inl tt) (inr x))
orNE x ()

inr-inj : (x y : Nat) -> Eq {Or Top Nat} (inr x) (inr y) -> Eq x y
inr-inj x .x refl = refl

shiftOr-inv : (c : Nat) (r : Or Top Nat) (J : Nat) -> Eq (shiftOr c r) (inr J)
            -> Sigma Nat (\ c' -> Pair (Eq r (inr c')) (Eq (su c c') J))
shiftOr-inv c (inl tt) J ()
shiftOr-inv c (inr j)  J e = mkSigma j (mkSigma refl (inr-inj (su c j) J e))

notCpl-of : (x : FEl) -> Bt x -> Not (IsCpl x)
notCpl-of (fbot k) e ic = ic
notCpl-of (fcpl k) e ic = bad k (hgt (fcpl k)) e
  where
    bad : (u v : Nat) -> Not (Eq (fcpl u) (fbot v))
    bad u v ()

------------------------------------------------------------------------
-- THE CONCLUSION
------------------------------------------------------------------------

VerdictFrom : Nat -> (Nat -> FEl) -> Set
VerdictFrom K u =
  Sigma Nat (\ K' -> Pair (LeN K K')
    (Or (IsCpl (u K'))
        (Pair ((k : Nat) -> LeN K' k -> Bt (u k))
              (PhiOK (\ k -> hgt (u k))))))

------------------------------------------------------------------------
-- WAITING FOR NOTHING: THE VALUE IS CONSTANT
--
-- `Agr (inl tt) X X'` is `Top`, so `sem-sat` needs no agreement at all.
------------------------------------------------------------------------

fedV-inl : (p : Nat) (T : Tr p) -> MonoTr p T
         -> (V : Nat -> FTup)
         -> ((k k' : Nat) -> LeN k k' -> LeX (V k) (V k'))
         -> (K : Nat) -> Eq (blockOn p T (V K)) (inl tt)
         -> VerdictFrom K (\ k -> sem p T (V k))
fedV-inl p T mt V Vmono K e =
  mkSigma K (mkSigma (LeN-refl K) (pick (IsCpl-dec (sem p T (V K)))))
  where
    same : (k : Nat) -> LeN K k -> Eq (sem p T (V K)) (sem p T (V k))
    same k lk = sem-sat p T mt (V K) (V k) (Vmono K k lk) ag
      where
        ag : Agr (blockOn p T (V K)) (V K) (V k)
        ag = Eq-transport (\ z -> Agr z (V K) (V k)) (Eq-sym e) tt

    pick : Dec (IsCpl (sem p T (V K)))
         -> Or (IsCpl (sem p T (V K)))
               (Pair ((k : Nat) -> LeN K k -> Bt (sem p T (V k)))
                     (PhiOK (\ k -> hgt (sem p T (V k)))))
    pick (yes ic) = inl ic
    pick (no  nc) = inr (mkSigma nvr (mkSigma K (inl con)))
      where
        nvr : (k : Nat) -> LeN K k -> Bt (sem p T (V k))
        nvr k lk =
          Eq-transport (\ z -> Bt z) (same k lk) (notCpl-bt (sem p T (V K)) nc)

        con : ConstFrom K (\ k -> hgt (sem p T (V k)))
        con k lk = Eq-sym (Eq-cong hgt (same k lk))

------------------------------------------------------------------------
-- A TAIL VERDICT IS A VERDICT, IF THE VALUE IS MONOTONE
------------------------------------------------------------------------

verdictFrom-verdict : (u : Nat -> FEl)
                    -> ((m n : Nat) -> LeN m n -> LeF (u m) (u n))
                    -> (K : Nat) -> VerdictFrom K u -> Verdict u
verdictFrom-verdict u mo K (mkSigma K' (mkSigma lk r)) = route r
  where
    route : Or (IsCpl (u K'))
               (Pair ((k : Nat) -> LeN K' k -> Bt (u k)) (PhiOK (\ k -> hgt (u k))))
          -> Verdict u
    route (inl ic) = inl (mkSigma K' ic)
    route (inr (mkSigma nv pk)) = inr (mkSigma nev pk)
      where
        nev : Never u
        nev k = pick (LeN-dec K' k)
          where
            pick : Dec (LeN K' k) -> Bt (u k)
            pick (yes l)  = nv k l
            pick (no  nl) = notCpl-bt (u k) nc
              where
                lkK : LeN k K'
                lkK =
                  LeN-trans {k} {suc k} {K'} (LeN-suc k) (nle-lt K' k nl)

                nc : Not (IsCpl (u k))
                nc ic =
                  notCpl-of (u K') (nv K' (LeN-refl K'))
                    (Eq-transport (\ z -> IsCpl z)
                      (cpl-max (u k) (u K') (mo k K' lkK) ic) ic)

------------------------------------------------------------------------
-- THE THEOREM
------------------------------------------------------------------------

fedV : (p : Nat) (T : Tr p) -> MonoTr p T -> MP1T p T
     -> (V : Nat -> FTup)
     -> ((k k' : Nat) -> LeN k k' -> LeX (V k) (V k'))
     -> (K J : Nat)
     -> ((k : Nat) -> LeN K k -> Eq (blockOn p T (V k)) (inr J))
     -> Or (OvSettles (\ k -> nth (fbot zero) J (V k)))
           (OvGrows (\ k -> nth (fbot zero) J (V k)))
     -> VerdictFrom K (\ k -> sem p T (V k))
------------------------------------------------------------------------
-- a `stop` waits for nothing, so its value is the constant `v`
------------------------------------------------------------------------
fedV p (stop v) mt m1 V Vmono K J stab reg = mkSigma K (mkSigma (LeN-refl K) (route (IsCpl-dec v)))
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
fedV (suc q) (node ivg ivgr ovg contg) mt m1 V Vmono K J stab reg =
  route reg
  where
    open SEMf q ivg ivgr ovg contg V Vmono mt

    Ng : Nat
    Ng = fst (fst m1)

    ivg-const : (n : Nat) -> LeN Ng n -> Eq (ivg n) (ivg Ng)
    ivg-const = snd (fst m1)

    vg : Verdict ovg
    vg = fst (snd m1)

    -- the outer value can never be total: it would make the demand `inl tt`
    ncov : (k : Nat) -> LeN K k -> Not (IsCpl (ovg (NG k)))
    ncov k lk ic = orNE J (Eq-trans (Eq-sym (blk-inl k ic)) (stab k lk))

    ------------------------------------------------------------------
    -- CASE 1: THE DEMANDED VALUE SETTLES -- `sem-sat` finishes at once
    ------------------------------------------------------------------

    settled : OvSettles (\ k -> nth (fbot zero) J (V k))
            -> VerdictFrom K SV
    settled (mkSigma n1 set) = mkSigma K1 (mkSigma lKK1 (pick (IsCpl-dec (SV K1))))
      where
        K1 : Nat
        K1 = maxN K n1

        lKK1 : LeN K K1
        lKK1 = maxN-le-l K n1

        ln1 : LeN n1 K1
        ln1 = maxN-le-r K n1

        same : (k : Nat) -> LeN K1 k -> Eq (SV K1) (SV k)
        same k lk = sem-sat (suc q) Tg mt (V K1) (V k) (Vmono K1 k lk) ag
          where
            uEq : Eq (nth (fbot zero) J (V K1)) (nth (fbot zero) J (V k))
            uEq =
              Eq-trans (set K1 ln1)
                (Eq-sym (set k (LeN-trans {n1} {K1} {k} ln1 lk)))

            ag : Agr (blockOn (suc q) Tg (V K1)) (V K1) (V k)
            ag =
              Eq-transport (\ z -> Agr z (V K1) (V k)) (Eq-sym (stab K1 lKK1)) uEq

        pick : Dec (IsCpl (SV K1))
             -> Or (IsCpl (SV K1))
                   (Pair ((k : Nat) -> LeN K1 k -> Bt (SV k))
                         (PhiOK (\ k -> hgt (SV k))))
        pick (yes ic) = inl ic
        pick (no  nc) = inr (mkSigma nvr (mkSigma K1 (inl con)))
          where
            nvr : (k : Nat) -> LeN K1 k -> Bt (SV k)
            nvr k lk =
              Eq-transport (\ z -> Bt z) (same k lk) (notCpl-bt (SV K1) nc)

            con : ConstFrom K1 (\ k -> hgt (SV k))
            con k lk = Eq-sym (Eq-cong hgt (same k lk))

    ------------------------------------------------------------------
    -- CASE 2: THE DEMANDED VALUE GROWS
    ------------------------------------------------------------------

    grows : OvGrows (\ k -> nth (fbot zero) J (V k))
          -> VerdictFrom K SV
    grows (mkSigma nev (mkSigma n1 si)) = finish (search Ng)
      where
        K2 : Nat
        K2 = maxN K n1

        lKK2 : LeN K K2
        lKK2 = maxN-le-l K n1

        ln1 : LeN n1 K2
        ln1 = maxN-le-r K n1

        lK2 : (k : Nat) -> LeN K2 k -> LeN K k
        lK2 k lk = LeN-trans {K} {K2} {k} lKK2 lk

        -- coordinate J is never complete, and grows by at least one
        naJ : (k : Nat) -> Not (IsCpl (nth (fbot zero) J (V k)))
        naJ k = notCpl-of (nth (fbot zero) J (V k)) (nev k)

        Jgrow : (k : Nat) -> LeN K2 k
              -> LeN (suc (hts (V k) J)) (hts (V (suc k)) J)
        Jgrow k lk = si k (LeN-trans {n1} {K2} {k} ln1 lk)

        -- while nothing is complete the demanded coordinate IS `J`
        cgJ : (k : Nat) -> LeN K2 k -> Not (IsCpl (at k)) -> Eq (cg k) J
        cgJ k lk na =
          inr-inj (cg k) J
            (Eq-trans (Eq-sym (blk-fbot k (ncov k (lK2 k lk)) na)) (stab k (lK2 k lk)))

        ----------------------------------------------------------------
        -- the bounded search for a descent
        ----------------------------------------------------------------

        Found : Set
        Found = Sigma Nat (\ k0 -> Pair (LeN K2 k0) (IsCpl (at k0)))

        NoDesc : Nat -> Set
        NoDesc t = (s : Nat) -> LeN s t -> Not (IsCpl (at (pl K2 s)))

        search : (t : Nat) -> Or Found (NoDesc t)
        search zero = pick (IsCpl-dec (at K2))
          where
            pick : Dec (IsCpl (at K2)) -> Or Found (NoDesc zero)
            pick (yes ic) = inl (mkSigma K2 (mkSigma (LeN-refl K2) ic))
            pick (no  nc) = inr go
              where
                go : NoDesc zero
                go zero    ls = nc
                go (suc s) ()
        search (suc t) = step (search t)
          where
            step : Or Found (NoDesc t) -> Or Found (NoDesc (suc t))
            step (inl f)  = inl f
            step (inr nd) = pick (IsCpl-dec (at (pl K2 (suc t))))
              where
                pick : Dec (IsCpl (at (pl K2 (suc t)))) -> Or Found (NoDesc (suc t))
                pick (yes ic) =
                  inl (mkSigma (pl K2 (suc t))
                        (mkSigma (pl-ge K2 (suc t)) ic))
                pick (no  nc) = inr go
                  where
                    go : NoDesc (suc t)
                    go s ls = route (LeN-dec s t)
                      where
                        route : Dec (LeN s t) -> Not (IsCpl (at (pl K2 s)))
                        route (yes l)  = nd s l
                        route (no  nl) =
                          Eq-transport (\ z -> Not (IsCpl (at (pl K2 z))))
                            (Eq-sym (eq' s t ls nl)) nc
                          where
                            eq' : (x y : Nat) -> LeN x (suc y) -> Not (LeN x y)
                                -> Eq x (suc y)
                            eq' zero    y       l n' = Empty-elim (n' tt)
                            eq' (suc x) zero    l n' =
                              Eq-cong suc (LeN-antisym {x} {zero} l tt)
                            eq' (suc x) (suc y) l n' = Eq-cong suc (eq' x y l n')

        ----------------------------------------------------------------
        -- (a) A DESCENT: recurse on a strictly smaller trace
        ----------------------------------------------------------------

        descend : Found -> VerdictFrom K SV
        descend (mkSigma k0 (mkSigma lk0 ic0)) = lift (fedV q CT0 mt' m1' V' Vmono' k0 c' stab' reg')
          where
            C0 : Nat
            C0 = cg k0

            CT0 : Tr q
            CT0 = CT k0

            -- the demanded coordinate stays complete, so the descent stays on
            ic : (k : Nat) -> LeN k0 k -> IsCpl (at k)
            ic k lk =
              Eq-transport (\ z -> IsCpl z)
                (Eq-trans
                  (cpl-max (nth (fbot zero) C0 (V k0)) (nth (fbot zero) C0 (V k))
                    (Vmono k0 k lk C0) ic0)
                  (Eq-cong (\ z -> nth (fbot zero) z (V k))
                    (Eq-sym (cg-freeze k0 ic0 k lk))))
                ic0

            semD : (k : Nat) -> LeN k0 k -> Eq (SV k) (sem q CT0 (del C0 (V k)))
            semD k lk =
              Eq-trans (sem-descend k (ncov k (lK2 k (LeN-trans {K2} {k0} {k} lk0 lk))) (ic k lk))
                (Eq-trans
                  (Eq-cong (\ T' -> sem q T' (del (cg k) (V k))) (CT-freeze k0 ic0 k lk))
                  (Eq-cong (\ z -> sem q CT0 (del z (V k))) (cg-freeze k0 ic0 k lk)))

            blkD : (k : Nat) -> LeN k0 k
                 -> Eq (shiftOr C0 (blockOn q CT0 (del C0 (V k)))) (inr J)
            blkD k lk =
              Eq-trans
                (Eq-sym
                  (Eq-trans
                    (Eq-cong (\ z -> shiftOr z (blockOn q (CT k) (del z (V k))))
                      (cg-freeze k0 ic0 k lk))
                    (Eq-cong (\ T' -> shiftOr C0 (blockOn q T' (del C0 (V k))))
                      (CT-freeze k0 ic0 k lk))))
                (Eq-trans
                  (Eq-sym (blk-descend k
                            (ncov k (lK2 k (LeN-trans {K2} {k0} {k} lk0 lk))) (ic k lk)))
                  (stab k (lK2 k (LeN-trans {K2} {k0} {k} lk0 lk))))

            cinv : Sigma Nat (\ c'' -> Pair (Eq (blockOn q CT0 (del C0 (V k0))) (inr c''))
                                            (Eq (su C0 c'') J))
            cinv = shiftOr-inv C0 (blockOn q CT0 (del C0 (V k0))) J (blkD k0 (LeN-refl k0))

            c' : Nat
            c' = fst cinv

            eJ : Eq (su C0 c') J
            eJ = snd (snd cinv)

            V' : Nat -> FTup
            V' k = del C0 (V k)

            Vmono' : (k k' : Nat) -> LeN k k' -> LeX (V' k) (V' k')
            Vmono' k k' le = LeX-del C0 (V k) (V k') (Vmono k k' le)

            mt' : MonoTr q CT0
            mt' = snd mt C0 (ivgr (NG k0)) (hts (V k0) C0)

            m1' : MP1T q CT0
            m1' = snd (snd m1) C0 (ivgr (NG k0)) (hts (V k0) C0)

            stab' : (k : Nat) -> LeN k0 k -> Eq (blockOn q CT0 (V' k)) (inr c')
            stab' k lk = shiftOr-inj (blkD k lk)
              where
                shiftOr-inj : Eq (shiftOr C0 (blockOn q CT0 (V' k))) (inr J)
                            -> Eq (blockOn q CT0 (V' k)) (inr c')
                shiftOr-inj e = go (shiftOr-inv C0 (blockOn q CT0 (V' k)) J e)
                  where
                    go : Sigma Nat (\ c'' ->
                           Pair (Eq (blockOn q CT0 (V' k)) (inr c''))
                                (Eq (su C0 c'') J))
                       -> Eq (blockOn q CT0 (V' k)) (inr c')
                    go (mkSigma c'' (mkSigma eb es)) =
                      Eq-trans eb (Eq-cong inr (su-inj C0 c'' c' (Eq-trans es (Eq-sym eJ))))
                      where
                        sinj : (u v : Nat) -> Eq (suc u) (suc v) -> Eq u v
                        sinj u .u refl = refl

                        su-inj : (i x y : Nat) -> Eq (su i x) (su i y) -> Eq x y
                        su-inj zero    x       y       e' = sinj x y e'
                        su-inj (suc i) zero    zero    e' = refl
                        su-inj (suc i) zero    (suc y) ()
                        su-inj (suc i) (suc x) zero    ()
                        su-inj (suc i) (suc x) (suc y) e' =
                          Eq-cong suc (su-inj i x y (sinj (su i x) (su i y) e'))

            -- the regime transports: coordinate `c'` of `V'` IS coordinate `J` of `V`
            eco : (k : Nat) -> Eq (nth (fbot zero) c' (V' k)) (nth (fbot zero) J (V k))
            eco k =
              Eq-trans (nth-del C0 c' (V k))
                (Eq-cong (\ z -> nth (fbot zero) z (V k)) eJ)

            reg' : Or (OvSettles (\ k -> nth (fbot zero) c' (V' k)))
                      (OvGrows (\ k -> nth (fbot zero) c' (V' k)))
            reg' =
              inr (mkSigma
                    (\ k -> Eq-transport (\ z -> Eq z (fbot (hgt z))) (Eq-sym (eco k)) (nev k))
                    (mkSigma n1 sic))
              where
                sic : StrictIncFrom n1 (\ k -> hgt (nth (fbot zero) c' (V' k)))
                sic m lm =
                  Eq-transport (\ z -> LeN (suc (hgt z)) (hgt (nth (fbot zero) c' (V' (suc m)))))
                    (Eq-sym (eco m))
                    (Eq-transport
                      (\ z -> LeN (suc (hgt (nth (fbot zero) J (V m)))) (hgt z))
                      (Eq-sym (eco (suc m))) (si m lm))

            lift : VerdictFrom k0 (\ k -> sem q CT0 (V' k)) -> VerdictFrom K SV
            lift (mkSigma K' (mkSigma lk' r)) =
              mkSigma K'
                (mkSigma
                  (LeN-trans {K} {k0} {K'} (lK2 k0 lk0) lk')
                  (tr r))
              where
                lk0K' : LeN k0 K'
                lk0K' = lk'

                tr : Or (IsCpl (sem q CT0 (V' K')))
                        (Pair ((k : Nat) -> LeN K' k -> Bt (sem q CT0 (V' k)))
                              (PhiOK (\ k -> hgt (sem q CT0 (V' k)))))
                   -> Or (IsCpl (SV K'))
                         (Pair ((k : Nat) -> LeN K' k -> Bt (SV k))
                               (PhiOK (\ k -> hgt (SV k))))
                tr (inl icc) =
                  inl (Eq-transport (\ z -> IsCpl z) (Eq-sym (semD K' lk0K')) icc)
                tr (inr (mkSigma nv (mkSigma kk pk))) =
                  inr (mkSigma
                        (\ k lk ->
                           Eq-transport (\ z -> Bt z)
                             (Eq-sym (semD k (LeN-trans {k0} {K'} {k} lk0K' lk)))
                             (nv k lk))
                        (mkSigma (maxN kk K') (phi pk)))
                  where
                    phi : Or (ConstFrom kk (\ k -> hgt (sem q CT0 (V' k))))
                             (StrictIncFrom kk (\ k -> hgt (sem q CT0 (V' k))))
                        -> Or (ConstFrom (maxN kk K') (\ k -> hgt (SV k)))
                              (StrictIncFrom (maxN kk K') (\ k -> hgt (SV k)))
                    phi (inl cf) = inl go
                      where
                        atk : (k : Nat) -> LeN (maxN kk K') k -> Eq (hgt (SV k)) (hgt (sem q CT0 (V' kk)))
                        atk k lk =
                          Eq-trans
                            (Eq-cong hgt
                              (semD k (LeN-trans {k0} {maxN kk K'} {k}
                                        (LeN-trans {k0} {K'} {maxN kk K'} lk0K'
                                          (maxN-le-r kk K')) lk)))
                            (cf k (LeN-trans {kk} {maxN kk K'} {k} (maxN-le-l kk K') lk))

                        go : ConstFrom (maxN kk K') (\ k -> hgt (SV k))
                        go k lk = Eq-trans (atk k lk) (Eq-sym (atk (maxN kk K') (LeN-refl (maxN kk K'))))
                    phi (inr sinc) = inr go
                      where
                        go : StrictIncFrom (maxN kk K') (\ k -> hgt (SV k))
                        go k lk =
                          Eq-transport (\ z -> LeN (suc (hgt z)) (hgt (SV (suc k))))
                            (Eq-sym (semD k lkk))
                            (Eq-transport
                              (\ z -> LeN (suc (hgt (sem q CT0 (V' k)))) (hgt z))
                              (Eq-sym (semD (suc k) (LeN-trans {k0} {k} {suc k} lkk (LeN-suc k))))
                              (sinc k (LeN-trans {kk} {maxN kk K'} {k} (maxN-le-l kk K') lk)))
                          where
                            lkk : LeN k0 k
                            lkk =
                              LeN-trans {k0} {maxN kk K'} {k}
                                (LeN-trans {k0} {K'} {maxN kk K'} lk0K' (maxN-le-r kk K')) lk

        ----------------------------------------------------------------
        -- (b) NO DESCENT: the replay climbs past `Ng` and stays there
        ----------------------------------------------------------------

        nodesc : NoDesc Ng -> VerdictFrom K SV
        nodesc nd = mkSigma Kf (mkSigma lKKf (inr (mkSigma btf (phiOf vg))))
          where
            -- along the searched stretch the demand is `J`, so the replay climbs
            climb : (s : Nat) -> LeN s Ng -> LeN s (NG (pl K2 s))
            climb zero    ls = tt
            climb (suc s) ls =
              LeN-trans {suc s} {suc (NG (pl K2 s))} {NG (suc (pl K2 s))}
                (climb s (LeN-trans {s} {suc s} {Ng} (LeN-suc s) ls))
                (NG-grow (pl K2 s) (suc (pl K2 s)) (LeN-suc (pl K2 s)) gr)
              where
                lk : LeN K2 (pl K2 s)
                lk = pl-ge K2 s

                ec : Eq (cg (pl K2 s)) J
                ec = cgJ (pl K2 s) lk (nd s (LeN-trans {s} {suc s} {Ng} (LeN-suc s) ls))

                gr : LeN (suc (hts (V (pl K2 s)) (cg (pl K2 s))))
                        (hts (V (suc (pl K2 s))) (cg (pl K2 s)))
                gr =
                  Eq-transport
                    (\ z -> LeN (suc (hts (V (pl K2 s)) z)) (hts (V (suc (pl K2 s))) z))
                    (Eq-sym ec) (Jgrow (pl K2 s) lk)

            Kf : Nat
            Kf = pl K2 Ng

            lKKf : LeN K Kf
            lKKf = LeN-trans {K} {K2} {Kf} lKK2 (pl-ge K2 Ng)

            lNgKf : LeN Ng (NG Kf)
            lNgKf = climb Ng (LeN-refl Ng)

            -- past `Kf` the demanded coordinate is `J`, for ever
            eJ0 : Eq (ivg Ng) J
            eJ0 =
              Eq-trans (Eq-sym (ivg-const (NG Kf) lNgKf))
                (cgJ Kf (pl-ge K2 Ng) (nd Ng (LeN-refl Ng)))

            cgf : (k : Nat) -> LeN Kf k -> Eq (cg k) J
            cgf k lk =
              Eq-trans
                (ivg-const (NG k) (LeN-trans {Ng} {NG Kf} {NG k} lNgKf (NG-mono Kf k lk)))
                eJ0

            naf : (k : Nat) -> LeN Kf k -> Not (IsCpl (at k))
            naf k lk =
              Eq-transport (\ z -> Not (IsCpl (nth (fbot zero) z (V k)))) (Eq-sym (cgf k lk))
                (naJ k)

            lKf : (k : Nat) -> LeN Kf k -> LeN K k
            lKf k lk = LeN-trans {K} {Kf} {k} lKKf lk

            semf : (k : Nat) -> LeN Kf k -> Eq (SV k) (ovg (NG k))
            semf k lk = sem-fbot k (ncov k (lKf k lk)) (naf k lk)

            NGf-grow : (k : Nat) -> LeN Kf k -> LeN (suc (NG k)) (NG (suc k))
            NGf-grow k lk =
              NG-grow k (suc k) (LeN-suc k)
                (Eq-transport (\ z -> LeN (suc (hts (V k) z)) (hts (V (suc k)) z))
                  (Eq-sym (cgf k lk))
                  (Jgrow k (LeN-trans {K2} {Kf} {k} (pl-ge K2 Ng) lk)))

            NGf-climb : (t : Nat) -> LeN t (NG (pl Kf t))
            NGf-climb zero    = tt
            NGf-climb (suc t) =
              LeN-trans {suc t} {suc (NG (pl Kf t))} {NG (suc (pl Kf t))}
                (NGf-climb t) (NGf-grow (pl Kf t) (pl-ge Kf t))

            -- the outer value can never be total, so its own `PhiOK` is available
            btf : (k : Nat) -> LeN Kf k -> Bt (SV k)
            btf k lk =
              Eq-transport (\ z -> Bt z) (Eq-sym (semf k lk))
                (notCpl-bt (ovg (NG k)) (ncov k (lKf k lk)))

            phiOf : Verdict ovg -> PhiOK (\ k -> hgt (SV k))
            phiOf (inl (mkSigma n0 icn)) =
              Empty-elim (ncov (pl Kf n0) (lKf (pl Kf n0) (pl-ge Kf n0)) big)
              where
                big : IsCpl (ovg (NG (pl Kf n0)))
                big =
                  Eq-transport (\ z -> IsCpl z)
                    (cpl-max (ovg n0) (ovg (NG (pl Kf n0)))
                      (fst mt n0 (NG (pl Kf n0)) (NGf-climb n0)) icn) icn
            phiOf (inr (mkSigma nvg (mkSigma k0' pk))) = split pk
              where
                Kc : Nat
                Kc = pl Kf k0'

                lKfKc : LeN Kf Kc
                lKfKc = pl-ge Kf k0'

                lk0Kc : LeN k0' (NG Kc)
                lk0Kc = NGf-climb k0'

                lKc : (k : Nat) -> LeN Kc k -> LeN k0' (NG k)
                lKc k lk = LeN-trans {k0'} {NG Kc} {NG k} lk0Kc (NG-mono Kc k lk)

                split : Or (ConstFrom k0' (\ n -> hgt (ovg n)))
                           (StrictIncFrom k0' (\ n -> hgt (ovg n)))
                      -> PhiOK (\ k -> hgt (SV k))
                split (inl cf) = mkSigma Kc (inl go)
                  where
                    atk : (k : Nat) -> LeN Kc k -> Eq (hgt (SV k)) (hgt (ovg k0'))
                    atk k lk =
                      Eq-trans
                        (Eq-cong hgt (semf k (LeN-trans {Kf} {Kc} {k} lKfKc lk)))
                        (cf (NG k) (lKc k lk))

                    go : ConstFrom Kc (\ k -> hgt (SV k))
                    go k lk = Eq-trans (atk k lk) (Eq-sym (atk Kc (LeN-refl Kc)))
                split (inr sinc) = mkSigma Kc (inr go)
                  where
                    go : StrictIncFrom Kc (\ k -> hgt (SV k))
                    go k lk =
                      Eq-transport (\ z -> LeN (suc (hgt z)) (hgt (SV (suc k))))
                        (Eq-sym (semf k lkf))
                        (Eq-transport (\ z -> LeN (suc (hgt (ovg (NG k)))) (hgt z))
                          (Eq-sym (semf (suc k) (LeN-trans {Kf} {k} {suc k} lkf (LeN-suc k))))
                          (sinc-mono-lt k0' (\ n -> hgt (ovg n)) sinc (NG k) (NG (suc k))
                            (lKc k lk) (NGf-grow k lkf)))
                      where
                        lkf : LeN Kf k
                        lkf = LeN-trans {Kf} {Kc} {k} lKfKc lk

        finish : Or Found (NoDesc Ng) -> VerdictFrom K SV
        finish (inl f)  = descend f
        finish (inr nd) = nodesc nd

    route : Or (OvSettles (\ k -> nth (fbot zero) J (V k)))
               (OvGrows (\ k -> nth (fbot zero) J (V k)))
          -> VerdictFrom K SV
    route (inl s) = settled s
    route (inr g) = grows g
