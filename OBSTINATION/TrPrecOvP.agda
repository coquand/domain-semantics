{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecOvP
--
-- **MP1's VALUE CLAUSE FOR `precTr`, WITHOUT PROPOSITION 1.**
--
--     ovP-verdict : Verdict (P.ovP p Th)
--
-- from `MonoTr`/`MP1T` of the step term, `Den`/`MonoF`, and
-- `EvConstN (P.ivP p Th)` -- the index clause, itself Prop-1-free since
-- `TrPrecIvPMP`.
--
-- THE ASSEMBLY.  `ovP k = Vd (Lv k) (Lv k 0)` is `f`'s value along `f`'s
-- OWN walk, and past `EvConstN ivP`'s threshold `N` that walk raises ONE
-- coordinate `I`.  Reading off `Lv (k+1) = bump (ivP k) (Lv k)`:
--
--   * every coordinate other than `I` is FROZEN at `Lv N` (`Lv-ne`);
--   * `I` grows by exactly one per step (`Lv-I`).
--
-- So there are two shapes, and each already has its theorem:
--
--   `I = 0`  -- the parameters are frozen and the recursion argument
--               grows, so `ovP (N+t) = Vd (Lv N) (c+t)`: this is the
--               CHAIN, and `TrPrecPhi.PHI.chain-phiok` is exactly its
--               `PhiOK` (IMG_0270), with `TrPrecDecMP.DEC.decide` saying
--               whether it ever answers.
--
--   `I >= 1`  -- the recursion depth is frozen at `c` and one parameter
--               grows, so `ovP (N+t) = Vd (Lt t) c` with
--               `Lt t = Lv (N+t)`: this is the UNROLLING, and
--               `TrPrecParPhi.PAR.unroll` is its verdict.  `Lv-ne` and
--               `Lv-I` are precisely `PAR`'s `Lt-reg`.
--
-- `shiftVF` then turns a verdict on the tail `t |-> ovP (N+t)` into one on
-- `ovP`, using only that `ovP` is monotone.
--
-- No Proposition 1.  No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecOvP where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using
  (FEl ; fbot ; fcpl ; LeF ; LeF-refl ; LeF-trans)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.BlkReplay using (plus ; nle-lt)
open import OBSTINATION.MP1 using
  (ConstFrom ; StrictIncFrom ; PhiOK ; phiok-shift-r ; phiok-cong-from)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.ReplayLv using (bump ; bump-eq ; bump-ne)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (IsCpl ; cpl-max ; MonoF ; MonoTr)
open import OBSTINATION.TrDen using (Den)
open import OBSTINATION.TrMP1 using (EvTot ; Never ; Verdict ; MP1T ; verdict-TN)
open import OBSTINATION.TrMono using (lev-mono)
open import OBSTINATION.TrPrec using (module R ; module P)
open import OBSTINATION.TrPrecDec using (Vd-mono ; Vd-mono-L)
open import OBSTINATION.TrCompVerdict using (VerdictFrom ; IsCpl-dec ; notCpl-of)
open import OBSTINATION.TrPrecChain using (Bt ; notCpl-bt ; tup-cong-le)
open import OBSTINATION.TrPrecDecMP using (pl ; pl-ge ; le-pl ; module DEC)
open import OBSTINATION.TrPrecPhi using (pl-ge-r ; suc-not ; module PHI)
open import OBSTINATION.TrPrecParPhi using (module PAR)
open import OBSTINATION.TrFeedR using (vfCong)

------------------------------------------------------------------------
-- ARITHMETIC
------------------------------------------------------------------------

pl-plus : (x t : Nat) -> Eq (pl x t) (plus t x)
pl-plus x zero    = refl
pl-plus x (suc t) = Eq-cong suc (pl-plus x t)

pl-mono-r : (x t t' : Nat) -> LeN t t' -> LeN (pl x t) (pl x t')
pl-mono-r x zero    t'       le = pl-ge x t'
pl-mono-r x (suc t) zero     ()
pl-mono-r x (suc t) (suc t') le = pl-mono-r x t t' le

-- `pl x` is injective on the order
pl-cancel : (x u v : Nat) -> LeN (pl x u) (pl x v) -> LeN u v
pl-cancel x zero     v       le = tt
pl-cancel x (suc u) zero     le =
  Empty-elim (suc-not (pl x u) (LeN-trans {suc (pl x u)} {x} {pl x u} le (pl-ge x u)))
pl-cancel x (suc u) (suc v) le = pl-cancel x u v le

------------------------------------------------------------------------
-- AN EVENTUALLY CONSTANT VALUE HAS A VERDICT
------------------------------------------------------------------------

evconst-verdict : (u : Nat -> FEl)
                -> ((m n : Nat) -> LeN m n -> LeF (u m) (u n))
                -> (M : Nat) -> ((k : Nat) -> LeN M k -> Eq (u k) (u M))
                -> Verdict u
evconst-verdict u mo M ev = route (IsCpl-dec (u M))
  where
    route : Dec (IsCpl (u M)) -> Verdict u
    route (yes ic) = inl (mkSigma M ic)
    route (no  nc) = inr (mkSigma nev (mkSigma M (inl con)))
      where
        nev : Never u
        nev k = notCpl-bt (u k) go
          where
            go : Not (IsCpl (u k))
            go ic = pick (LeN-dec M k)
              where
                pick : Dec (LeN M k) -> Empty
                pick (yes l) = nc (Eq-transport (\ z -> IsCpl z) (ev k l) ic)
                pick (no  n) =
                  nc (Eq-transport (\ z -> IsCpl z)
                       (cpl-max (u k) (u M) (mo k M lkM) ic) ic)
                  where
                    lkM : LeN k M
                    lkM = LeN-trans {k} {suc k} {M} (LeN-suc k) (nle-lt M k n)

        con : ConstFrom M (\ k -> hgt (u k))
        con k lk = Eq-cong hgt (ev k lk)

------------------------------------------------------------------------
-- A TAIL VERDICT, SHIFTED BACK
------------------------------------------------------------------------

shiftVF : (u : Nat -> FEl)
        -> ((m n : Nat) -> LeN m n -> LeF (u m) (u n))
        -> (N : Nat) -> VerdictFrom zero (\ t -> u (pl N t)) -> Verdict u
shiftVF u mo N (mkSigma K' (mkSigma _ r)) = route r
  where
    route : Or (IsCpl (u (pl N K')))
               (Pair ((t : Nat) -> LeN K' t -> Bt (u (pl N t)))
                     (PhiOK (\ t -> hgt (u (pl N t)))))
          -> Verdict u
    route (inl ic) = inl (mkSigma (pl N K') ic)
    route (inr (mkSigma nv pk)) = inr (mkSigma nev (phi pk))
      where
        --------------------------------------------------------------
        -- nothing is complete anywhere: below the tail by monotonicity
        --------------------------------------------------------------
        nev : Never u
        nev k = notCpl-bt (u k) go
          where
            s : Nat
            s = maxN k K'

            lks : LeN k (pl N s)
            lks = LeN-trans {k} {s} {pl N s} (maxN-le-l k K') (pl-ge-r N s)

            go : Not (IsCpl (u k))
            go ic =
              notCpl-of (u (pl N s)) (nv s (maxN-le-r k K'))
                (Eq-transport (\ z -> IsCpl z)
                  (cpl-max (u k) (u (pl N s)) (mo k (pl N s) lks) ic) ic)

        --------------------------------------------------------------
        -- and the height clause moves back along `pl N`
        --------------------------------------------------------------
        phi : PhiOK (\ t -> hgt (u (pl N t))) -> PhiOK (\ k -> hgt (u k))
        phi (mkSigma kk (inl cf)) = mkSigma (pl N kk) (inl con)
          where
            con : ConstFrom (pl N kk) (\ k -> hgt (u k))
            con m lm = grab (le-pl N m (LeN-trans {N} {pl N kk} {m} (pl-ge N kk) lm))
              where
                grab : Sigma Nat (\ t -> Eq m (pl N t))
                     -> Eq (hgt (u m)) (hgt (u (pl N kk)))
                grab (mkSigma t et) =
                  Eq-transport (\ z -> Eq (hgt (u z)) (hgt (u (pl N kk)))) (Eq-sym et)
                    (cf t (pl-cancel N kk t
                            (Eq-transport (\ z -> LeN (pl N kk) z) et lm)))
        phi (mkSigma kk (inr si)) = mkSigma (pl N kk) (inr inc)
          where
            inc : StrictIncFrom (pl N kk) (\ k -> hgt (u k))
            inc m lm = grab (le-pl N m (LeN-trans {N} {pl N kk} {m} (pl-ge N kk) lm))
              where
                grab : Sigma Nat (\ t -> Eq m (pl N t))
                     -> LeN (suc (hgt (u m))) (hgt (u (suc m)))
                grab (mkSigma t et) =
                  Eq-transport (\ z -> LeN (suc (hgt (u z))) (hgt (u (suc z))))
                    (Eq-sym et)
                    (si t (pl-cancel N kk t
                            (Eq-transport (\ z -> LeN (pl N kk) z) et lm)))

------------------------------------------------------------------------
-- CONGRUENCE OF THE RECURSION IN THE PARAMETER LEVELS
------------------------------------------------------------------------

Vd-cong-L : (p : Nat) (Th : Tr (suc (suc p))) (L L' : Nat -> Nat)
          -> ((i : Nat) -> Eq (L (suc i)) (L' (suc i)))
          -> (j : Nat) -> Eq (R.Vd p Th L j) (R.Vd p Th L' j)
Vd-cong-L p Th L L' e zero    = refl
Vd-cong-L p Th L L' e (suc j) =
  Eq-cong (\ X -> sem (suc (suc p)) Th X)
    (tup-cong-le (suc (suc p)) (R.avf p Th L j) (R.avf p Th L' j) pt)
  where
    pt : (c : Nat) -> LeN (suc c) (suc (suc p))
       -> Eq (R.avf p Th L j c) (R.avf p Th L' j c)
    pt zero          lc = refl
    pt (suc zero)    lc = Vd-cong-L p Th L L' e j
    pt (suc (suc i)) lc = Eq-cong fbot (e i)

------------------------------------------------------------------------
-- THE CHAIN'S VERDICT AT A FIXED PARAMETER LEVEL
--
-- `TrPrecDecMP.DEC.decide` says whether it answers, and if it does not,
-- `TrPrecPhi.PHI.chain-phiok` -- IMG_0270's theorem -- gives its `PhiOK`.
------------------------------------------------------------------------

chainV : (p : Nat) (Th : Tr (suc (suc p)))
       -> MonoTr (suc (suc p)) Th -> MP1T (suc (suc p)) Th
       -> (g h : FTup -> FEl)
       -> Den (suc (suc p)) Th h -> MonoF p g -> MonoF (suc (suc p)) h
       -> (L : Nat -> Nat)
       -> Or (Sigma Nat (\ j0 -> IsCpl (R.Vd p Th L j0)))
             (Pair ((j : Nat) -> Bt (R.Vd p Th L j))
                   (PhiOK (\ j -> hgt (R.Vd p Th L j))))
------------------------------------------------------------------------
-- a `stop` step term: the chain is `bot , v , v , ...`
------------------------------------------------------------------------
chainV p (stop v) mth m1th g h dh mg mh L = route (IsCpl-dec v)
  where
    route : Dec (IsCpl v)
          -> Or (Sigma Nat (\ j0 -> IsCpl (R.Vd p (stop v) L j0)))
                (Pair ((j : Nat) -> Bt (R.Vd p (stop v) L j))
                      (PhiOK (\ j -> hgt (R.Vd p (stop v) L j))))
    route (yes ic) = inl (mkSigma (suc zero) ic)
    route (no  nc) = inr (mkSigma nv (mkSigma (suc zero) (inl con)))
      where
        nv : (j : Nat) -> Bt (R.Vd p (stop v) L j)
        nv zero    = refl
        nv (suc j) = notCpl-bt v nc

        con : ConstFrom (suc zero) (\ j -> hgt (R.Vd p (stop v) L j))
        con zero    ()
        con (suc j) lj = refl
------------------------------------------------------------------------
-- a `node` step term: `decide` then `chain-phiok`
------------------------------------------------------------------------
chainV p (node ivh ivhr ovh conth) mth m1th g h dh mg mh L =
  route (DEC.decide p ivh ivhr ovh conth L (fst mth) Vmono (verdict-TN ovh (fst (snd m1th))))
  where
    Th : Tr (suc (suc p))
    Th = node ivh ivhr ovh conth

    Vmono : (j j' : Nat) -> LeN j j' -> LeF (R.Vd p Th L j) (R.Vd p Th L j')
    Vmono = Vd-mono p Th g h dh mg mh L

    route : Or (Sigma Nat (\ j0 -> IsCpl (R.Vd p Th L j0)))
               ((j : Nat) -> Not (IsCpl (R.Vd p Th L j)))
          -> Or (Sigma Nat (\ j0 -> IsCpl (R.Vd p Th L j0)))
                (Pair ((j : Nat) -> Bt (R.Vd p Th L j))
                      (PhiOK (\ j -> hgt (R.Vd p Th L j))))
    route (inl w)  = inl w
    route (inr nc) = inr (mkSigma nv phi)
      where
        nv : (j : Nat) -> Bt (R.Vd p Th L j)
        nv j = notCpl-bt (R.Vd p Th L j) (nc j)

        phi : PhiOK (\ j -> hgt (R.Vd p Th L j))
        phi =
          PHI.chain-phiok p ivh ivhr ovh conth L (fst mth) Vmono
            (fst (snd m1th)) (fst m1th) nv

------------------------------------------------------------------------
-- MP1's VALUE CLAUSE FOR `precTr`
------------------------------------------------------------------------

ovP-verdict : (p : Nat) (Th : Tr (suc (suc p)))
            -> MonoTr (suc (suc p)) Th -> MP1T (suc (suc p)) Th
            -> (g h : FTup -> FEl)
            -> Den (suc (suc p)) Th h -> MonoF p g -> MonoF (suc (suc p)) h
            -> EvConstN (P.ivP p Th)
            -> Verdict (P.ovP p Th)
ovP-verdict p Th mth m1th g h dh mg mh evP = route (EqNat-dec I zero)
  where
    Lv : Nat -> Nat -> Nat
    Lv = P.Lv p Th

    ivP : Nat -> Nat
    ivP = P.ivP p Th

    ovP : Nat -> FEl
    ovP = P.ovP p Th

    N : Nat
    N = fst evP

    ivP-const : (n : Nat) -> LeN N n -> Eq (ivP n) (ivP N)
    ivP-const = snd evP

    I : Nat
    I = ivP N

    c0 : Nat
    c0 = Lv N zero

    Lv-mono : (m n : Nat) -> LeN m n -> (c : Nat) -> LeN (Lv m c) (Lv n c)
    Lv-mono = lev-mono ivP Lv (\ k c -> refl)

    ----------------------------------------------------------------------
    -- past `N` only coordinate `I` moves, and it moves by one per step
    ----------------------------------------------------------------------

    Lv-ne : (t c : Nat) -> Not (Eq c I) -> Eq (Lv (pl N t) c) (Lv N c)
    Lv-ne zero    c ne = refl
    Lv-ne (suc t) c ne =
      Eq-trans (bump-ne (ivP (pl N t)) (Lv (pl N t)) c ne') (Lv-ne t c ne)
      where
        ne' : Not (Eq c (ivP (pl N t)))
        ne' e = ne (Eq-trans e (ivP-const (pl N t) (pl-ge N t)))

    Lv-I : (t : Nat) -> Eq (Lv (pl N t) I) (pl (Lv N I) t)
    Lv-I zero    = refl
    Lv-I (suc t) =
      Eq-trans
        (bump-eq (ivP (pl N t)) (Lv (pl N t)) I
          (Eq-sym (ivP-const (pl N t) (pl-ge N t))))
        (Eq-cong suc (Lv-I t))

    ovP-mono : (m n : Nat) -> LeN m n -> LeF (ovP m) (ovP n)
    ovP-mono m n le =
      LeF-trans
        {R.Vd p Th (Lv m) (Lv m zero)}
        {R.Vd p Th (Lv n) (Lv m zero)}
        {R.Vd p Th (Lv n) (Lv n zero)}
        (Vd-mono-L p Th g h dh mg mh (Lv m) (Lv n)
          (\ i -> Lv-mono m n le (suc i)) (Lv m zero))
        (Vd-mono p Th g h dh mg mh (Lv n) (Lv m zero) (Lv n zero)
          (Lv-mono m n le zero))

    ----------------------------------------------------------------------
    -- `I >= 1`: the recursion depth is frozen, one parameter grows
    ----------------------------------------------------------------------

    par : Not (Eq I zero) -> Verdict ovP
    par ne = shiftVF ovP ovP-mono N (vfC (PAR.unroll p Th mth m1th g h dh mg mh Lt Lt-mono Lt-reg c0))
      where
        Lt : Nat -> Nat -> Nat
        Lt t = Lv (pl N t)

        Lt-mono : (t t' : Nat) -> LeN t t' -> (i : Nat) -> LeN (Lt t i) (Lt t' i)
        Lt-mono t t' le i = Lv-mono (pl N t) (pl N t') (pl-mono-r N t t' le) i

        Lt-reg : (i : Nat)
               -> Sigma Nat (\ ki ->
                    Or ((t t' : Nat) -> LeN ki t -> LeN t t' -> Eq (Lt t' i) (Lt t i))
                       ((t : Nat) -> LeN ki t -> LeN (suc (Lt t i)) (Lt (suc t) i)))
        Lt-reg i = mkSigma zero (pick (EqNat-dec i I))
          where
            pick : Dec (Eq i I)
                 -> Or ((t t' : Nat) -> LeN zero t -> LeN t t' -> Eq (Lt t' i) (Lt t i))
                       ((t : Nat) -> LeN zero t -> LeN (suc (Lt t i)) (Lt (suc t) i))
            pick (yes ei) = inr grow
              where
                grow : (t : Nat) -> LeN zero t -> LeN (suc (Lt t i)) (Lt (suc t) i)
                grow t _ =
                  Eq-transport (\ z -> LeN (suc (Lt t i)) z) (Eq-sym step)
                    (LeN-refl (suc (Lt t i)))
                  where
                    step : Eq (Lt (suc t) i) (suc (Lt t i))
                    step =
                      bump-eq (ivP (pl N t)) (Lv (pl N t)) i
                        (Eq-trans ei (Eq-sym (ivP-const (pl N t) (pl-ge N t))))
            pick (no ni) = inl fix
              where
                fix : (t t' : Nat) -> LeN zero t -> LeN t t' -> Eq (Lt t' i) (Lt t i)
                fix t t' _ _ = Eq-trans (Lv-ne t' i ni) (Eq-sym (Lv-ne t i ni))

        nz : Not (Eq zero I)
        nz e = ne (Eq-sym e)

        ovP-eq : (t : Nat) -> Eq (ovP (pl N t)) (R.Vd p Th (Lt t) c0)
        ovP-eq t = Eq-cong (\ z -> R.Vd p Th (Lt t) z) (Lv-ne t zero nz)

        vfC : VerdictFrom zero (\ t -> R.Vd p Th (Lt t) c0)
            -> VerdictFrom zero (\ t -> ovP (pl N t))
        vfC = vfCong (\ t -> ovP (pl N t)) (\ t -> R.Vd p Th (Lt t) c0) zero
                (\ t lt -> ovP-eq t)

    ----------------------------------------------------------------------
    -- `I = 0`: the parameters are frozen, the recursion argument grows
    ----------------------------------------------------------------------

    rec : Eq I zero -> Verdict ovP
    rec ei = split (chainV p Th mth m1th g h dh mg mh (Lv N))
      where
        parEq : (t : Nat) -> (i : Nat) -> Eq (Lv (pl N t) (suc i)) (Lv N (suc i))
        parEq t i = Lv-ne t (suc i) (\ e -> nsuc (Eq-trans e ei))
          where
            nsuc : Not (Eq (suc i) zero)
            nsuc ()

        lv0 : (t : Nat) -> Eq (Lv (pl N t) zero) (pl c0 t)
        lv0 t =
          Eq-transport (\ z -> Eq (Lv (pl N t) z) (pl (Lv N z) t)) ei (Lv-I t)

        Vpar : (t : Nat) -> Eq (ovP (pl N t)) (R.Vd p Th (Lv N) (pl c0 t))
        Vpar t =
          Eq-trans
            (Vd-cong-L p Th (Lv (pl N t)) (Lv N) (parEq t) (Lv (pl N t) zero))
            (Eq-cong (\ z -> R.Vd p Th (Lv N) z) (lv0 t))

        split : Or (Sigma Nat (\ j0 -> IsCpl (R.Vd p Th (Lv N) j0)))
                   (Pair ((j : Nat) -> Bt (R.Vd p Th (Lv N) j))
                         (PhiOK (\ j -> hgt (R.Vd p Th (Lv N) j))))
              -> Verdict ovP
        --------------------------------------------------------------
        -- the chain answers: so does `f`
        --------------------------------------------------------------
        split (inl (mkSigma j0 ic)) = inl (mkSigma (pl N j0) icc)
          where
            big : IsCpl (R.Vd p Th (Lv N) (pl c0 j0))
            big =
              Eq-transport (\ z -> IsCpl z)
                (cpl-max (R.Vd p Th (Lv N) j0) (R.Vd p Th (Lv N) (pl c0 j0))
                  (Vd-mono p Th g h dh mg mh (Lv N) j0 (pl c0 j0) (pl-ge-r c0 j0)) ic)
                ic

            icc : IsCpl (ovP (pl N j0))
            icc = Eq-transport (\ z -> IsCpl z) (Eq-sym (Vpar j0)) big
        --------------------------------------------------------------
        -- it never does: `chain-phiok`, shifted by the frozen depth
        --------------------------------------------------------------
        split (inr (mkSigma nv pk)) =
          shiftVF ovP ovP-mono N
            (mkSigma zero (mkSigma tt (inr (mkSigma nvr phi'))))
          where
            nvr : (t : Nat) -> LeN zero t -> Bt (ovP (pl N t))
            nvr t _ =
              Eq-transport (\ z -> Bt z) (Eq-sym (Vpar t)) (nv (pl c0 t))

            phi' : PhiOK (\ t -> hgt (ovP (pl N t)))
            phi' =
              phiok-cong-from
                (\ z -> hgt (R.Vd p Th (Lv N) (plus z c0)))
                (\ t -> hgt (ovP (pl N t))) zero agree
                (phiok-shift-r (\ j -> hgt (R.Vd p Th (Lv N) j)) pk c0)
              where
                agree : (m : Nat) -> LeN zero m
                      -> Eq (hgt (R.Vd p Th (Lv N) (plus m c0))) (hgt (ovP (pl N m)))
                agree m _ =
                  Eq-sym
                    (Eq-trans (Eq-cong hgt (Vpar m))
                      (Eq-cong (\ z -> hgt (R.Vd p Th (Lv N) z)) (pl-plus c0 m)))

    route : Dec (Eq I zero) -> Verdict ovP
    route (yes ei) = rec ei
    route (no  ne) = par ne
