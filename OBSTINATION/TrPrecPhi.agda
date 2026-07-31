{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecPhi
--
-- **phi FOR THE RECURSION, FROM THE STEP TERM'S MP1 ALONE -- NO PROP 1.**
--
--     PHI.chain-phiok : PhiOK (\ j -> hgt (V j))
--
-- i.e. the number of successors of  f(S^j bot, Y)  is EVENTUALLY CONSTANT
-- OR STRICTLY INCREASING in `j`, for
--
--     f(bot,Y) = bot ,   f(S^(j+1) bot, Y) = g(S^j bot, f(S^j bot,Y), Y),
--
-- given only MP1 for the step term `g` -- its `Verdict ovh` and its
-- `EvConstN ivh` -- and that the chain never answers.
--
-- THIS IS IMG_0270's THEOREM.  With `g`'s sequence written
-- `(n_p, x_p, y_p, z_p)` -- `n_p` successors after `p` steps, having gone
-- `x_p` deep in the recursion argument, `y_p` in the recursive value,
-- `z_p` in the parameters -- Thierry's statement is
--
--     f loops in its first argument  iff  exists p with
--         y(p+1) = y(p) + 1    and    n_p <= y_p,
--
-- and then `f`'s sequence is ultimately `(n_p, x, z), (n_p, x+1, z), ...`
-- -- CONSTANT `n` -- while otherwise it is "en gros comme la suite h".
-- Here `y(p+1) = y(p)+1` is `ivh p = 1` and `n_p <= y_p` is exactly the
-- replay being blocked on the recursive value, i.e. a STALL, and
-- `TrPrecStall` says a stall is permanent.  So:
--
--     either the replay stalls -- and `hgt o V` is CONSTANT from there --
--     or it strictly increases at every depth, and then `g`'s own `PhiOK`
--     transfers verbatim.
--
-- WHY THE SEARCH IS BOUNDED (the point that was missing).  A stall is
-- never on the recursion argument (`TrPrecStall.stall-not-zero`), so past
-- `EvConstN ivh`'s threshold `Nh` the stalled coordinate must be the
-- eventual demand `Ih`, and
--
--   * `Ih = 0` -- impossible, so any stall is at a depth below `Nh`;
--   * `Ih >= 2` -- a parameter: `lv Ih` grows by one per step past `Nh`
--     while `ReplayLv.find-below` caps it at the parameter's own level, so
--     any stall is at a depth below `Nh + (that level) + 1`;
--   * `Ih = 1` -- the recursive value: a stall needs
--     `hgt (ov (NJ j)) <= lv 1 (NJ j) <= hgt (V j)`, i.e. `n_p <= y_p`,
--     while `StrictIncFrom` forces `hgt (V (j+1)) > hgt (V j)` once the
--     replay is past `k0`; so any stall is at a depth below `k0 + 1`.
--
-- One bounded search of length `max (Nh + AV 0 Ih) k0 + 1` therefore
-- decides it.  Both halves of MP1 for `g` are used, and Proposition 1 is
-- used nowhere.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecPhi where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.BlkReplay using (nle-lt ; le-ne-lt)
open import OBSTINATION.ReplayLv using (lv ; bump-eq)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.MP1 using (ConstFrom ; StrictIncFrom ; PhiOK)
open import OBSTINATION.PhiComp using (sinc-mono-lt)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (IsCpl ; cpl-max ; MonoTr)
open import OBSTINATION.TrMP1 using (EvTot ; Never ; Verdict)
open import OBSTINATION.TrPrec using (module R)
open import OBSTINATION.TrPrecChain using (Bt ; bt-notCpl ; module CH)
open import OBSTINATION.TrPrecStall using (module ST)
open import OBSTINATION.TrPrecDecMP using (pl ; pl-ge ; le-pl ; module DEC)

------------------------------------------------------------------------
-- ARITHMETIC
------------------------------------------------------------------------

pl-ge-r : (x t : Nat) -> LeN t (pl x t)
pl-ge-r x zero    = tt
pl-ge-r x (suc t) = pl-ge-r x t

suc-not : (x : Nat) -> Not (LeN (suc x) x)
suc-not zero    ()
suc-not (suc x) l = suc-not x l

le-eq : (x y : Nat) -> LeN x y -> Not (LeN (suc x) y) -> Eq x y
le-eq zero    zero    l nl = refl
le-eq zero    (suc y) l nl = Empty-elim (nl tt)
le-eq (suc x) zero    () nl
le-eq (suc x) (suc y) l nl = Eq-cong suc (le-eq x y l nl)

------------------------------------------------------------------------
-- THE RECURSION'S phi
------------------------------------------------------------------------

module PHI (p : Nat)
           (ivh : Nat -> Nat)
           (ivhr : (n : Nat) -> LeN (suc (ivh n)) (suc (suc p)))
           (ovh : Nat -> FEl)
           (conth : (c : Nat) -> LeN (suc c) (suc (suc p)) -> (v : Nat)
                  -> Tr (suc p))
           (L : Nat -> Nat)
           (ov-mono : (m n : Nat) -> LeN m n -> LeF (ovh m) (ovh n))
           (V-mono : (j j' : Nat) -> LeN j j'
                   -> LeF (R.Vd p (node ivh ivhr ovh conth) L j)
                          (R.Vd p (node ivh ivhr ovh conth) L j'))
           -- MP1 for the step term: the value clause ...
           (vrd : Verdict ovh)
           -- ... and the index clause
           (evc : EvConstN ivh)
           -- the chain never answers (otherwise `f` is Case 1)
           (nv : (j : Nat) -> Bt (R.Vd p (node ivh ivhr ovh conth) L j))
           where

  open CH p ivh ivhr ovh conth L
  open ST p ivh ivhr ovh conth L
  open DEC p ivh ivhr ovh conth L ov-mono V-mono vrd using (NJ-mono)

  W : Nat -> Nat
  W j = hgt (V j)

  H : Nat -> Nat
  H n = hgt (ovh n)

  LV : Nat -> Nat -> Nat
  LV = lv a ivh ivhr

  Nh : Nat
  Nh = fst evc

  Ih : Nat
  Ih = ivh Nh

  ivh-const : (n : Nat) -> LeN Nh n -> Eq (ivh n) Ih
  ivh-const = snd evc

  -- the chain step, always available since the chain never answers
  chain : (j : Nat) -> Eq (W (suc j)) (H (NJ j))
  chain j = Eq-cong hgt (step j (nv j))

  ----------------------------------------------------------------------
  -- PAST `Nh` THE WALK PUMPS ONE COORDINATE
  ----------------------------------------------------------------------

  lv-pump : (t : Nat) -> Eq (LV Ih (pl Nh t)) (pl (LV Ih Nh) t)
  lv-pump zero    = refl
  lv-pump (suc t) =
    Eq-trans
      (bump-eq (ivh (pl Nh t)) (\ d -> LV d (pl Nh t)) Ih
        (Eq-sym (ivh-const (pl Nh t) (pl-ge Nh t))))
      (Eq-cong suc (lv-pump t))

  lv-ge : (t : Nat) -> LeN t (LV Ih (pl Nh t))
  lv-ge t =
    Eq-transport (\ z -> LeN t z) (Eq-sym (lv-pump t)) (pl-ge-r (LV Ih Nh) t)

  lv-mono : (c m n : Nat) -> LeN m n -> LeN (LV c m) (LV c n)
  lv-mono c m zero    le =
    Eq-transport (\ z -> LeN (LV c z) (LV c zero))
      (Eq-sym (LeN-antisym {m} {zero} le tt)) (LeN-refl (LV c zero))
  lv-mono c m (suc n) le = route (LeN-dec m n)
    where
      one : LeN (LV c n) (LV c (suc n))
      one = pick (EqNat-dec c (ivh n))
        where
          pick : Dec (Eq c (ivh n)) -> LeN (LV c n) (LV c (suc n))
          pick (yes e) =
            Eq-transport (\ z -> LeN (LV c n) z)
              (Eq-sym (bump-eq (ivh n) (\ d -> LV d n) c e)) (LeN-suc (LV c n))
          pick (no ne) =
            Eq-transport (\ z -> LeN (LV c n) z)
              (Eq-sym (bump-ne (ivh n) (\ d -> LV d n) c ne)) (LeN-refl (LV c n))
            where
              open import OBSTINATION.ReplayLv using (bump-ne)

      route : Dec (LeN m n) -> LeN (LV c m) (LV c (suc n))
      route (yes l) =
        LeN-trans {LV c m} {LV c n} {LV c (suc n)} (lv-mono c m n l) one
      route (no nl) =
        Eq-transport (\ z -> LeN (LV c z) (LV c (suc n)))
          (Eq-sym (eq' m n le nl)) (LeN-refl (LV c (suc n)))
        where
          eq' : (x y : Nat) -> LeN x (suc y) -> Not (LeN x y) -> Eq x (suc y)
          eq' zero    y       l nl' = Empty-elim (nl' tt)
          eq' (suc x) zero    l nl' = Eq-cong suc (LeN-antisym {x} {zero} l tt)
          eq' (suc x) (suc y) l nl' = Eq-cong suc (eq' x y l nl')

  ----------------------------------------------------------------------
  -- A STALL, AND ITS PERMANENCE
  ----------------------------------------------------------------------

  Stall : Nat -> Set
  Stall j = Eq (NJ (suc j)) (NJ j)

  stall-run : (j0 : Nat) -> Stall j0 -> (t : Nat) -> Stall (pl j0 t)
  stall-run j0 st zero    = st
  stall-run j0 st (suc t) =
    stall-perm (pl j0 t) (nv (pl j0 t)) (nv (suc (pl j0 t))) (stall-run j0 st t)

  frz-nj : (j0 : Nat) -> Stall j0 -> (t : Nat) -> Eq (NJ (pl j0 t)) (NJ j0)
  frz-nj j0 st zero    = refl
  frz-nj j0 st (suc t) = Eq-trans (stall-run j0 st t) (frz-nj j0 st t)

  -- a stall freezes the number of successors
  frz-const : (j0 : Nat) -> Stall j0 -> ConstFrom (suc j0) W
  frz-const j0 st zero     ()
  frz-const j0 st (suc m') lm = go (le-pl j0 m' lm)
    where
      go : Sigma Nat (\ t -> Eq m' (pl j0 t)) -> Eq (W (suc m')) (W (suc j0))
      go (mkSigma t e) =
        Eq-trans (chain m')
          (Eq-trans (Eq-cong (\ z -> H (NJ z)) e)
            (Eq-trans (Eq-cong H (frz-nj j0 st t)) (Eq-sym (chain j0))))

  ----------------------------------------------------------------------
  -- THE BOUNDED SEARCH FOR A STALL
  ----------------------------------------------------------------------

  NoSt : Nat -> Set
  NoSt t = (j : Nat) -> LeN (suc j) t -> Not (Stall j)

  search : (t : Nat) -> Or (Sigma Nat Stall) (NoSt t)
  search zero    = inr (\ j ())
  search (suc t) = route (search t)
    where
      route : Or (Sigma Nat Stall) (NoSt t) -> Or (Sigma Nat Stall) (NoSt (suc t))
      route (inl w)  = inl w
      route (inr ns) = dec (EqNat-dec (NJ (suc t)) (NJ t))
        where
          dec : Dec (Stall t) -> Or (Sigma Nat Stall) (NoSt (suc t))
          dec (yes e) = inl (mkSigma t e)
          dec (no ne) = inr ext
            where
              ext : NoSt (suc t)
              ext j lj = pick (LeN-dec (suc j) t)
                where
                  pick : Dec (LeN (suc j) t) -> Not (Stall j)
                  pick (yes l)  = ns j l
                  pick (no  nl) =
                    Eq-transport (\ z -> Not (Stall z)) (Eq-sym (le-eq j t lj nl)) ne

  -- without a stall the replay outruns the depth
  step-up : (j : Nat) -> LeN j (NJ j) -> Not (Stall j) -> LeN (suc j) (NJ (suc j))
  step-up j lnj nst =
    LeN-trans {suc j} {suc (NJ j)} {NJ (suc j)} lnj
      (le-ne-lt (NJ j) (NJ (suc j)) (NJ-mono j (suc j) (LeN-suc j)) nst)

  nj-ge : (t : Nat) -> NoSt t -> (j : Nat) -> LeN j t -> LeN j (NJ j)
  nj-ge t ns zero     lj = tt
  nj-ge t ns (suc j') lj =
    step-up j' (nj-ge t ns j' (LeN-trans {j'} {suc j'} {t} (LeN-suc j') lj))
      (ns j' lj)

  ----------------------------------------------------------------------
  -- CASE `EvTot`: the chain must stall
  ----------------------------------------------------------------------

  module TOT (n0 : Nat) (cn0 : IsCpl (ovh n0)) where

    cpl-above : (n : Nat) -> LeN n0 n -> IsCpl (ovh n)
    cpl-above n ln =
      Eq-transport (\ z -> IsCpl z)
        (cpl-max (ovh n0) (ovh n) (ov-mono n0 n ln) cn0) cn0

    nj-small : (j : Nat) -> Not (LeN n0 (NJ j))
    nj-small j l =
      bt-notCpl (V (suc j)) (nv (suc j))
        (Eq-transport (\ z -> IsCpl z) (Eq-sym (step j (nv j))) (cpl-above (NJ j) l))

    tot-phiok : PhiOK W
    tot-phiok = route (search n0)
      where
        route : Or (Sigma Nat Stall) (NoSt n0) -> PhiOK W
        route (inl (mkSigma j0 st)) = mkSigma (suc j0) (inl (frz-const j0 st))
        route (inr ns) = Empty-elim (nj-small n0 (nj-ge n0 ns n0 (LeN-refl n0)))

  ----------------------------------------------------------------------
  -- CASE `Never`, `ConstFrom`: the successors settle
  ----------------------------------------------------------------------

  module CF (k0 : Nat) (cf : ConstFrom k0 H) where

    cf-phiok : PhiOK W
    cf-phiok = route (search k0)
      where
        route : Or (Sigma Nat Stall) (NoSt k0) -> PhiOK W
        route (inl (mkSigma j0 st)) = mkSigma (suc j0) (inl (frz-const j0 st))
        route (inr ns) = mkSigma (suc k0) (inl con)
          where
            base : LeN k0 (NJ k0)
            base = nj-ge k0 ns k0 (LeN-refl k0)

            at : (m : Nat) -> LeN k0 m -> Eq (W (suc m)) (H k0)
            at m lm =
              Eq-trans (chain m)
                (cf (NJ m)
                  (LeN-trans {k0} {NJ k0} {NJ m} base (NJ-mono k0 m lm)))

            con : ConstFrom (suc k0) W
            con zero     ()
            con (suc m') lm = Eq-trans (at m' lm) (Eq-sym (at k0 (LeN-refl k0)))

  ----------------------------------------------------------------------
  -- CASE `Never`, `StrictIncFrom`: either a stall (below a computable
  -- bound) or the successors grow strictly for ever
  ----------------------------------------------------------------------

  module SI (k0 : Nat) (si : StrictIncFrom k0 H) where

    AVI : Nat
    AVI = AV zero Ih

    B0 : Nat
    B0 = maxN (pl Nh AVI) k0

    Bnd : Nat
    Bnd = suc B0

    lk0 : LeN k0 B0
    lk0 = maxN-le-r (pl Nh AVI) k0

    lNhB : LeN (pl Nh AVI) B0
    lNhB = maxN-le-l (pl Nh AVI) k0

    ------------------------------------------------------------------
    -- past the bound a stall is impossible
    ------------------------------------------------------------------

    no-stall-suc : (j : Nat) -> LeN B0 j -> LeN j (NJ j) -> Not (Stall j)
                 -> Not (Stall (suc j))
    no-stall-suc j lB lnj nst st = bad Ih refl
      where
        n : Nat
        n = NJ (suc j)

        lsj : LeN (suc j) n
        lsj = step-up j lnj nst

        lNh : LeN Nh n
        lNh =
          LeN-trans {Nh} {suc j} {n}
            (LeN-trans {Nh} {j} {suc j}
              (LeN-trans {Nh} {B0} {j}
                (LeN-trans {Nh} {pl Nh AVI} {B0} (pl-ge Nh AVI) lNhB) lB)
              (LeN-suc j))
            lsj

        eI : Eq (ivh n) Ih
        eI = ivh-const n lNh

        -- the stalled coordinate
        nz : Not (Eq (ivh n) zero)
        nz = stall-not-zero (suc j) st

        -- the replay is still stuck at `n` one depth later
        blk : LeN (AV (suc (suc j)) (ivh n)) (LV (ivh n) n)
        blk =
          Eq-transport (\ m -> LeN (AV (suc (suc j)) (ivh m)) (LV (ivh m) m)) st
            (blocked (suc (suc j)))

        -- ... and its levels were below what was available at depth `j+1`
        bel : (c : Nat) -> LeN (LV c n) (AV (suc j) c)
        bel = below (suc j)

        bad : (c : Nat) -> Eq Ih c -> Empty
        bad zero          e = nz (Eq-trans eI e)
        bad (suc zero)    e = suc-not (W (suc j)) grow-bad
          where
            e1 : Eq (ivh n) (suc zero)
            e1 = Eq-trans eI e

            -- `n_p <= y_p` : the stall pins the successors
            down : LeN (W (suc (suc j))) (W (suc j))
            down =
              LeN-trans {W (suc (suc j))} {LV (suc zero) n} {W (suc j)}
                (Eq-transport (\ z -> LeN z (LV (suc zero) n))
                  (AV-one (suc (suc j)))
                  (Eq-transport (\ c -> LeN (AV (suc (suc j)) c) (LV c n)) e1 blk))
                (Eq-transport (\ z -> LeN (LV (suc zero) n) z)
                  (AV-one (suc j)) (bel (suc zero)))

            -- but `StrictIncFrom` makes them grow
            up : LeN (suc (W (suc j))) (W (suc (suc j)))
            up =
              Eq-transport (\ z -> LeN (suc z) (W (suc (suc j))))
                (Eq-sym (chain j))
                (Eq-transport (\ z -> LeN (suc (H (NJ j))) z) (Eq-sym (chain (suc j)))
                  (sinc-mono-lt k0 H si (NJ j) n
                    (LeN-trans {k0} {j} {NJ j} (LeN-trans {k0} {B0} {j} lk0 lB) lnj)
                    (le-ne-lt (NJ j) n (NJ-mono j (suc j) (LeN-suc j)) nst)))

            grow-bad : LeN (suc (W (suc j))) (W (suc j))
            grow-bad = LeN-trans {suc (W (suc j))} {W (suc (suc j))} {W (suc j)} up down
        bad (suc (suc i)) e = suc-not AVI absurd
          where
            e2 : Eq (ivh n) (suc (suc i))
            e2 = Eq-trans eI e

            li : LeN (suc (suc (suc i))) a
            li = Eq-transport (\ z -> LeN (suc z) a) e2 (ivhr n)

            -- a parameter's level never changes
            par : Eq (AV (suc j) Ih) AVI
            par =
              Eq-transport (\ z -> Eq (AV (suc j) z) (AV zero z)) (Eq-sym e)
                (AV-par i (suc j) zero li)

            cap : LeN (LV Ih n) AVI
            cap =
              Eq-transport (\ z -> LeN (LV Ih n) z) par
                (Eq-transport (\ c -> LeN (LV c n) (AV (suc j) c)) eI
                  (bel (ivh n)))

            -- ... while `lv Ih` grows by one per step past `Nh`
            reach : LeN (suc AVI) (LV Ih n)
            reach =
              LeN-trans {suc AVI} {LV Ih (pl Nh (suc AVI))} {LV Ih n}
                (lv-ge (suc AVI))
                (lv-mono Ih (pl Nh (suc AVI)) n
                  (LeN-trans {pl Nh (suc AVI)} {suc j} {n}
                    (LeN-trans {suc (pl Nh AVI)} {suc B0} {suc j} lNhB lB) lsj))

            absurd : LeN (suc AVI) AVI
            absurd = LeN-trans {suc AVI} {LV Ih n} {AVI} reach cap

    ------------------------------------------------------------------
    -- so from the bound on, the replay strictly increases
    ------------------------------------------------------------------

    run : NoSt Bnd -> (t : Nat)
        -> Pair (LeN (pl Bnd t) (NJ (pl Bnd t))) (Not (Stall (pl Bnd t)))
    run ns zero    = mkSigma lb nb
      where
        lb : LeN Bnd (NJ Bnd)
        lb = nj-ge Bnd ns Bnd (LeN-refl Bnd)

        nb : Not (Stall Bnd)
        nb =
          no-stall-suc B0 (LeN-refl B0)
            (nj-ge Bnd ns B0 (LeN-suc B0)) (ns B0 (LeN-refl B0))
    run ns (suc t) = mkSigma (step-up j (fst ih) (snd ih)) nsuc
      where
        j : Nat
        j = pl Bnd t

        ih : Pair (LeN j (NJ j)) (Not (Stall j))
        ih = run ns t

        lBj : LeN B0 j
        lBj = LeN-trans {B0} {Bnd} {j} (LeN-suc B0) (pl-ge Bnd t)

        nsuc : Not (Stall (suc j))
        nsuc = no-stall-suc j lBj (fst ih) (snd ih)

    si-phiok : PhiOK W
    si-phiok = route (search Bnd)
      where
        route : Or (Sigma Nat Stall) (NoSt Bnd) -> PhiOK W
        route (inl (mkSigma j0 st)) = mkSigma (suc j0) (inl (frz-const j0 st))
        route (inr ns) = mkSigma (suc Bnd) (inr inc)
          where
            at : (m : Nat) -> LeN Bnd m
               -> Pair (LeN m (NJ m)) (Not (Stall m))
            at m lm = go (le-pl Bnd m lm)
              where
                go : Sigma Nat (\ t -> Eq m (pl Bnd t))
                   -> Pair (LeN m (NJ m)) (Not (Stall m))
                go (mkSigma t e) =
                  Eq-transport
                    (\ z -> Pair (LeN z (NJ z)) (Not (Stall z))) (Eq-sym e) (run ns t)

            inc : StrictIncFrom (suc Bnd) W
            inc zero     ()
            inc (suc m') lm =
              Eq-transport (\ z -> LeN (suc z) (W (suc (suc m'))))
                (Eq-sym (chain m'))
                (Eq-transport (\ z -> LeN (suc (H (NJ m'))) z)
                  (Eq-sym (chain (suc m')))
                  (sinc-mono-lt k0 H si (NJ m') (NJ (suc m'))
                    (LeN-trans {k0} {m'} {NJ m'}
                      (LeN-trans {k0} {Bnd} {m'}
                        (LeN-trans {k0} {B0} {Bnd} lk0 (LeN-suc B0)) lm)
                      (fst (at m' lm)))
                    (le-ne-lt (NJ m') (NJ (suc m'))
                      (NJ-mono m' (suc m') (LeN-suc m')) (snd (at m' lm)))))

  ----------------------------------------------------------------------
  -- THE THEOREM
  ----------------------------------------------------------------------

  chain-phiok : PhiOK W
  chain-phiok = route vrd
    where
      route : Verdict ovh -> PhiOK W
      route (inl (mkSigma n0 cn0)) = TOT.tot-phiok n0 cn0
      route (inr (mkSigma nev pk)) = split pk
        where
          split : PhiOK H -> PhiOK W
          split (mkSigma k0 (inl cf)) = CF.cf-phiok k0 cf
          split (mkSigma k0 (inr si)) = SI.si-phiok k0 si
