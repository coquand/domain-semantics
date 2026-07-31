{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrFeed
--
-- **FEEDING A TRACE A FAMILY OF ARGUMENTS: THE VERDICT TRANSFERS.**
--
--     FEED.feed-verdict : Verdict (\ t -> sem q T (Y t))
--
-- where `T` is a trace with MP1 -- `Verdict ov` and `EvConstN iv`, the
-- INDUCTION HYPOTHESIS -- and `Y t` is a family of argument tuples that is
-- monotone, never complete, and whose every coordinate has `PhiOK`
-- heights.  No Proposition 1.
--
-- THE ARGUMENT is IMG_0269's, read one level up.  Since no coordinate is
-- ever complete, `TrSat.sem-bot` collapses the semantics to one lookup:
--
--     sem q T (Y t) = ov (M t) ,    M t = nOf q iv ivr (heights of Y t),
--
-- so the whole question is how `M` -- the replay depth -- moves.  It is
-- monotone, and at each `t` it is stuck on the coordinate `d = iv (M t)`,
-- with (`ReplayLv.stuck`, `find-below`)
--
--     lv d (M t)  =  the height coordinate `d` offers at time `t`.
--
-- So past `d`'s own `PhiOK` threshold there is no third possibility:
--
--   * `d` CONSTANT   -- coordinate `d` never grows again, so the replay is
--                       stuck at `M t` for ever (`frozen`);
--   * `d` STRICTLY INCREASING -- it grows by at least one, which is
--                       exactly what the replay was waiting for, so the
--                       replay advances (`advance`).
--
-- Hence `M` strictly increases until it freezes, and it freezes for good.
-- Deciding which is a BOUNDED search: if `M` has not frozen by
-- `K + Ng` -- `K` the largest coordinate threshold, `Ng` the threshold of
-- `EvConstN iv` -- then `M (K+Ng) >= Ng`, so from there the stuck
-- coordinate is the single eventual demand `I`, whose regime is already
-- known.  Frozen gives `ConstFrom`; never frozen gives `M` strictly
-- increasing, and `T`'s own `PhiOK` transfers verbatim.
--
-- TWO LIMITS, AND EXACTLY WHAT WOULD LIFT THEM.
--
-- 1. NOTHING MAY GO COMPLETE (`bt`).  If a coordinate becomes a numeral,
--    `TraceDef.sem` descends into `cont` and this lookup is wrong.  The
--    fix is a recursion on the ARITY: at the first such time, freeze that
--    coordinate and re-enter with `contOf T c lc v`, which is exactly what
--    `MP1T`'s continuation clause is for.  At most `q` descents.
--
-- 2. THE HYPOTHESIS `regP` IS TOO STRONG FOR `comp`.  In `TrComp`,
--    coordinate `i` of the family is `ovOf (Ths i) (dep k i)`, and
--    `dep k i` advances only when argument `i` is SELECTED -- so its
--    height PLATEAUS in between and is not `PhiOK` in `k`.  But `frozen`
--    and `advance` below do not use `PhiOK`: they use only
--
--      Fix c :  c never grows again past `regK c`;
--      Gro c :  c grows by one whenever it is the coordinate the replay is
--               stuck on, at a time past `regK c`,
--
--    and `TrComp`'s walk raises exactly the level the selected argument
--    needs, so `Gro` is what its per-argument `StrictIncFrom` gives.
--    Restating `regP` as `Or (Fix c) (Gro c)` -- which has to live in an
--    inner module, since `Fix`/`Gro` mention the derived `A` and `D` --
--    makes this lemma serve `comp` as well.  `PhiOK` implies both.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrFeed where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.BlkReplay using (nle-lt ; le-ne-lt)
open import OBSTINATION.ReplayLv using
  (lv ; Adv ; nOf ; nOf-mono ; nOf-le ; stuck ; sumTo ; find-below ; Below)
open import OBSTINATION.MutIdxWalk using (EvConstN)
open import OBSTINATION.MP1 using (ConstFrom ; StrictIncFrom ; PhiOK)
open import OBSTINATION.PhiComp using (sinc-mono-lt)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (IsCpl ; cpl-max ; botTup ; sem-bot)
open import OBSTINATION.TrMP1 using (EvTot ; Never ; Verdict)
open import OBSTINATION.TrPrecChain using (Bt ; bt-notCpl ; notCpl-bt ; tup-cong-le)
open import OBSTINATION.TrPrecStall using (nOf-below)
open import OBSTINATION.TrPrecDecMP using (pl ; pl-ge ; le-pl)
open import OBSTINATION.TrPrecPhi using (pl-ge-r ; suc-not ; le-eq)

------------------------------------------------------------------------
-- A BOUNDED MAXIMUM
------------------------------------------------------------------------

maxTo : Nat -> (Nat -> Nat) -> Nat
maxTo zero    f = zero
maxTo (suc n) f = maxN (f n) (maxTo n f)

maxTo-ge : (n : Nat) (f : Nat -> Nat) (c : Nat) -> LeN (suc c) n
         -> LeN (f c) (maxTo n f)
maxTo-ge zero    f c ()
maxTo-ge (suc n) f c lc = route (LeN-dec (suc c) n)
  where
    route : Dec (LeN (suc c) n) -> LeN (f c) (maxN (f n) (maxTo n f))
    route (yes l) =
      LeN-trans {f c} {maxTo n f} {maxN (f n) (maxTo n f)}
        (maxTo-ge n f c l) (maxN-le-r (f n) (maxTo n f))
    route (no nl) =
      Eq-transport (\ z -> LeN (f z) (maxN (f n) (maxTo n f)))
        (Eq-sym (le-eq c n lc nl)) (maxN-le-l (f n) (maxTo n f))

------------------------------------------------------------------------
-- THE FEED
------------------------------------------------------------------------

module FEED (q' : Nat)
            (iv : Nat -> Nat)
            (ivr : (n : Nat) -> LeN (suc (iv n)) (suc q'))
            (ov : Nat -> FEl)
            (cont : (c : Nat) -> LeN (suc c) (suc q') -> (v : Nat) -> Tr q')
            -- the family, coordinate by coordinate
            (AVF : Nat -> Nat -> FEl)
            -- it is never complete ...
            (bt : (t c : Nat) -> Bt (AVF t c))
            -- ... and every coordinate is monotone with `PhiOK` heights
            (regK : Nat -> Nat)
            (regP : (c : Nat) -> LeN (suc c) (suc q')
                  -> Or (ConstFrom (regK c) (\ t -> hgt (AVF t c)))
                        (StrictIncFrom (regK c) (\ t -> hgt (AVF t c))))
            (avm : (t c : Nat) -> LeN (hgt (AVF t c)) (hgt (AVF (suc t) c)))
            -- MP1 for the trace being fed: the value clause ...
            (ovm : (m n : Nat) -> LeN m n -> LeF (ov m) (ov n))
            (vrd : Verdict ov)
            -- ... and the index clause
            (evc : EvConstN iv)
            where

  q : Nat
  q = suc q'

  T : Tr q
  T = node iv ivr ov cont

  Y : Nat -> FTup
  Y t = tup q (AVF t)

  FV : Nat -> FEl
  FV t = sem q T (Y t)

  A : Nat -> Nat -> Nat
  A t = hts (Y t)

  M : Nat -> Nat
  M t = nOf q iv ivr (A t)

  LV : Nat -> Nat -> Nat
  LV = lv q iv ivr

  H : Nat -> Nat
  H n = hgt (ov n)

  ----------------------------------------------------------------------
  -- the coordinates
  ----------------------------------------------------------------------

  A-in : (t c : Nat) -> LeN (suc c) q -> Eq (A t c) (hgt (AVF t c))
  A-in t c lc = Eq-cong hgt (tup-nth q (AVF t) c lc)

  A-out : (c : Nat) -> Not (LeN (suc c) q) -> (t : Nat) -> Eq (A t c) zero
  A-out c nc t = Eq-cong hgt (tup-out q (AVF t) c nc)

  A-mono : (t c : Nat) -> LeN (A t c) (A (suc t) c)
  A-mono t c = route (LeN-dec (suc c) q)
    where
      route : Dec (LeN (suc c) q) -> LeN (A t c) (A (suc t) c)
      route (yes lc) =
        Eq-transport (\ z -> LeN z (A (suc t) c)) (Eq-sym (A-in t c lc))
          (Eq-transport (\ z -> LeN (hgt (AVF t c)) z) (Eq-sym (A-in (suc t) c lc))
            (avm t c))
      route (no nc) =
        Eq-transport (\ z -> LeN z (A (suc t) c)) (Eq-sym (A-out c nc t))
          (Eq-transport (\ z -> LeN zero z) (Eq-sym (A-out c nc (suc t))) tt)

  A-mono-le : (t t' : Nat) -> LeN t t' -> (c : Nat) -> LeN (A t c) (A t' c)
  A-mono-le t zero     le c =
    Eq-transport (\ z -> LeN (A z c) (A zero c))
      (Eq-sym (LeN-antisym {t} {zero} le tt)) (LeN-refl (A zero c))
  A-mono-le t (suc t') le c = route (LeN-dec t t')
    where
      route : Dec (LeN t t') -> LeN (A t c) (A (suc t') c)
      route (yes l) =
        LeN-trans {A t c} {A t' c} {A (suc t') c} (A-mono-le t t' l c) (A-mono t' c)
      route (no nl) =
        Eq-transport (\ z -> LeN (A z c) (A (suc t') c))
          (Eq-sym (eq' t t' le nl)) (LeN-refl (A (suc t') c))
        where
          eq' : (x y : Nat) -> LeN x (suc y) -> Not (LeN x y) -> Eq x (suc y)
          eq' zero    y       l nl' = Empty-elim (nl' tt)
          eq' (suc x) zero    l nl' = Eq-cong suc (LeN-antisym {x} {zero} l tt)
          eq' (suc x) (suc y) l nl' = Eq-cong suc (eq' x y l nl')

  M-mono : (t t' : Nat) -> LeN t t' -> LeN (M t) (M t')
  M-mono t t' le = nOf-mono q iv ivr (A t) (A t') (A-mono-le t t' le)

  ----------------------------------------------------------------------
  -- NOTHING IS COMPLETE, SO THE SEMANTICS IS ONE LOOKUP
  ----------------------------------------------------------------------

  botify : (t : Nat) -> Eq (Y t) (botTup q (A t))
  botify t = tup-cong-le q (AVF t) (\ c -> fbot (A t c)) pt
    where
      pt : (c : Nat) -> LeN (suc c) q -> Eq (AVF t c) (fbot (A t c))
      pt c lc =
        Eq-transport (\ z -> Eq (AVF t c) (fbot z)) (Eq-sym (A-in t c lc)) (bt t c)

  look : (t : Nat) -> Eq (FV t) (ov (M t))
  look t =
    Eq-trans (Eq-cong (\ X -> sem q T X) (botify t))
      (sem-bot q T (A t) (\ c nc -> A-out c nc t))

  ----------------------------------------------------------------------
  -- THE REPLAY IS STUCK ON ONE COORDINATE
  ----------------------------------------------------------------------

  D : Nat -> Nat
  D t = iv (M t)

  Dr : (t : Nat) -> LeN (suc (D t)) q
  Dr t = ivr (M t)

  blocked : (t : Nat) -> LeN (A t (D t)) (LV (D t) (M t))
  blocked t =
    nle-lt (suc (LV (D t) (M t))) (A t (D t)) (stuck q iv ivr (A t))

  below : (t c : Nat) -> LeN (LV c (M t)) (A t c)
  below t = nOf-below q iv ivr (A t)

  ----------------------------------------------------------------------
  -- CONSTANT COORDINATE  ==>  THE REPLAY IS FROZEN FOR EVER
  ----------------------------------------------------------------------

  frozen : (t : Nat) -> LeN (regK (D t)) t
         -> ConstFrom (regK (D t)) (\ s -> hgt (AVF s (D t)))
         -> (t' : Nat) -> LeN t t' -> Eq (M t') (M t)
  frozen t lk cf t' lt =
    LeN-antisym {M t'} {M t} (nOf-le q iv ivr (A t') (M t) still)
      (M-mono t t' lt)
    where
      same : Eq (A t' (D t)) (A t (D t))
      same =
        Eq-trans (A-in t' (D t) (Dr t))
          (Eq-trans (Eq-trans (cf t' (LeN-trans {regK (D t)} {t} {t'} lk lt))
                      (Eq-sym (cf t lk)))
            (Eq-sym (A-in t (D t) (Dr t))))

      still : Not (Adv q iv ivr (A t') (M t))
      still ad =
        suc-not (LV (D t) (M t))
          (LeN-trans {suc (LV (D t) (M t))} {A t (D t)} {LV (D t) (M t)}
            (Eq-transport (\ z -> LeN (suc (LV (D t) (M t))) z) same ad)
            (blocked t))

  ----------------------------------------------------------------------
  -- STRICTLY INCREASING COORDINATE  ==>  THE REPLAY ADVANCES
  ----------------------------------------------------------------------

  advance : (t : Nat) -> LeN (regK (D t)) t
          -> StrictIncFrom (regK (D t)) (\ s -> hgt (AVF s (D t)))
          -> LeN (suc (M t)) (M (suc t))
  advance t lk si =
    le-ne-lt (M t) (M (suc t)) (M-mono t (suc t) (LeN-suc t)) ne
    where
      -- the coordinate the replay waits on grows, and that is exactly the
      -- level it was waiting for
      ad : Adv q iv ivr (A (suc t)) (M t)
      ad =
        Eq-transport (\ z -> LeN (suc (LV (D t) (M t))) z)
          (Eq-sym (A-in (suc t) (D t) (Dr t)))
          (LeN-trans {suc (LV (D t) (M t))} {suc (hgt (AVF t (D t)))}
                     {hgt (AVF (suc t) (D t))}
            (Eq-transport (\ z -> LeN (LV (D t) (M t)) z) (A-in t (D t) (Dr t))
              (below t (D t)))
            (si t lk))

      ne : Not (Eq (M (suc t)) (M t))
      ne e = stuck q iv ivr (A (suc t)) (Eq-transport (\ z -> Adv q iv ivr (A (suc t)) z) (Eq-sym e) ad)

  ----------------------------------------------------------------------
  -- THE DICHOTOMY AT ONE TIME, PAST ALL THE THRESHOLDS
  ----------------------------------------------------------------------

  K : Nat
  K = maxTo q regK

  lK : (c : Nat) -> LeN (suc c) q -> LeN (regK c) K
  lK c lc = maxTo-ge q regK c lc

  Frozen : Nat -> Set
  Frozen t = (t' : Nat) -> LeN t t' -> Eq (M t') (M t)

  dich : (t : Nat) -> LeN K t -> Or (Frozen t) (LeN (suc (M t)) (M (suc t)))
  dich t lt = route (regP (D t) (Dr t))
    where
      lk : LeN (regK (D t)) t
      lk = LeN-trans {regK (D t)} {K} {t} (lK (D t) (Dr t)) lt

      route : Or (ConstFrom (regK (D t)) (\ s -> hgt (AVF s (D t))))
                 (StrictIncFrom (regK (D t)) (\ s -> hgt (AVF s (D t))))
            -> Or (Frozen t) (LeN (suc (M t)) (M (suc t)))
      route (inl cf) = inl (frozen t lk cf)
      route (inr si) = inr (advance t lk si)

  ----------------------------------------------------------------------
  -- THE BOUNDED SEARCH
  ----------------------------------------------------------------------

  Ng : Nat
  Ng = fst evc

  iv-const : (n : Nat) -> LeN Ng n -> Eq (iv n) (iv Ng)
  iv-const = snd evc

  -- either the replay freezes, or it has climbed `t` times since `K`
  climb : (t : Nat) -> Or (Sigma Nat Frozen) (LeN t (M (pl K t)))
  climb zero    = inr tt
  climb (suc t) = route (climb t)
    where
      route : Or (Sigma Nat Frozen) (LeN t (M (pl K t)))
            -> Or (Sigma Nat Frozen) (LeN (suc t) (M (pl K (suc t))))
      route (inl w)  = inl w
      route (inr le) = pick (dich (pl K t) (pl-ge K t))
        where
          pick : Or (Frozen (pl K t)) (LeN (suc (M (pl K t))) (M (suc (pl K t))))
               -> Or (Sigma Nat Frozen) (LeN (suc t) (M (suc (pl K t))))
          pick (inl fz) = inl (mkSigma (pl K t) fz)
          pick (inr gr) =
            inr (LeN-trans {suc t} {suc (M (pl K t))} {M (suc (pl K t))} le gr)

  ----------------------------------------------------------------------
  -- FROZEN  ==>  THE VALUE SETTLES
  ----------------------------------------------------------------------

  frozen-const : (t0 : Nat) -> Frozen t0 -> ConstFrom t0 (\ t -> hgt (FV t))
  frozen-const t0 fz t lt =
    Eq-trans (Eq-cong hgt (look t))
      (Eq-trans (Eq-cong H (fz t lt)) (Eq-sym (Eq-cong hgt (look t0))))

  frozen-never : (t0 : Nat) -> Frozen t0 -> Not (IsCpl (ov (M t0)))
               -> (t : Nat) -> LeN t0 t -> Not (IsCpl (FV t))
  frozen-never t0 fz nc t lt ic =
    nc (Eq-transport (\ z -> IsCpl (ov z)) (fz t lt)
         (Eq-transport (\ z -> IsCpl z) (look t) ic))

  ----------------------------------------------------------------------
  -- COMPLETENESS TRAVELS DOWNWARDS
  ----------------------------------------------------------------------

  notCpl-below : (n n' : Nat) -> LeN n n' -> Not (IsCpl (ov n')) -> Not (IsCpl (ov n))
  notCpl-below n n' le nc ic =
    nc (Eq-transport (\ z -> IsCpl z) (cpl-max (ov n) (ov n') (ovm n n' le) ic) ic)

  frozen-bt : (t0 : Nat) -> Frozen t0 -> Not (IsCpl (ov (M t0))) -> (t : Nat) -> Bt (FV t)
  frozen-bt t0 fz nc t = notCpl-bt (FV t) go
    where
      nco : Not (IsCpl (ov (M t)))
      nco = route (LeN-dec t t0)
        where
          route : Dec (LeN t t0) -> Not (IsCpl (ov (M t)))
          route (yes l)  = notCpl-below (M t) (M t0) (M-mono t t0 l) nc
          route (no  nl) =
            Eq-transport (\ z -> Not (IsCpl (ov z)))
              (Eq-sym (fz t (LeN-trans {t0} {suc t0} {t} (LeN-suc t0) (nle-lt t t0 nl))))
              nc

      go : Not (IsCpl (FV t))
      go ic = nco (Eq-transport (\ z -> IsCpl z) (look t) ic)

  ----------------------------------------------------------------------
  -- THE FROZEN OUTCOME, ASSEMBLED
  ----------------------------------------------------------------------

  frozen-verdict : (t0 : Nat) -> Frozen t0 -> Verdict FV
  frozen-verdict t0 fz = route (IsCpl-dec (ov (M t0)))
    where
      IsCpl-dec : (x : FEl) -> Dec (IsCpl x)
      IsCpl-dec (fbot k) = no  (\ z -> z)
      IsCpl-dec (fcpl k) = yes tt

      route : Dec (IsCpl (ov (M t0))) -> Verdict FV
      route (yes ic) =
        inl (mkSigma t0 (Eq-transport (\ z -> IsCpl z) (Eq-sym (look t0)) ic))
      route (no  nc) =
        inr (mkSigma (frozen-bt t0 fz nc)
              (mkSigma t0 (inl (frozen-const t0 fz))))

  ----------------------------------------------------------------------
  -- NEVER FROZEN: PAST `K + Ng` THE STUCK COORDINATE IS THE EVENTUAL
  -- DEMAND, SO ONE `regP` SETTLES THE REGIME FOR EVER
  ----------------------------------------------------------------------

  I : Nat
  I = iv Ng

  Ir : LeN (suc I) q
  Ir = ivr Ng

  eD : (t : Nat) -> LeN Ng (M t) -> Eq (D t) I
  eD t le = iv-const (M t) le

  lKt : (t : Nat) -> LeN K t -> LeN (regK (D t)) t
  lKt t lt = LeN-trans {regK (D t)} {K} {t} (lK (D t) (Dr t)) lt

  -- the strictly-increasing regime, transported to the stuck coordinate
  si-at : StrictIncFrom (regK I) (\ s -> hgt (AVF s I))
        -> (t : Nat) -> LeN Ng (M t)
        -> StrictIncFrom (regK (D t)) (\ s -> hgt (AVF s (D t)))
  si-at si t le =
    Eq-transport (\ z -> StrictIncFrom (regK z) (\ s -> hgt (AVF s z)))
      (Eq-sym (eD t le)) si

  cf-at : ConstFrom (regK I) (\ s -> hgt (AVF s I))
        -> (t : Nat) -> LeN Ng (M t)
        -> ConstFrom (regK (D t)) (\ s -> hgt (AVF s (D t)))
  cf-at cf t le =
    Eq-transport (\ z -> ConstFrom (regK z) (\ s -> hgt (AVF s z)))
      (Eq-sym (eD t le)) cf

  ----------------------------------------------------------------------
  -- THE STRICTLY INCREASING RUN
  ----------------------------------------------------------------------

  module RUN (Base : Nat) (lKB : LeN K Base) (lNB : LeN Ng (M Base))
             (si : StrictIncFrom (regK I) (\ s -> hgt (AVF s I)))
             where

    go : (t : Nat)
       -> Pair (LeN Ng (M (pl Base t)))
               (LeN (suc (M (pl Base t))) (M (suc (pl Base t))))
    go zero    =
      mkSigma lNB
        (advance Base (lKt Base lKB) (si-at si Base lNB))
    go (suc t) = mkSigma lN' (advance j (lKt j lKj) (si-at si j lN'))
      where
        j : Nat
        j = suc (pl Base t)

        ih : Pair (LeN Ng (M (pl Base t)))
                  (LeN (suc (M (pl Base t))) (M (suc (pl Base t))))
        ih = go t

        lN' : LeN Ng (M j)
        lN' =
          LeN-trans {Ng} {M (pl Base t)} {M j} (fst ih)
            (M-mono (pl Base t) j (LeN-suc (pl Base t)))

        lKj : LeN K j
        lKj =
          LeN-trans {K} {Base} {j} lKB
            (LeN-trans {Base} {pl Base t} {j} (pl-ge Base t) (LeN-suc (pl Base t)))

    at : (m : Nat) -> LeN Base m
       -> Pair (LeN Ng (M m)) (LeN (suc (M m)) (M (suc m)))
    at m lm = lift (le-pl Base m lm)
      where
        lift : Sigma Nat (\ t -> Eq m (pl Base t))
             -> Pair (LeN Ng (M m)) (LeN (suc (M m)) (M (suc m)))
        lift (mkSigma t e) =
          Eq-transport
            (\ z -> Pair (LeN Ng (M z)) (LeN (suc (M z)) (M (suc z)))) (Eq-sym e) (go t)

  ----------------------------------------------------------------------
  -- THE VERDICT
  ----------------------------------------------------------------------

  never-of : Never ov -> (t : Nat) -> Bt (FV t)
  never-of nev t =
    Eq-transport (\ z -> Eq z (fbot (hgt z))) (Eq-sym (look t)) (nev (M t))

  -- Case `EvTot ov`: either the replay reaches the answering depth, or it
  -- freezes short of it
  tot-verdict : (n0 : Nat) -> IsCpl (ov n0) -> Verdict FV
  tot-verdict n0 cn0 = route (climb n0)
    where
      cpl-above : (n : Nat) -> LeN n0 n -> IsCpl (ov n)
      cpl-above n ln =
        Eq-transport (\ z -> IsCpl z) (cpl-max (ov n0) (ov n) (ovm n0 n ln) cn0) cn0

      route : Or (Sigma Nat Frozen) (LeN n0 (M (pl K n0))) -> Verdict FV
      route (inl (mkSigma t0 fz)) = frozen-verdict t0 fz
      route (inr le) =
        inl (mkSigma (pl K n0)
              (Eq-transport (\ z -> IsCpl z) (Eq-sym (look (pl K n0)))
                (cpl-above (M (pl K n0)) le)))

  -- Case `Never ov`: the value never answers, and its height is `PhiOK`
  nev-verdict : Never ov -> PhiOK H -> Verdict FV
  nev-verdict nev pk =
    inr (mkSigma (never-of nev) (split pk))
    where
      split : PhiOK H -> PhiOK (\ t -> hgt (FV t))
      --------------------------------------------------------------
      -- the fed trace's own height settles
      --------------------------------------------------------------
      split (mkSigma k0 (inl cf)) = route (climb k0)
        where
          route : Or (Sigma Nat Frozen) (LeN k0 (M (pl K k0)))
                -> PhiOK (\ t -> hgt (FV t))
          route (inl (mkSigma t0 fz)) = mkSigma t0 (inl (frozen-const t0 fz))
          route (inr le) = mkSigma (pl K k0) (inl con)
            where
              at : (t : Nat) -> LeN (pl K k0) t -> Eq (hgt (FV t)) (H k0)
              at t lt =
                Eq-trans (Eq-cong hgt (look t))
                  (cf (M t)
                    (LeN-trans {k0} {M (pl K k0)} {M t} le (M-mono (pl K k0) t lt)))

              con : ConstFrom (pl K k0) (\ t -> hgt (FV t))
              con t lt = Eq-trans (at t lt) (Eq-sym (at (pl K k0) (LeN-refl (pl K k0))))
      --------------------------------------------------------------
      -- ... or it grows, and then so does the composite's, provided the
      -- replay never freezes -- which `regP I` decides outright
      --------------------------------------------------------------
      split (mkSigma k0 (inr si)) = route (climb B)
        where
          B : Nat
          B = maxN k0 Ng

          Base : Nat
          Base = pl K B

          route : Or (Sigma Nat Frozen) (LeN B (M Base)) -> PhiOK (\ t -> hgt (FV t))
          route (inl (mkSigma t0 fz)) = mkSigma t0 (inl (frozen-const t0 fz))
          route (inr le) = decide (regP I Ir)
            where
              lNB : LeN Ng (M Base)
              lNB = LeN-trans {Ng} {B} {M Base} (maxN-le-r k0 Ng) le

              lk0B : LeN k0 (M Base)
              lk0B = LeN-trans {k0} {B} {M Base} (maxN-le-l k0 Ng) le

              lKB : LeN K Base
              lKB = pl-ge K B

              decide : Or (ConstFrom (regK I) (\ s -> hgt (AVF s I)))
                          (StrictIncFrom (regK I) (\ s -> hgt (AVF s I)))
                     -> PhiOK (\ t -> hgt (FV t))
              -- the eventual demand settles: the replay freezes here
              decide (inl cf) =
                mkSigma Base
                  (inl (frozen-const Base
                         (frozen Base (lKt Base lKB) (cf-at cf Base lNB))))
              -- the eventual demand keeps growing: the replay never freezes
              decide (inr si') = mkSigma Base (inr inc)
                where
                  open RUN Base lKB lNB si'

                  inc : StrictIncFrom Base (\ t -> hgt (FV t))
                  inc m lm =
                    Eq-transport (\ z -> LeN (suc z) (hgt (FV (suc m))))
                      (Eq-sym (Eq-cong hgt (look m)))
                      (Eq-transport (\ z -> LeN (suc (H (M m))) z)
                        (Eq-sym (Eq-cong hgt (look (suc m))))
                        (sinc-mono-lt k0 H si (M m) (M (suc m))
                          (LeN-trans {k0} {M Base} {M m} lk0B (M-mono Base m lm))
                          (snd (at m lm))))

  feed-verdict : Verdict FV
  feed-verdict = route vrd
    where
      route : Verdict ov -> Verdict FV
      route (inl (mkSigma n0 cn0))  = tot-verdict n0 cn0
      route (inr (mkSigma nev pk))  = nev-verdict nev pk
