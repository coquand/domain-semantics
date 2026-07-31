{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecDecMP
--
-- **DOES THE RECURSION CHAIN EVER BECOME A NUMERAL? -- DECIDED FROM THE
-- STEP TERM'S OWN VERDICT, WITH NO USE OF PROPOSITION 1.**
--
--     DEC.decide : Or (Sigma Nat (\ j0 -> IsCpl (V j0)))
--                     ((j : Nat) -> Not (IsCpl (V j)))
--
-- for  f(bot,Y) = bot ,  f(S^(j+1) bot, Y) = g(S^j bot, f(S^j bot,Y), Y).
--
-- This replaces `TrPrecDec.Vd-tot-or-never`, which took
-- `UO (precFun g h)` -- Proposition 1 for THE RECURSION ITSELF -- as a
-- hypothesis.  Here the only input is `TrMP1.Verdict ovh`, i.e. the
-- INDUCTION HYPOTHESIS: MP1 for the step term `g`.
--
-- THE ARGUMENT.  While the chain value `V j` is incomplete, every
-- coordinate of `g`'s argument tuple is a `fbot`, so
-- (`TrPrecChain.step`)
--
--     V (j+1) = ovh (NJ j)        NJ j = g's replay depth at depth j.
--
--   * `Never ovh` -- `g` never answers on such a tuple -- gives the right
--     branch by induction at once.
--
--   * `EvTot ovh` at `n0` -- `ovh n` is complete for every `n >= n0`,
--     since completeness is maximal and `ovh` is monotone.  So scan
--     `V 0 , ... , V B` for `B = 2*n0+1`; if one is complete, the left
--     branch.  If none is, then `NJ i < n0` for every `i < B`, and `NJ`
--     is monotone, so a REPEAT `NJ (i+1) = NJ i` must occur with
--     `n0 <= i` -- otherwise `NJ` would have climbed `n0+1` times and
--     passed `n0`.  A repeat at such an `i` FREEZES: past it the two
--     height vectors differ only in coordinate 0 (the recursion
--     argument), both are already at least `n0` there, and the replay
--     stops strictly below `n0` -- which is exactly `ReplayLv.nOf-sat`.
--     So `V` is constant from `i+1` on, and never complete.
--
-- The recursion argument is the ONLY coordinate that grows on its own, so
-- saturating it is what turns "the replay stalled once" into "the replay
-- has stalled for ever".  Nothing here is about `f`; everything is read
-- off `g`'s trace.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecDecMP where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.BlkReplay using (nle-lt ; le-ne-lt)
open import OBSTINATION.ReplayLv using (nOf ; nOf-mono ; nOf-sat)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using (IsCpl ; cpl-max ; leF-hgt ; MonoTr)
open import OBSTINATION.TrMP1 using (EvTot ; Never ; Verdict)
open import OBSTINATION.TrPrec using (module R)
open import OBSTINATION.TrPrecChain using (Bt ; bt-notCpl ; notCpl-bt ; module CH)

------------------------------------------------------------------------
-- SMALL ARITHMETIC: an addition that recurses on the SECOND argument, so
-- that an induction "from a fixed start" reduces
------------------------------------------------------------------------

pl : Nat -> Nat -> Nat
pl x zero    = x
pl x (suc t) = suc (pl x t)

pl-ge : (x t : Nat) -> LeN x (pl x t)
pl-ge x zero    = LeN-refl x
pl-ge x (suc t) = LeN-trans {x} {pl x t} {suc (pl x t)} (pl-ge x t) (LeN-suc (pl x t))

-- every point above `x` is `x` plus something
le-pl : (x m : Nat) -> LeN x m -> Sigma Nat (\ t -> Eq m (pl x t))
le-pl zero    m       lm = mkSigma m (go m)
  where
    go : (k : Nat) -> Eq k (pl zero k)
    go zero    = refl
    go (suc k) = Eq-cong suc (go k)
le-pl (suc x) zero    ()
le-pl (suc x) (suc m) lm = bump (le-pl x m lm)
  where
    bump : Sigma Nat (\ t -> Eq m (pl x t)) -> Sigma Nat (\ t -> Eq (suc m) (pl (suc x) t))
    bump (mkSigma t e) = mkSigma t (Eq-trans (Eq-cong suc e) (shift x t))
      where
        shift : (y s : Nat) -> Eq (suc (pl y s)) (pl (suc y) s)
        shift y zero    = refl
        shift y (suc s) = Eq-cong suc (shift y s)

IsCpl-dec : (x : FEl) -> Dec (IsCpl x)
IsCpl-dec (fbot k) = no  (\ z -> z)
IsCpl-dec (fcpl k) = yes tt

-- bottom is least
leF-bot : (y : FEl) -> LeF (fbot zero) y
leF-bot (fbot k) = tt
leF-bot (fcpl k) = tt

------------------------------------------------------------------------
-- THE DECISION
------------------------------------------------------------------------

module DEC (p : Nat)
           (ivh : Nat -> Nat)
           (ivhr : (n : Nat) -> LeN (suc (ivh n)) (suc (suc p)))
           (ovh : Nat -> FEl)
           (conth : (c : Nat) -> LeN (suc c) (suc (suc p)) -> (v : Nat)
                  -> Tr (suc p))
           (L : Nat -> Nat)
           -- the step term's trace is monotone ...
           (ov-mono : (m n : Nat) -> LeN m n -> LeF (ovh m) (ovh n))
           -- ... and the chain is monotone in the depth (`TrPrecDec.Vd-mono`,
           -- which uses `Den` and `MonoF` only -- never Proposition 1)
           (V-mono : (j j' : Nat) -> LeN j j'
                   -> LeF (R.Vd p (node ivh ivhr ovh conth) L j)
                          (R.Vd p (node ivh ivhr ovh conth) L j'))
           -- THE INDUCTION HYPOTHESIS: MP1's value clause for the step term
           (vrd : Or (EvTot ovh) (Never ovh))
           where

  open CH p ivh ivhr ovh conth L

  ----------------------------------------------------------------------
  -- the replay depth is monotone, because the heights are
  ----------------------------------------------------------------------

  AV-mono : (j j' : Nat) -> LeN j j' -> (c : Nat) -> LeN (AV j c) (AV j' c)
  AV-mono j j' le c = route (LeN-dec (suc c) a)
    where
      route : Dec (LeN (suc c) a) -> LeN (AV j c) (AV j' c)
      route (no nc) =
        Eq-transport (\ z -> LeN z (AV j' c)) (Eq-sym (AV-out c nc j))
          (Eq-transport (\ z -> LeN zero z) (Eq-sym (AV-out c nc j')) tt)
      route (yes lc) = shape c lc
        where
          shape : (d : Nat) -> LeN (suc d) a -> LeN (AV j d) (AV j' d)
          shape zero ld =
            Eq-transport (\ z -> LeN z (AV j' zero)) (Eq-sym (AV-zero j))
              (Eq-transport (\ z -> LeN j z) (Eq-sym (AV-zero j')) le)
          shape (suc zero) ld =
            Eq-transport (\ z -> LeN z (AV j' (suc zero))) (Eq-sym (AV-one j))
              (Eq-transport (\ z -> LeN (hgt (V j)) z) (Eq-sym (AV-one j'))
                (leF-hgt (V j) (V j') (V-mono j j' le)))
          shape (suc (suc i)) ld =
            Eq-transport (\ z -> LeN (AV j (suc (suc i))) z)
              (AV-par i j j' ld) (LeN-refl (AV j (suc (suc i))))

  NJ-mono : (j j' : Nat) -> LeN j j' -> LeN (NJ j) (NJ j')
  NJ-mono j j' le = nOf-mono a ivh ivhr (AV j) (AV j') (AV-mono j j' le)

  ----------------------------------------------------------------------
  -- CASE `Never`: the chain never answers
  ----------------------------------------------------------------------

  never-chain : Never ovh -> (j : Nat) -> Bt (V j)
  never-chain nv zero    = refl
  never-chain nv (suc j) =
    Eq-transport (\ z -> Eq z (fbot (hgt z))) (Eq-sym (step j (never-chain nv j)))
      (nv (NJ j))

  ----------------------------------------------------------------------
  -- CASE `EvTot`: the bounded scan, the repeat, and the freeze
  ----------------------------------------------------------------------

  module TOT (n0 : Nat) (cn0 : IsCpl (ovh n0)) where

    -- past `n0` the step term's recorded value is complete: completeness
    -- is maximal, and `ovh` is monotone
    cpl-above : (n : Nat) -> LeN n0 n -> IsCpl (ovh n)
    cpl-above n ln =
      Eq-transport (\ z -> IsCpl z) (cpl-max (ovh n0) (ovh n) (ov-mono n0 n ln) cn0) cn0

    -- so an incomplete chain value pins the replay strictly below `n0`
    nj-small : (i : Nat) -> Bt (V (suc i)) -> LeN (suc (NJ i)) n0
    nj-small i bv = nle-lt n0 (NJ i) nl
      where
        nl : Not (LeN n0 (NJ i))
        nl l =
          bt-notCpl (V (suc i)) bv
            (Eq-transport (\ z -> IsCpl z) (Eq-sym (step i (bt-prev i bv)))
              (cpl-above (NJ i) l))
          where
            -- `V i` is incomplete too: it is below `V (suc i)`, which is
            bt-prev : (k : Nat) -> Bt (V (suc k)) -> Bt (V k)
            bt-prev k b = notCpl-bt (V k) nc
              where
                nc : Not (IsCpl (V k))
                nc ic =
                  bt-notCpl (V (suc k)) b
                    (Eq-transport (\ z -> IsCpl z)
                      (cpl-max (V k) (V (suc k)) (V-mono k (suc k) (LeN-suc k)) ic) ic)

    ------------------------------------------------------------------
    -- the scan
    ------------------------------------------------------------------

    Scan : Nat -> Set
    Scan k = (i : Nat) -> LeN i k -> Bt (V i)

    scan : (k : Nat) -> Or (Sigma Nat (\ j0 -> IsCpl (V j0))) (Scan k)
    scan zero = inr (\ i li ->
      Eq-transport (\ z -> Bt (V z)) (Eq-sym (LeN-antisym {i} {zero} li tt)) refl)
    scan (suc k) = route (scan k)
      where
        route : Or (Sigma Nat (\ j0 -> IsCpl (V j0))) (Scan k)
              -> Or (Sigma Nat (\ j0 -> IsCpl (V j0))) (Scan (suc k))
        route (inl w)  = inl w
        route (inr sc) = here (IsCpl-dec (V (suc k)))
          where
            here : Dec (IsCpl (V (suc k)))
                 -> Or (Sigma Nat (\ j0 -> IsCpl (V j0))) (Scan (suc k))
            here (yes ic) = inl (mkSigma (suc k) ic)
            here (no  nc) = inr ext
              where
                ext : Scan (suc k)
                ext i li = pick (LeN-dec i k)
                  where
                    pick : Dec (LeN i k) -> Bt (V i)
                    pick (yes l)  = sc i l
                    pick (no  nl) =
                      Eq-transport (\ z -> Bt (V z)) (Eq-sym (eq' i k li nl))
                        (notCpl-bt (V (suc k)) nc)
                      where
                        eq' : (x y : Nat) -> LeN x (suc y) -> Not (LeN x y)
                            -> Eq x (suc y)
                        eq' zero    y       l nl' = Empty-elim (nl' tt)
                        eq' (suc x) zero    l nl' =
                          Eq-cong suc (LeN-antisym {x} {zero} l tt)
                        eq' (suc x) (suc y) l nl' = Eq-cong suc (eq' x y l nl')

    ------------------------------------------------------------------
    -- the bound, and the repeat
    ------------------------------------------------------------------

    B : Nat
    B = suc (pl n0 n0)

    Rep : Set
    Rep = Sigma Nat (\ i -> Pair (LeN n0 i)
                       (Pair (LeN (suc i) B) (Eq (NJ (suc i)) (NJ i))))

    -- either a repeat is found at or after `n0`, or `NJ` has climbed `t` times
    search : Scan B -> (t : Nat) -> LeN t n0 -> Or Rep (LeN t (NJ (pl n0 t)))
    search sc zero    lt = inr tt
    search sc (suc t) lt = route (search sc t lt')
      where
        lt' : LeN t n0
        lt' = LeN-trans {t} {suc t} {n0} (LeN-suc t) lt

        i : Nat
        i = pl n0 t

        li : LeN n0 i
        li = pl-ge n0 t

        -- `i+1 <= B`, so `Scan B` covers `V (i+1)`
        lB : LeN (suc i) B
        lB = plus-le t n0 lt'
          where
            plus-le : (s y : Nat) -> LeN s y -> LeN (suc (pl y s)) (suc (pl y y))
            plus-le s y ls = mono y s y ls
              where
                mono : (z u v : Nat) -> LeN u v -> LeN (pl z u) (pl z v)
                mono z zero    v       lu = pl-ge z v
                mono z (suc u) zero    ()
                mono z (suc u) (suc v) lu = mono z u v lu

        route : Or Rep (LeN t (NJ i)) -> Or Rep (LeN (suc t) (NJ (pl n0 (suc t))))
        route (inl r)  = inl r
        route (inr le) = dec (EqNat-dec (NJ (suc i)) (NJ i))
          where
            dec : Dec (Eq (NJ (suc i)) (NJ i))
                -> Or Rep (LeN (suc t) (NJ (suc i)))
            dec (yes e) = inl (mkSigma i (mkSigma li (mkSigma lB e)))
            dec (no ne) =
              inr (LeN-trans {suc t} {suc (NJ i)} {NJ (suc i)} le
                     (le-ne-lt (NJ i) (NJ (suc i))
                       (NJ-mono i (suc i) (LeN-suc i)) ne))

    findRep : Scan B -> Rep
    findRep sc = finish (search sc n0 (LeN-refl n0))
      where
        finish : Or Rep (LeN n0 (NJ (pl n0 n0))) -> Rep
        finish (inl r)  = r
        finish (inr le) =
          Empty-elim
            (LeN-suc-not (NJ (pl n0 n0))
              (LeN-trans {suc (NJ (pl n0 n0))} {n0} {NJ (pl n0 n0)}
                (nj-small (pl n0 n0) (sc (suc (pl n0 n0)) (LeN-refl B))) le))
          where
            LeN-suc-not : (x : Nat) -> Not (LeN (suc x) x)
            LeN-suc-not zero    ()
            LeN-suc-not (suc x) l = LeN-suc-not x l

    ------------------------------------------------------------------
    -- THE FREEZE
    --
    -- Past a repeat at `i >= n0` the chain is constant.  `nOf-sat` is the
    -- whole content: the two height vectors differ only in coordinate 0,
    -- both offer at least `n0` there, and the replay sticks strictly
    -- below `n0` -- so coordinate 0 cannot matter, and the replay depth
    -- is the same.
    ------------------------------------------------------------------

    module FRZ (sc : Scan B) (i : Nat) (li : LeN n0 i)
               (lB : LeN (suc i) B) (rep : Eq (NJ (suc i)) (NJ i)) where

      -- the replay at `i+1` is already below `n0`
      small : Not (LeN n0 (NJ (suc i)))
      small l =
        LeN-suc-not (NJ i)
          (LeN-trans {suc (NJ i)} {n0} {NJ i}
            (nj-small i (sc (suc i) lB))
            (Eq-transport (\ z -> LeN n0 z) rep l))
        where
          LeN-suc-not : (x : Nat) -> Not (LeN (suc x) x)
          LeN-suc-not zero    ()
          LeN-suc-not (suc x) l' = LeN-suc-not x l'

      -- a depth at which the chain has the same value has the same replay
      same-nj : (m : Nat) -> LeN i m -> Eq (V (suc m)) (V (suc i))
              -> Eq (NJ (suc i)) (NJ (suc m))
      same-nj m lm ev =
        nOf-sat a ivh ivhr (AV (suc i)) (AV (suc m)) n0 zero agree
          (Eq-transport (\ z -> LeN n0 z) (Eq-sym (AV-zero (suc i)))
            (LeN-trans {n0} {i} {suc i} li (LeN-suc i)))
          (Eq-transport (\ z -> LeN n0 z) (Eq-sym (AV-zero (suc m)))
            (LeN-trans {n0} {m} {suc m}
              (LeN-trans {n0} {i} {m} li lm) (LeN-suc m)))
          small
        where
          agree : (d : Nat) -> Not (Eq d zero)
                -> Eq (AV (suc i) d) (AV (suc m) d)
          agree d nd = route (LeN-dec (suc d) a)
            where
              route : Dec (LeN (suc d) a) -> Eq (AV (suc i) d) (AV (suc m) d)
              route (no nc) =
                Eq-trans (AV-out d nc (suc i)) (Eq-sym (AV-out d nc (suc m)))
              route (yes lc) = shape d lc nd
                where
                  shape : (e : Nat) -> LeN (suc e) a -> Not (Eq e zero)
                        -> Eq (AV (suc i) e) (AV (suc m) e)
                  shape zero          le' ne = Empty-elim (ne refl)
                  shape (suc zero)    le' ne =
                    Eq-trans (AV-one (suc i))
                      (Eq-trans (Eq-cong hgt (Eq-sym ev)) (Eq-sym (AV-one (suc m))))
                  shape (suc (suc k)) le' ne = AV-par k (suc i) (suc m) le'

      bt-i : Bt (V i)
      bt-i = sc i (LeN-trans {i} {suc i} {B} (LeN-suc i) lB)

      -- ... so the chain is constant from `i+1` on
      frz : (t : Nat) -> Eq (V (suc (pl i t))) (V (suc i))
      frz zero    = refl
      frz (suc t) =
        Eq-trans (step (suc m) btm)
          (Eq-trans (Eq-cong ovh (Eq-sym (same-nj m (pl-ge i t) ih)))
            (Eq-trans (Eq-cong ovh rep) (Eq-sym (step i bt-i))))
        where
          m : Nat
          m = pl i t

          ih : Eq (V (suc m)) (V (suc i))
          ih = frz t

          btm : Bt (V (suc m))
          btm = Eq-transport (\ z -> Bt z) (Eq-sym ih) (sc (suc i) lB)

      -- ... hence never complete, at any depth
      never-cpl : (j : Nat) -> Not (IsCpl (V j))
      never-cpl zero    = bt-notCpl (V zero) refl
      never-cpl (suc m) = route (LeN-dec m i)
        where
          route : Dec (LeN m i) -> Not (IsCpl (V (suc m)))
          route (yes l) =
            bt-notCpl (V (suc m)) (sc (suc m) (LeN-trans {suc m} {suc i} {B} l lB))
          route (no nl) = bt-notCpl (V (suc m)) (lift (le-pl i m lmi))
            where
              lmi : LeN i m
              lmi = LeN-trans {i} {suc i} {m} (LeN-suc i) (nle-lt m i nl)

              lift : Sigma Nat (\ t -> Eq m (pl i t)) -> Bt (V (suc m))
              lift (mkSigma t e) =
                Eq-transport (\ z -> Bt (V (suc z))) (Eq-sym e)
                  (Eq-transport (\ z -> Bt z) (Eq-sym (frz t)) (sc (suc i) lB))

    ------------------------------------------------------------------
    -- the case `EvTot`, assembled
    ------------------------------------------------------------------

    decide-tot : Or (Sigma Nat (\ j0 -> IsCpl (V j0)))
                    ((j : Nat) -> Not (IsCpl (V j)))
    decide-tot = route (scan B)
      where
        route : Or (Sigma Nat (\ j0 -> IsCpl (V j0))) (Scan B)
              -> Or (Sigma Nat (\ j0 -> IsCpl (V j0)))
                    ((j : Nat) -> Not (IsCpl (V j)))
        route (inl w)  = inl w
        route (inr sc) = use (findRep sc)
          where
            use : Rep -> Or (Sigma Nat (\ j0 -> IsCpl (V j0)))
                            ((j : Nat) -> Not (IsCpl (V j)))
            use (mkSigma i (mkSigma li (mkSigma lB rep))) =
              inr (FRZ.never-cpl sc i li lB rep)

  ----------------------------------------------------------------------
  -- THE THEOREM
  ----------------------------------------------------------------------

  decide : Or (Sigma Nat (\ j0 -> IsCpl (V j0)))
              ((j : Nat) -> Not (IsCpl (V j)))
  decide = route vrd
    where
      route : Or (EvTot ovh) (Never ovh)
            -> Or (Sigma Nat (\ j0 -> IsCpl (V j0)))
                  ((j : Nat) -> Not (IsCpl (V j)))
      route (inl (mkSigma n0 cn0))  = TOT.decide-tot n0 cn0
      route (inr nv)                =
        inr (\ j -> bt-notCpl (V j) (never-chain nv j))
